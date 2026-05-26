#include "create-disp_shared.h"

namespace create_disp {

std::unordered_map<long long, int> g_hwc_to_drv;
std::unordered_map<int, long long> g_drv_to_hwc;
std::array<int, kMaxDriverDisplays> g_free_drv_ids = {};
int g_free_drv_count = 0;
bool g_free_drv_ids_initialized = false;
std::atomic<bool> drm_ready{false};
std::array<std::atomic<bool>, kMaxDriverDisplays> g_resync_pending{};

std::mutex g_display_mutex;
std::mutex g_buffer_mutex;
std::array<std::mutex, kMaxDriverDisplays> g_hwc_mutex;
std::shared_mutex g_drm_mutex;

std::atomic<uint32_t> g_update_wake_seq{0};
std::array<std::atomic<uint8_t>, kMaxDriverDisplays> g_update_work = {};
std::atomic<uint32_t> g_update_pending_mask{0};
std::atomic<int> g_update_rr{0};
std::thread g_update_thread;

std::atomic<bool> g_reopen_requested{false};
std::atomic<int> g_modeset_inflight{0};

std::thread g_present_thread;
std::atomic<uint32_t> g_present_ready_mask{0};
std::atomic<int> g_present_rr{0};
std::atomic<uint32_t> g_present_wake_seq{0};

std::thread g_poll_thread;
std::atomic<bool> g_running{true};

hwc2_compat_device_t* hwcDevice = nullptr;
int drm_fd = -1;

std::unordered_map<int, Display> g_displays;
std::array<DisplayRuntime, kMaxDriverDisplays> g_display_runtime;

std::array<std::atomic<BufferSegment*>, kBufferMaxSegments> g_buffer_segments{};
std::mutex g_buffer_segment_alloc_mutex;
std::atomic<uint32_t> g_next_buffer_id{1};
std::array<std::unordered_set<int>, kMaxDriverDisplays> g_display_bound_buffers;

std::array<PresentMailbox, kMaxDriverDisplays> g_present_mailboxes;

SpscRingBuffer<QueuedEvdiEvent, 256> g_evdi_event_queue;
std::atomic<uint32_t> g_evdi_event_wake_seq{0};
std::thread g_evdi_event_thread;

void request_reopen()
{
    (void)g_reopen_requested.exchange(true, std::memory_order_release);
}

int ioctl_retry(int fd, unsigned long req, void *arg)
{
    int rc;
    do {
        rc = ::ioctl(fd, req, arg);
    } while (rc < 0 && errno == EINTR);
    return rc;
}

int drm_get_fd()
{
    std::shared_lock<std::shared_mutex> lk(g_drm_mutex);
    return drm_fd;
}

void drm_shutdown_close_fd()
{
    std::unique_lock<std::shared_mutex> lk(g_drm_mutex);
    if (drm_fd >= 0) {
        ::close(drm_fd);
        drm_fd = -1;
    }
    drm_ready.store(false, std::memory_order_release);
}

int drm_ioctl(unsigned long req, void *arg)
{
    int fd = drm_get_fd();
    if (fd < 0) {
        errno = EBADF;
        return -1;
    }
    return ioctl_retry(fd, req, arg);
}

bool should_request_reopen(int err)
{
    return drm_ready.load(std::memory_order_acquire) &&
           (err == ENODEV || err == EBADF) &&
           g_modeset_inflight.load(std::memory_order_acquire) == 0;
}

void clear_pending_work_atomic(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    g_update_work[drv_display_id].store(kUpdateWorkNone, std::memory_order_release);
    g_update_pending_mask.fetch_and(~(uint32_t(1) << uint32_t(drv_display_id)),
                                    std::memory_order_acquire);
}

void publish_update_work(int drv_display_id, uint8_t work_bits)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    g_update_work[drv_display_id].fetch_or(work_bits, std::memory_order_release);
    const uint32_t bit = uint32_t(1) << uint32_t(drv_display_id);
    const uint32_t prev =
        g_update_pending_mask.fetch_or(bit, std::memory_order_release);
    if ((prev & bit) == 0) {
        g_update_wake_seq.fetch_add(1, std::memory_order_release);
        g_update_wake_seq.notify_one();
    }
}

void schedule_update(int drv_display_id)
{
    publish_update_work(drv_display_id, kUpdateWorkRefresh);
}

void schedule_disconnect(int drv_display_id)
{
    publish_update_work(drv_display_id, kUpdateWorkDisconnect);
}

bool take_next_update_display(int& out_drv_display_id)
{
    const uint32_t mask = g_update_pending_mask.load(std::memory_order_acquire);
    if (mask == 0) {
        return false;
    }

    const int start = g_update_rr.fetch_add(1, std::memory_order_relaxed);
    for (int i = 0; i < kMaxDriverDisplays; ++i) {
        const int d = (start + i) % kMaxDriverDisplays;
        const uint32_t bit = uint32_t(1) << uint32_t(d);

        if ((mask & bit) == 0) {
            continue;
        }

        const uint32_t prev = g_update_pending_mask.fetch_and(~bit, std::memory_order_acquire);
        if (prev & bit) {
            out_drv_display_id = d;
            return true;
        }
    }

    return false;
}

void notify_present_thread()
{
    g_present_wake_seq.fetch_add(1, std::memory_order_release);
    g_present_wake_seq.notify_one();
}

void wait_for_present_work()
{
    uint32_t seq = g_present_wake_seq.load(std::memory_order_acquire);

    if (g_present_ready_mask.load(std::memory_order_acquire) != 0)
        return;
    if (!g_running.load(std::memory_order_acquire))
        return;

    g_present_wake_seq.wait(seq, std::memory_order_relaxed);
}

bool take_next_present_display(int& out_drv_display_id)
{
    const uint32_t mask = g_present_ready_mask.load(std::memory_order_acquire);
    if (mask == 0) {
        return false;
    }

    const int start = g_present_rr.fetch_add(1, std::memory_order_relaxed);
    for (int i = 0; i < kMaxDriverDisplays; ++i) {
        const int d = (start + i) % kMaxDriverDisplays;
        const uint32_t bit = uint32_t(1) << uint32_t(d);

        if ((mask & bit) == 0) {
            continue;
        }

        const uint32_t prev = g_present_ready_mask.fetch_and(~bit, std::memory_order_acquire);
        if (prev & bit) {
            out_drv_display_id = d;
            return true;
        }
    }

    return false;
}

bool try_dequeue_present_job(int drv_display_id, PresentJob& out)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return false;
    }

    PresentJob* p = g_present_mailboxes[drv_display_id].job_ptr.exchange(
        nullptr, std::memory_order_acquire);
    if (!p) {
        return false;
    }

    out = std::move(*p);
    delete p;
    return true;
}

void enqueue_present_job(PresentJob&& j)
{
    if (j.drv_display_id < 0 || j.drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    const int d = j.drv_display_id;
    PresentJob* new_job = new PresentJob(std::move(j));
    PresentJob* old = g_present_mailboxes[d].job_ptr.exchange(
        new_job, std::memory_order_release);
    delete old;

    const uint32_t bit = uint32_t(1) << uint32_t(d);
    const uint32_t prev = g_present_ready_mask.fetch_or(bit, std::memory_order_release);
    if ((prev & bit) == 0) {
        notify_present_thread();
    }
}

void flush_present_jobs_for_display(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    PresentJob* old = g_present_mailboxes[drv_display_id].job_ptr.exchange(
        nullptr, std::memory_order_acquire);
    delete old;

    g_present_ready_mask.fetch_and(~(uint32_t(1) << uint32_t(drv_display_id)),
                                   std::memory_order_acquire);
}

void handle_signal(int signo)
{
    (void)signo;
    g_running.store(false, std::memory_order_release);
    g_update_wake_seq.fetch_add(1, std::memory_order_release);
    g_update_wake_seq.notify_all();
    g_evdi_event_wake_seq.fetch_add(1, std::memory_order_release);
    g_evdi_event_wake_seq.notify_all();
    notify_present_thread();
}

void kick_thread_out_of_ioctl(std::thread& t)
{
    if (!t.joinable()) {
        return;
    }
    (void)pthread_kill(t.native_handle(), kShutdownKickSignal);
}

void install_signal_handlers()
{
    struct sigaction sa;
    std::memset(&sa, 0, sizeof(sa));
    sa.sa_handler = handle_signal;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGINT, &sa, nullptr);
    sigaction(SIGTERM, &sa, nullptr);

    struct sigaction sb;
    std::memset(&sb, 0, sizeof(sb));
    sb.sa_handler = [](int) {};
    sigemptyset(&sb.sa_mask);
    sigaction(kShutdownKickSignal, &sb, nullptr);
}

}
