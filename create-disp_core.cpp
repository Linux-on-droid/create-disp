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

std::mutex g_update_mutex;
std::condition_variable g_update_cv;
std::array<std::atomic<uint8_t>, kMaxDriverDisplays> g_update_work = {};
std::atomic<uint32_t> g_update_pending_mask{0};
std::atomic<int> g_update_rr{0};
std::thread g_update_thread;

std::atomic<bool> g_reopen_requested{false};
std::atomic<int> g_modeset_inflight{0};

std::thread g_present_thread;
std::atomic<uint32_t> g_present_ready_mask{0};
std::atomic<int> g_present_rr{0};
int g_present_event_fd = -1;

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
std::atomic<bool> g_evdi_event_thread_sleeping{false};
std::mutex g_evdi_event_mutex;
std::condition_variable g_evdi_event_cv;
std::thread g_evdi_event_thread;

void request_reopen()
{
    (void)g_reopen_requested.exchange(true, std::memory_order_acq_rel);
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
                                    std::memory_order_acq_rel);
}

void publish_update_work(int drv_display_id, uint8_t work_bits)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    g_update_work[drv_display_id].fetch_or(work_bits, std::memory_order_acq_rel);
    const uint32_t bit = uint32_t(1) << uint32_t(drv_display_id);
    const uint32_t prev =
        g_update_pending_mask.fetch_or(bit, std::memory_order_acq_rel);
    if ((prev & bit) == 0) {
        g_update_cv.notify_one();
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

        const uint32_t prev = g_update_pending_mask.fetch_and(~bit, std::memory_order_acq_rel);
        if (prev & bit) {
            out_drv_display_id = d;
            return true;
        }
    }

    return false;
}

void notify_present_thread()
{
    if (g_present_event_fd < 0) {
        return;
    }

    const uint64_t one = 1;
    ssize_t rc;
    do {
        rc = ::write(g_present_event_fd, &one, sizeof(one));
    } while (rc < 0 && errno == EINTR);
}

void wait_for_present_work()
{
    if (g_present_event_fd < 0) {
        return;
    }

    uint64_t cnt = 0;
    for (;;) {
        ssize_t rc = ::read(g_present_event_fd, &cnt, sizeof(cnt));
        if (rc == (ssize_t)sizeof(cnt)) {
            return;
        }
        if (rc < 0 && errno == EINTR) {
            if (!g_running.load(std::memory_order_acquire)) {
                return;
            }
            continue;
        }
        return;
    }
}

void lock_present_mailbox(int drv_display_id)
{
    PresentMailbox& m = g_present_mailboxes[drv_display_id];
    while (m.lock.test_and_set(std::memory_order_acquire)) {
        std::this_thread::yield();
    }
}

void unlock_present_mailbox(int drv_display_id)
{
    g_present_mailboxes[drv_display_id].lock.clear(std::memory_order_release);
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

        const uint32_t prev = g_present_ready_mask.fetch_and(~bit, std::memory_order_acq_rel);
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

    PresentMailbox& m = g_present_mailboxes[drv_display_id];
    if (!m.pending.load(std::memory_order_acquire)) {
        return false;
    }

    if (m.lock.test_and_set(std::memory_order_acquire)) {
        return false;
    }

    if (!m.pending.load(std::memory_order_acquire)) {
        m.lock.clear(std::memory_order_release);
        return false;
    }

    out = std::move(m.job);
    m.job = PresentJob{};
    m.pending.store(false, std::memory_order_release);
    m.lock.clear(std::memory_order_release);
    return true;
}

void enqueue_present_job(PresentJob&& j)
{
    if (j.drv_display_id < 0 || j.drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    const int d = j.drv_display_id;
    lock_present_mailbox(d);
    PresentMailbox& m = g_present_mailboxes[d];
    m.job = std::move(j);
    m.pending.store(true, std::memory_order_release);
    unlock_present_mailbox(d);

    const uint32_t bit = uint32_t(1) << uint32_t(d);
    const uint32_t prev = g_present_ready_mask.fetch_or(bit, std::memory_order_acq_rel);
    if ((prev & bit) == 0) {
        notify_present_thread();
    }
}

void flush_present_jobs_for_display(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    lock_present_mailbox(drv_display_id);
    PresentMailbox& m = g_present_mailboxes[drv_display_id];
    m.job = PresentJob{};
    m.pending.store(false, std::memory_order_release);
    unlock_present_mailbox(drv_display_id);

    g_present_ready_mask.fetch_and(~(uint32_t(1) << uint32_t(drv_display_id)),
                                   std::memory_order_acq_rel);
}

void handle_signal(int signo)
{
    (void)signo;
    g_running.store(false, std::memory_order_release);
    g_update_cv.notify_all();
    g_evdi_event_cv.notify_all();
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
