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
std::thread g_update_thread;

std::atomic<bool> g_reopen_requested{false};
std::atomic<int> g_modeset_inflight{0};

std::thread g_poll_thread;
std::atomic<bool> g_running{true};

hwc2_compat_device_t* hwcDevice = nullptr;
std::atomic<int> drm_fd{-1};

std::array<Display, kMaxDriverDisplays> g_displays{};
std::array<DisplayRuntime, kMaxDriverDisplays> g_display_runtime;

std::array<std::atomic<BufferSegment*>, kBufferMaxSegments> g_buffer_segments{};
std::mutex g_buffer_segment_alloc_mutex;
std::atomic<uint32_t> g_next_buffer_id{1};
std::array<std::unordered_set<int>, kMaxDriverDisplays> g_display_bound_buffers;
#ifndef TARGET_USES_REAL_HWC
std::array<std::atomic<int>, kMaxDriverDisplays> g_display_power_mode = {1, 1, 1, 1, 1};
#endif

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
    return drm_fd.load(std::memory_order_acquire);
}

void drm_shutdown_close_fd()
{
    int fd = drm_fd.exchange(-1, std::memory_order_acq_rel);
    if (fd >= 0) {
        ::close(fd);
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
    if ((prev & bit) == 0) [[likely]] {
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
    uint32_t mask = g_update_pending_mask.load(std::memory_order_acquire);
    for (;;) {
        if (mask == 0) [[unlikely]] {
            return false;
        }

        const int d = std::countr_zero(mask);
        const uint32_t bit = uint32_t(1) << uint32_t(d);

        const uint32_t prev = g_update_pending_mask.fetch_and(~bit, std::memory_order_acquire);
        if (prev & bit) [[likely]] {
            out_drv_display_id = d;
            return true;
        }

        mask = g_update_pending_mask.load(std::memory_order_acquire);
    }
}

bool do_present(PresentJob& j)
{
    if (j.drv_display_id < 0 || j.drv_display_id >= kMaxDriverDisplays || !j.rwb) [[unlikely]] {
        return false;
    }

    DisplayRuntimeSnapshot dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
    if (!display_runtime_present_ready(dsnap, j.generation)) [[unlikely]] {
        return false;
    }

    {
        hwc2_compat_display_t* hwcDisp = dsnap.hwcDisplay;
        hwc2_error_t err = HWC2_ERROR_NONE;
        {
            std::lock_guard<std::mutex> hwc_lk(g_hwc_mutex[j.drv_display_id]);

            dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
            if (!display_runtime_present_ready(dsnap, j.generation)) [[unlikely]] {
                return false;
            }

            hwcDisp = dsnap.hwcDisplay;
            if (!hwcDisp) [[unlikely]] {
                return false;
            }

#ifdef TARGET_USES_REAL_HWC
            uint32_t numTypes = 0;
            uint32_t numRequests = 0;
#endif

            err = hwc2_compat_display_set_client_target(hwcDisp, j.slot, j.rwb.get(),
                                                        -1, HAL_DATASPACE_UNKNOWN);
            if (err != HWC2_ERROR_NONE) [[unlikely]] {
                fprintf(stderr, "set_client_target failed: %d\n", (int)err);
                request_display_resync(j.drv_display_id);
                return false;
            }

#ifdef TARGET_USES_REAL_HWC
            err = hwc2_compat_display_validate(hwcDisp, &numTypes, &numRequests);
            if (err == HWC2_ERROR_HAS_CHANGES && (numTypes || numRequests)) {
                (void)hwc2_compat_display_accept_changes(hwcDisp);
            } else if (err != HWC2_ERROR_NONE) [[unlikely]] {
                fprintf(stderr, "validate failed: %d\n", (int)err);
                request_display_resync(j.drv_display_id);
                return false;
            }

            int presentFence = -1;
            err = hwc2_compat_display_present(hwcDisp, &presentFence);
            if (presentFence >= 0)
                close(presentFence);
#endif
        }

#ifdef TARGET_USES_REAL_HWC
        if (err != HWC2_ERROR_NONE) [[unlikely]] {
            fprintf(stderr, "present failed: %d\n", (int)err);
            request_display_resync(j.drv_display_id);
            return false;
        }
#endif
    }

    dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
    if (!display_runtime_present_ready(dsnap, j.generation)) [[unlikely]] {
        return false;
    }

    g_resync_pending[j.drv_display_id].store(false, std::memory_order_release);
    return true;
}

void handle_signal(int signo)
{
    (void)signo;
    g_running.store(false, std::memory_order_release);
    g_update_wake_seq.fetch_add(1, std::memory_order_release);
    g_update_wake_seq.notify_all();
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
