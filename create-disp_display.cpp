#include "create-disp_shared.h"

namespace create_disp {

Display& get_or_create_display(int display_id)
{
    auto it = g_displays.find(display_id);
    if (it != g_displays.end()) {
        return it->second;
    }

    auto [ins_it, inserted] = g_displays.try_emplace(display_id);
    (void)inserted;
    ins_it->second.display_id = display_id;
    return ins_it->second;
}

void publish_display_runtime_locked(int display_id)
{
    if (display_id < 0 || display_id >= kMaxDriverDisplays) {
        return;
    }

    Display& D = get_or_create_display(display_id);
    DisplayRuntime& R = g_display_runtime[display_id];

    uint64_t seq = R.seq.load(std::memory_order_relaxed);
    R.seq.store(seq + 1, std::memory_order_release);
    R.hwc_id.store(D.hwc_id, std::memory_order_relaxed);
    R.hwcDisplay.store(reinterpret_cast<uintptr_t>(D.hwcDisplay), std::memory_order_relaxed);
    R.width.store(D.width, std::memory_order_relaxed);
    R.height.store(D.height, std::memory_order_relaxed);
    R.stride.store(D.stride, std::memory_order_relaxed);
    R.connected.store(D.connected, std::memory_order_relaxed);
    R.generation.store(D.generation, std::memory_order_relaxed);
    R.seq.store(seq + 2, std::memory_order_release);
}

DisplayRuntimeSnapshot snapshot_display_runtime_atomic(int display_id)
{
    DisplayRuntimeSnapshot s;
    if (display_id < 0 || display_id >= kMaxDriverDisplays) {
        return s;
    }

    DisplayRuntime& R = g_display_runtime[display_id];

    for (;;) {
        uint64_t seq1 = R.seq.load(std::memory_order_acquire);
        if (seq1 & 1ULL) [[unlikely]] {
            std::this_thread::yield();
            continue;
        }

        s.hwc_id = R.hwc_id.load(std::memory_order_relaxed);
        s.hwcDisplay = reinterpret_cast<hwc2_compat_display_t*>(R.hwcDisplay.load(std::memory_order_relaxed));
        s.width = R.width.load(std::memory_order_relaxed);
        s.height = R.height.load(std::memory_order_relaxed);
        s.stride = R.stride.load(std::memory_order_relaxed);
        s.connected = R.connected.load(std::memory_order_relaxed);
        s.generation = R.generation.load(std::memory_order_relaxed);

        uint64_t seq2 = R.seq.load(std::memory_order_acquire);
        if (seq1 == seq2) [[likely]] {
            return s;
        }
    }
}

bool display_runtime_present_ready(const DisplayRuntimeSnapshot& s, uint64_t generation)
{
    return s.connected &&
           s.hwcDisplay != nullptr &&
           s.generation == generation;
}

void request_display_resync(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    bool expected = false;
    if (!g_resync_pending[drv_display_id].compare_exchange_strong(
            expected, true, std::memory_order_acq_rel)) [[unlikely]] {
        return;
    }

    schedule_update(drv_display_id);
}

int drv_id_for_hwc_atomic(long long hwc_id)
{
    if (hwc_id == 0) {
        return -1;
    }

    for (int d = 0; d < kMaxDriverDisplays; ++d) {
        DisplayRuntimeSnapshot s = snapshot_display_runtime_atomic(d);
        if (!s.connected) {
            continue;
        }
        if (s.hwc_id == hwc_id) {
            return d;
        }
    }

    return -1;
}

int drv_id_for_hwc(long long hwc_id)
{
    auto it = g_hwc_to_drv.find(hwc_id);
    return it == g_hwc_to_drv.end() ? -1 : it->second;
}

void init_free_driver_slots_once()
{
    if (g_free_drv_ids_initialized) {
        return;
    }

    g_free_drv_count = 0;
    for (int i = kMaxDriverDisplays - 1; i >= 0; --i) {
        g_free_drv_ids[g_free_drv_count++] = i;
    }
    g_free_drv_ids_initialized = true;
}

int alloc_driver_slot_for_hwc(long long hwc_id)
{
    int drv = drv_id_for_hwc(hwc_id);
    if (drv >= 0) {
        return drv;
    }
    if (g_free_drv_count <= 0) {
        return -1;
    }

    drv = g_free_drv_ids[--g_free_drv_count];
    g_hwc_to_drv[hwc_id] = drv;
    g_drv_to_hwc[drv] = hwc_id;
    return drv;
}

void release_driver_slot_for_hwc(long long hwc_id)
{
    auto it = g_hwc_to_drv.find(hwc_id);
    if (it == g_hwc_to_drv.end()) {
        return;
    }

    int drv = it->second;
    g_hwc_to_drv.erase(it);
    g_drv_to_hwc.erase(drv);

    for (int i = 0; i < g_free_drv_count; ++i) {
        if (g_free_drv_ids[i] == drv) {
            return;
        }
    }

    if (g_free_drv_count < kMaxDriverDisplays) {
        g_free_drv_ids[g_free_drv_count++] = drv;
    } else {
        fprintf(stderr, "release_driver_slot_for_hwc: free list overflow for drv %d\n", drv);
    }
}

int evdi_vsync(int drv_display_id)
{
    struct drm_evdi_vsync cmd = {};
    cmd.display_id = (uint32_t)drv_display_id;

    int fd = drm_get_fd();
    if (fd < 0) {
        return -EBADF;
    }

    return ioctl_retry(fd, DRM_IOCTL_EVDI_VSYNC, &cmd);
}

bool is_evdi_lindroid(int fd)
{
    drmVersionPtr version = drmGetVersion(fd);
    if (version) {
        std::string driver_name(version->name, version->name_len);
        drmFreeVersion(version);
        return driver_name == "evdi-lindroid";
    }
    return false;
}

int find_evdi_lindroid_device()
{
    static const char* dri_path = "/dev/dri/";
    DIR* dir = opendir(dri_path);
    if (!dir) {
        return -1;
    }

    int found_fd = -1;
    struct dirent* entry;
    while ((entry = readdir(dir)) != nullptr) {
        if (strncmp(entry->d_name, "card", 4) != 0) {
            continue;
        }

        std::string path = std::string(dri_path) + entry->d_name;
        int fd = open(path.c_str(), O_RDWR | O_CLOEXEC);
        if (fd < 0) {
            continue;
        }

        if (!is_evdi_lindroid(fd)) {
            close(fd);
            continue;
        }

        std::cout << "Found evdi-lindroid at " << path << std::endl;
        if (drmIsMaster(fd)) {
            if (ioctl(fd, DRM_IOCTL_DROP_MASTER, nullptr) < 0) {
                std::cerr << "Failed to drop master on " << path << ": " << strerror(errno) << std::endl;
                close(fd);
                break;
            }
        }

        found_fd = fd;
        break;
    }

    closedir(dir);
    return found_fd;
}

int open_evdi_lindroid_or_create()
{
    int fd = find_evdi_lindroid_device();
    if (fd >= 0) {
        return fd;
    }

    std::cout << "evdi-lindroid not found. Attempting to create..." << std::endl;
    std::ofstream evdi_add("/sys/devices/evdi-lindroid/add");
    if (!evdi_add) {
        std::cerr << "Failed to write to /sys/devices/evdi-lindroid/add: " << strerror(errno) << std::endl;
        return -1;
    }

    evdi_add << "1";
    evdi_add.close();

    int wait_interval = 1;
    int total_wait_limit = 30;
    for (int wait_time = 0; wait_time < total_wait_limit; wait_time += wait_interval) {
        fd = find_evdi_lindroid_device();
        if (fd >= 0) {
            return fd;
        }
        sleep(wait_interval);
    }

    std::cerr << "evdi-lindroid still not available after add attempt." << std::endl;
    return -1;
}

int evdi_connect(int device_index, uint32_t width, uint32_t height, uint32_t refresh_rate, uint32_t display_id, int connected)
{
    drm_evdi_connect cmd = {
        .connected = connected,
        .dev_index = device_index,
        .width = width,
        .height = height,
        .refresh_rate = refresh_rate,
        .display_id = display_id,
    };

    if (drm_ioctl(DRM_IOCTL_EVDI_CONNECT, &cmd) < 0) {
        perror("DRM_IOCTL_EVDI_CONNECT failed");
        return -1;
    }

    return 0;
}

void onVsyncReceived(HWC2EventListener* listener, int32_t sequenceId, hwc2_display_t display, int64_t timestamp)
{
    (void)listener;
    (void)sequenceId;
    (void)timestamp;

    const long long hwc_id = (long long)display;
    int drv_id = drv_id_for_hwc_atomic(hwc_id);

    if (drv_id < 0) {
        std::lock_guard<std::mutex> lk(g_display_mutex);
        drv_id = drv_id_for_hwc(hwc_id);
    }

    if (drv_id >= 0) {
        int vsync_ret = evdi_vsync(drv_id);
        if (vsync_ret < 0 && errno != ETIMEDOUT && errno != ENODEV && errno != EBADF) {
            fprintf(stderr, "vsync failed for display %d: %d (%s)\n",
                    drv_id, errno, strerror(errno));
        }
    }
}

void onHotplugReceived(HWC2EventListener* listener, int32_t sequenceId, hwc2_display_t display, bool connected, bool primaryDisplay)
{
    (void)listener;

    printf("onHotplugReceived(%d, %" PRIu64 ", %s, %s)\n",
           sequenceId, display,
           connected ? "connected" : "disconnected",
           primaryDisplay ? "primary" : "external");

    hwc2_compat_device_on_hotplug(hwcDevice, display, connected);
    init_free_driver_slots_once();

    const long long hwc_id = (long long)display;
    int drv_id = -1;

    if (connected) {
        hwc2_compat_display_t* hwc_display =
            hwc2_compat_device_get_display_by_id(hwcDevice, display);

        {
            std::lock_guard<std::mutex> lk(g_display_mutex);
            drv_id = drv_id_for_hwc(hwc_id);
            if (drv_id < 0) {
                drv_id = alloc_driver_slot_for_hwc(hwc_id);
                if (drv_id < 0) {
                    std::cerr << "No free driver display slots; ignoring hotplug for HWC id "
                              << hwc_id << std::endl;
                    return;
                }
            }
        }

        {
            std::unique_lock<std::mutex> state_lk(g_display_mutex, std::defer_lock);
            std::unique_lock<std::mutex> hwc_lk(g_hwc_mutex[drv_id], std::defer_lock);
            std::lock(state_lk, hwc_lk);

            Display& D = get_or_create_display(drv_id);
            D.display_id = drv_id;
            D.hwc_id = hwc_id;
            D.hwcDisplay = hwc_display;
            D.connected = true;
            publish_display_runtime_locked(drv_id);
        }

        schedule_update(drv_id);
        if (hwc_display) {
            hwc2_compat_display_set_vsync_enabled(hwc_display, HWC2_VSYNC_ENABLE);
        }
    } else {
        {
            std::lock_guard<std::mutex> lk(g_display_mutex);
            drv_id = drv_id_for_hwc(hwc_id);
            if (drv_id < 0) {
                return;
            }
        }

        {
            std::unique_lock<std::mutex> state_lk(g_display_mutex, std::defer_lock);
            std::unique_lock<std::mutex> hwc_lk(g_hwc_mutex[drv_id], std::defer_lock);
            std::lock(state_lk, hwc_lk);

            Display& D = get_or_create_display(drv_id);
            D.connected = false;
            publish_display_runtime_locked(drv_id);
        }
        schedule_disconnect(drv_id);
    }
}

void onRefreshReceived(HWC2EventListener* listener, int32_t sequenceId, hwc2_display_t display)
{
    (void)listener;
    (void)sequenceId;

    const long long hwc_id = (long long)display;
    int drv_id = drv_id_for_hwc_atomic(hwc_id);

    if (drv_id < 0) {
        std::lock_guard<std::mutex> lk(g_display_mutex);
        drv_id = drv_id_for_hwc(hwc_id);
    }

    if (drv_id < 0) {
        return;
    }

    //printf("onRefreshReceived (HWC %" PRIu64 ") -> driver slot %d\n", (uint64_t)hwc_id, drv_id);
    schedule_update(drv_id);
}

HWC2EventListener eventListener = {
    &onVsyncReceived,
    &onHotplugReceived,
    &onRefreshReceived
};

int hz_from_period_ns(int32_t ns)
{
    if (ns <= 0) {
        return 60;
    }

    const double hz_f = 1e9 / static_cast<double>(ns);
    return static_cast<int>(std::lround(hz_f));
}

int get_refresh_hz_from_active_config(const HWC2DisplayConfig* cfg)
{
    return hz_from_period_ns(cfg->vsyncPeriod);
}

int reconnect_display_mode(int display_id, int target_width, int target_height, int refresh_hz, bool disconnect_first)
{
    g_modeset_inflight.fetch_add(1, std::memory_order_release);
    int rc = 0;

    if (disconnect_first) {
        if (evdi_connect(0, 0, 0, 0, (uint32_t)display_id, 0) < 0) {
            rc = -1;
        }
    }

    if (rc == 0) {
        rc = evdi_connect(0,
                          (uint32_t)target_width, (uint32_t)target_height,
                          (uint32_t)refresh_hz, (uint32_t)display_id, 1);
    }

    g_modeset_inflight.fetch_sub(1, std::memory_order_release);
    return rc;
}

int update_display(int display_id)
{
    if (display_id < 0 || display_id >= kMaxDriverDisplays) {
        return -1;
    }

    if (!drm_ready.load(std::memory_order_acquire)) {
        fprintf(stderr, "update_display(%d): DRM not ready, deferring CONNECT\n", display_id);
        return -1;
    }

    if (g_modeset_inflight.load(std::memory_order_acquire) > 0) {
        fprintf(stderr, "update_display(%d): mode set in-flight, deferring", display_id);
        return -1;
    }

    flush_present_jobs_for_display(display_id);

    int target_width = 0;
    int target_height = 0;
    int refresh_hz = 60;
    uint64_t generation = 0;
    uint32_t new_stride = 0;
    bool force_reconnect = g_resync_pending[display_id].exchange(false, std::memory_order_acquire);
    bool had_previous_mode = false;
    bool mode_changed = false;

    {
        std::unique_lock<std::mutex> state_lk(g_display_mutex, std::defer_lock);
        std::unique_lock<std::mutex> hwc_lk(g_hwc_mutex[display_id], std::defer_lock);
        std::lock(state_lk, hwc_lk);

        Display& D = get_or_create_display(display_id);
        hwc2_compat_display_t* hwcDisp = D.hwcDisplay;
        if (!D.connected || !hwcDisp) {
            return -1;
        }

        HWC2DisplayConfig* config = hwc2_compat_display_get_active_config(hwcDisp);
        if (!config) {
            fprintf(stderr, "update_display(%d): no active HWC config yet, will retry on next refresh\n",
                    display_id);
            return -1;
        }

        if (config->width <= 0 || config->height <= 0) {
            fprintf(stderr, "update_display(%d): invalid geometry %dx%d, deferring\n",
                    display_id, config->width, config->height);
            return -1;
        }

        target_width = config->width;
        target_height = config->height;
        refresh_hz = get_refresh_hz_from_active_config(config);
        had_previous_mode = (D.width > 0 && D.height > 0 && D.stride != 0);
        mode_changed = (D.width != target_width || D.height != target_height);

        if (!force_reconnect && !mode_changed && D.stride != 0) [[likely]] {
            return 0;
        }

        printf("display %d width: %i height: %i%s%s\n",
               display_id, target_width, target_height,
               mode_changed ? " (mode change)" : "",
               force_reconnect ? " (forced resync)" : "");

        reset_display_bindings_locked(display_id);

        D.generation++;
        generation = D.generation;
        D.width = target_width;
        D.height = target_height;
        D.stride = 0;
        publish_display_runtime_locked(display_id);
    }

    buffer_handle_t handle = nullptr;
    int r = hybris_gralloc_allocate(target_width, target_height, HAL_PIXEL_FORMAT_RGBX_8888,
                                    kRwbUsage, &handle, &new_stride);
    if (r == 0 && handle) {
        (void)hybris_gralloc_release(handle, 1);
    } else {
        fprintf(stderr, "update_display(%d): failed to determine stride for %dx%d\n",
                display_id, target_width, target_height);
        return -1;
    }

    std::ostringstream oss;
    oss << "EDID for " << target_width << "x" << target_height
        << "@" << refresh_hz << "Hz 'Lindroid display " << display_id << "'";
    std::cout << oss.str() << std::endl;

    if (reconnect_display_mode(display_id,
                               target_width, target_height, refresh_hz,
                               force_reconnect || mode_changed || had_previous_mode) < 0) {
        return EXIT_FAILURE;
    }

    {
        std::lock_guard<std::mutex> lk(g_display_mutex);
        Display& D = get_or_create_display(display_id);
        if (D.generation == generation) {
            D.width = target_width;
            D.height = target_height;
            D.stride = new_stride;
            publish_display_runtime_locked(display_id);
        }
    }

    return 0;
}

void disconnect_display(int drv_id)
{
    if (drv_id < 0 || drv_id >= kMaxDriverDisplays) {
        return;
    }

    flush_present_jobs_for_display(drv_id);

    if (drm_ready.load(std::memory_order_acquire)) {
        g_modeset_inflight.fetch_add(1, std::memory_order_release);
        (void)evdi_connect(0, 0, 0, 0, (uint32_t)drv_id, 0);
        g_modeset_inflight.fetch_sub(1, std::memory_order_release);
    }

    {
        std::unique_lock<std::mutex> state_lk(g_display_mutex, std::defer_lock);
        std::unique_lock<std::mutex> hwc_lk(g_hwc_mutex[drv_id], std::defer_lock);
        std::lock(state_lk, hwc_lk);

        Display& D = get_or_create_display(drv_id);
        reset_display_bindings_locked(drv_id);

        const long long hwc_id = D.hwc_id;
        D.generation++;
        D.hwcDisplay = nullptr;
        D.width = 0;
        D.height = 0;
        D.stride = 0;
        D.connected = false;
        D.hwc_id = 0;
        publish_display_runtime_locked(drv_id);

        g_resync_pending[drv_id].store(false, std::memory_order_release);
        clear_pending_work_atomic(drv_id);

        if (hwc_id != 0) {
            release_driver_slot_for_hwc(hwc_id);
        }
    }
}

}
