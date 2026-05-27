#include "create-disp_shared.h"

namespace create_disp {

void present_thread_main()
{
    while (g_running.load(std::memory_order_acquire)) {
        bool did_work = false;
        int d = -1;

        while (take_next_present_display(d)) {
            PresentJob j;
            if (!try_dequeue_present_job(d, j)) [[unlikely]] {
                continue;
            }

            did_work = true;

            if (j.drv_display_id < 0 || j.drv_display_id >= kMaxDriverDisplays || !j.rwb) {
                continue;
            }

            DisplayRuntimeSnapshot dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
            if (!display_runtime_present_ready(dsnap, j.generation)) {
                continue;
            }

            {
                hwc2_compat_display_t* hwcDisp = dsnap.hwcDisplay;
                hwc2_error_t err = HWC2_ERROR_NONE;
                {
                    std::lock_guard<std::mutex> hwc_lk(g_hwc_mutex[j.drv_display_id]);

                    dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
                    if (!display_runtime_present_ready(dsnap, j.generation)) {
                        continue;
                    }

                    hwcDisp = dsnap.hwcDisplay;
                    if (!hwcDisp) {
                        continue;
                    }

                    uint32_t numTypes = 0;
                    uint32_t numRequests = 0;

                    err = hwc2_compat_display_set_client_target(hwcDisp, j.slot, j.rwb.get(),
                                                                -1, HAL_DATASPACE_UNKNOWN);
                    if (err != HWC2_ERROR_NONE) {
                        fprintf(stderr, "set_client_target failed: %d\n", (int)err);
                        request_display_resync(j.drv_display_id);
                        continue;
                    }

                    err = hwc2_compat_display_validate(hwcDisp, &numTypes, &numRequests);
                    if (err == HWC2_ERROR_HAS_CHANGES && (numTypes || numRequests)) {
                        (void)hwc2_compat_display_accept_changes(hwcDisp);
                    } else if (err != HWC2_ERROR_NONE) {
                        fprintf(stderr, "validate failed: %d\n", (int)err);
                        request_display_resync(j.drv_display_id);
                        continue;
                    }

                    int presentFence = -1;
                    err = hwc2_compat_display_present(hwcDisp, &presentFence);
                }

                if (err != HWC2_ERROR_NONE) {
                    fprintf(stderr, "present failed: %d\n", (int)err);
                    request_display_resync(j.drv_display_id);
                    continue;
                }
            }

            dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
            if (!display_runtime_present_ready(dsnap, j.generation)) {
                continue;
            }

            g_resync_pending[j.drv_display_id].store(false, std::memory_order_release);
        }

        if (!g_running.load(std::memory_order_acquire)) {
            break;
        }

        if (!did_work) {
            wait_for_present_work();
        }
    }
}

void update_thread_main()
{
    for (;;) {
        int disp = -1;

        if (g_running.load(std::memory_order_acquire) &&
            g_update_pending_mask.load(std::memory_order_acquire) == 0) {
            uint32_t seq = g_update_wake_seq.load(std::memory_order_acquire);
            if (g_running.load(std::memory_order_acquire) &&
                g_update_pending_mask.load(std::memory_order_acquire) == 0) {
                g_update_wake_seq.wait(seq, std::memory_order_relaxed);
            }
        }

        if (!g_running.load(std::memory_order_acquire)) {
            break;
        }

        if (!take_next_update_display(disp)) [[unlikely]] {
            continue;
        }

        const uint8_t work =
            g_update_work[disp].exchange(kUpdateWorkNone, std::memory_order_acquire);
        const bool do_disconnect = (work & kUpdateWorkDisconnect) != 0;
        const bool do_update = (work & kUpdateWorkRefresh) != 0;

        if (do_disconnect) {
            disconnect_display(disp);
        }
        if (do_update) {
            (void)update_display(disp);
        }
    }
}

void poll_thread_main()
{
    int hard_poll_failures = 0;

    for (;;) {
        if (!g_running.load(std::memory_order_acquire)) {
            break;
        }

        if (g_reopen_requested.exchange(false, std::memory_order_acquire)) {
            std::unique_lock<std::shared_mutex> lk(g_drm_mutex);

            int old_fd = drm_fd.exchange(-1, std::memory_order_acq_rel);
            if (old_fd >= 0) {
                ::close(old_fd);
            }
            drm_ready.store(false, std::memory_order_release);

            for (int tries = 0; tries < 30; ++tries) {
                int fd = open_evdi_lindroid_or_create();
                if (fd >= 0) {
                    drm_fd.store(fd, std::memory_order_release);
                    drm_ready.store(true, std::memory_order_release);
                    fprintf(stderr, "Reopened evdi-lindroid fd=%d\n", fd);
                    break;
                }
                std::this_thread::sleep_for(std::chrono::milliseconds(50));
            }

            hard_poll_failures = 0;

            if (drm_ready.load(std::memory_order_acquire)) {
                std::array<int, kMaxDriverDisplays> reconnect_displays = {};
                int reconnect_count = 0;

                {
                    std::lock_guard<std::mutex> slk(g_display_mutex);
                    for (int d = 0; d < kMaxDriverDisplays; ++d) {
                        auto& D = g_displays[d];
                        reset_display_bindings_locked(d);
                        if (D.connected && D.hwcDisplay) {
                            D.width = 0;
                            D.height = 0;
                            D.stride = 0;
                            publish_display_runtime_locked(d);
                            g_resync_pending[d].store(true, std::memory_order_release);
                            if (reconnect_count < kMaxDriverDisplays) {
                                reconnect_displays[reconnect_count++] = d;
                            }
                        }
                    }
                }

                for (int i = 0; i < reconnect_count; ++i) {
                    schedule_update(reconnect_displays[i]);
                }
            }
        }

        drm_evdi_poll poll_cmd = {};
        std::array<uint8_t, 32> poll_payload{};
        poll_cmd.data = poll_payload.data();

        int ret = drm_ioctl(DRM_IOCTL_EVDI_POLL, &poll_cmd);
        if (ret < 0) [[unlikely]] {
            if (errno == EINTR || errno == ERESTART) {
                if (!g_running.load(std::memory_order_acquire)) {
                    break;
                }
                continue;
            }

            if (errno == ENODEV || errno == EBADF) {
                if (should_request_reopen(errno) && ++hard_poll_failures >= 3) {
                    request_reopen();
                }
                std::this_thread::sleep_for(std::chrono::milliseconds(50));
            } else {
                hard_poll_failures = 0;
            }

            continue;
        }

        hard_poll_failures = 0;

        if (poll_cmd.event != none) [[likely]] {
            if (poll_cmd.event == swap_to) [[likely]] {
                swap_to_buff(poll_payload, poll_cmd.poll_id);
            } else {
                switch (poll_cmd.event) {
                    case get_buf:
                        get_buf_from_map(poll_payload, poll_cmd.poll_id);
                        break;
                    case destroy_buf:
                        destroy_buff(poll_payload, poll_cmd.poll_id);
                        break;
                    case create_buf:
                        create_buff(poll_payload, poll_cmd.poll_id);
                        break;
                    default:
                        break;
                }
            }
        }
    }
}

int run_create_disp()
{
    int composerSequenceId = 0;

    sd_notifyf(0, "MAINPID=%lu", (unsigned long)getpid());
    sd_notify(0, "STATUS=Initializing create-disp…");

    init_free_driver_slots_once();

    buffer_table_reserve_ids(kExpectedHandles);
    g_hwc_to_drv.reserve(kMaxDriverDisplays);
    g_drv_to_hwc.reserve(kMaxDriverDisplays);

    drm_fd.store(-1, std::memory_order_relaxed);
    for (int i = 0; i < 5 * 1000; ++i) {
        int fd = find_evdi_lindroid_device();
        if (fd >= 0) {
            drm_fd.store(fd, std::memory_order_relaxed);
            break;
        }
        usleep(1000);
    }

    if (drm_fd.load(std::memory_order_relaxed) < 0) {
        int fd = open_evdi_lindroid_or_create();
        if (fd >= 0) {
            drm_fd.store(fd, std::memory_order_relaxed);
        }
    }
    if (drm_fd.load(std::memory_order_relaxed) < 0) {
        return EXIT_FAILURE;
    }

    drm_ready.store(true, std::memory_order_release);

    hwcDevice = hwc2_compat_device_new(false);
    if (!hwcDevice) {
        return EXIT_FAILURE;
    }

    assert(hwcDevice);
    hwc2_compat_device_register_callback(hwcDevice, &eventListener, composerSequenceId);

    try {
        g_update_thread = std::thread(update_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create update thread\n");
        {
            int fd = drm_fd.exchange(-1, std::memory_order_relaxed);
            if (fd >= 0) ::close(fd);
        }
        return EXIT_FAILURE;
    }

    install_signal_handlers();

    sd_notify(0, "READY=1");
    sd_notify(0, "STATUS=create-disp ready.");

    try {
        g_present_thread = std::thread(present_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create present thread\n");
        g_running.store(false, std::memory_order_release);
        g_update_wake_seq.fetch_add(1, std::memory_order_release);
        g_update_wake_seq.notify_all();
        {
            int fd = drm_fd.exchange(-1, std::memory_order_acq_rel);
            if (fd >= 0) ::close(fd);
        }
        return EXIT_FAILURE;
    }

    try {
        g_poll_thread = std::thread(poll_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create poll thread\n");
        g_running.store(false, std::memory_order_release);
        notify_present_thread();

        if (g_present_thread.joinable()) {
            g_present_thread.join();
        }
        if (g_update_thread.joinable()) {
            g_update_wake_seq.fetch_add(1, std::memory_order_release);
            g_update_wake_seq.notify_all();
            g_update_thread.join();
        }

        {
            int fd = drm_fd.exchange(-1, std::memory_order_acq_rel);
            if (fd >= 0) ::close(fd);
        }
        return EXIT_FAILURE;
    }

    while (g_running.load(std::memory_order_acquire)) {
        pause();
    }

    notify_present_thread();
    g_update_wake_seq.fetch_add(1, std::memory_order_release);
    g_update_wake_seq.notify_all();

    if (g_poll_thread.joinable()) {
        kick_thread_out_of_ioctl(g_poll_thread);
    }

    sd_notify(0, "STATUS=Stopping poll thread…");
    if (g_poll_thread.joinable()) {
        g_poll_thread.join();
    }

    sd_notify(0, "STATUS=Stopping present thread…");
    notify_present_thread();
    if (g_present_thread.joinable()) {
        g_present_thread.join();
    }

    drm_shutdown_close_fd();

    sd_notify(0, "STATUS=Stopping update thread…");
    g_update_wake_seq.fetch_add(1, std::memory_order_release);
    g_update_wake_seq.notify_all();
    if (g_update_thread.joinable()) {
        g_update_thread.join();
    }

    buffer_table_shutdown();

    sd_notify(0, "STATUS=Shutting down…");
    return EXIT_SUCCESS;
}

}
