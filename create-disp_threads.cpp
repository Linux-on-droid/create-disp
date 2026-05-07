#include "create-disp_shared.h"

namespace create_disp {

void present_thread_main()
{
    while (g_running.load(std::memory_order_acquire)) {
        bool did_work = false;
        int d = -1;

        while (take_next_present_display(d)) {
            PresentJob j;
            if (!try_dequeue_present_job(d, j)) {
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
                }

                int presentFence = -1;
                {
                    std::lock_guard<std::mutex> hwc_lk(g_hwc_mutex[j.drv_display_id]);
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

        {
            std::unique_lock<std::mutex> lk(g_update_mutex);
            g_update_cv.wait(lk, [] {
                return !g_running.load(std::memory_order_acquire) ||
                       g_update_pending_mask.load(std::memory_order_acquire) != 0;
            });

            if (!g_running.load(std::memory_order_acquire)) {
                break;
            }
        }

        if (!take_next_update_display(disp)) {
            continue;
        }

        const uint8_t work =
            g_update_work[disp].exchange(kUpdateWorkNone, std::memory_order_acq_rel);
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

void evdi_event_thread_main()
{
    while (g_running.load(std::memory_order_acquire)) {
        QueuedEvdiEvent ev;

        while (g_evdi_event_queue.pop(ev)) {
            switch (ev.event) {
                case swap_to:
                    swap_to_buff(ev.data, ev.poll_id);
                    break;
                case get_buf:
                    get_buf_from_map(ev.data, ev.poll_id);
                    break;
                case destroy_buf:
                    destroy_buff(ev.data, ev.poll_id);
                    break;
                case create_buf:
                    create_buff(ev.data, ev.poll_id);
                    break;
                default:
                    break;
            }
        }

        if (g_evdi_event_queue.empty()) {
            std::unique_lock<std::mutex> lk(g_evdi_event_mutex);
            if (g_evdi_event_queue.empty()) {
                g_evdi_event_thread_sleeping.store(true, std::memory_order_release);
                g_evdi_event_cv.wait(lk, [] {
                    return !g_running.load(std::memory_order_acquire) ||
                           !g_evdi_event_queue.empty();
                });
                g_evdi_event_thread_sleeping.store(false, std::memory_order_release);
            }
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

        if (g_reopen_requested.exchange(false, std::memory_order_acq_rel)) {
            std::unique_lock<std::shared_mutex> lk(g_drm_mutex);

            if (drm_fd >= 0) {
                ::close(drm_fd);
                drm_fd = -1;
            }
            drm_ready.store(false, std::memory_order_release);

            for (int tries = 0; tries < 30; ++tries) {
                int fd = open_evdi_lindroid_or_create();
                if (fd >= 0) {
                    drm_fd = fd;
                    drm_ready.store(true, std::memory_order_release);
                    fprintf(stderr, "Reopened evdi-lindroid fd=%d\n", drm_fd);
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
                    for (auto &kv : g_displays) {
                        reset_display_bindings_locked(kv.first);
                        if (kv.second.connected && kv.second.hwcDisplay) {
                            kv.second.width = 0;
                            kv.second.height = 0;
                            kv.second.stride = 0;
                            publish_display_runtime_locked(kv.first);
                            g_resync_pending[kv.first].store(true, std::memory_order_release);
                            if (reconnect_count < kMaxDriverDisplays) {
                                reconnect_displays[reconnect_count++] = kv.first;
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
        uint8_t poll_payload[32];
        poll_cmd.data = poll_payload;

        int ret = drm_ioctl(DRM_IOCTL_EVDI_POLL, &poll_cmd);
        if (ret < 0) {
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

        if (poll_cmd.event != none) {
            QueuedEvdiEvent q_ev;
            q_ev.event = poll_cmd.event;
            q_ev.poll_id = poll_cmd.poll_id;
            std::memcpy(q_ev.data, poll_payload, sizeof(poll_payload));

            if (!g_evdi_event_queue.push(q_ev)) {
                fprintf(stderr, "WARNING: EVDI event queue is full! Dropping event.\n");
            }

            if (g_evdi_event_thread_sleeping.load(std::memory_order_acquire)) {
                g_evdi_event_cv.notify_one();
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
    g_displays.reserve(kMaxDriverDisplays);
    g_hwc_to_drv.reserve(kMaxDriverDisplays);
    g_drv_to_hwc.reserve(kMaxDriverDisplays);

    drm_fd = -1;
    for (int i = 0; i < 5 * 1000; ++i) {
        drm_fd = find_evdi_lindroid_device();
        if (drm_fd >= 0) {
            break;
        }
        usleep(1000);
    }

    if (drm_fd < 0) {
        drm_fd = open_evdi_lindroid_or_create();
    }
    if (drm_fd < 0) {
        return EXIT_FAILURE;
    }

    drm_ready.store(true, std::memory_order_release);

    g_present_event_fd = eventfd(0, EFD_CLOEXEC);
    if (g_present_event_fd < 0) {
        perror("eventfd");
        close(drm_fd);
        return EXIT_FAILURE;
    }

    hwcDevice = hwc2_compat_device_new(false);
    if (!hwcDevice) {
        close(g_present_event_fd);
        g_present_event_fd = -1;
        return EXIT_FAILURE;
    }

    assert(hwcDevice);
    hwc2_compat_device_register_callback(hwcDevice, &eventListener, composerSequenceId);

    try {
        g_update_thread = std::thread(update_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create update thread\n");
        close(g_present_event_fd);
        g_present_event_fd = -1;
        close(drm_fd);
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
        g_update_cv.notify_all();
        close(g_present_event_fd);
        g_present_event_fd = -1;
        close(drm_fd);
        return EXIT_FAILURE;
    }

    try {
        g_evdi_event_thread = std::thread(evdi_event_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create evdi event thread\n");
        g_running.store(false, std::memory_order_release);
        notify_present_thread();
        close(g_present_event_fd);
        g_present_event_fd = -1;
        close(drm_fd);
        return EXIT_FAILURE;
    }

    try {
        g_poll_thread = std::thread(poll_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create poll thread\n");
        g_running.store(false, std::memory_order_release);
        notify_present_thread();
        g_evdi_event_cv.notify_all();

        if (g_evdi_event_thread.joinable()) {
            g_evdi_event_thread.join();
        }
        if (g_present_thread.joinable()) {
            g_present_thread.join();
        }
        if (g_update_thread.joinable()) {
            g_update_cv.notify_all();
            g_update_thread.join();
        }

        close(g_present_event_fd);
        g_present_event_fd = -1;
        close(drm_fd);
        return EXIT_FAILURE;
    }

    while (g_running.load(std::memory_order_acquire)) {
        pause();
    }

    notify_present_thread();
    g_update_cv.notify_all();
    g_evdi_event_cv.notify_all();

    if (g_poll_thread.joinable()) {
        kick_thread_out_of_ioctl(g_poll_thread);
    }

    sd_notify(0, "STATUS=Stopping poll thread…");
    if (g_poll_thread.joinable()) {
        g_poll_thread.join();
    }

    sd_notify(0, "STATUS=Stopping evdi event thread…");
    g_evdi_event_cv.notify_all();
    if (g_evdi_event_thread.joinable()) {
        g_evdi_event_thread.join();
    }

    sd_notify(0, "STATUS=Stopping present thread…");
    notify_present_thread();
    if (g_present_thread.joinable()) {
        g_present_thread.join();
    }

    if (g_present_event_fd >= 0) {
        close(g_present_event_fd);
        g_present_event_fd = -1;
    }

    drm_shutdown_close_fd();

    sd_notify(0, "STATUS=Stopping update thread…");
    g_update_cv.notify_all();
    if (g_update_thread.joinable()) {
        g_update_thread.join();
    }

    buffer_table_shutdown();

    sd_notify(0, "STATUS=Shutting down…");
    return EXIT_SUCCESS;
}

}
