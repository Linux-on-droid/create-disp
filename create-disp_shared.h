#pragma once

#include <inttypes.h>
#include <dirent.h>
#include <fcntl.h>
#include <pthread.h>
#include <unistd.h>
#include <sys/eventfd.h>
#include <sys/ioctl.h>

#include <array>
#include <atomic>
#include <cassert>
#include <cerrno>
#include <climits>
#include <cmath>
#include <condition_variable>
#include <cstdint>
#include <csignal>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <mutex>
#include <new>
#include <shared_mutex>
#include <sstream>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <xf86drm.h>
#include <systemd/sd-daemon.h>

#include <hybris/gralloc/gralloc.h>
#include <hybris/hwc2/hwc2_compatibility_layer.h>
#include <hybris/platforms/common/windowbuffer.h>

namespace create_disp {

struct drm_evdi_vsync {
    uint32_t display_id;
};

#define DRM_EVDI_CONNECT 0x00
#define DRM_EVDI_REQUEST_UPDATE 0x01
#define DRM_EVDI_GRABPIX 0x02
#define DRM_EVDI_ENABLE_CURSOR_EVENTS 0x03
#define DRM_EVDI_POLL 0x04
#define DRM_EVDI_GBM_ADD_BUFF 0x05
#define DRM_EVDI_GBM_GET_BUFF 0x06
#define DRM_EVDI_ADD_BUFF_CALLBACK 0x07
#define DRM_EVDI_GET_BUFF_CALLBACK 0x08
#define DRM_EVDI_DESTROY_BUFF_CALLBACK 0x09
#define DRM_EVDI_GBM_DEL_BUFF 0x0B
#define DRM_EVDI_GBM_CREATE_BUFF 0x0C
#define DRM_EVDI_GBM_CREATE_BUFF_CALLBACK 0x0D
#define DRM_EVDI_VSYNC 0x0E

#define DRM_IOCTL_EVDI_CONNECT DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_CONNECT, struct drm_evdi_connect)
#define DRM_IOCTL_EVDI_REQUEST_UPDATE DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_REQUEST_UPDATE, struct drm_evdi_request_update)
#define DRM_IOCTL_EVDI_GRABPIX DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_GRABPIX, struct drm_evdi_grabpix)
#define DRM_IOCTL_EVDI_ENABLE_CURSOR_EVENTS DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_ENABLE_CURSOR_EVENTS, struct drm_evdi_enable_cursor_events)
#define DRM_IOCTL_EVDI_POLL DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_POLL, struct drm_evdi_poll)
#define DRM_IOCTL_EVDI_GBM_ADD_BUFF DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_GBM_ADD_BUFF, struct drm_evdi_gbm_add_buf)
#define DRM_IOCTL_EVDI_GBM_GET_BUFF DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_GBM_GET_BUFF, struct drm_evdi_gbm_get_buff)
#define DRM_IOCTL_EVDI_ADD_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_ADD_BUFF_CALLBACK, struct drm_evdi_add_buff_callabck)
#define DRM_IOCTL_EVDI_GET_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_GET_BUFF_CALLBACK, struct drm_evdi_get_buff_callabck)
#define DRM_IOCTL_EVDI_DESTROY_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_DESTROY_BUFF_CALLBACK, struct drm_evdi_destroy_buff_callback)
#define DRM_IOCTL_EVDI_GBM_CREATE_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE + DRM_EVDI_GBM_CREATE_BUFF_CALLBACK, struct drm_evdi_create_buff_callabck)
#define DRM_IOCTL_EVDI_VSYNC DRM_IOW(DRM_COMMAND_BASE + DRM_EVDI_VSYNC, struct drm_evdi_vsync)

enum poll_event_type {
    none,
    add_buf,
    get_buf,
    destroy_buf,
    swap_to,
    create_buf
};

struct drm_evdi_request_update {
    int32_t reserved;
};

struct drm_evdi_connect {
    int32_t connected;
    int32_t dev_index;
    uint32_t width;
    uint32_t height;
    uint32_t refresh_rate;
    uint32_t display_id;
};

struct drm_evdi_poll {
    poll_event_type event;
    int poll_id;
    void *data;
};

struct drm_evdi_add_buff_callabck {
    int poll_id;
    int buff_id;
};

struct drm_evdi_get_buff_callabck {
    int poll_id;
    int version;
    int numFds;
    int numInts;
    int *fd_ints;
    int *data_ints;
};

struct drm_evdi_destroy_buff_callback {
    int poll_id;
};

struct drm_evdi_gbm_get_buff {
    int id;
    void *native_handle;
};

struct drm_evdi_gbm_create_buff {
    int *id;
    uint32_t *stride;
    uint32_t format;
    uint32_t width;
    uint32_t height;
};

struct drm_evdi_create_buff_callabck {
    int poll_id;
    int id;
    uint32_t stride;
};

#ifndef likely
#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#endif

struct RwbDeleter {
    void operator()(RemoteWindowBuffer* p) const {
        delete p;
    }
};

using SharedRwb = std::shared_ptr<RemoteWindowBuffer>;

constexpr int kMaxDriverDisplays = 5;
constexpr int kRwbUsage =
    GRALLOC_USAGE_HW_TEXTURE |
    GRALLOC_USAGE_HW_RENDER |
    GRALLOC_USAGE_HW_COMPOSER;
constexpr size_t kExpectedHandles = 4096;
constexpr int kShutdownKickSignal = SIGUSR1;
constexpr uint8_t kUpdateWorkNone = 0;
constexpr uint8_t kUpdateWorkRefresh = 1u << 0;
constexpr uint8_t kUpdateWorkDisconnect = 1u << 1;
constexpr size_t kBufferSegmentShift = 10;
constexpr size_t kBufferSegmentSize = size_t{1} << kBufferSegmentShift;
constexpr size_t kBufferSegmentMask = kBufferSegmentSize - 1;
constexpr size_t kBufferMaxSegments = 4096;

struct SlotManager {
    static constexpr uint32_t kCapacity = 32;

    std::array<int, kCapacity> slot_bufid{};
    std::array<uint64_t, kCapacity> slot_lastused{};
    std::array<uint8_t, kCapacity> slot_in_use{};
    uint64_t use_counter = 0;

    SlotManager();
    void reset();
    uint32_t assign(int bufid);
    void release(int bufid);
};

struct Display {
    int display_id = -1;
    long long hwc_id = 0;
    int width = 0;
    int height = 0;
    uint32_t stride = 0;
    bool connected = false;
    hwc2_compat_display_t* hwcDisplay = nullptr;
    SlotManager slot_mgr;
    uint64_t generation = 1;

    Display() = default;
    Display(const Display&) = default;
    Display& operator=(const Display&) = default;
};

struct DisplayRuntimeSnapshot {
    long long hwc_id = 0;
    hwc2_compat_display_t* hwcDisplay = nullptr;
    int width = 0;
    int height = 0;
    uint32_t stride = 0;
    bool connected = false;
    uint64_t generation = 0;
};

struct alignas(64) DisplayRuntime {
    std::atomic<uint64_t> seq{0};
    std::atomic<long long> hwc_id{0};
    std::atomic<uintptr_t> hwcDisplay{0};
    std::atomic<int> width{0};
    std::atomic<int> height{0};
    std::atomic<uint32_t> stride{0};
    std::atomic<bool> connected{false};
    std::atomic<uint64_t> generation{0};
};

enum class BufferOrigin : uint8_t {
    Imported = 0,
    Allocated = 1,
};

struct BufferEntry {
    BufferOrigin origin = BufferOrigin::Imported;
    native_handle_t* handle = nullptr;
    std::atomic<bool> live{true};
    std::atomic<SharedRwb> rwb;
    std::atomic<int> rwb_w{0};
    std::atomic<int> rwb_h{0};
    std::atomic<uint32_t> rwb_stride{0};
    std::atomic<int> rwb_format{0};
    int format = 0;
    uint32_t stride = 0;
    int width = 0;
    int height = 0;
    std::atomic<int> bound_display_id{-1};
    std::atomic<uint64_t> bound_generation{0};
    std::atomic<uint32_t> bound_slot{UINT32_MAX};

    ~BufferEntry();
};

struct BufferSlot {
    std::atomic<std::shared_ptr<BufferEntry>> entry;
};

struct BufferSegment {
    BufferSlot slots[kBufferSegmentSize];
};

struct PresentJob {
    int drv_display_id = 0;
    int buf_id = -1;
    uint32_t slot = 0;
    uint64_t generation = 0;
    SharedRwb rwb;
};

enum class PreparePresentJobResult : uint8_t {
    Ready = 0,
    NeedSlow = 1,
    Abort = 2,
};

struct alignas(64) PresentMailbox {
    std::atomic<bool> pending{false};
    std::atomic_flag lock = ATOMIC_FLAG_INIT;
    PresentJob job;
};

struct QueuedEvdiEvent {
    poll_event_type event;
    int poll_id;
    uint8_t data[32];
};

template <typename T, size_t Capacity>
class SpscRingBuffer {
    static_assert((Capacity != 0) && ((Capacity & (Capacity - 1)) == 0), "Capacity must be power of 2");

private:
    struct alignas(64) {
        std::atomic<size_t> head{0};
        size_t cached_tail{0};
    } producer;

    struct alignas(64) {
        std::atomic<size_t> tail{0};
        size_t cached_head{0};
    } consumer;

    T buffer[Capacity];

public:
    bool push(const T& item) {
        size_t h = producer.head.load(std::memory_order_relaxed);
        size_t next = (h + 1) & (Capacity - 1);
        if (next == producer.cached_tail) {
            producer.cached_tail = consumer.tail.load(std::memory_order_acquire);
            if (next == producer.cached_tail) {
                return false;
            }
        }
        buffer[h] = item;
        producer.head.store(next, std::memory_order_release);
        return true;
    }

    bool pop(T& item) {
        size_t t = consumer.tail.load(std::memory_order_relaxed);
        if (t == consumer.cached_head) {
            consumer.cached_head = producer.head.load(std::memory_order_acquire);
            if (t == consumer.cached_head) {
                return false;
            }
        }
        item = buffer[t];
        consumer.tail.store((t + 1) & (Capacity - 1), std::memory_order_release);
        return true;
    }

    bool empty() const {
        return producer.head.load(std::memory_order_acquire) ==
               consumer.tail.load(std::memory_order_relaxed);
    }
};

extern std::unordered_map<long long, int> g_hwc_to_drv;
extern std::unordered_map<int, long long> g_drv_to_hwc;
extern std::array<int, kMaxDriverDisplays> g_free_drv_ids;
extern int g_free_drv_count;
extern bool g_free_drv_ids_initialized;
extern std::atomic<bool> drm_ready;
extern std::array<std::atomic<bool>, kMaxDriverDisplays> g_resync_pending;

extern std::mutex g_display_mutex;
extern std::mutex g_buffer_mutex;
extern std::array<std::mutex, kMaxDriverDisplays> g_hwc_mutex;
extern std::shared_mutex g_drm_mutex;

extern std::mutex g_update_mutex;
extern std::condition_variable g_update_cv;
extern std::array<std::atomic<uint8_t>, kMaxDriverDisplays> g_update_work;
extern std::atomic<uint32_t> g_update_pending_mask;
extern std::atomic<int> g_update_rr;
extern std::thread g_update_thread;

extern std::atomic<bool> g_reopen_requested;
extern std::atomic<int> g_modeset_inflight;

extern std::thread g_present_thread;
extern std::atomic<uint32_t> g_present_ready_mask;
extern std::atomic<int> g_present_rr;
extern int g_present_event_fd;

extern std::thread g_poll_thread;
extern std::atomic<bool> g_running;

extern hwc2_compat_device_t* hwcDevice;
extern HWC2EventListener eventListener;
extern int drm_fd;

extern std::unordered_map<int, Display> g_displays;
extern std::array<DisplayRuntime, kMaxDriverDisplays> g_display_runtime;

extern std::array<std::atomic<BufferSegment*>, kBufferMaxSegments> g_buffer_segments;
extern std::mutex g_buffer_segment_alloc_mutex;
extern std::atomic<uint32_t> g_next_buffer_id;
extern std::array<std::unordered_set<int>, kMaxDriverDisplays> g_display_bound_buffers;

extern std::array<PresentMailbox, kMaxDriverDisplays> g_present_mailboxes;

extern SpscRingBuffer<QueuedEvdiEvent, 256> g_evdi_event_queue;
extern std::atomic<bool> g_evdi_event_thread_sleeping;
extern std::mutex g_evdi_event_mutex;
extern std::condition_variable g_evdi_event_cv;
extern std::thread g_evdi_event_thread;

void request_reopen();
int ioctl_retry(int fd, unsigned long req, void *arg);
int drm_get_fd();
void drm_shutdown_close_fd();
int drm_ioctl(unsigned long req, void *arg);
bool should_request_reopen(int err);
void clear_pending_work_atomic(int drv_display_id);
void publish_update_work(int drv_display_id, uint8_t work_bits);
void schedule_update(int drv_display_id);
void schedule_disconnect(int drv_display_id);
bool take_next_update_display(int& out_drv_display_id);

SharedRwb make_rwb(int w, int h, uint32_t stride, int format, int usage, buffer_handle_t handle);

Display& get_or_create_display(int display_id);
void publish_display_runtime_locked(int display_id);
DisplayRuntimeSnapshot snapshot_display_runtime_atomic(int display_id);
bool display_runtime_present_ready(const DisplayRuntimeSnapshot& s, uint64_t generation);

void request_display_resync(int drv_display_id);
int drv_id_for_hwc_atomic(long long hwc_id);
int drv_id_for_hwc(long long hwc_id);
void init_free_driver_slots_once();
int alloc_driver_slot_for_hwc(long long hwc_id);
void release_driver_slot_for_hwc(long long hwc_id);

bool buffer_id_to_indices(int id, size_t& seg_idx, size_t& slot_idx);
BufferSegment* get_buffer_segment_if_present(size_t seg_idx);
BufferSegment* ensure_buffer_segment(size_t seg_idx);
BufferSlot* get_buffer_slot_if_present(int id);
BufferSlot* ensure_buffer_slot(int id);
std::shared_ptr<BufferEntry> get_entry_atomic(int id);
void unbind_buffer_from_display_locked(int buf_id, int drv_display_id);
void reset_buffer_binding_locked(int buf_id, const std::shared_ptr<BufferEntry>& entry);
bool buffer_entry_is_live_atomic(int buf_id, const std::shared_ptr<BufferEntry>& entry);
void bind_buffer_to_display_locked(int buf_id, const std::shared_ptr<BufferEntry>& entry, int drv_display_id, uint64_t generation, uint32_t slot);
std::shared_ptr<BufferEntry> remove_entry_atomic(int id);
void unbind_buffer_everywhere_locked(int buf_id);
void erase_buffer_locked(int buf_id);
void reset_display_bindings_locked(int drv_display_id);
void buffer_table_reserve_ids(size_t count);
void buffer_table_shutdown();
int add_handle(native_handle_t* handle, BufferOrigin origin, int format, uint32_t stride, uint32_t width, uint32_t height);

SharedRwb load_entry_rwb_atomic(const std::shared_ptr<BufferEntry>& entry);
void store_entry_rwb_atomic(const std::shared_ptr<BufferEntry>& entry, const SharedRwb& rwb);
void get_entry_buffer_geometry(const std::shared_ptr<BufferEntry>& entry, const DisplayRuntimeSnapshot& dsnap, uint32_t& buf_stride, int& buf_w, int& buf_h, int& buf_format);
bool entry_rwb_matches_atomic(const std::shared_ptr<BufferEntry>& entry, int buf_w, int buf_h, uint32_t buf_stride, int buf_format, SharedRwb& out_rwb);
PreparePresentJobResult prepare_present_job_fast(int id, int drv_display_id, const std::shared_ptr<BufferEntry>& entry, PresentJob& out);
bool prepare_present_job_slow(int id, int drv_display_id, const std::shared_ptr<BufferEntry>& entry, PresentJob& out);

void notify_present_thread();
void wait_for_present_work();
void lock_present_mailbox(int drv_display_id);
void unlock_present_mailbox(int drv_display_id);
bool take_next_present_display(int& out_drv_display_id);
bool try_dequeue_present_job(int drv_display_id, PresentJob& out);
void enqueue_present_job(PresentJob&& j);
void flush_present_jobs_for_display(int drv_display_id);

int evdi_vsync(int drv_display_id);
bool is_evdi_lindroid(int fd);
int find_evdi_lindroid_device();
int open_evdi_lindroid_or_create();
int evdi_connect(int device_index, uint32_t width, uint32_t height, uint32_t refresh_rate, uint32_t display_id, int connected);
int hz_from_period_ns(int32_t ns);
int get_refresh_hz_from_active_config(const HWC2DisplayConfig* cfg);
int reconnect_display_mode(int display_id, int target_width, int target_height, int refresh_hz, bool disconnect_first);
int update_display(int display_id);
void disconnect_display(int drv_id);

void onVsyncReceived(HWC2EventListener* listener, int32_t sequenceId, hwc2_display_t display, int64_t timestamp);
void onHotplugReceived(HWC2EventListener* listener, int32_t sequenceId, hwc2_display_t display, bool connected, bool primaryDisplay);
void onRefreshReceived(HWC2EventListener* listener, int32_t sequenceId, hwc2_display_t display);

void get_buf_from_map(void *data, int poll_id);
void swap_to_buff(void *data, int poll_id);
void destroy_buff(void *data, int poll_id);
void create_buff(void *data, int poll_id);

void present_thread_main();
void update_thread_main();
void evdi_event_thread_main();
void poll_thread_main();

void handle_signal(int signo);
void kick_thread_out_of_ioctl(std::thread& t);
void install_signal_handlers();

int run_create_disp();
}
