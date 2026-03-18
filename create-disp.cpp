#include <inttypes.h>
#include <dirent.h>
#include <fcntl.h>
#include <iostream>
#include <sstream>
#include <cstring>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/eventfd.h>
#include <cerrno>
#include <xf86drm.h>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <new>
#include <vector>
#include <fstream>
#include <poll.h>
#include <cmath>
#include <climits>
#include <cstdint>
#include <deque>
#include <chrono>
#include <array>
#include <thread>
#include <atomic>
#include <csignal>
#include <mutex>
#include <shared_mutex>
#include <condition_variable>

#include <systemd/sd-daemon.h>

#include <hybris/hwc2/hwc2_compatibility_layer.h>
#include <hybris/gralloc/gralloc.h>
#include <hybris/platforms/common/windowbuffer.h>

struct drm_evdi_vsync {
    uint32_t display_id;
};

#define DRM_EVDI_CONNECT          0x00
#define DRM_EVDI_REQUEST_UPDATE   0x01
#define DRM_EVDI_GRABPIX          0x02
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

#define DRM_IOCTL_EVDI_CONNECT DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_CONNECT, struct drm_evdi_connect)
#define DRM_IOCTL_EVDI_REQUEST_UPDATE DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_REQUEST_UPDATE, struct drm_evdi_request_update)
#define DRM_IOCTL_EVDI_GRABPIX DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_GRABPIX, struct drm_evdi_grabpix)
#define DRM_IOCTL_EVDI_ENABLE_CURSOR_EVENTS DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_ENABLE_CURSOR_EVENTS, struct drm_evdi_enable_cursor_events)
#define DRM_IOCTL_EVDI_POLL DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_POLL, struct drm_evdi_poll)
#define DRM_IOCTL_EVDI_GBM_ADD_BUFF DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_GBM_ADD_BUFF, struct drm_evdi_gbm_add_buf)
#define DRM_IOCTL_EVDI_GBM_GET_BUFF DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_GBM_GET_BUFF, struct drm_evdi_gbm_get_buff)
#define DRM_IOCTL_EVDI_ADD_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_ADD_BUFF_CALLBACK, struct drm_evdi_add_buff_callabck)
#define DRM_IOCTL_EVDI_GET_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_GET_BUFF_CALLBACK, struct drm_evdi_get_buff_callabck)
#define DRM_IOCTL_EVDI_DESTROY_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_DESTROY_BUFF_CALLBACK, struct drm_evdi_destroy_buff_callback)
#define DRM_IOCTL_EVDI_GBM_CREATE_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE +  \
	DRM_EVDI_GBM_CREATE_BUFF_CALLBACK, struct drm_evdi_create_buff_callabck)
#define DRM_IOCTL_EVDI_VSYNC DRM_IOW(DRM_COMMAND_BASE +  \
        DRM_EVDI_VSYNC, struct drm_evdi_vsync)

static const int kMaxDriverDisplays = 5;
static std::unordered_map<long long, int> g_hwc_to_drv;
static std::unordered_map<int, long long> g_drv_to_hwc;
static std::array<int, kMaxDriverDisplays> g_free_drv_ids = {};
static int g_free_drv_count = 0;
static bool g_free_drv_ids_initialized = false;
static std::atomic<bool> drm_ready{false};
static std::array<std::atomic<bool>, kMaxDriverDisplays> g_resync_pending{};

static std::mutex g_state_mutex;
static std::array<std::mutex, kMaxDriverDisplays> g_hwc_mutex;

static std::shared_mutex g_drm_mutex;

static std::mutex g_update_mutex;
static std::condition_variable g_update_cv;
enum : uint8_t {
    kUpdateWorkNone       = 0,
    kUpdateWorkRefresh    = 1u << 0,
    kUpdateWorkDisconnect = 1u << 1,
};
static std::array<std::atomic<uint8_t>, kMaxDriverDisplays> g_update_work = {};
static std::atomic<uint32_t> g_update_pending_mask{0};
static std::atomic<int> g_update_rr{0};
static std::thread g_update_thread;

static std::atomic<bool> g_reopen_requested{false};
static std::atomic<int> g_modeset_inflight{0};

static std::thread g_present_thread;
static std::atomic<uint32_t> g_present_ready_mask{0};
static std::atomic<int> g_present_rr{0};
static int g_present_event_fd = -1;

static constexpr int kShutdownKickSignal = SIGUSR1;

int drm_fd;

static inline void request_reopen()
{
    (void)g_reopen_requested.exchange(true, std::memory_order_acq_rel);
}

static inline int ioctl_retry(int fd, unsigned long req, void *arg)
{
    int rc;
    do {
        rc = ::ioctl(fd, req, arg);
    } while (rc < 0 && errno == EINTR);
    return rc;
}

static inline int drm_get_fd()
{
    std::shared_lock<std::shared_mutex> lk(g_drm_mutex);
    return drm_fd;
}

static inline void drm_shutdown_close_fd()
{
    std::unique_lock<std::shared_mutex> lk(g_drm_mutex);
    if (drm_fd >= 0) {
        ::close(drm_fd);
        drm_fd = -1;
    }
    drm_ready.store(false, std::memory_order_release);
}

static inline int drm_ioctl(unsigned long req, void *arg)
{
    int fd = drm_get_fd();
    if (fd < 0) {
        errno = EBADF;
        return -1;
    }
    return ioctl_retry(fd, req, arg);
}

static inline bool should_request_reopen(int err)
{
    return drm_ready.load(std::memory_order_acquire) &&
           (err == ENODEV || err == EBADF) &&
           g_modeset_inflight.load(std::memory_order_acquire) == 0;
}

static inline void clear_pending_work_atomic(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays)
        return;

    g_update_work[drv_display_id].store(kUpdateWorkNone, std::memory_order_release);
    g_update_pending_mask.fetch_and(~(uint32_t(1) << uint32_t(drv_display_id)),
                                    std::memory_order_acq_rel);
}

static inline void request_display_resync(int drv_display_id);
static inline void publish_update_work(int drv_display_id, uint8_t work_bits)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays)
        return;

    g_update_work[drv_display_id].fetch_or(work_bits, std::memory_order_acq_rel);
    g_update_pending_mask.fetch_or(uint32_t(1) << uint32_t(drv_display_id),
                                   std::memory_order_acq_rel);
    g_update_cv.notify_one();
}

static inline void schedule_update(int drv_display_id)
{
    publish_update_work(drv_display_id, kUpdateWorkRefresh);
}

static inline void schedule_disconnect(int drv_display_id)
{
    publish_update_work(drv_display_id, kUpdateWorkDisconnect);
}

static inline bool take_next_update_display(int& out_drv_display_id)
{
    const uint32_t mask = g_update_pending_mask.load(std::memory_order_acquire);
    if (mask == 0)
        return false;

    const int start = g_update_rr.fetch_add(1, std::memory_order_relaxed);
    for (int i = 0; i < kMaxDriverDisplays; ++i) {
        const int d = (start + i) % kMaxDriverDisplays;
        const uint32_t bit = uint32_t(1) << uint32_t(d);

        if ((mask & bit) == 0)
            continue;

        const uint32_t prev =
            g_update_pending_mask.fetch_and(~bit, std::memory_order_acq_rel);
        if (prev & bit) {
            out_drv_display_id = d;
            return true;
        }
    }

    return false;
}

namespace {
struct RwbDeleter {
    void operator()(RemoteWindowBuffer* p) const {
        delete p;
    }
};
using SharedRwb = std::shared_ptr<RemoteWindowBuffer>;

static inline SharedRwb make_rwb(int w, int h, uint32_t stride,
                                 int format, int usage,
                                 buffer_handle_t handle)
{
    RemoteWindowBuffer* rb = new (std::nothrow) RemoteWindowBuffer(w, h, stride, format, usage, handle);
    if (!rb) return {};
    return SharedRwb(rb, RwbDeleter{});
}
} // namespace

struct SlotManager {
    static constexpr uint32_t kCapacity = 32;

    std::unordered_map<int, uint32_t>      bufid_to_slot;
    std::unordered_map<uint32_t, int>      slot_to_bufid;
    std::unordered_map<uint32_t, uint64_t> slot_lastused;
    std::array<uint8_t, kCapacity>         slot_free;
    uint64_t                               use_counter = 0;

    SlotManager() { slot_free.fill(1); }

    void reset() {
        bufid_to_slot.clear();
        slot_to_bufid.clear();
        slot_lastused.clear();
        slot_free.fill(1);
        use_counter = 0;
    }

    uint32_t assign(int bufid) {
        auto it = bufid_to_slot.find(bufid);
        if (it != bufid_to_slot.end()) {
            slot_lastused[it->second] = ++use_counter;
            return it->second;
        }
        for (uint32_t i = 0; i < kCapacity; i++) {
            if (slot_free[i]) {
                slot_free[i] = 0;
                bufid_to_slot[bufid]  = i;
                slot_to_bufid[i]      = bufid;
                slot_lastused[i]      = ++use_counter;
                return i;
            }
        }
        uint32_t lru_slot = UINT32_MAX;
        uint64_t lru_time = UINT64_MAX;
        for (auto& kv : slot_lastused) {
            if (kv.second < lru_time) {
                lru_time = kv.second;
                lru_slot = kv.first;
            }
        }
        if (lru_slot == UINT32_MAX) {
            fprintf(stderr, "SlotManager: exhausted all %u slots\n", kCapacity);
            return UINT32_MAX;
        }
        int evicted = slot_to_bufid[lru_slot];
        bufid_to_slot.erase(evicted);
        bufid_to_slot[bufid]     = lru_slot;
        slot_to_bufid[lru_slot]  = bufid;
        slot_lastused[lru_slot]  = ++use_counter;
        fprintf(stderr, "SlotManager: evicted bufid %d from slot %u for bufid %d\n",
                evicted, lru_slot, bufid);
        return lru_slot;
    }

    void release(int bufid) {
        auto it = bufid_to_slot.find(bufid);
        if (it == bufid_to_slot.end()) return;
        uint32_t slot = it->second;
        slot_free[slot] = 1;
        slot_to_bufid.erase(slot);
        slot_lastused.erase(slot);
        bufid_to_slot.erase(it);
    }
};

struct BufferEntry;

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

static std::unordered_map<int, Display> g_displays;

// Poll thread
static std::thread g_poll_thread;
static std::atomic<bool> g_running{true};

#ifndef likely
#define likely(x)	__builtin_expect(!!(x), 1)
#define unlikely(x)	__builtin_expect(!!(x), 0)
#endif

static constexpr int kRwbUsage =
	GRALLOC_USAGE_HW_TEXTURE |
	GRALLOC_USAGE_HW_RENDER |
	GRALLOC_USAGE_HW_COMPOSER;

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

static inline Display& get_or_create_display(int display_id) {
    auto it = g_displays.find(display_id);
    if (it != g_displays.end())
        return it->second;
    auto [ins_it, inserted] = g_displays.try_emplace(display_id);
    ins_it->second.display_id = display_id;
    return ins_it->second;
}

static std::array<DisplayRuntime, kMaxDriverDisplays> g_display_runtime;

static inline void publish_display_runtime_locked(int display_id)
{
    if (display_id < 0 || display_id >= kMaxDriverDisplays)
        return;

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

static inline DisplayRuntimeSnapshot snapshot_display_runtime_atomic(int display_id)
{
    DisplayRuntimeSnapshot s;
    if (display_id < 0 || display_id >= kMaxDriverDisplays)
        return s;

    DisplayRuntime& R = g_display_runtime[display_id];
    for (;;) {
        uint64_t seq1 = R.seq.load(std::memory_order_acquire);
        if (seq1 & 1ULL) {
            std::this_thread::yield();
            continue;
        }

        s.hwc_id = R.hwc_id.load(std::memory_order_relaxed);
        s.hwcDisplay = reinterpret_cast<hwc2_compat_display_t*>(
            R.hwcDisplay.load(std::memory_order_relaxed));
        s.width = R.width.load(std::memory_order_relaxed);
        s.height = R.height.load(std::memory_order_relaxed);
        s.stride = R.stride.load(std::memory_order_relaxed);
        s.connected = R.connected.load(std::memory_order_relaxed);
        s.generation = R.generation.load(std::memory_order_relaxed);

        uint64_t seq2 = R.seq.load(std::memory_order_acquire);
        if (likely(seq1 == seq2))
            return s;
    }
}

static inline bool display_runtime_present_ready(const DisplayRuntimeSnapshot& s,
                                                 uint64_t generation)
{
    return s.connected &&
           s.hwcDisplay != nullptr &&
           s.generation == generation;
}

hwc2_compat_device_t* hwcDevice;

static inline void request_display_resync(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays)
        return;

    bool expected = false;
    if (!g_resync_pending[drv_display_id].compare_exchange_strong(
            expected, true, std::memory_order_acq_rel))
        return;

    schedule_update(drv_display_id);
}

static inline int drv_id_for_hwc_atomic(long long hwc_id)
{
    if (hwc_id == 0)
        return -1;

    for (int d = 0; d < kMaxDriverDisplays; ++d) {
        DisplayRuntimeSnapshot s = snapshot_display_runtime_atomic(d);
        if (!s.connected)
            continue;
        if (s.hwc_id == hwc_id)
            return d;
    }

    return -1;
}

enum class BufferOrigin : uint8_t {
    Imported = 0,
    Allocated = 1,
};

struct BufferEntry {
    BufferOrigin origin = BufferOrigin::Imported;
    native_handle_t* handle = nullptr;
    // created first swap_to:
    SharedRwb rwb;
    // Track geometry used to build rwb so we can detect mismatch
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

    ~BufferEntry() {
        rwb.reset();
        if (!handle) return;
        if (origin == BufferOrigin::Imported) {
            for (int i = 0; i < handle->numFds; i++)
                close(handle->data[i]);
            free(handle);
        } else {
            (void)hybris_gralloc_release((buffer_handle_t)handle, 1);
        }
        handle = nullptr;
    }
};

static std::unordered_map<int, std::shared_ptr<BufferEntry>> g_buffers;

static inline void erase_buffer_locked(int buf_id)
{
    auto it = g_buffers.find(buf_id);
    if (it != g_buffers.end())
        g_buffers.erase(it);

    for (auto& kv : g_displays)
        kv.second.slot_mgr.release(buf_id);
}

static inline void reset_buffer_binding_locked(const std::shared_ptr<BufferEntry>& entry)
{
    if (!entry)
        return;

    entry->bound_display_id.store(-1, std::memory_order_relaxed);
    entry->bound_generation.store(0, std::memory_order_relaxed);
    entry->bound_slot.store(UINT32_MAX, std::memory_order_relaxed);
}

static inline void reset_display_bindings_locked(int drv_display_id)
{
    Display& D = get_or_create_display(drv_display_id);

    std::vector<int> buffer_ids;
    buffer_ids.reserve(g_buffers.size());
    for (const auto& kv : g_buffers)
        buffer_ids.push_back(kv.first);

    for (int buf_id : buffer_ids)
        D.slot_mgr.release(buf_id);

    for (int buf_id : buffer_ids) {
        auto it = g_buffers.find(buf_id);
        if (it != g_buffers.end()) {
            const std::shared_ptr<BufferEntry>& entry = it->second;
            if (entry &&
                entry->bound_display_id.load(std::memory_order_relaxed) == drv_display_id)
                reset_buffer_binding_locked(entry);
        }
    }

    D.slot_mgr.reset();
}

static constexpr size_t kExpectedHandles = 4096;
/* buffer ids must be > 0 to not break PRIME export */
int next_id = 1;
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
            if (next == producer.cached_tail) return false;
        }
        buffer[h] = item;
        producer.head.store(next, std::memory_order_release);
        return true;
    }

    bool pop(T& item) {
        size_t t = consumer.tail.load(std::memory_order_relaxed);
        if (t == consumer.cached_head) {
            consumer.cached_head = producer.head.load(std::memory_order_acquire);
            if (t == consumer.cached_head) return false;
        }
        item = buffer[t];
        consumer.tail.store((t + 1) & (Capacity - 1), std::memory_order_release);
        return true;
    }

    bool empty() const {
        return producer.head.load(std::memory_order_acquire) == consumer.tail.load(std::memory_order_relaxed);
    }
};

static SpscRingBuffer<QueuedEvdiEvent, 256> g_evdi_event_queue;
static std::atomic<bool> g_evdi_event_thread_sleeping{false};
static std::mutex g_evdi_event_mutex;
static std::condition_variable g_evdi_event_cv;
static std::thread g_evdi_event_thread;

static inline int evdi_vsync(int drv_display_id)
{
    struct drm_evdi_vsync cmd = {};
    cmd.display_id = (uint32_t)drv_display_id;
    
    int fd = drm_get_fd();
    if (fd < 0)
        return -EBADF;

    return ioctl_retry(fd, DRM_IOCTL_EVDI_VSYNC, &cmd);
}

static inline int add_handle(native_handle_t* handle,
                                BufferOrigin origin,
                                int format,
                                uint32_t stride,
                                uint32_t width,
                                uint32_t height)
{
    std::lock_guard<std::mutex> lk(g_state_mutex);

    if (next_id <= 0)
        next_id = 1;

    int id = next_id++;
    auto e = std::make_shared<BufferEntry>();
    e->origin = origin;
    e->handle = handle;

    e->format = format;
    e->stride = stride;
    e->width = width;
    e->height = height;

    g_buffers[id] = std::move(e);
    return id;
}

static inline std::shared_ptr<BufferEntry> get_entry_locked_nolock(int id)
{
    auto it = g_buffers.find(id);
    return (it != g_buffers.end()) ? it->second : nullptr;
}

struct PresentJob {
    int drv_display_id = 0;
    int buf_id = -1;
    uint32_t slot = 0;
    uint64_t generation = 0;
    std::shared_ptr<BufferEntry> entry;
    SharedRwb rwb;
};

static inline SharedRwb load_entry_rwb_atomic(const std::shared_ptr<BufferEntry>& entry)
{
    return std::atomic_load(&entry->rwb);
}

static inline void store_entry_rwb_atomic(const std::shared_ptr<BufferEntry>& entry,
                                          const SharedRwb& rwb)
{
    std::atomic_store(&entry->rwb, rwb);
}

static inline void get_entry_buffer_geometry(const std::shared_ptr<BufferEntry>& entry,
                                             const DisplayRuntimeSnapshot& dsnap,
                                             uint32_t& buf_stride,
                                             int& buf_w,
                                             int& buf_h,
                                             int& buf_format)
{
    buf_format = entry->format;
    buf_stride = entry->stride;

    if (entry->origin == BufferOrigin::Imported) {
        buf_w = entry->width;
        buf_h = entry->height;
    } else {
        buf_w = entry->width ? entry->width : dsnap.width;
        buf_h = entry->height ? entry->height : dsnap.height;
    }
}

static inline bool entry_rwb_matches_atomic(const std::shared_ptr<BufferEntry>& entry,
                                           int buf_w,
                                            int buf_h,
                                            uint32_t buf_stride,
                                            int buf_format,
                                            SharedRwb& out_rwb)
{
    out_rwb = load_entry_rwb_atomic(entry);
    if (!out_rwb)
        return false;

    return entry->rwb_w.load(std::memory_order_acquire) == buf_w &&
           entry->rwb_h.load(std::memory_order_acquire) == buf_h &&
           entry->rwb_stride.load(std::memory_order_acquire) == buf_stride &&
           entry->rwb_format.load(std::memory_order_acquire) == buf_format;
}

static inline bool prepare_present_job_fast(int id,
                                            int drv_display_id,
                                            const std::shared_ptr<BufferEntry>& entry,
                                           PresentJob& out)
{
    DisplayRuntimeSnapshot dsnap = snapshot_display_runtime_atomic(drv_display_id);
    if (unlikely(!dsnap.hwcDisplay || !dsnap.connected ||
                 dsnap.width <= 0 || dsnap.height <= 0 || dsnap.stride == 0)) {
        request_display_resync(drv_display_id);
        return false;
    }

    const int bound_display =
        entry->bound_display_id.load(std::memory_order_acquire);
    const uint64_t bound_generation =
       entry->bound_generation.load(std::memory_order_acquire);
    const uint32_t bound_slot =
        entry->bound_slot.load(std::memory_order_acquire);

    if (bound_display != drv_display_id ||
        bound_generation != dsnap.generation ||
        bound_slot == UINT32_MAX)
        return false;

    uint32_t buf_stride = 0;
    int buf_w = 0;
    int buf_h = 0;
   int buf_format = 0;
    get_entry_buffer_geometry(entry, dsnap, buf_stride, buf_w, buf_h, buf_format);

    if (unlikely(buf_stride == 0 || buf_w <= 0 || buf_h <= 0)) {
        fprintf(stderr,
                "Invalid buffer geometry for id=%d (origin=%d, w=%d, h=%d, stride=%u)\n",
                id, (int)entry->origin, buf_w, buf_h, buf_stride);
       request_display_resync(drv_display_id);
        return false;
    }

    SharedRwb rwb;
    if (!entry_rwb_matches_atomic(entry, buf_w, buf_h, buf_stride, buf_format, rwb))
        return false;

    out.drv_display_id = drv_display_id;
    out.buf_id = id;
    out.generation = dsnap.generation;
    out.slot = bound_slot;
    out.entry = entry;
    out.rwb = std::move(rwb);
    return true;
}

static inline bool prepare_present_job_slow(int id,
                                            int drv_display_id,
                                            const std::shared_ptr<BufferEntry>& entry,
                                            PresentJob& out)
{
    DisplayRuntimeSnapshot dsnap;
    uint32_t slot = UINT32_MAX;
    uint32_t buf_stride = 0;
    int buf_w = 0;
    int buf_h = 0;
    int buf_format = 0;

    {
        std::lock_guard<std::mutex> lk(g_state_mutex);

        if (get_entry_locked_nolock(id) != entry || !entry->handle) {
            request_display_resync(drv_display_id);
            return false;
        }

        Display& D = get_or_create_display(drv_display_id);
        dsnap.hwcDisplay = D.hwcDisplay;
        dsnap.width = D.width;
        dsnap.height = D.height;
        dsnap.stride = D.stride;
        dsnap.connected = D.connected;
        dsnap.generation = D.generation;

        if (unlikely(!dsnap.hwcDisplay || !dsnap.connected ||
                     dsnap.width <= 0 || dsnap.height <= 0 || dsnap.stride == 0)) {
            request_display_resync(drv_display_id);
            return false;
        }

        const int bound_display =
            entry->bound_display_id.load(std::memory_order_relaxed);
        const uint64_t bound_generation =
            entry->bound_generation.load(std::memory_order_relaxed);

        if (bound_generation != 0 && bound_generation != dsnap.generation) {
            request_display_resync(drv_display_id);
            return false;
        }

        if (bound_display >= 0 &&
            bound_display != drv_display_id &&
            bound_generation == dsnap.generation) {
            request_display_resync(drv_display_id);
            return false;
        }

        if (bound_display != drv_display_id || bound_generation != dsnap.generation) {
            if ((entry->width  != 0 && entry->width  != dsnap.width) ||
                (entry->height != 0 && entry->height != dsnap.height)) {
                fprintf(stderr,
                        "Dropping stale/mismatched buffer id=%d for display=%d "
                        "(buf=%dx%d, display=%dx%d)\n",
                        id, drv_display_id,
                        entry->width, entry->height,
                        dsnap.width, dsnap.height);
                request_display_resync(drv_display_id);
                return false;
            }
           reset_buffer_binding_locked(entry);
            entry->bound_display_id.store(drv_display_id, std::memory_order_relaxed);
            entry->bound_generation.store(dsnap.generation, std::memory_order_relaxed);
        }

        slot = D.slot_mgr.assign(id);
        if (slot == UINT32_MAX) {
            fprintf(stderr,
                    "SlotManager: failed to assign slot for bufid %d on display %d\n",
                    id, drv_display_id);
            return false;
        }

        entry->bound_slot.store(slot, std::memory_order_relaxed);
        get_entry_buffer_geometry(entry, dsnap, buf_stride, buf_w, buf_h, buf_format);
    }

    if (unlikely(buf_stride == 0 || buf_w <= 0 || buf_h <= 0)) {
        fprintf(stderr,
                "Invalid buffer geometry for id=%d (origin=%d, w=%d, h=%d, stride=%u)\n",
                id, (int)entry->origin, buf_w, buf_h, buf_stride);
        request_display_resync(drv_display_id);
        return false;
    }

    SharedRwb rwb;
    if (!entry_rwb_matches_atomic(entry, buf_w, buf_h, buf_stride, buf_format, rwb)) {
        SharedRwb new_rwb = make_rwb(buf_w, buf_h, buf_stride, buf_format,
                                     kRwbUsage, entry->handle);
        if (unlikely(!new_rwb)) {
            fprintf(stderr, "Failed to allocate RemoteWindowBuffer for id=%d\n", id);
            return false;
        }

        if (entry->bound_display_id.load(std::memory_order_acquire) != drv_display_id ||
            entry->bound_generation.load(std::memory_order_acquire) != dsnap.generation ||
            entry->bound_slot.load(std::memory_order_acquire) != slot) {
            return false;
        }

        store_entry_rwb_atomic(entry, new_rwb);
        entry->rwb_w.store(buf_w, std::memory_order_release);
        entry->rwb_h.store(buf_h, std::memory_order_release);
        entry->rwb_stride.store(buf_stride, std::memory_order_release);
        entry->rwb_format.store(buf_format, std::memory_order_release);
        rwb = std::move(new_rwb);
    }

    out.drv_display_id = drv_display_id;
    out.buf_id = id;
    out.generation = dsnap.generation;
    out.slot = slot;
    out.entry = entry;
    out.rwb = std::move(rwb);
    return true;
}

struct alignas(64) PresentMailbox {
    std::atomic<bool> pending{false};
    std::atomic_flag lock = ATOMIC_FLAG_INIT;
    PresentJob job;
};

static std::array<PresentMailbox, kMaxDriverDisplays> g_present_mailboxes;

static inline void notify_present_thread()
{
    if (g_present_event_fd < 0)
        return;

    const uint64_t one = 1;
    ssize_t rc;
    do {
        rc = ::write(g_present_event_fd, &one, sizeof(one));
    } while (rc < 0 && errno == EINTR);
}

static inline void wait_for_present_work()
{
    if (g_present_event_fd < 0)
        return;

    uint64_t cnt = 0;
    for (;;) {
        ssize_t rc = ::read(g_present_event_fd, &cnt, sizeof(cnt));
        if (rc == (ssize_t)sizeof(cnt))
            return;
        if (rc < 0 && errno == EINTR) {
            if (!g_running.load(std::memory_order_acquire))
                return;
            continue;
        }
        return;
    }
}

static inline void lock_present_mailbox(int drv_display_id)
{
    PresentMailbox& m = g_present_mailboxes[drv_display_id];
    while (m.lock.test_and_set(std::memory_order_acquire))
        std::this_thread::yield();
}

static inline void unlock_present_mailbox(int drv_display_id)
{
    g_present_mailboxes[drv_display_id].lock.clear(std::memory_order_release);
}

static inline bool take_next_present_display(int& out_drv_display_id)
{
    const uint32_t mask = g_present_ready_mask.load(std::memory_order_acquire);
    if (mask == 0)
        return false;

    const int start = g_present_rr.fetch_add(1, std::memory_order_relaxed);
    for (int i = 0; i < kMaxDriverDisplays; ++i) {
        const int d = (start + i) % kMaxDriverDisplays;
        const uint32_t bit = uint32_t(1) << uint32_t(d);

        if ((mask & bit) == 0)
            continue;

        const uint32_t prev =
            g_present_ready_mask.fetch_and(~bit, std::memory_order_acq_rel);
        if (prev & bit) {
            out_drv_display_id = d;
            return true;
        }
    }

    return false;
}

static inline bool try_dequeue_present_job(int drv_display_id, PresentJob& out)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays)
        return false;

    PresentMailbox& m = g_present_mailboxes[drv_display_id];
    if (!m.pending.load(std::memory_order_acquire))
        return false;

    if (m.lock.test_and_set(std::memory_order_acquire))
        return false;

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

static inline void enqueue_present_job(PresentJob&& j)
{
    if (j.drv_display_id < 0 || j.drv_display_id >= kMaxDriverDisplays)
        return;

    const int d = j.drv_display_id;
    lock_present_mailbox(d);
    PresentMailbox& m = g_present_mailboxes[d];
    m.job = std::move(j);
    m.pending.store(true, std::memory_order_release);
    unlock_present_mailbox(d);

    const uint32_t bit = uint32_t(1) << uint32_t(d);
    const uint32_t prev = g_present_ready_mask.fetch_or(bit, std::memory_order_acq_rel);
    if ((prev & bit) == 0)
        notify_present_thread();
}

static inline void flush_present_jobs_for_display(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays)
        return;

    lock_present_mailbox(drv_display_id);
    PresentMailbox& m = g_present_mailboxes[drv_display_id];
    m.job = PresentJob{};
    m.pending.store(false, std::memory_order_release);
    unlock_present_mailbox(drv_display_id);

    g_present_ready_mask.fetch_and(~(uint32_t(1) << uint32_t(drv_display_id)),
                                   std::memory_order_acq_rel);
}

static void present_thread_main()
{
    while (g_running.load(std::memory_order_acquire)) {
        bool did_work = false;
        int d = -1;

        while (take_next_present_display(d)) {
            PresentJob j;
            if (!try_dequeue_present_job(d, j))
                continue;

            did_work = true;

            if (j.drv_display_id < 0 || j.drv_display_id >= kMaxDriverDisplays || !j.rwb)
                continue;

            DisplayRuntimeSnapshot dsnap =
                snapshot_display_runtime_atomic(j.drv_display_id);

            if (!display_runtime_present_ready(dsnap, j.generation))
                continue;

            {
                std::lock_guard<std::mutex> hwc_lk(g_hwc_mutex[j.drv_display_id]);

                dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
                hwc2_compat_display_t* hwcDisp = dsnap.hwcDisplay;
                if (!display_runtime_present_ready(dsnap, j.generation))
                    continue;

                uint32_t numTypes = 0, numRequests = 0;
                hwc2_error_t err = HWC2_ERROR_NONE;

                err = hwc2_compat_display_set_client_target(hwcDisp, j.slot, j.rwb.get(),
                                                            -1, HAL_DATASPACE_UNKNOWN);
                if (err != HWC2_ERROR_NONE) {
                    fprintf(stderr, "set_client_target failed: %d\n", (int)err);
                    request_display_resync(j.drv_display_id);
                    continue;
                }

                err = hwc2_compat_display_validate(hwcDisp, &numTypes, &numRequests);
                if (err == HWC2_ERROR_HAS_CHANGES && (numTypes || numRequests))
                    (void)hwc2_compat_display_accept_changes(hwcDisp);
                else if (err != HWC2_ERROR_NONE) {
                    fprintf(stderr, "validate failed: %d\n", (int)err);
                    request_display_resync(j.drv_display_id);
                    continue;
                }

                int presentFence = -1;
                err = hwc2_compat_display_present(hwcDisp, &presentFence);
                if (err != HWC2_ERROR_NONE) {
                    fprintf(stderr, "present failed: %d\n", (int)err);
                    request_display_resync(j.drv_display_id);
                    continue;
                }
            }
            dsnap = snapshot_display_runtime_atomic(j.drv_display_id);
            if (!display_runtime_present_ready(dsnap, j.generation))
                continue;

            g_resync_pending[j.drv_display_id].store(false, std::memory_order_release);
        }
        if (!g_running.load(std::memory_order_acquire))
            break;

        if (!did_work)
            wait_for_present_work();
    }
}

static inline void init_free_driver_slots_once() {
    if (g_free_drv_ids_initialized)
        return;
    g_free_drv_count = 0;
    for (int i = kMaxDriverDisplays - 1; i >= 0; --i)
        g_free_drv_ids[g_free_drv_count++] = i;
    g_free_drv_ids_initialized = true;
}

bool is_evdi_lindroid(int fd) {
    drmVersionPtr version = drmGetVersion(fd);
    if (version) {
        std::string driver_name(version->name, version->name_len);
        drmFreeVersion(version);
        return (driver_name == "evdi-lindroid");
    }
    return false;
}

int find_evdi_lindroid_device() {
    static const char* dri_path = "/dev/dri/";
    DIR* dir = opendir(dri_path);
    if (!dir)
        return -1;

    int found_fd = -1;
    struct dirent* entry;
    while ((entry = readdir(dir)) != nullptr) {
        if (strncmp(entry->d_name, "card", 4) != 0)
            continue;

        std::string path = std::string(dri_path) + entry->d_name;
        int fd = open(path.c_str(), O_RDWR | O_CLOEXEC);
        if (fd < 0) continue;

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

int open_evdi_lindroid_or_create() {
    int fd = find_evdi_lindroid_device();
    if (fd >= 0) {
        return fd;
    }

    //try to create device
    std::cout << "evdi-lindroid not found. Attempting to create..." << std::endl;
    std::ofstream evdi_add("/sys/devices/evdi-lindroid/add");
    if (!evdi_add) {
        std::cerr << "Failed to write to /sys/devices/evdi-lindroid/add: " << strerror(errno) << std::endl;
        return -1;
    }

    evdi_add << "1";
    evdi_add.close();

    int wait_interval = 1; // interval between evdi device check
    int total_wait_limit = 30; // total wait time limit for evdi device check
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

static inline int evdi_connect(int device_index,
                                       uint32_t width, uint32_t height,
                                       uint32_t refresh_rate, uint32_t display_id,
                                       int connected)
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

int update_display(int display_id);

static inline int drv_id_for_hwc(long long hwc_id) {
    auto it = g_hwc_to_drv.find(hwc_id);
    return it == g_hwc_to_drv.end() ? -1 : it->second;
}

void onVsyncReceived(HWC2EventListener* listener, int32_t sequenceId,
                     hwc2_display_t display, int64_t timestamp)
{
    const long long hwc_id = (long long)display;
    int drv_id = drv_id_for_hwc_atomic(hwc_id);

    if (drv_id < 0) {
        std::lock_guard<std::mutex> lk(g_state_mutex);
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

static inline int alloc_driver_slot_for_hwc(long long hwc_id) {
    int drv = drv_id_for_hwc(hwc_id);
    if (drv >= 0) return drv;
    if (g_free_drv_count <= 0) return -1;
    drv = g_free_drv_ids[--g_free_drv_count];
    g_hwc_to_drv[hwc_id] = drv;
    g_drv_to_hwc[drv] = hwc_id;
    return drv;
}

static inline void release_driver_slot_for_hwc(long long hwc_id) {
    auto it = g_hwc_to_drv.find(hwc_id);
    if (it == g_hwc_to_drv.end()) return;
    int drv = it->second;
    g_hwc_to_drv.erase(it);
    g_drv_to_hwc.erase(drv);

    for (int i = 0; i < g_free_drv_count; ++i) {
        if (g_free_drv_ids[i] == drv)
            return;
    }

    if (g_free_drv_count < kMaxDriverDisplays)
        g_free_drv_ids[g_free_drv_count++] = drv;
    else
        fprintf(stderr, "release_driver_slot_for_hwc: free list overflow for drv %d\n", drv);
}

void onHotplugReceived(HWC2EventListener* listener, int32_t sequenceId,
                       hwc2_display_t display, bool connected,
                       bool primaryDisplay)
{
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
                std::lock_guard<std::mutex> lk(g_state_mutex);
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
                std::unique_lock<std::mutex> state_lk(g_state_mutex, std::defer_lock);
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
            if (hwc_display)
                hwc2_compat_display_set_vsync_enabled(hwc_display, HWC2_VSYNC_ENABLE);
        } else {
            {
                std::lock_guard<std::mutex> lk(g_state_mutex);
                drv_id = drv_id_for_hwc(hwc_id);
                if (drv_id < 0) return;
            }
            {
                std::unique_lock<std::mutex> state_lk(g_state_mutex, std::defer_lock);
                std::unique_lock<std::mutex> hwc_lk(g_hwc_mutex[drv_id], std::defer_lock);
                std::lock(state_lk, hwc_lk);
                Display& D = get_or_create_display(drv_id);
                D.connected = false;
                publish_display_runtime_locked(drv_id);
            }
            schedule_disconnect(drv_id);
        }
}

void onRefreshReceived(HWC2EventListener* listener,
                       int32_t sequenceId, hwc2_display_t display)
{
    const long long hwc_id = (long long)display;
    int drv_id = drv_id_for_hwc_atomic(hwc_id);

    if (drv_id < 0) {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        drv_id = drv_id_for_hwc(hwc_id);
    }
    if (drv_id < 0)
        return;
    printf("onRefreshReceived (HWC %" PRIu64 ") -> driver slot %d\n", (uint64_t)hwc_id, drv_id);
    schedule_update(drv_id);
}

HWC2EventListener eventListener = {
    &onVsyncReceived,
    &onHotplugReceived,
    &onRefreshReceived
};

void get_buf_from_map(void *data, int poll_id) {
    int id;
    struct drm_evdi_get_buff_callabck cmd = {};
    memcpy(&id, data, sizeof(int));

    cmd.poll_id = poll_id;

    std::shared_ptr<BufferEntry> entry;
    native_handle_t* handle = nullptr;
    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        entry = get_entry_locked_nolock(id);
        handle = (entry && entry->handle) ? entry->handle : nullptr;
    }

    if (!handle) {
        cmd.version = -1;
        cmd.numFds  = -1;
        cmd.numInts = -1;
        cmd.fd_ints   = nullptr;
        cmd.data_ints = nullptr;
    } else {
        cmd.version = handle->version;
        cmd.numFds  = handle->numFds;
        cmd.numInts = handle->numInts;
        cmd.fd_ints = (handle->numFds > 0)
            ? const_cast<int *>(&handle->data[0])
            : nullptr;
        cmd.data_ints = (handle->numInts > 0)
            ? const_cast<int *>(&handle->data[handle->numFds])
            : nullptr;
    }
//    printf("get_buf_from_map id: %d, version: %d\n", id, handle->version);
    (void)drm_ioctl(DRM_IOCTL_EVDI_GET_BUFF_CALLBACK, &cmd);
}

void swap_to_buff(void *data, int poll_id) {
    struct { int id; int display_id; } ex = { -1, 0 };
    memcpy(&ex, data, sizeof(ex));
    const int id = ex.id;
    const int drv_display_id = ex.display_id;

    std::shared_ptr<BufferEntry> entry;

    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        entry = get_entry_locked_nolock(id);
    }

    if (!entry || !entry->handle) {
        request_display_resync(drv_display_id);
        return;
    }

    PresentJob j;
    if (!prepare_present_job_fast(id, drv_display_id, entry, j) &&
        !prepare_present_job_slow(id, drv_display_id, entry, j)) {
        return;
    }
    enqueue_present_job(std::move(j));
    return;
}

void destroy_buff(void *data, int poll_id) {
        int id = *(int *)data;
        {
            std::lock_guard<std::mutex> lk(g_state_mutex);
            erase_buffer_locked(id);
        }

        struct drm_evdi_destroy_buff_callback cmd = {.poll_id=poll_id};
        (void)drm_ioctl(DRM_IOCTL_EVDI_DESTROY_BUFF_CALLBACK, &cmd);
}


void create_buff(void *data, int poll_id) {
    struct drm_evdi_gbm_create_buff buff_params;
    struct drm_evdi_create_buff_callabck cmd;
    memcpy(&buff_params, data, sizeof(struct drm_evdi_gbm_create_buff));
    const native_handle_t *full_handle;
    int req_format = (buff_params.format != 0) ? (int)buff_params.format : HAL_PIXEL_FORMAT_RGBA_8888;

    int ret = hybris_gralloc_allocate(buff_params.width, buff_params.height, req_format,
                                      kRwbUsage, (buffer_handle_t*)&full_handle, &cmd.stride);
    if (ret != 0) {
        fprintf(stderr, "[libgbm-hybris] hybris_gralloc_allocate failed: %d\n", ret);
        cmd.id = -1;
        cmd.poll_id = poll_id;
        cmd.stride = 0;
        (void)drm_ioctl(DRM_IOCTL_EVDI_GBM_CREATE_BUFF_CALLBACK, &cmd);
        return;
    }
    cmd.id = add_handle(const_cast<native_handle_t*>(full_handle), BufferOrigin::Allocated,
                           req_format, cmd.stride, buff_params.width, buff_params.height);
    cmd.poll_id = poll_id;
    ret = drm_ioctl(DRM_IOCTL_EVDI_GBM_CREATE_BUFF_CALLBACK, &cmd);
    if (ret < 0) {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        erase_buffer_locked(cmd.id);
    }
}

static inline int hz_from_period_ns(int32_t ns)
{
    if (ns <= 0) return 60;
    const double hz_f = 1e9 / static_cast<double>(ns);
    int hz = static_cast<int>(std::lround(hz_f));
    return hz;
}

static inline int get_refresh_hz_from_active_config(const HWC2DisplayConfig* cfg)
{
    return hz_from_period_ns(cfg->vsyncPeriod);
}

static inline int reconnect_display_mode(int display_id,
                                         int target_width,
                                         int target_height,
                                         int refresh_hz,
                                         bool disconnect_first)
{
    g_modeset_inflight.fetch_add(1, std::memory_order_acq_rel);
    int rc = 0;

    if (disconnect_first) {
        if (evdi_connect(0, 0, 0, 0, (uint32_t)display_id, 0) < 0)
            rc = -1;
    }

    if (rc == 0) {
        rc = evdi_connect(0,
                                  (uint32_t)target_width, (uint32_t)target_height,
                                  (uint32_t)refresh_hz, (uint32_t)display_id, 1);
    }

    g_modeset_inflight.fetch_sub(1, std::memory_order_acq_rel);
    return rc;
}

int update_display(int display_id) {
    if (display_id < 0 || display_id >= kMaxDriverDisplays)
        return -1;

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
    bool force_reconnect = g_resync_pending[display_id].exchange(false, std::memory_order_acq_rel);
    bool had_previous_mode = false;
    bool mode_changed = false;

    {
        std::unique_lock<std::mutex> state_lk(g_state_mutex, std::defer_lock);
        std::unique_lock<std::mutex> hwc_lk(g_hwc_mutex[display_id], std::defer_lock);
        std::lock(state_lk, hwc_lk);
        Display& D = get_or_create_display(display_id);
        hwc2_compat_display_t* hwcDisp = D.hwcDisplay;
        if (!D.connected || !hwcDisp)
            return -1;

        HWC2DisplayConfig* config =
            hwc2_compat_display_get_active_config(hwcDisp);
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

        if (!force_reconnect && !mode_changed && D.stride != 0)
            return 0;

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
        // Free immediately since this was only used to determine stride
        (void)hybris_gralloc_release(handle, /*was_allocated=*/1);
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
        std::lock_guard<std::mutex> lk(g_state_mutex);
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

static void disconnect_display(int drv_id)
{
    if (drv_id < 0 || drv_id >= kMaxDriverDisplays)
        return;

    flush_present_jobs_for_display(drv_id);
    if (drm_ready.load(std::memory_order_acquire)) {
        g_modeset_inflight.fetch_add(1, std::memory_order_acq_rel);
        (void)evdi_connect(0, 0, 0, 0, (uint32_t)drv_id, 0);
        g_modeset_inflight.fetch_sub(1, std::memory_order_acq_rel);
    }
    {
        std::unique_lock<std::mutex> state_lk(g_state_mutex, std::defer_lock);
        std::unique_lock<std::mutex> hwc_lk(g_hwc_mutex[drv_id], std::defer_lock);
        std::lock(state_lk, hwc_lk);
        Display& D = get_or_create_display(drv_id);
        reset_display_bindings_locked(drv_id);
        const long long hwc_id = D.hwc_id;
        D.generation++;
        D.hwcDisplay = nullptr;
        D.width = D.height = 0;
        D.stride = 0;
        D.connected = false;
        D.hwc_id = 0;
        publish_display_runtime_locked(drv_id);
        g_resync_pending[drv_id].store(false, std::memory_order_release);
        clear_pending_work_atomic(drv_id);
        if (hwc_id != 0)
            release_driver_slot_for_hwc(hwc_id);
    }
}

static void update_thread_main()
{
    for (;;) {
        int disp = -1;

        {
            std::unique_lock<std::mutex> lk(g_update_mutex);
            g_update_cv.wait(lk, []{
                return !g_running.load(std::memory_order_acquire) ||
                       g_update_pending_mask.load(std::memory_order_acquire) != 0;
            });

            if (!g_running.load(std::memory_order_acquire))
                break;
        }

        if (!take_next_update_display(disp))
            continue;

        const uint8_t work =
            g_update_work[disp].exchange(kUpdateWorkNone, std::memory_order_acq_rel);
        const bool do_disconnect = (work & kUpdateWorkDisconnect) != 0;
        const bool do_update = (work & kUpdateWorkRefresh) != 0;

        if (do_disconnect)
            disconnect_display(disp);
        else if (do_update)
            (void)update_display(disp);
    }
}

static void evdi_event_thread_main()
{
    while (g_running.load(std::memory_order_acquire)) {
        QueuedEvdiEvent ev;

        if (g_evdi_event_queue.pop(ev)) {
            switch (ev.event) {
            case get_buf:
                get_buf_from_map(ev.data, ev.poll_id);
                break;
            case swap_to:
                swap_to_buff(ev.data, ev.poll_id);
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
        } else {
            std::unique_lock<std::mutex> lk(g_evdi_event_mutex);
            if (!g_evdi_event_queue.empty()) {
                continue;
            }
            g_evdi_event_thread_sleeping.store(true, std::memory_order_release);
            g_evdi_event_cv.wait(lk, []{ return !g_running.load(std::memory_order_acquire) || !g_evdi_event_queue.empty(); });
            g_evdi_event_thread_sleeping.store(false, std::memory_order_release);
        }
    }
}

static void poll_thread_main()
{
    int hard_poll_failures = 0;
    for (;;) {
        if (!g_running.load(std::memory_order_acquire))
            break;

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
                    std::lock_guard<std::mutex> slk(g_state_mutex);
                    for (auto &kv : g_displays) {
                        reset_display_bindings_locked(kv.first);
                        if (kv.second.connected && kv.second.hwcDisplay) {
                            kv.second.width = 0;
                            kv.second.height = 0;
                            kv.second.stride = 0;
                            publish_display_runtime_locked(kv.first);
                            g_resync_pending[kv.first].store(true, std::memory_order_release);
                            if (reconnect_count < kMaxDriverDisplays)
                                reconnect_displays[reconnect_count++] = kv.first;
                        }
                    }
                }
                for (int i = 0; i < reconnect_count; ++i)
                    schedule_update(reconnect_displays[i]);
            }
        }

        drm_evdi_poll poll_cmd = {};
        // Match EVDI_EVENT_PAYLOAD_MAX
        uint8_t poll_payload[32];
        poll_cmd.data = poll_payload;

        int ret = drm_ioctl(DRM_IOCTL_EVDI_POLL, &poll_cmd);
        if (ret < 0) {
            if (errno == EINTR || errno == ERESTART) {
                if (!g_running.load(std::memory_order_acquire))
                    break;
                continue;
            }
            if (errno == ENODEV || errno == EBADF) {
                if (should_request_reopen(errno) && ++hard_poll_failures >= 3)
                    request_reopen();
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

static void handle_signal(int signo)
{
    (void)signo;
    g_running.store(false, std::memory_order_release);
    g_update_cv.notify_all();
    g_evdi_event_cv.notify_all();
    notify_present_thread();
}

static void kick_thread_out_of_ioctl(std::thread& t)
{
    if (!t.joinable())
        return;
    (void)pthread_kill(t.native_handle(), kShutdownKickSignal);
}

static void install_signal_handlers()
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

int main() {
    int composerSequenceId = 0;

    sd_notifyf(0, "MAINPID=%lu", (unsigned long)getpid());
    sd_notify(0, "STATUS=Initializing create-disp…");

    init_free_driver_slots_once();

    g_buffers.reserve(kExpectedHandles);
    g_displays.reserve(kMaxDriverDisplays);
    g_hwc_to_drv.reserve(kMaxDriverDisplays);
    g_drv_to_hwc.reserve(kMaxDriverDisplays);

    // Wait up to 5s for evdi; then open
    drm_fd = -1;
    for (int i = 0; i < 5 * 1000; ++i) {
        drm_fd = find_evdi_lindroid_device();
        if (drm_fd >= 0)
            break;
        usleep(1000);
    }
    if (drm_fd < 0) drm_fd = open_evdi_lindroid_or_create();
    if (drm_fd < 0) return EXIT_FAILURE;
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
    hwc2_compat_device_register_callback(hwcDevice, &eventListener,
                                         composerSequenceId);

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

    // Start present thread
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

    // Start EVDI worker thread
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

    // Start poll thread
    try {
        g_poll_thread = std::thread(poll_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create poll thread\n");
        g_running.store(false, std::memory_order_release);
        notify_present_thread();
        g_evdi_event_cv.notify_all();
        if (g_evdi_event_thread.joinable())
            g_evdi_event_thread.join();
        if (g_present_thread.joinable())
            g_present_thread.join();
        if (g_update_thread.joinable()) {
            g_update_cv.notify_all();
            g_update_thread.join();
        }
        close(g_present_event_fd);
        g_present_event_fd = -1;
        close(drm_fd);
        return EXIT_FAILURE;
    }

     // Main thread loop.
    while (g_running.load(std::memory_order_acquire)) {
        pause();
    }

    notify_present_thread();
    g_update_cv.notify_all();
    g_evdi_event_cv.notify_all();

    if (g_poll_thread.joinable())
        kick_thread_out_of_ioctl(g_poll_thread);

    // Shutdown
    sd_notify(0, "STATUS=Stopping poll thread…");
    if (g_poll_thread.joinable())
        g_poll_thread.join();

    sd_notify(0, "STATUS=Stopping evdi event thread…");
    g_evdi_event_cv.notify_all();
    if (g_evdi_event_thread.joinable())
        g_evdi_event_thread.join();

    sd_notify(0, "STATUS=Stopping present thread…");
    notify_present_thread();
    if (g_present_thread.joinable())
        g_present_thread.join();

    if (g_present_event_fd >= 0) {
        close(g_present_event_fd);
        g_present_event_fd = -1;
    }

    drm_shutdown_close_fd();

    sd_notify(0, "STATUS=Stopping update thread…");
    g_update_cv.notify_all();
    if (g_update_thread.joinable())
        g_update_thread.join();

    sd_notify(0, "STATUS=Shutting down…");
    return EXIT_SUCCESS;
}
