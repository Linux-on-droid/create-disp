#include <inttypes.h>
#include <dirent.h>
#include <fcntl.h>
#include <iostream>
#include <sstream>
#include <cstring>
#include <unistd.h>
#include <sys/ioctl.h>
#include <cerrno>
#include <xf86drm.h>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <map>
#include <vector>
#include <new>
#include <fstream>
#include <poll.h>
#include <cmath>
#include <climits>
#include <cstdint>
#include <set>
#include <chrono>
#include <thread>
#include <atomic>
#include <csignal>
#include <mutex>
#include <condition_variable>

#include <systemd/sd-daemon.h>

#include <hybris/hwc2/hwc2_compatibility_layer.h>
#include <hybris/gralloc/gralloc.h>
#include <hybris/platforms/common/windowbuffer.h>

struct drm_evdi_swap_callback;
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
#define DRM_EVDI_SWAP_CALLBACK 0x0A
#define DRM_EVDI_GBM_DEL_BUFF 0x0B
#define DRM_EVDI_GBM_CREATE_BUFF 0x0C
#define DRM_EVDI_GBM_CREATE_BUFF_CALLBACK 0x0D

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
#define DRM_IOCTL_EVDI_SWAP_CALLBACK DRM_IOWR(DRM_COMMAND_BASE +  \
        DRM_EVDI_SWAP_CALLBACK, struct drm_evdi_swap_callback)
#define DRM_IOCTL_EVDI_GBM_CREATE_BUFF_CALLBACK DRM_IOWR(DRM_COMMAND_BASE +  \
	DRM_EVDI_GBM_CREATE_BUFF_CALLBACK, struct drm_evdi_create_buff_callabck)

static const int kMaxDriverDisplays = 5;
static std::unordered_map<long long, int> g_hwc_to_drv;
static std::unordered_map<int, long long> g_drv_to_hwc;
static std::vector<int> g_free_drv_ids;
static std::atomic<bool> drm_ready{false};

static constexpr uint32_t kHwcMaxSlots = 64;

static constexpr uint32_t kSlotsPerDisplay = kHwcMaxSlots / uint32_t(kMaxDriverDisplays);
static_assert(kSlotsPerDisplay >= 4, "Need at least 4 slots per display");
static_assert(kSlotsPerDisplay * uint32_t(kMaxDriverDisplays) <= kHwcMaxSlots, "Slot partition overflow");
static uint32_t g_slot_cursor[kMaxDriverDisplays] = {};

static std::mutex g_state_mutex;

static std::mutex g_drm_mutex;

static std::mutex g_update_mutex;
static std::condition_variable g_update_cv;
static std::set<int> g_pending_updates;
static std::set<int> g_pending_disconnects;
static std::thread g_update_thread;

static std::atomic<bool> g_reopen_requested{false};

static inline void request_reopen()
{
    g_reopen_requested.store(true, std::memory_order_release);
}

static inline int ioctl_retry(int fd, unsigned long req, void *arg)
{
    int rc;
    do {
        rc = ::ioctl(fd, req, arg);
    } while (rc < 0 && errno == EINTR);
    return rc;
}

static inline int drm_ioctl(unsigned long req, void *arg)
{
    std::lock_guard<std::mutex> lk(g_drm_mutex);
    extern int drm_fd;
    if (drm_fd < 0) {
        errno = EBADF;
        return -1;
    }
    return ioctl_retry(drm_fd, req, arg);
}

static inline void schedule_update(int drv_display_id)
{
    {
        std::lock_guard<std::mutex> lk(g_update_mutex);
        if (drv_display_id >= 0 && drv_display_id < kMaxDriverDisplays)
            g_pending_updates.insert(drv_display_id);
    }
    g_update_cv.notify_one();
}

static inline void schedule_disconnect(int drv_display_id)
{
    {
        std::lock_guard<std::mutex> lk(g_update_mutex);
        if (drv_display_id >= 0 && drv_display_id < kMaxDriverDisplays) {
            g_pending_disconnects.insert(drv_display_id);
            g_pending_updates.erase(drv_display_id);
        }
    }
    g_update_cv.notify_one();
}

static inline uint32_t slot_for_display_locked(int display_id)
{
    if (display_id < 0 || display_id >= kMaxDriverDisplays)
        return 0;
    const uint32_t base = uint32_t(display_id) * kSlotsPerDisplay;
    const uint32_t idx  = (g_slot_cursor[display_id]++) % kSlotsPerDisplay;
    return base + idx;
}

namespace {
struct RwbPool {
    std::vector<void*> free_blocks;
    void* acquire() {
        if (!free_blocks.empty()) {
            void* p = free_blocks.back();
            free_blocks.pop_back();
            return p;
        }
        return ::operator new(sizeof(RemoteWindowBuffer));
    }
    void release(void* p) { if (p) free_blocks.push_back(p); }
    ~RwbPool() {
        for (void* p : free_blocks) ::operator delete(p);
        free_blocks.clear();
    }
};
static RwbPool g_rwb_pool;
struct RwbDeleter { void operator()(RemoteWindowBuffer* p) const { if (!p) return; p->~RemoteWindowBuffer(); g_rwb_pool.release(static_cast<void*>(p)); } };
using UniqueRwb = std::unique_ptr<RemoteWindowBuffer, RwbDeleter>;
} // namespace

struct Display {
    int display_id = -1;
    int width = 0;
    int height = 0;
    uint32_t stride = 0;
    bool connected = false;
    hwc2_compat_display_t* hwcDisplay = nullptr;
    hwc2_compat_layer_t* layer = nullptr;
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

static inline Display& get_or_create_display(int display_id) {
    auto it = g_displays.find(display_id);
    if (it != g_displays.end()) return it->second;
    Display d;
    d.display_id = display_id;
    g_displays.emplace(display_id, d);
    return g_displays[display_id];
}

struct HandleInfo {
    std::unique_ptr<native_handle_t> handle;
    int id;
};

int drm_fd;
hwc2_compat_device_t* hwcDevice;

struct HandleFreeDeleter {
    void operator()(native_handle_t* h) const {
        if (h) ::free(h);
    }
};
using UniqueHandle = std::unique_ptr<native_handle_t, HandleFreeDeleter>;

struct BufferEntry {
    UniqueHandle handle;
    // created first swap_to:
    UniqueRwb rwb;
};
static std::unordered_map<int, BufferEntry> g_buffers;

static inline RemoteWindowBuffer* alloc_rwb(int w, int h, uint32_t stride,
                                           int format, int usage,
                                           buffer_handle_t handle)
{
    void* mem = g_rwb_pool.acquire();
    return new (mem) RemoteWindowBuffer(w, h, stride, format, usage, handle);
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

struct drm_evdi_swap_callback {
        int poll_id;
};

struct drm_evdi_create_buff_callabck {
	int poll_id;
	int id;
	uint32_t stride;
};

static inline int evdi_swap_reply(int poll_id)
{
    struct drm_evdi_swap_callback cmd = {
        .poll_id = poll_id,
    };
    int rc = drm_ioctl(DRM_IOCTL_EVDI_SWAP_CALLBACK, &cmd);
    if (rc < 0 && (errno == ENODEV || errno == EBADF)) {
        request_reopen();
    }
    return rc;
}

int add_handle(const native_handle_t& handle)
{
    const size_t total_size =
        sizeof(native_handle_t) + (size_t(handle.numFds) + size_t(handle.numInts)) * sizeof(int);
    native_handle_t* copied_handle = (native_handle_t*)::malloc(total_size);
    if (!copied_handle) {
        printf("Memory allocation failed for handle copy\n");
        return -1;
    }
    memcpy(copied_handle, &handle, total_size);

    std::lock_guard<std::mutex> lk(g_state_mutex);

    if (next_id <= 0)
        next_id = 1;

    int id = next_id++;
    BufferEntry &e = g_buffers[id];
    e.handle.reset(copied_handle);
    e.rwb.reset();
    return id;
}

static inline BufferEntry* get_entry_locked_nolock(int id)
{
    auto it = g_buffers.find(id);
    return (it != g_buffers.end()) ? &it->second : nullptr;
}

static inline void init_free_driver_slots_once() {
    if (!g_free_drv_ids.empty()) return;
    g_free_drv_ids.reserve(kMaxDriverDisplays);
    for (int i = kMaxDriverDisplays - 1; i >= 0; --i) {
        g_free_drv_ids.push_back(i);
    }
}

static int drm_auth_magic(int fd, drm_magic_t magic) {
    drm_auth_t auth{};
    auth.magic = magic;
    if (ioctl(fd, DRM_IOCTL_AUTH_MAGIC, &auth)) {
        return -errno;
    }
    return 0;
}

static bool drm_is_master(int fd) {
    return drm_auth_magic(fd, 0) != -EACCES;
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
    const std::string dri_path = "/dev/dri/";
    std::vector<std::string> candidates;

    if (DIR* dir = opendir(dri_path.c_str())) {
        struct dirent* entry;
        while ((entry = readdir(dir)) != nullptr) {
            if (strncmp(entry->d_name, "card", 4) == 0) {
                candidates.emplace_back(dri_path + entry->d_name);
            }
        }
        closedir(dir);
    }

    for (const auto& path : candidates) {
        int fd = open(path.c_str(), O_RDWR | O_CLOEXEC);
        if (fd < 0) continue;

        if (is_evdi_lindroid(fd)) {
            std::cout << "Found evdi-lindroid at " << path << std::endl;

            if (drmIsMaster(fd)) {
                if (ioctl(fd, DRM_IOCTL_DROP_MASTER, nullptr) < 0) {
                    std::cerr << "Failed to drop master on " << path << ": " << strerror(errno) << std::endl;
                    close(fd);
                    return -1;
                }
            }

            return fd;
        }

        close(fd);
    }

    return -1;
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

static inline int evdi_connect(int fd, int device_index,
                               uint32_t width, uint32_t height,
                               uint32_t refresh_rate, uint32_t display_id,
                               int connected) {
    drm_evdi_connect cmd = {
        .connected = connected,
        .dev_index = device_index,
        .width = width,
        .height = height,
        .refresh_rate = refresh_rate,
        .display_id = display_id,
    };

    if (ioctl(fd, DRM_IOCTL_EVDI_CONNECT, &cmd) < 0) {
        perror("DRM_IOCTL_EVDI_CONNECT failed");
        return -1;
    }

    return 0;
}

int update_display(int display_id);

void onVsyncReceived(HWC2EventListener* listener, int32_t sequenceId,
                     hwc2_display_t display, int64_t timestamp)
{
}

static inline int drv_id_for_hwc(long long hwc_id) {
    auto it = g_hwc_to_drv.find(hwc_id);
    return it == g_hwc_to_drv.end() ? -1 : it->second;
}

static inline int alloc_driver_slot_for_hwc(long long hwc_id) {
    int drv = drv_id_for_hwc(hwc_id);
    if (drv >= 0) return drv;
    if (g_free_drv_ids.empty()) return -1;
    drv = g_free_drv_ids.back();
    g_free_drv_ids.pop_back();
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
    g_free_drv_ids.push_back(drv);
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
                Display& D = get_or_create_display(drv_id);
                D.display_id = drv_id;
                D.hwcDisplay = hwc2_compat_device_get_display_by_id(hwcDevice, display);
                D.connected = true;
            }
            schedule_update(drv_id);
        } else {
            {
                std::lock_guard<std::mutex> lk(g_state_mutex);
                drv_id = drv_id_for_hwc(hwc_id);
                if (drv_id < 0) return;
                Display& D = get_or_create_display(drv_id);
                D.connected = false;
            }
            schedule_disconnect(drv_id);
        }
}

void onRefreshReceived(HWC2EventListener* listener,
                       int32_t sequenceId, hwc2_display_t display)
{
    const long long hwc_id = (long long)display;
    int drv_id = -1;
    {
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

void add_buf_to_map(void *data, int poll_id, int drm_fd) {
    int fd = -1;
    std::memcpy(&fd, data, sizeof(int));
    if (fd < 0 || fcntl(fd, F_GETFD) == -1) {
        printf("Invalid or closed file descriptor: %d\n", fd);
        return;
    }

    int header[3];
    if (pread(fd, header, sizeof(header), 0) != (ssize_t)sizeof(header)) {
        printf("Fd read header failed fd: %d\n", fd);
        close(fd);
        return;
    }

    const int version = header[0];
    const int numFds  = header[1];
    const int numInts = header[2];
    if (version <= 0 || numFds < 0 || numInts < 0) {
        printf("Bad native_handle header v=%d fds=%d ints=%d (fd=%d)\n",
               version, numFds, numInts, fd);
        close(fd);
        return;
    }

    const size_t total_size =
        sizeof(native_handle_t) + (size_t(numFds) + size_t(numInts)) * sizeof(int);

    native_handle_t *full_handle = (native_handle_t*)::malloc(total_size);
    if (!full_handle) {
        printf("malloc failed size: %zu\n", total_size);
        close(fd);
        return;
    }

    std::memcpy(full_handle, header, sizeof(header));
    const size_t already = sizeof(header);
    const size_t remain  = (total_size > already) ? (total_size - already) : 0;
    if (remain) {
        if (pread(fd, (char*)full_handle + already, remain, (off_t)already) != (ssize_t)remain) {
            printf("Fd read body failed fd: %d\n", fd);
            ::free(full_handle);
            close(fd);
            return;
        }
    }

    // always assign a new id per incoming handle.
    const int id = add_handle(*full_handle);

    ::free(full_handle);
    close(fd);

    struct drm_evdi_add_buff_callabck cmd = {.poll_id=poll_id, .buff_id=id};
    if (drm_ioctl(DRM_IOCTL_EVDI_ADD_BUFF_CALLBACK, &cmd) < 0) {
        if (errno == ENODEV || errno == EBADF) {
            request_reopen();
        }
    }
}

void get_buf_from_map(void *data, int poll_id, int drm_fd) {
    int id;
    struct drm_evdi_get_buff_callabck cmd;
    memcpy(&id, data, sizeof(int));

    std::memset(&cmd, 0, sizeof(cmd));
    cmd.poll_id = poll_id;

    native_handle_t* handle = nullptr;
    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        BufferEntry* E = get_entry_locked_nolock(id);
        handle = (E && E->handle) ? E->handle.get() : nullptr;
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
        cmd.fd_ints   = const_cast<int *>(&handle->data[0]);
        cmd.data_ints = const_cast<int *>(&handle->data[handle->numFds]);
    }
//    printf("get_buf_from_map id: %d, version: %d\n", id, handle->version);
    ioctl(drm_fd, DRM_IOCTL_EVDI_GET_BUFF_CALLBACK, &cmd);
}

void swap_to_buff(void *data, int poll_id, int drm_fd) {
    struct { int id; int display_id; } ex = { -1, 0 };
    std::memset(&ex, 0, sizeof(ex));
    ex.id = -1;
    ex.display_id = 0;
    uint32_t numTypes = 0;
    uint32_t numRequests = 0;
    hwc2_error_t error = HWC2_ERROR_NONE;
    memcpy(&ex, data, sizeof(ex));
    const int id = ex.id;
    const int drv_display_id = ex.display_id;

    struct SwapReplyGuard {
        int poll_id;
        bool replied = false;
        ~SwapReplyGuard() { if (!replied) (void)evdi_swap_reply(poll_id); }
    } reply{poll_id};

    hwc2_compat_display_t* hwcDisp = nullptr;
    Display Dsnap;
    native_handle_t* in_handle = nullptr;
    RemoteWindowBuffer* buf = nullptr;
    uint32_t slot = 0;

    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        BufferEntry *E = get_entry_locked_nolock(id);
        in_handle = (E && E->handle) ? E->handle.get() : nullptr;
        if (unlikely(in_handle == nullptr)) {
            printf("Failed to find buf: %d\n", id);
            return;
        }
        Display& D = get_or_create_display(drv_display_id);
        Dsnap = D;
        hwcDisp = D.hwcDisplay;
        slot = slot_for_display_locked(drv_display_id);

        if (!hwcDisp || D.width == 0 || D.height == 0 || D.stride == 0) {
            return;
        }
        if (E) {
            if (!E->rwb) {
                E->rwb.reset(alloc_rwb(D.width, D.height, D.stride,
                                      HAL_PIXEL_FORMAT_RGBA_8888, kRwbUsage, in_handle));
            } else {
                RemoteWindowBuffer *cur = E->rwb.get();
                if (cur->width != D.width || cur->height != D.height || cur->stride != D.stride) {
                    E->rwb.reset();
                    E->rwb.reset(alloc_rwb(D.width, D.height, D.stride,
                                          HAL_PIXEL_FORMAT_RGBA_8888, kRwbUsage, in_handle));
                }
            }
            buf = E->rwb.get();
        }
    }

    if (unlikely(!hwcDisp || Dsnap.width == 0 || Dsnap.height == 0 || Dsnap.stride == 0 || !buf)) {
        printf("Display %d not ready (no HWC or size)\n", drv_display_id);
        return;
    }

    error = hwc2_compat_display_set_client_target(hwcDisp,
                                                 slot,
                                                 buf,
                                                 -1,
                                                 HAL_DATASPACE_UNKNOWN);
    if (error != HWC2_ERROR_NONE) {
        fprintf(stderr, "set_client_target failed: %d\n", (int)error);
        //return;
    }

    error = hwc2_compat_display_validate(hwcDisp, &numTypes, &numRequests);
    if (error != HWC2_ERROR_NONE) {
        fprintf(stderr, "validate failed: %d\n", (int)error);
        //return;
    }

    if (numTypes || numRequests)
        (void)hwc2_compat_display_accept_changes(hwcDisp);

    int presentFence = -1;
    (void)hwc2_compat_display_present(hwcDisp, &presentFence);

    if (evdi_swap_reply(poll_id) == 0)
        reply.replied = true;

    return;
}

void destroy_buff(void *data, int poll_id, int drm_fd) {
        int id = *(int *)data;
        int ret;
        {
            std::lock_guard<std::mutex> lk(g_state_mutex);
            BufferEntry *E = get_entry_locked_nolock(id);
            if (E && E->handle) {
                native_handle_close(E->handle.get());
            }
            g_buffers.erase(id);
        }

        struct drm_evdi_destroy_buff_callback cmd = {.poll_id=poll_id};
        ret = drm_ioctl(DRM_IOCTL_EVDI_DESTROY_BUFF_CALLBACK, &cmd);
        if (ret < 0 && (errno == ENODEV || errno == EBADF))
            request_reopen();
}


void create_buff(void *data, int poll_id, int drm_fd) {
//printf("Hi from create_buff\n");
    struct drm_evdi_gbm_create_buff buff_params;
    struct drm_evdi_create_buff_callabck cmd;
    memcpy(&buff_params, data, sizeof(struct drm_evdi_gbm_create_buff));
    const native_handle_t *full_handle;
    int ret = hybris_gralloc_allocate(buff_params.width, buff_params.height, HAL_PIXEL_FORMAT_RGBA_8888, GRALLOC_USAGE_HW_TEXTURE | GRALLOC_USAGE_HW_RENDER | GRALLOC_USAGE_HW_COMPOSER, &full_handle, &cmd.stride);
    if (ret != 0) {
        fprintf(stderr, "[libgbm-hybris] hybris_gralloc_allocate failed: %d\n", ret);
    }
    cmd.id = add_handle(*full_handle);
    cmd.poll_id = poll_id;
    drm_ioctl(DRM_IOCTL_EVDI_GBM_CREATE_BUFF_CALLBACK, &cmd);
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
int update_display(int display_id) {
    Display Dsnap;
    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        Dsnap = get_or_create_display(display_id);
    }
    if (!Dsnap.hwcDisplay) return -1;
    HWC2DisplayConfig* config = hwc2_compat_display_get_active_config(Dsnap.hwcDisplay);
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

    if (!drm_ready.load(std::memory_order_acquire)) {
        fprintf(stderr, "update_display(%d): DRM not ready, deferring CONNECT\n", display_id);
        return -1;
    }

    printf("display %d width: %i height: %i\n", display_id, config->width, config->height);
    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        Display& D = get_or_create_display(display_id);
        if (D.width == (int)config->width && D.height == (int)config->height && D.stride != 0)
            return 0;

        for (auto &kv : g_buffers) {
            kv.second.rwb.reset();
        }
        if (display_id >= 0 && display_id < kMaxDriverDisplays)
            g_slot_cursor[display_id] = 0;
        D.width = config->width;
        D.height = config->height;
        D.stride = 0;
        if (D.layer && D.hwcDisplay) {
            hwc2_compat_display_destroy_layer(D.hwcDisplay, D.layer);
            D.layer = nullptr;
        }
        if (D.hwcDisplay) {
            D.layer = hwc2_compat_display_create_layer(D.hwcDisplay);
            if (D.layer) {
                hwc2_compat_layer_set_composition_type(D.layer, HWC2_COMPOSITION_CLIENT);
                hwc2_compat_layer_set_blend_mode(D.layer, HWC2_BLEND_MODE_NONE);
                hwc2_compat_layer_set_source_crop(D.layer, 0.0f, 0.0f, config->width, config->height);
                hwc2_compat_layer_set_display_frame(D.layer, 0, 0, config->width, config->height);
                hwc2_compat_layer_set_visible_region(D.layer, 0, 0, config->width, config->height);
            }
        }
    }
    buffer_handle_t handle = NULL;
    hybris_gralloc_allocate(config->width, config->height, HAL_PIXEL_FORMAT_RGBA_8888,
                            GRALLOC_USAGE_HW_TEXTURE | GRALLOC_USAGE_HW_RENDER | GRALLOC_USAGE_HW_COMPOSER,
                            &handle, &Dsnap.stride);

    int refresh_hz = get_refresh_hz_from_active_config(config);

    std::ostringstream oss;
    oss << "EDID for " << config->width << "x" << config->height
        << "@" << refresh_hz << "Hz 'Lindroid display " << display_id << "'";
    std::cout << oss.str() << std::endl;

    if (evdi_connect(drm_fd, 0,
                     (uint32_t)config->width, (uint32_t)config->height,
                     (uint32_t)refresh_hz, (uint32_t)display_id, 1) < 0) {
        return EXIT_FAILURE;
    }
    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        Display& D = get_or_create_display(display_id);
        D.stride = Dsnap.stride;
    }
    return 0;
}

static void disconnect_display(int drv_id)
{
    Display snap;
    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        snap = get_or_create_display(drv_id);
    }

    if (drm_ready.load(std::memory_order_acquire)) {
        (void)evdi_connect(drm_fd, 0, 0, 0, 0, (uint32_t)drv_id, 0);
    }

    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        Display& D = get_or_create_display(drv_id);
        if (D.layer && D.hwcDisplay)
            hwc2_compat_display_destroy_layer(D.hwcDisplay, D.layer);
        D.layer = nullptr;
        D.hwcDisplay = nullptr;
        D.width = D.height = 0;
        D.stride = 0;
        D.connected = false;
        if (drv_id >= 0 && drv_id < kMaxDriverDisplays)
            g_slot_cursor[drv_id] = 0;
    }
}

static void update_thread_main()
{
    for (;;) {
        int disp = -1;
        bool do_disconnect = false;

        {
            std::unique_lock<std::mutex> lk(g_update_mutex);
            g_update_cv.wait(lk, []{
                extern std::atomic<bool> g_running;
                return !g_running.load(std::memory_order_acquire) ||
                       !g_pending_disconnects.empty() ||
                       !g_pending_updates.empty();
            });

            extern std::atomic<bool> g_running;
            if (!g_running.load(std::memory_order_acquire))
                break;

            if (!g_pending_disconnects.empty()) {
                disp = *g_pending_disconnects.begin();
                g_pending_disconnects.erase(g_pending_disconnects.begin());
                do_disconnect = true;
            } else if (!g_pending_updates.empty()) {
                disp = *g_pending_updates.begin();
                g_pending_updates.erase(g_pending_updates.begin());
            }
        }

        if (disp < 0)
            continue;
        if (do_disconnect)
            disconnect_display(disp);
        else
            (void)update_display(disp);
    }
}

static void poll_thread_main()
{
    for (;;) {
        if (!g_running.load(std::memory_order_acquire))
            break;

        if (g_reopen_requested.exchange(false, std::memory_order_acq_rel)) {
            std::lock_guard<std::mutex> lk(g_drm_mutex);

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
                std::this_thread::sleep_for(std::chrono::milliseconds(250));
            }

            if (drm_ready.load(std::memory_order_acquire)) {
                std::lock_guard<std::mutex> slk(g_state_mutex);
                for (auto &kv : g_displays) {
                    if (kv.second.connected && kv.second.hwcDisplay) {
                        kv.second.width = 0;
                        kv.second.height = 0;
                        kv.second.stride = 0;
                        if (kv.first >= 0 && kv.first < kMaxDriverDisplays)
                            g_slot_cursor[kv.first] = 0;
                        schedule_update(kv.first);
                    }
                }
            }
        }

        drm_evdi_poll poll_cmd;
        // Match EVDI_EVENT_PAYLOAD_MAX
        uint8_t poll_payload[32];
        poll_cmd.data = poll_payload;

        int ret = drm_ioctl(DRM_IOCTL_EVDI_POLL, &poll_cmd);
        if (ret < 0) {
            if (errno == ENODEV || errno == EBADF) {
                request_reopen();
                std::this_thread::sleep_for(std::chrono::milliseconds(50));
            }
            continue;
        }

        switch (poll_cmd.event) {
        case add_buf:
            add_buf_to_map(poll_cmd.data, poll_cmd.poll_id, drm_fd);
            break;
        case get_buf:
            get_buf_from_map(poll_cmd.data, poll_cmd.poll_id, drm_fd);
            break;
        case swap_to:
            swap_to_buff(poll_cmd.data, poll_cmd.poll_id, drm_fd);
            break;
        case destroy_buf:
            destroy_buff(poll_cmd.data, poll_cmd.poll_id, drm_fd);
            break;
        case create_buf:
            create_buff(poll_cmd.data, poll_cmd.poll_id, drm_fd);
            break;
        default:
            break;
        }
    }
}

static void handle_signal(int signo)
{
    (void)signo;
    g_running.store(false, std::memory_order_release);
    g_update_cv.notify_all();
}

static void install_signal_handlers()
{
    struct sigaction sa;
    std::memset(&sa, 0, sizeof(sa));
    sa.sa_handler = handle_signal;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGINT, &sa, nullptr);
    sigaction(SIGTERM, &sa, nullptr);
}

int main() {
    int device_index = 0;
    int composerSequenceId = 0;
    int ret =0;

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

    hwcDevice = hwc2_compat_device_new(false);
    if (!hwcDevice)
        return EXIT_FAILURE;
    assert(hwcDevice);
    hwc2_compat_device_register_callback(hwcDevice, &eventListener,
                                         composerSequenceId);

    try {
        g_update_thread = std::thread(update_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create update thread\n");
        close(drm_fd);
        return EXIT_FAILURE;
    }

    for (const auto& kv : g_hwc_to_drv) {
        int drv_id = kv.second;
        auto it = g_displays.find(drv_id);
        if (it == g_displays.end())
            continue;
        Display& D = it->second;
        if (!D.hwcDisplay) {
            long long hwc_id = g_drv_to_hwc[drv_id];
            D.hwcDisplay = hwc2_compat_device_get_display_by_id(hwcDevice, (hwc2_display_t)hwc_id);
        }
        if (D.hwcDisplay)
            (void)update_display(drv_id);
    }

    install_signal_handlers();

    sd_notify(0, "READY=1");
    sd_notify(0, "STATUS=create-disp ready.");

    // Start poll thread
    try {
        g_poll_thread = std::thread(poll_thread_main);
    } catch (...) {
        fprintf(stderr, "Failed to create poll thread\n");
        close(drm_fd);
        return EXIT_FAILURE;
    }

     // Main thread loop.
    while (g_running.load(std::memory_order_acquire)) {
        pause();
    }

    // Shutdown
    sd_notify(0, "STATUS=Stopping poll thread…");
    if (g_poll_thread.joinable())
        g_poll_thread.join();

    sd_notify(0, "STATUS=Stopping update thread…");
    g_update_cv.notify_all();
    if (g_update_thread.joinable())
        g_update_thread.join();

    close(drm_fd);
    sd_notify(0, "STATUS=Shutting down…");
    return EXIT_SUCCESS;
}
