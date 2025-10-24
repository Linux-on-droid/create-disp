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
#include <fstream>
#include <cmath>
#include <climits>
#include <chrono>

#include <systemd/sd-daemon.h>

#include <hybris/hwc2/hwc2_compatibility_layer.h>
#include <hybris/gralloc/gralloc.h>
#include <hybris/platforms/common/windowbuffer.h>

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
static volatile bool drm_ready = false;

struct Display {
    int display_id = -1;
    int width = 0;
    int height = 0;
    uint32_t stride = 0;
    hwc2_compat_display_t* hwcDisplay = nullptr;
    hwc2_compat_layer_t* layer = nullptr;
};

static std::unordered_map<int, Display> g_displays;

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
static std::unordered_map<int, std::unique_ptr<RemoteWindowBuffer>> buffers_map;
static std::unordered_map<int, std::unique_ptr<native_handle_t>> handles_map;
static std::unordered_map<std::string, int> handle_index;
static inline std::string make_handle_key(const native_handle_t* h) {
	const int total_ints = h->numInts;
	const size_t key_bytes = (3 + total_ints) * sizeof(int);
	std::string key(key_bytes, '\0');
	size_t off = 0;
	memcpy(&key[off], &h->version, sizeof(int)); off += sizeof(int);
	memcpy(&key[off], &h->numFds, sizeof(int));  off += sizeof(int);
	memcpy(&key[off], &h->numInts, sizeof(int)); off += sizeof(int);
	memcpy(&key[off], &h->data[h->numFds], total_ints * sizeof(int));
	return key;
}
int next_id = 0;
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

struct drm_evdi_swap_callback {
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

int add_handle(const native_handle_t& handle) {
    size_t total_size = sizeof(native_handle_t) + (handle.numFds + handle.numInts) * sizeof(int);
    native_handle_t* copied_handle = (native_handle_t*)malloc(total_size);
    if (!copied_handle) {
        printf("Memory allocation failed for handle copy\n");
        return -1;
    }
    memcpy(copied_handle, &handle, total_size);

    int id = next_id++;
    handles_map[id] = std::unique_ptr<native_handle_t>(copied_handle);
    return id;
}

native_handle_t* get_handle(int id) {
    auto it = handles_map.find(id);
    return (it != handles_map.end()) ? it->second.get() : nullptr;
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
        int drv_id = drv_id_for_hwc(hwc_id);

        if (connected) {
            if (drv_id < 0) {
                drv_id = alloc_driver_slot_for_hwc(hwc_id);
                if (drv_id < 0) {
                    std::cerr << "No free driver display slots; ignoring hotplug for HWC id " << hwc_id << std::endl;
                    return;
                }
            }
            Display& D = get_or_create_display(drv_id);
            D.display_id = drv_id;
            D.hwcDisplay = hwc2_compat_device_get_display_by_id(hwcDevice, display);
            if (!D.hwcDisplay) {
                std::cerr << "HWC display handle not available for id " << hwc_id << std::endl;
                return;
            }
            hwc2_compat_display_set_power_mode(D.hwcDisplay, HWC2_POWER_MODE_ON);
            if (drm_ready && drm_fd >= 0) {
                update_display(drv_id);
            } else {
                printf("Deferring CONNECT for driver slot %d (HWC %" PRIu64 ")\n",
                       drv_id, (uint64_t)hwc_id);
            }
        } else {
            if (drv_id < 0) return;
            Display& D = get_or_create_display(drv_id);
            evdi_connect(drm_fd, 0, 0, 0, 0, (uint32_t)drv_id, 0);
            if (D.layer) D.layer = nullptr;
            D.width = D.height = 0;
            D.stride = 0;
            release_driver_slot_for_hwc(hwc_id);
        }
}

void onRefreshReceived(HWC2EventListener* listener,
                       int32_t sequenceId, hwc2_display_t display)
{
    const long long hwc_id = (long long)display;
    int drv_id = drv_id_for_hwc(hwc_id);
    if (drv_id < 0) return;
    printf("onRefreshReceived (HWC %" PRIu64 ") -> driver slot %d\n", (uint64_t)hwc_id, drv_id);
    Display& D = get_or_create_display(drv_id);
    if (D.hwcDisplay)
        update_display(drv_id);
}

HWC2EventListener eventListener = {
    &onVsyncReceived,
    &onHotplugReceived,
    &onRefreshReceived
};

void add_buf_to_map(void *data, int poll_id, int drm_fd) {
    int fd;
    native_handle_t handle;
    int id = -1;
    memcpy(&fd, data, sizeof(int));
    if (fcntl(fd, F_GETFD) == -1) {
        printf("Invalid or closed file descriptor: %d\n", fd);
        return;
    }
    if (lseek(fd, 0, SEEK_SET) == -1) {
        printf("Failed to seek fd: %d\n", fd);
        return;
    }
    int header[3];
    if (read(fd, header, sizeof(header)) != sizeof(header)) {
        printf("Fd1 read failed fd: %d\n", fd);
        return;
    }
    int version = header[0];
    int numFds = header[1];
    int numInts = header[2];

    if (lseek(fd, 0, SEEK_SET) == -1) {
        printf("Failed to seek fd: %d\n", fd);
        return;
    }
    // Allocate memory for the full handle, including FDs and ints
    size_t total_size = sizeof(buffer_handle_t) + 
                        ((numFds + numInts) * sizeof(int));
    native_handle_t *full_handle = (native_handle_t*)malloc(total_size);
    if (!full_handle) {
        printf("malloc failed size: %zu\n", total_size);
        return;
    }
    if(read(fd, full_handle, total_size) != total_size) {
        printf("Fd1 read failed fd: %d\n", fd);
        return;
    }

    {
        const std::string key = make_handle_key(full_handle);
        auto it = handle_index.find(key);
        if (it != handle_index.end()) {
            printf("Identical buffer found, returning existing id: %d\n", it->second);
            id = it->second;
            free(full_handle);
        }
        if (id == -1) {
            id = add_handle(*full_handle);
            handle_index.emplace(key, id);
            free(full_handle);
        }
    }

    close(fd);  
    struct drm_evdi_add_buff_callabck cmd = {.poll_id=poll_id, .buff_id=id};
    ioctl(drm_fd, DRM_IOCTL_EVDI_ADD_BUFF_CALLBACK, &cmd);
}

void get_buf_from_map(void *data, int poll_id, int drm_fd) {
    int id;
    struct drm_evdi_get_buff_callabck cmd;
    memcpy(&id, data, sizeof(int));

    buffer_handle_t handle = get_handle(id);
    if(!handle) {
        cmd = {.poll_id = poll_id, .version = -1, .numFds = -1, .numInts = -1, .fd_ints = nullptr, .data_ints = nullptr};
    } else {
        cmd = {.poll_id = poll_id, .version = handle->version, .numFds = handle->numFds, .numInts = handle->numInts, .fd_ints = const_cast<int *>(&handle->data[0]), .data_ints = const_cast<int *>(&handle->data[handle->numFds])};
    }
//    printf("get_buf_from_map id: %d, version: %d\n", id, handle->version);
    ioctl(drm_fd, DRM_IOCTL_EVDI_GET_BUFF_CALLBACK, &cmd);
}

void swap_to_buff(void *data, int poll_id, int drm_fd) {
    const native_handle_t* out_handle = NULL;
    struct { int id; int display_id; } ex = { -1, 0 };
    int ret;
    memcpy(&ex, data, sizeof(ex));
    const int id = ex.id;
    const int drv_display_id = ex.display_id;

    buffer_handle_t in_handle = get_handle(id);
    RemoteWindowBuffer *buf = nullptr;
    if (in_handle == nullptr) {
        printf("Failed to find buf: %d\n", id);
        struct drm_evdi_swap_callback cmd = {.poll_id=poll_id};
        ioctl(drm_fd, DRM_IOCTL_EVDI_SWAP_CALLBACK, &cmd);
        return;
    }

    Display& D = get_or_create_display(drv_display_id);
    if (!D.hwcDisplay || D.width == 0 || D.height == 0) {
        printf("Display %d not ready (no HWC or size)\n", drv_display_id);
        struct drm_evdi_swap_callback cmd = {.poll_id=poll_id};
        ioctl(drm_fd, DRM_IOCTL_EVDI_SWAP_CALLBACK, &cmd);
        return;
    }
    if (g_drv_to_hwc.find(drv_display_id) == g_drv_to_hwc.end()) {
        struct drm_evdi_swap_callback cmd = {.poll_id = poll_id};
        ioctl(drm_fd, DRM_IOCTL_EVDI_SWAP_CALLBACK, &cmd);
        return;
    }

    {
        auto it_buf = buffers_map.find(id);
        if (it_buf == buffers_map.end()) {
            auto new_buf = std::make_unique<RemoteWindowBuffer>(
                D.width, D.height, D.stride,
                HAL_PIXEL_FORMAT_RGBA_8888,
                GRALLOC_USAGE_HW_TEXTURE | GRALLOC_USAGE_HW_RENDER | GRALLOC_USAGE_HW_COMPOSER, in_handle);
            buf = new_buf.get();
            buffers_map[id] = std::move(new_buf);
        } else {
            buf = it_buf->second.get();
            if (buf->width != D.width || buf->height != D.height) {
                auto new_buf = std::make_unique<RemoteWindowBuffer>(
                    D.width, D.height, D.stride,
                    HAL_PIXEL_FORMAT_RGBA_8888,
                    GRALLOC_USAGE_HW_TEXTURE | GRALLOC_USAGE_HW_RENDER | GRALLOC_USAGE_HW_COMPOSER, in_handle);
                buf = new_buf.get();
                buffers_map[id] = std::move(new_buf);
            }
        }
    }
    hwc2_error_t error;
    if (buf->width > D.width || buf->height > D.height) {
        struct drm_evdi_swap_callback cmd = {.poll_id=poll_id};
        ioctl(drm_fd, DRM_IOCTL_EVDI_SWAP_CALLBACK, &cmd);
        return;
    }
    hwc2_compat_display_set_client_target(D.hwcDisplay, /* slot */0, buf,
                                              -1,
                                              HAL_DATASPACE_UNKNOWN);

    int presentFence;
    error = hwc2_compat_display_present(D.hwcDisplay, &presentFence);
    if (error != HWC2_ERROR_NONE) {
        std::cerr << "Failed to present display: " << error << std::endl;
    }
    struct drm_evdi_swap_callback cmd = {.poll_id=poll_id};
    ioctl(drm_fd, DRM_IOCTL_EVDI_SWAP_CALLBACK, &cmd);
}

void destroy_buff(void *data, int poll_id, int drm_fd) {
        const native_handle_t* out_handle = NULL;
        int id = *(int *)data;
        int ret;
        native_handle_t *handle = get_handle(id);
        if(handle) {
                native_handle_close(handle);
        }
	buffers_map.erase(id);
        handles_map.erase(id);
        struct drm_evdi_destroy_buff_callback cmd = {.poll_id=poll_id};
        ret=ioctl(drm_fd, DRM_IOCTL_EVDI_DESTROY_BUFF_CALLBACK, &cmd);
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
    ioctl(drm_fd, DRM_IOCTL_EVDI_GBM_CREATE_BUFF_CALLBACK, &cmd);
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
    Display& D = get_or_create_display(display_id);
    if (!D.hwcDisplay) return -1;
    HWC2DisplayConfig* config = hwc2_compat_display_get_active_config(D.hwcDisplay);
    if (!config) {
        fprintf(stderr, "update_display(%d): no active HWC config yet, will retry on next refresh\n",
                display_id);
        return -1;
    }

    if (!D.hwcDisplay) {
        long long hwc_id = g_drv_to_hwc[display_id];
        D.hwcDisplay = hwc2_compat_device_get_display_by_id(hwcDevice, (hwc2_display_t)hwc_id);
        if (D.hwcDisplay) hwc2_compat_display_set_power_mode(D.hwcDisplay, HWC2_POWER_MODE_ON);
    }

    if (config->width <= 0 || config->height <= 0) {
        fprintf(stderr, "update_display(%d): invalid geometry %dx%d, deferring\n",
                display_id, config->width, config->height);
        return -1;
    }

    if (!drm_ready || drm_fd < 0) {
        fprintf(stderr, "update_display(%d): DRM not ready, deferring CONNECT\n", display_id);
        return -1;
    }

    printf("display %d width: %i height: %i\n", display_id, config->width, config->height);
    if (D.width != config->width || D.height != config->height) {
        buffers_map.clear();
        D.width = config->width;
        D.height = config->height;
        buffer_handle_t handle = NULL;

        hybris_gralloc_allocate(D.width, D.height, HAL_PIXEL_FORMAT_RGBA_8888,
                                GRALLOC_USAGE_HW_TEXTURE | GRALLOC_USAGE_HW_RENDER | GRALLOC_USAGE_HW_COMPOSER,
                                &handle, &D.stride);

        if (D.layer) {
            hwc2_compat_display_destroy_layer(D.hwcDisplay, D.layer);
            D.layer = nullptr;
        }
        D.layer = hwc2_compat_display_create_layer(D.hwcDisplay);

        hwc2_compat_layer_set_composition_type(D.layer, HWC2_COMPOSITION_CLIENT);
        hwc2_compat_layer_set_blend_mode(D.layer, HWC2_BLEND_MODE_NONE);
        hwc2_compat_layer_set_source_crop(D.layer, 0.0f, 0.0f, config->width, config->height);
        hwc2_compat_layer_set_display_frame(D.layer, 0, 0, config->width, config->height);
        hwc2_compat_layer_set_visible_region(D.layer, 0, 0, config->width, config->height);

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
    }
    return 0;
}

int main() {
    int device_index = 0;
    int composerSequenceId = 0;
    int ret =0;

    sd_notifyf(0, "MAINPID=%lu", (unsigned long)getpid());
    sd_notify(0, "STATUS=Initializing create-disp…");

    init_free_driver_slots_once();

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
    drm_ready = true;

    hwcDevice = hwc2_compat_device_new(false);
    assert(hwcDevice);
    hwc2_compat_device_register_callback(hwcDevice, &eventListener,
                                         composerSequenceId);

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

    sd_notify(0, "READY=1");
    sd_notify(0, "STATUS=create-disp ready.");

    drm_evdi_poll poll_cmd;
    poll_cmd.data = malloc(1024);

    while (true) {
        ret = ioctl(drm_fd, DRM_IOCTL_EVDI_POLL, &poll_cmd);
        if(ret)
            continue;
        switch(poll_cmd.event) {
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
        }
	//uncomment for debugging
	//printf("Got event: %d\n", poll_cmd.event);
    }

    free(poll_cmd.data);
    close(drm_fd);
    sd_notify(0, "STATUS=Shutting down…");
    return EXIT_SUCCESS;
}
