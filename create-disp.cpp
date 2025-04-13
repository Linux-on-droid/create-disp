#include <fcntl.h>
#include <iostream>
#include <cstring>
#include <unistd.h>
#include <sys/ioctl.h>
#include <cerrno>
#include <xf86drm.h>
#include <memory>
#include <cassert>
#include <unordered_map>
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


struct HandleInfo {
    std::unique_ptr<native_handle_t> handle;
    int id;
};

hwc2_compat_display_t* hwcDisplay;
hwc2_compat_device_t* hwcDevice;
std::unordered_map<int, std::unique_ptr<native_handle_t>> handles_map;
int global_width, global_height;
uint32_t global_stride;
int next_id = 0;
hwc2_compat_layer_t* layer;
enum poll_event_type {
    none,
    add_buf,
    get_buf,
    destroy_buf,
    swap_to
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

int evdi_open(const std::string& device_path) {
    int fd = open(device_path.c_str(), O_RDWR);
    if (fd < 0) {
        perror("Failed to open device");
        return -1;
    }

    if (drm_is_master(fd)) {
        std::cerr << "Process has master on " << device_path << ", err: " << strerror(errno) << std::endl;
        if (ioctl(fd, DRM_IOCTL_DROP_MASTER, nullptr) < 0) {
            std::cerr << "Drop master on " << device_path << " failed, err: " << strerror(errno) << std::endl;
            close(fd);
            return -1;
        }
    }

    if (drm_is_master(fd)) {
        std::cerr << "Drop master on " << device_path << " failed, err: " << strerror(errno) << std::endl;
        close(fd);
        return -1;
    }

    return fd;
}

int evdi_connect(int fd, int device_index, uint32_t width, uint32_t height, uint32_t refresh_rate) {
    drm_evdi_connect cmd = {
        .connected = 1,
        .dev_index = device_index,
        .width = width,
        .height = height,
        .refresh_rate = refresh_rate,
    };

    if (ioctl(fd, DRM_IOCTL_EVDI_CONNECT, &cmd) < 0) {
        perror("DRM_IOCTL_EVDI_CONNECT failed");
        return -1;
    }

    return 0;
}

void onVsyncReceived(HWC2EventListener* listener, int32_t sequenceId,
                     hwc2_display_t display, int64_t timestamp)
{
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
}

void onRefreshReceived(HWC2EventListener* listener,
                       int32_t sequenceId, hwc2_display_t display)
{
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
    printf("Going to read from fd: %d\n", fd);
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
    printf("Got native_handle_t, version: %d numFds: %d numInts: %d\n", version, numFds, numInts);

    if (lseek(fd, 0, SEEK_SET) == -1) {
        printf("Failed to seek fd: %d\n", fd);
        return;
    }
    // Allocate memory for the full handle, including FDs and ints
    size_t total_size = sizeof(buffer_handle_t) + 
                        ((numFds + numInts) * sizeof(int));
    native_handle_t *full_handle = (native_handle_t*)malloc(total_size);
    if (!full_handle) {
        printf("malloc failed size: %d\n", total_size);
        return;
    }
    printf("Going to read %d bytes\n", total_size);
    if(read(fd, full_handle, total_size) != total_size) {
        printf("Fd1 read failed fd: %d\n", fd);
        return;
    }

    printf("Got native_handle_t, version: %d numFds: %d numInts: %d\n", full_handle->version, full_handle->numFds, full_handle->numInts);
    printf("data:");
    for(int i=0; i<full_handle->numFds + full_handle->numInts; i++) {
        printf(" %d ", full_handle->data[i]);
    }
    printf("\n");

    for (const auto& [existing_id, existing_handle] : handles_map) {
        if (existing_handle->version == header[0] &&
            existing_handle->numFds == header[1] &&
            existing_handle->numInts == header[2] &&
            memcmp(existing_handle->data + (header[1]* sizeof(int)), full_handle->data+ (header[1]* sizeof(int)), 
                   (header[2]) * sizeof(int)) == 0) {
            printf("Identical buffer found, returning existing id: %d\n", existing_id);
            id=existing_id;
        }
    }

    if(id == -1) {
        id = add_handle(*full_handle);
    }

    printf("Got fd: %d\n", id);
    close(fd);  
    struct drm_evdi_add_buff_callabck cmd = {.poll_id=poll_id, .buff_id=id};
    ioctl(drm_fd, DRM_IOCTL_EVDI_ADD_BUFF_CALLBACK, &cmd);
}

void get_buf_from_map(void *data, int poll_id, int drm_fd) {
    int id;
    memcpy(&id, data, sizeof(int));
    buffer_handle_t handle = get_handle(id);
    struct drm_evdi_get_buff_callabck cmd = {.poll_id = poll_id, .version = handle->version, .numFds = handle->numFds, .numInts = handle->numInts, .fd_ints = const_cast<int *>(&handle->data[0]), .data_ints = const_cast<int *>(&handle->data[handle->numFds])};
    printf("get_buf_from_map id: %d, version: %d\n", id, handle->version);
    ioctl(drm_fd, DRM_IOCTL_EVDI_GET_BUFF_CALLBACK, &cmd);
}

void swap_to_buff(void *data, int poll_id, int drm_fd) {
        const native_handle_t* out_handle = NULL;
        int id;
        int ret;
        memcpy(&id, data, sizeof(int));

        buffer_handle_t in_handle = get_handle(id);
        RemoteWindowBuffer *buf;

        if(in_handle == nullptr) {
                printf("Failed to find buf: %d\n", id);
                goto done;
        } 
printf("Got native_handle_t, version: %d numFds: %d numInts: %d\n", in_handle->version, in_handle->numFds, in_handle->numInts);
    printf("data:");
    for(int i=0; i<in_handle->numFds + in_handle->numInts; i++) {
        printf(" %d ", in_handle->data[i]);
    }
printf("\n");

uint32_t  stride;

        buf = new RemoteWindowBuffer(global_width, global_height, global_stride, HAL_PIXEL_FORMAT_RGBA_8888, GRALLOC_USAGE_HW_TEXTURE | GRALLOC_USAGE_HW_RENDER | GRALLOC_USAGE_HW_COMPOSER, in_handle);
hwc2_error_t error;
        hwc2_compat_display_set_client_target(hwcDisplay, /* slot */0, buf,
                                              -1,
                                              HAL_DATASPACE_UNKNOWN);

        int presentFence;
        error =hwc2_compat_display_present(hwcDisplay, &presentFence);
    if (error != HWC2_ERROR_NONE) {
        std::cerr << "Failed to present display: " << error << std::endl;
    } else {
//        std::cout << "Displayed red screen successfully!" << std::endl;
    }
done:
    struct drm_evdi_swap_callback cmd = {.poll_id=poll_id};
    ioctl(drm_fd, DRM_IOCTL_EVDI_SWAP_CALLBACK, &cmd);
}

void destroy_buff(void *data, int poll_id, int drm_fd) {
        const native_handle_t* out_handle = NULL;
        int id = *(int *)data;
        int ret;
        native_handle *handle = get_handle(id);
  //      printf("Going to release buff: %d handle: %d\n", id, handle);
        if(handle) {
                native_handle_close(handle);
        }
        handles_map.erase(id);
        struct drm_evdi_destroy_buff_callback cmd = {.poll_id=poll_id};
        ioctl(drm_fd, DRM_IOCTL_EVDI_DESTROY_BUFF_CALLBACK, &cmd);
}


int main() {
    const std::string device_path = "/dev/dri/card1";
    int device_index = 0;
    int composerSequenceId = 0;
    int ret =0;

   hwcDevice = hwc2_compat_device_new(false);
        assert(hwcDevice);

        hwc2_compat_device_register_callback(hwcDevice, &eventListener,
                                             composerSequenceId);

        for (int i = 0; i < 5 * 1000; ++i) {
                /* Wait at most 5s for hotplug events */
                if ((hwcDisplay = hwc2_compat_device_get_display_by_id(hwcDevice, 0)))
                        break;
                usleep(1000);
        }
        assert(hwcDisplay);

        hwc2_compat_display_set_power_mode(hwcDisplay, HWC2_POWER_MODE_ON);

        HWC2DisplayConfig* config = hwc2_compat_display_get_active_config(hwcDisplay);

        printf("width: %i height: %i\n", config->width, config->height);
    global_width = config->width;
    global_height = config->height;
buffer_handle_t handle = NULL;

    ret = hybris_gralloc_allocate(global_width, global_height, HAL_PIXEL_FORMAT_RGBA_8888, GRALLOC_USAGE_HW_TEXTURE | GRALLOC_USAGE_HW_RENDER | GRALLOC_USAGE_HW_COMPOSER, &handle, &global_stride);

        layer = hwc2_compat_display_create_layer(hwcDisplay);

        hwc2_compat_layer_set_composition_type(layer, HWC2_COMPOSITION_CLIENT);
        hwc2_compat_layer_set_blend_mode(layer, HWC2_BLEND_MODE_NONE);
        hwc2_compat_layer_set_source_crop(layer, 0.0f, 0.0f, config->width,
                                          config->height);
        hwc2_compat_layer_set_display_frame(layer, 0, 0, config->width,
                                            config->height);
        hwc2_compat_layer_set_visible_region(layer, 0, 0, config->width,
                                             config->height);

    int fd = evdi_open(device_path);
    if (fd < 0) {
        return EXIT_FAILURE;
    }

    if (evdi_connect(fd, device_index, config->width, config->height, 60) < 0) {
        close(fd);
        return EXIT_FAILURE;
    }

    std::cout << "EDID for 1080p60Hz 'Lindroid display' written successfully." << std::endl;

    drm_evdi_poll poll_cmd;
    poll_cmd.data = malloc(1024);

    while (true) {
        ret = ioctl(fd, DRM_IOCTL_EVDI_POLL, &poll_cmd);
        if(ret)
            continue;
        switch(poll_cmd.event) {
           case add_buf:
               add_buf_to_map(poll_cmd.data, poll_cmd.poll_id, fd);
               break;
           case get_buf:
               get_buf_from_map(poll_cmd.data, poll_cmd.poll_id, fd);
               break;
           case swap_to:
               swap_to_buff(poll_cmd.data, poll_cmd.poll_id, fd);
               break;
           case destroy_buf:
               destroy_buff(poll_cmd.data, poll_cmd.poll_id, fd);
               break;
        }
    }

    free(poll_cmd.data);
    close(fd);
    return EXIT_SUCCESS;
}
