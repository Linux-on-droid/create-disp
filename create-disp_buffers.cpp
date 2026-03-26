#include "create-disp_shared.h"

namespace create_disp {

SlotManager::SlotManager()
{
    reset();
}

void SlotManager::reset()
{
    slot_bufid.fill(-1);
    slot_lastused.fill(0);
    slot_in_use.fill(0);
    use_counter = 0;
}

uint32_t SlotManager::assign(int bufid)
{
    const uint64_t now = ++use_counter;
    uint32_t free_slot = UINT32_MAX;
    uint32_t lru_slot = UINT32_MAX;
    uint64_t lru_time = UINT64_MAX;

    for (uint32_t i = 0; i < kCapacity; ++i) {
        if (!slot_in_use[i]) {
            if (free_slot == UINT32_MAX) {
                free_slot = i;
            }
            continue;
        }

        if (slot_bufid[i] == bufid) {
            slot_lastused[i] = now;
            return i;
        }

        if (slot_lastused[i] < lru_time) {
            lru_time = slot_lastused[i];
            lru_slot = i;
        }
    }

    if (free_slot != UINT32_MAX) {
        slot_in_use[free_slot] = 1;
        slot_bufid[free_slot] = bufid;
        slot_lastused[free_slot] = now;
        return free_slot;
    }

    if (lru_slot == UINT32_MAX) {
        fprintf(stderr, "SlotManager: exhausted all %u slots\n", kCapacity);
        return UINT32_MAX;
    }

    const int evicted = slot_bufid[lru_slot];
    slot_bufid[lru_slot] = bufid;
    slot_lastused[lru_slot] = now;
    fprintf(stderr, "SlotManager: evicted bufid %d from slot %u for bufid %d\n",
            evicted, lru_slot, bufid);
    return lru_slot;
}

void SlotManager::release(int bufid)
{
    for (uint32_t i = 0; i < kCapacity; ++i) {
        if (!slot_in_use[i] || slot_bufid[i] != bufid) {
            continue;
        }

        slot_in_use[i] = 0;
        slot_bufid[i] = -1;
        slot_lastused[i] = 0;
        return;
    }
}

BufferEntry::~BufferEntry()
{
    rwb.reset();
    if (!handle) {
        return;
    }

    if (origin == BufferOrigin::Imported) {
        for (int i = 0; i < handle->numFds; ++i) {
            close(handle->data[i]);
        }
        free(handle);
    } else {
        (void)hybris_gralloc_release((buffer_handle_t)handle, 1);
    }

    handle = nullptr;
}

SharedRwb make_rwb(int w, int h, uint32_t stride, int format, int usage, buffer_handle_t handle)
{
    RemoteWindowBuffer* rb = new (std::nothrow) RemoteWindowBuffer(w, h, stride, format, usage, handle);
    if (!rb) {
        return {};
    }
    return SharedRwb(rb, RwbDeleter{});
}

bool buffer_id_to_indices(int id, size_t& seg_idx, size_t& slot_idx)
{
    if (id <= 0) {
        return false;
    }

    const uint32_t zero_based = static_cast<uint32_t>(id - 1);
    seg_idx = zero_based >> kBufferSegmentShift;
    if (seg_idx >= kBufferMaxSegments) {
        return false;
    }

    slot_idx = zero_based & kBufferSegmentMask;
    return true;
}

BufferSegment* get_buffer_segment_if_present(size_t seg_idx)
{
    return g_buffer_segments[seg_idx].load(std::memory_order_acquire);
}

BufferSegment* ensure_buffer_segment(size_t seg_idx)
{
    BufferSegment* seg = get_buffer_segment_if_present(seg_idx);
    if (seg) {
        return seg;
    }

    std::lock_guard<std::mutex> lk(g_buffer_segment_alloc_mutex);
    seg = get_buffer_segment_if_present(seg_idx);
    if (seg) {
        return seg;
    }

    seg = new (std::nothrow) BufferSegment();
    if (!seg) {
        return nullptr;
    }

    g_buffer_segments[seg_idx].store(seg, std::memory_order_release);
    return seg;
}

BufferSlot* get_buffer_slot_if_present(int id)
{
    size_t seg_idx = 0;
    size_t slot_idx = 0;
    if (!buffer_id_to_indices(id, seg_idx, slot_idx)) {
        return nullptr;
    }

    BufferSegment* seg = get_buffer_segment_if_present(seg_idx);
    if (!seg) {
        return nullptr;
    }

    return &seg->slots[slot_idx];
}

BufferSlot* ensure_buffer_slot(int id)
{
    size_t seg_idx = 0;
    size_t slot_idx = 0;
    if (!buffer_id_to_indices(id, seg_idx, slot_idx)) {
        return nullptr;
    }

    BufferSegment* seg = ensure_buffer_segment(seg_idx);
    if (!seg) {
        return nullptr;
    }

    return &seg->slots[slot_idx];
}

std::shared_ptr<BufferEntry> get_entry_atomic(int id)
{
    BufferSlot* slot = get_buffer_slot_if_present(id);
    if (!slot) {
        return {};
    }

    return std::atomic_load_explicit(&slot->entry, std::memory_order_acquire);
}

void unbind_buffer_from_display_locked(int buf_id, int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    g_display_bound_buffers[drv_display_id].erase(buf_id);
    Display& D = get_or_create_display(drv_display_id);
    D.slot_mgr.release(buf_id);
}

void reset_buffer_binding_locked(int buf_id, const std::shared_ptr<BufferEntry>& entry)
{
    (void)buf_id;
    if (!entry) {
        return;
    }

    entry->bound_display_id.store(-1, std::memory_order_relaxed);
    entry->bound_generation.store(0, std::memory_order_relaxed);
    entry->bound_slot.store(UINT32_MAX, std::memory_order_relaxed);
}

bool buffer_entry_is_live_atomic(int buf_id, const std::shared_ptr<BufferEntry>& entry)
{
    return entry &&
           entry->live.load(std::memory_order_acquire) &&
           get_entry_atomic(buf_id) == entry;
}

void bind_buffer_to_display_locked(int buf_id, const std::shared_ptr<BufferEntry>& entry, int drv_display_id, uint64_t generation, uint32_t slot)
{
    if (!entry || drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    g_display_bound_buffers[drv_display_id].insert(buf_id);
    entry->bound_display_id.store(drv_display_id, std::memory_order_relaxed);
    entry->bound_generation.store(generation, std::memory_order_relaxed);
    entry->bound_slot.store(slot, std::memory_order_relaxed);
}

std::shared_ptr<BufferEntry> remove_entry_atomic(int id)
{
    BufferSlot* slot = get_buffer_slot_if_present(id);
    if (!slot) {
        return {};
    }

    std::shared_ptr<BufferEntry> entry =
        std::atomic_exchange_explicit(&slot->entry,
                                      std::shared_ptr<BufferEntry>{},
                                      std::memory_order_acq_rel);
    if (entry) {
        entry->live.store(false, std::memory_order_release);
    }
    return entry;
}

void unbind_buffer_everywhere_locked(int buf_id)
{
    for (int d = 0; d < kMaxDriverDisplays; ++d) {
        g_display_bound_buffers[d].erase(buf_id);
        auto it = g_displays.find(d);
        if (it != g_displays.end()) {
            it->second.slot_mgr.release(buf_id);
        }
    }
}

void erase_buffer_locked(int buf_id)
{
    std::shared_ptr<BufferEntry> entry = remove_entry_atomic(buf_id);
    if (!entry) {
        return;
    }

    reset_buffer_binding_locked(buf_id, entry);
    unbind_buffer_everywhere_locked(buf_id);
}

void reset_display_bindings_locked(int drv_display_id)
{
    if (drv_display_id < 0 || drv_display_id >= kMaxDriverDisplays) {
        return;
    }

    Display& D = get_or_create_display(drv_display_id);

    for (int buf_id : g_display_bound_buffers[drv_display_id]) {
        std::shared_ptr<BufferEntry> entry = get_entry_atomic(buf_id);
        if (entry) {
            reset_buffer_binding_locked(buf_id, entry);
        }
    }

    g_display_bound_buffers[drv_display_id].clear();
    D.slot_mgr.reset();
}

void buffer_table_reserve_ids(size_t count)
{
    if (count == 0) {
        return;
    }

    const size_t need_segments = (count + kBufferSegmentSize - 1) / kBufferSegmentSize;
    for (size_t i = 0; i < need_segments && i < kBufferMaxSegments; ++i) {
        (void)ensure_buffer_segment(i);
    }
}

void buffer_table_shutdown()
{
    for (size_t i = 0; i < kBufferMaxSegments; ++i) {
        BufferSegment* seg = g_buffer_segments[i].exchange(nullptr, std::memory_order_acq_rel);
        if (!seg) {
            continue;
        }

        for (size_t j = 0; j < kBufferSegmentSize; ++j) {
            std::atomic_store_explicit(&seg->slots[j].entry,
                                       std::shared_ptr<BufferEntry>{},
                                       std::memory_order_release);
        }

        delete seg;
    }
}

int add_handle(native_handle_t* handle, BufferOrigin origin, int format, uint32_t stride, uint32_t width, uint32_t height)
{
    const uint32_t raw_id = g_next_buffer_id.fetch_add(1, std::memory_order_acq_rel);
    if (raw_id == 0 || raw_id > static_cast<uint32_t>(INT_MAX)) {
        return -1;
    }

    const int id = static_cast<int>(raw_id);
    BufferSlot* slot = ensure_buffer_slot(id);
    if (!slot) {
        return -1;
    }

    auto e = std::make_shared<BufferEntry>();
    e->origin = origin;
    e->handle = handle;
    e->format = format;
    e->stride = stride;
    e->width = width;
    e->height = height;

    if (std::atomic_load_explicit(&slot->entry, std::memory_order_acquire)) {
        fprintf(stderr, "Buffer slot collision for id=%d\n", id);
        return -1;
    }

    std::atomic_store_explicit(&slot->entry, e, std::memory_order_release);
    return id;
}

SharedRwb load_entry_rwb_atomic(const std::shared_ptr<BufferEntry>& entry)
{
    return std::atomic_load(&entry->rwb);
}

void store_entry_rwb_atomic(const std::shared_ptr<BufferEntry>& entry, const SharedRwb& rwb)
{
    std::atomic_store(&entry->rwb, rwb);
}

void get_entry_buffer_geometry(const std::shared_ptr<BufferEntry>& entry, const DisplayRuntimeSnapshot& dsnap, uint32_t& buf_stride, int& buf_w, int& buf_h, int& buf_format)
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

bool entry_rwb_matches_atomic(const std::shared_ptr<BufferEntry>& entry, int buf_w, int buf_h, uint32_t buf_stride, int buf_format, SharedRwb& out_rwb)
{
    out_rwb = load_entry_rwb_atomic(entry);
    if (!out_rwb) {
        return false;
    }

    return entry->rwb_w.load(std::memory_order_acquire) == buf_w &&
           entry->rwb_h.load(std::memory_order_acquire) == buf_h &&
           entry->rwb_stride.load(std::memory_order_acquire) == buf_stride &&
           entry->rwb_format.load(std::memory_order_acquire) == buf_format;
}

bool prepare_present_job_fast(int id, int drv_display_id, const std::shared_ptr<BufferEntry>& entry, PresentJob& out)
{
    if (unlikely(!entry || !entry->live.load(std::memory_order_acquire))) {
        return false;
    }

    DisplayRuntimeSnapshot dsnap = snapshot_display_runtime_atomic(drv_display_id);
    if (unlikely(!dsnap.hwcDisplay || !dsnap.connected || dsnap.width <= 0 || dsnap.height <= 0 || dsnap.stride == 0)) {
        request_display_resync(drv_display_id);
        return false;
    }

    const int bound_display = entry->bound_display_id.load(std::memory_order_acquire);
    const uint64_t bound_generation = entry->bound_generation.load(std::memory_order_acquire);
    const uint32_t bound_slot = entry->bound_slot.load(std::memory_order_acquire);

    if (bound_display != drv_display_id ||
        bound_generation != dsnap.generation ||
        bound_slot == UINT32_MAX) {
        return false;
    }

    uint32_t buf_stride = 0;
    int buf_w = 0;
    int buf_h = 0;
    int buf_format = 0;
    get_entry_buffer_geometry(entry, dsnap, buf_stride, buf_w, buf_h, buf_format);

    if (unlikely(buf_stride == 0 || buf_w <= 0 || buf_h <= 0)) {
        fprintf(stderr, "Invalid buffer geometry for id=%d (origin=%d, w=%d, h=%d, stride=%u)\n",
                id, (int)entry->origin, buf_w, buf_h, buf_stride);
        request_display_resync(drv_display_id);
        return false;
    }

    SharedRwb rwb;
    if (!entry_rwb_matches_atomic(entry, buf_w, buf_h, buf_stride, buf_format, rwb)) {
        return false;
    }

    if (unlikely(!entry->live.load(std::memory_order_acquire))) {
        return false;
    }

    out.drv_display_id = drv_display_id;
    out.buf_id = id;
    out.generation = dsnap.generation;
    out.slot = bound_slot;
    out.entry = entry;
    out.rwb = std::move(rwb);
    return true;
}

bool prepare_present_job_slow(int id, int drv_display_id, const std::shared_ptr<BufferEntry>& entry, PresentJob& out)
{
    DisplayRuntimeSnapshot dsnap;
    uint32_t slot = UINT32_MAX;
    uint32_t buf_stride = 0;
    int buf_w = 0;
    int buf_h = 0;
    int buf_format = 0;

    {
        std::lock_guard<std::mutex> lk(g_state_mutex);

        if (!buffer_entry_is_live_atomic(id, entry) || !entry->handle) {
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

        if (unlikely(!dsnap.hwcDisplay || !dsnap.connected || dsnap.width <= 0 || dsnap.height <= 0 || dsnap.stride == 0)) {
            request_display_resync(drv_display_id);
            return false;
        }

        const int bound_display = entry->bound_display_id.load(std::memory_order_relaxed);
        const uint64_t bound_generation = entry->bound_generation.load(std::memory_order_relaxed);

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
            if ((entry->width != 0 && entry->width != dsnap.width) ||
                (entry->height != 0 && entry->height != dsnap.height)) {
                fprintf(stderr,
                        "Dropping stale/mismatched buffer id=%d for display=%d (buf=%dx%d, display=%dx%d)\n",
                        id, drv_display_id, entry->width, entry->height, dsnap.width, dsnap.height);
                request_display_resync(drv_display_id);
                return false;
            }
            reset_buffer_binding_locked(id, entry);
        }

        slot = D.slot_mgr.assign(id);
        if (slot == UINT32_MAX) {
            fprintf(stderr, "SlotManager: failed to assign slot for bufid %d on display %d\n",
                    id, drv_display_id);
            return false;
        }

        bind_buffer_to_display_locked(id, entry, drv_display_id, dsnap.generation, slot);
        get_entry_buffer_geometry(entry, dsnap, buf_stride, buf_w, buf_h, buf_format);
    }

    if (unlikely(buf_stride == 0 || buf_w <= 0 || buf_h <= 0)) {
        fprintf(stderr, "Invalid buffer geometry for id=%d (origin=%d, w=%d, h=%d, stride=%u)\n",
                id, (int)entry->origin, buf_w, buf_h, buf_stride);
        request_display_resync(drv_display_id);
        return false;
    }

    SharedRwb rwb;
    if (!entry_rwb_matches_atomic(entry, buf_w, buf_h, buf_stride, buf_format, rwb)) {
        SharedRwb new_rwb = make_rwb(buf_w, buf_h, buf_stride, buf_format, kRwbUsage, entry->handle);
        if (unlikely(!new_rwb)) {
            fprintf(stderr, "Failed to allocate RemoteWindowBuffer for id=%d\n", id);
            return false;
        }

        if (entry->bound_display_id.load(std::memory_order_acquire) != drv_display_id ||
            entry->bound_generation.load(std::memory_order_acquire) != dsnap.generation ||
            entry->bound_slot.load(std::memory_order_acquire) != slot ||
            !entry->live.load(std::memory_order_acquire)) {
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

void get_buf_from_map(void *data, int poll_id)
{
    int id;
    struct drm_evdi_get_buff_callabck cmd = {};
    memcpy(&id, data, sizeof(int));
    cmd.poll_id = poll_id;

    std::shared_ptr<BufferEntry> entry = get_entry_atomic(id);
    native_handle_t* handle =
        (entry && entry->live.load(std::memory_order_acquire)) ? entry->handle : nullptr;

    if (!handle) {
        cmd.version = -1;
        cmd.numFds = -1;
        cmd.numInts = -1;
        cmd.fd_ints = nullptr;
        cmd.data_ints = nullptr;
    } else {
        cmd.version = handle->version;
        cmd.numFds = handle->numFds;
        cmd.numInts = handle->numInts;
        cmd.fd_ints = (handle->numFds > 0) ? const_cast<int *>(&handle->data[0]) : nullptr;
        cmd.data_ints = (handle->numInts > 0) ? const_cast<int *>(&handle->data[handle->numFds]) : nullptr;
    }

    (void)drm_ioctl(DRM_IOCTL_EVDI_GET_BUFF_CALLBACK, &cmd);
}

void swap_to_buff(void *data, int poll_id)
{
    (void)poll_id;

    struct {
        int id;
        int display_id;
    } ex = { -1, 0 };

    memcpy(&ex, data, sizeof(ex));

    const int id = ex.id;
    const int drv_display_id = ex.display_id;

    std::shared_ptr<BufferEntry> entry = get_entry_atomic(id);
    if (!entry || !entry->live.load(std::memory_order_acquire) || !entry->handle) {
        request_display_resync(drv_display_id);
        return;
    }

    PresentJob j;
    if (!prepare_present_job_fast(id, drv_display_id, entry, j) &&
        !prepare_present_job_slow(id, drv_display_id, entry, j)) {
        return;
    }

    enqueue_present_job(std::move(j));
}

void destroy_buff(void *data, int poll_id)
{
    int id = *(int *)data;
    {
        std::lock_guard<std::mutex> lk(g_state_mutex);
        erase_buffer_locked(id);
    }

    struct drm_evdi_destroy_buff_callback cmd = { .poll_id = poll_id };
    (void)drm_ioctl(DRM_IOCTL_EVDI_DESTROY_BUFF_CALLBACK, &cmd);
}

void create_buff(void *data, int poll_id)
{
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

}
