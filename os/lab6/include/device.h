#ifndef DEVICE_H
#define DEVICE_H

#include <stddef.h>
#include <utils/hash_table.h>

struct device {
    uint64_t ref_count;
    struct device *parent;
    struct hash_table_node hash_node;

    const char *device_name;
    uint64_t device_id;
    void *match_data;

    void *driver_data;

    uint64_t interface_flag;
    void *(*get_interface)(struct device *, uint64_t interface_id);
};

struct driver_match_table {
    const char *compatible;
    void *match_data;
};

struct device_driver {
    const char *driver_name;
    struct driver_match_table *match_table;

    uint64_t (*device_probe)(struct device *dev);
};

#define DEVICE_TABLE_BUFFER_LENGTH 11
extern struct hash_table device_table;
void init_device_table();
uint32_t device_table_get_major_num(uint32_t major);
uint32_t device_table_get_next_minor(uint32_t major, uint32_t minor_start);
void load_drivers();

static inline void device_set_data(struct device *dev, void *data) {
    dev->driver_data = data;
}
static inline void *device_get_data(struct device *dev) {
    return dev->driver_data;
}
static inline void device_set_interface(struct device *dev, uint64_t flag, void *(*getter)(struct device *, uint64_t)) {
    dev->interface_flag = flag;
    dev->get_interface = getter;
}
static inline uint32_t device_get_major(struct device *dev) {
    return dev->device_id >> 32;
}
static inline uint32_t device_get_minor(struct device *dev) {
    return dev->device_id & 0xFFFFFFFF;
}
static inline uint64_t device_set_major(struct device *dev, uint32_t major) {
    return dev->device_id = ((uint64_t)major << 32) | device_get_minor(dev);
}
static inline uint64_t device_set_minor(struct device *dev, uint32_t minor) {
    return dev->device_id = ((uint64_t)minor & 0xFFFFFFFF) | device_get_major(dev);
}
static inline void device_register(struct device *dev, const char *name, uint32_t major, struct device *parent) {
    uint32_t minor = device_table_get_next_minor(major, 1);
    device_set_major(dev, major);
    device_set_minor(dev, minor);
    dev->device_name = name;
    dev->ref_count = 0;
    dev->parent = parent;
    if (parent) dev->parent->ref_count += 1;
    hash_table_set(&device_table, &dev->hash_node);
}
#endif
