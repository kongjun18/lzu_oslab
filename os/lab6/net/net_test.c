#include <net/netdev.h>

uint64_t net_test() {
    uint8_t arp_packet[] = {
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0x52, 0x54, 0x00, 0x12, 0x34, 0x56,
        0x08, 0x06,
        0x00, 0x01,
        0x08, 0x00,
        0x06, 0x04,
        0x00, 0x01,
        0x52, 0x54, 0x00, 0x12, 0x34, 0x56,
        10, 0, 0, 15, // src ip
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        10, 0, 0, 2   // dst ip
    };
    netdev_send(arp_packet, sizeof(arp_packet));
    return 0;
}
