#ifndef _USER_VIRTIO_MBR_H_
#define _USER_VIRTIO_MBR_H_

#include <gcc.h>
#include <types.h>

struct mbr {
	uint8_t bootloader[436];
	uint8_t disk_sig[10];
	struct {
		uint8_t bootable;
#define INACTIVE_PARTITION	0x00
#define BOOTABLE_PARTITION	0x80
		uint8_t first_chs[3];
		uint8_t id;
#define EMPTY_PARTITION		0x00
#define LINUX_PARTITION		0x83
#define EXTENDED_PARTITION	0x5
		uint8_t last_chs[3];
		uint32_t first_lba;
		uint32_t sectors_count;
	} gcc_packed partition[4];
	uint8_t signature[2];
} gcc_packed;

#endif /* !_USER_VIRTIO_MBR_H_ */
