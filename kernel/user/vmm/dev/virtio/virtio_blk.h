#ifndef _VDEV_VIRTIO_BLK_H_
#define _VDEV_VIRTIO_BLK_H_

#include <types.h>

#include "virtio.h"

#define ATA_SECTOR_SIZE		512

/* VirtIO block device features */
#define VIRTIO_BLK_F_BARRIER	(1 << 0)
#define VIRTIO_BLK_F_SIZE_MAX	(1 << 1)
#define VIRTIO_BLK_F_SEG_MAX	(1 << 2)
#define VIRTIO_BLK_F_GEOMETRY	(1 << 4)
#define VIRTIO_BLK_F_RO		(1 << 5)
#define VIRTIO_BLK_F_BLK_SIZE	(1 << 6)
#define VIRTIO_BLK_F_SCSI	(1 << 7)
#define VIRTIO_BLK_F_FLUSH	(1 << 9)

/* VirtIO block device configuration layout */
struct virtio_blk_config {
	uint64_t capacity;	/* in 512 byte sectors */
	uint32_t size_max;
	uint32_t seg_max;

	struct virtio_blk_geometry {
		uint16_t cylinders;
		uint8_t heads;
		uint8_t sectors;
	} geometry;

	uint32_t blk_size;
};

struct virtio_blk_outhdr {
	uint32_t type;
#define VIRTIO_BLK_T_IN			0x00000000
#define VIRTIO_BLK_T_OUT		0x00000001
#define VIRTIO_BLK_T_SCSI_CMD		0x00000002
#define VIRTIO_BLK_T_FLUSH		0x00000004
#define VIRTIO_BLK_T_GET_ID		0x00000008
#define VIRTIO_BLK_T_BARRIER		0x80000000
	uint32_t ioprio;
	uint64_t sector;
};

#define VIRTIO_BLK_S_OK			0x00000000
#define VIRTIO_BLK_S_IOERR		0x00000001
#define VIRTIO_BLK_S_UNSUPP		0x00000002

#define VIRTIO_BLK_QUEUE_SIZE		128

#define VIRTIO_BLK_DEVICE_NAME		"virtio block drive"
#define VIRTIO_BLK_DEVICE_NAME_LEN				\
	(sizeof(VIRTIO_BLK_DEVICE_NAME) / sizeof(char) - 1)

struct virtio_blk {
	/* common virtio device header */
	struct virtio_device common_header;

	/* specific header of virtio block device */
	struct virtio_blk_config blk_header;

	/* virtqueue/vring of the virtio block device */
	struct vring vring;

	/* are there unhandled requests in the virtqueue? */
	bool pending_req;
};

int virtio_blk_init(struct vdev *vdev, void *pci, void *blk);

#endif /* !_SYS_VIRT_DEV_VIRTIO_BLK_H_ */
