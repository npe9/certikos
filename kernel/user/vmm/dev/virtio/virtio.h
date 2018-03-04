/*
 * virtio.h and virtio.c define the common interface to implement a virtio
 * device.
 */

#ifndef _VDEV_VIRTIO_H_
#define _VDEV_VIRTIO_H_

#include <gcc.h>
#include <types.h>

#include "pci.h"
#include "../../vmm_dev.h"

#define VIRTIO_PCI_VENDOR_ID		0x1af4
/* NOTE: SeaBIOS requires the device ID of a VirtIO block device be 0x1001. */
#define VIRTIO_PCI_DEVICE_BLK		0x1001
#define VIRTIO_PCI_REVISION		0x0

#define VIRTIO_PCI_SUBDEV_NIC		0x1
#define VIRTIO_PCI_SUBDEV_BLK		0x2
#define VIRTIO_PCI_SUBDEV_CONSOLE	0x3
#define VIRTIO_PCI_SUBDEV_ENTROPY	0x4
#define VIRTIO_PCI_SUBDEV_BALLOON	0x5
#define VIRTIO_PCI_SUBDEV_IOMEM		0x6
#define VIRTIO_PCI_SUBDEV_RPMSG		0x7
#define VIRTIO_PCI_SUBDEV_SCSI		0x8
#define VIRTIO_PCI_SUBDEV_9P		0x9

/* reserved features bits */
#define VIRTIO_F_NOTIFY_ON_EMPTY	(1 << 24)
#define VIRTIO_F_RING_INDIRECT_DESC	(1 << 28)
#define VIRTIO_F_RING_EVENT_IDX		(1 << 29)

/*
 * A VirtIO device is recognized as a PCI device with vendor ID 0x1af4 and
 * device ID 0x1000 ~ 0x103f. BAR0 of a VirtIO device points to a VirtIO header
 * which describes the basic inforamtion of this device and is accessed through
 * reading/writing I/O ports.
 *
 *
 *                Device Configuration
 * PCI BAR0 ----> +---------------+  offset: 0x0
 * (I/O port)     |               |
 *                | VirtIO Header |  (struct virtio_header) -------------------+
 *                |               |                                            |
 *                +---------------+  offset: 0x14                              |
 *                |               |                                            |
 *                |   MSI Header  |  (struct virtio_ms_header)                 |
 *                |   (optional)  |  (not implemented in CertiKOS)             |
 *                |               |                                            |
 *                +---------------+  offset: 0x18/0x14                         |
 *                |               |                                            |
 *                | Device Header |  (strcut virtio_blk_config, ...)           |
 *                |               |                                            |
 *                +---------------+     +--------------------------------------+
 *                                      |
 *  /-----------------------------------^-------------------------------------\
 * /                                                                           \
 * VirtIO Header (struct virtio_header) (I/O port)
 * 0x14  0x13     0x12     0x10      0xe     0xc       0x8        0x4        0x0
 * +--------+--------+--------+--------+-------+---------+----------+----------+
 * |  ISR   | Device | Queue  | Queue  | Queue |  Queue  |  Guest   |  Device  |
 * | Status | Status | Notify | Select |  Size | Address | Features | Features |
 * +--------+--------+--------+--------+-------+---------+----------+----------+
 *                                                  |
 *              VRing (MMIO)                        | x 4096
 *              +----------------------+ <----------+
 *          +-- |   VRing Descriptor0  | (struct vring_desc)
 *          |   :         ...          :
 *          |   |   VRing DescriptorN  |
 *          |   +----------------------+
 *       +--^-- | Available Rings Info | (struct vring_avail)
 *       |  |   +----------------------+
 *       |  |   :                      : Padding to the next 4096 boundary
 *       |  |   +----------------------+
 *    +--^--^-- |    Used Rings Info   | (struct vring_used)
 *    |  |  |   +----------------------+
 *    |  |  |
 *    |  |  +--------------------+
 *    |  |                       |
 *    |  |      /----------------^----------------\
 *    |  |      VRing Descriptor 0 (MMIO)
 *    |  |      0x10 0xe     0xc      0x8       0x0
 *    |  |      +------+-------+--------+---------+
 *    |  |      | next | flags | length | address |
 *    |  |      +------+-------+--------+---------+
 *    |  |          |
 *    |  |          +-----------------------------+
 *    |  |                                        |
 *    |  |      VRing Descriptor 1 (MMIO)         V
 *    |  |      0x10 0xe     0xc      0x8       0x0
 *    |  |      +------+-------+--------+---------+
 *    |  |      | next | flags | length | address |
 *    |  |      +------+-------+--------+---------+
 *    |  |
 *    |  |                     ...
 *    |  |
 *    |  +--------------------------------+
 *    |                                   |
 *    |         /-------------------------^----------------------------\
 *    |         Available Rings Info (struct vring_avail) (MMIO)
 *    |                                      0x6     0x4     0x2     0x0
 *    |         +------------+-------+---------+-------+-------+-------+
 *    |         | Used Event | RingN |   ...   | Ring0 | index | flags |
 *    |         +------------+-------+---------+-------+-------+-------+
 *    |
 *    +--------------------------------------+
 *                                           |
 *              /----------------------------^--------------------------------\
 *              Used Rings Info (struct vring_used) (MMIO)
 *                                               0xc        0x4     0x2     0x0
 *              +-------------+----------+---------+----------+-------+-------+
 *              | Avail Event | idN,lenN |   ...   | id0,len0 | index | flags |
 *              +-------------+----------+---------+----------+-------+-------+
 *
 */

/* VirtIO Header */
struct virtio_header {
	uint32_t device_features;	/* R */
	uint32_t guest_features;	/* RW */
	uint32_t queue_addr;		/* RW */
	uint16_t queue_size;		/* R */
	uint16_t queue_select;		/* RW */
	uint16_t queue_notify;		/* RW */
	uint8_t device_status;		/* RW */
#define VIRTIO_CONFIG_S_ACKNOWLEDGE	(1 << 0)
#define VIRTIO_CONFIG_S_DRIVER		(1 << 1)
#define VIRTIO_CONFIG_S_DRIVER_OK	(1 << 2)
#define VIRTIO_CONFIG_S_FAILED		(1 << 8)
	uint8_t isr_status;		/* R */
};

/* VirtIO MSI Header (optional, not implemented in CertiKOS) */
struct virtio_msi_header {
	uint16_t config_vector;		/* RW */
	uint16_t queue_vector;		/* RW */
};

/* VRing Descriptor */
struct vring_desc {
	uint64_t addr;
	uint32_t len;
	uint16_t flags;
#define VRING_DESC_F_NEXT		(1 << 0)
#define VRING_DESC_F_WRITE		(1 << 1)
#define VRING_DESC_F_INDIRECT		(1 << 2)
	uint16_t next;
} gcc_packed;

/* Available Rings Info */
struct vring_avail {
	uint16_t flags;
#define VRING_AVAIL_F_NO_INTERRUPT	(1 << 0)
	uint16_t idx;
	uint16_t ring[0];
} gcc_packed;

/* Used Rings Info */
struct vring_used {
	uint16_t flags;
#define VRING_USED_F_NO_NOTIFY		(1 << 0)
	uint16_t idx;
	struct vring_used_elem {
		uint32_t id;
		uint32_t len;
	} ring[0];
} gcc_packed;

/* VRing */
struct vring {
	uint16_t queue_size;
	uintptr_t desc_guest_addr;
	uintptr_t avail_guest_addr;
	uintptr_t used_guest_addr;
	uint16_t last_avail_idx;
	bool need_notify;
	struct vdev *vdev;
};

/*
 * There are three things a concrete virtio device MUST do.
 *
 * A concrete virtio device (e.g. a virtio block device) should put an object
 * of type struct virtio_device in the beginning of its structure. (See the
 * comments of struct virtio_device below)
 *
 * Another structure a concrete virtio device should provide is an object of
 * type struct virtio_device_ops. A concrete virtio device provides hooks for
 * the device-specific operations. (See the comments of struct virtio_device_ops
 * below.)
 *
 * The initialization function of a concrete virtio device should call
 * virtio_device_init().
 *
 * (You may check virtio_blk.h and virtio_blk.c as an example.)
 */

struct virtio_device;

struct virtio_device_ops {
	/*
	 * I/O port handlers for reading/writing the PCI configuration.
	 *
	 * CertiKOS does not provide a framework for PCI emulation, so each PCI
	 * device has to handle the PCI reading/writing operations by itself.
	 *
	 * @param dev      point to a virtio_device structure
	 * @param pci_addr the 32 bits value in PCI address port (default 0xcf8)
	 * @param val      the value to be written in (for pci_conf_Write()); it
	 *                 will be truncated according to parameter sz
	 * @param sz       the width of the data to be accessed
	 */
	uint32_t (*pci_conf_read)(void *dev, uint32_t pci_addr, data_sz_t sz);
	void (*pci_conf_write)(void *dev, uint32_t pci_addr,
			       uint32_t val, data_sz_t sz);

	/*
	 * I/O port handlers for reading/writing the device header.
	 */
	void (*update_ioport_handlers)(struct virtio_device *);

	/* get the amount of virtqueues/vrings of the virtio device */
	uint8_t (*get_vrings_amount)(struct virtio_device *);

	/*
	 * Get virtqueue/vring #vq_idx.
	 *
	 * @return NULL if the virtqueue/vring does not exist
	 */
	struct vring * (*get_vring)(struct virtio_device *, uint8_t vq_idx);

	/*
	 * Handle the request which is described by the descriptor #desc_idx in
	 * virtqueue/vring #vq_idx.
	 *
	 * XXX: It's this function's duty to update the used index.
	 *
	 * @return 0 if no errors happen
	 */
	int (*handle_req)(struct virtio_device *,
			  uint8_t vq_idx, uint16_t desc_idx);
};

/*
 * Common virtio device header.
 *
 * XXX: It should be put in the beginning of the data structure of concrete
 *      virtio devices, e.g. the data structure of a virtio block is like
 *              struct virtio_blk {
 *                      struct virtio_device common_header;
 *                      ...
 *              };
 */
struct virtio_device {
	struct vdev *vdev;
	struct pci_general pci_conf;		/* PCI header */
	struct vpci_device pci_dev;		/* vPCI device */

	struct virtio_header virtio_header;	/* VirtIO header */

	uint16_t iobase;			/* base of I/O ports */
	uint16_t iosize;			/* size in byte of I/O ports */

	struct virtio_device_ops *ops;		/* device-specific operations */
};

/*
 * Get the descriptor #idx of virtqueue/vring #ring.
 */
int vring_get_desc(struct vring *ring, uint16_t idx, struct vring_desc *desc);

/*
 * Get the avail structure of virtqueue/vring #ring.
 */
int vring_get_avail(struct vring *ring, struct vring_avail *avail);

/*
 * Get the used structure of virtqueue/vring #ring.
 */
int vring_get_used(struct vring *ring, struct vring_used *used);

int vring_set_used(struct vring *, struct vring_used *);

int vring_get_used_elem(struct vring *, int idx, struct vring_used_elem *);

int vring_set_used_elem(struct vring *, int idx, struct vring_used_elem *);

/*
 * Do the common intialization for a virtio device.
 */
int virtio_device_init(struct virtio_device *, struct virtio_device_ops *,
		       struct vpci_host *, struct vdev *);

void virtio_handle_guest_in(struct virtio_device *dev,
			    uint16_t port, data_sz_t width, void *data);
void virtio_handle_guest_out(struct virtio_device *dev,
			     uint16_t port, data_sz_t width, uint32_t data);

/*
 * Reregister I/O port handlers for reading/writing the device configuration
 * The device-specific function (virtio_device_ops.update_ioport_handlers) is
 * called at the end.
 *
 * XXX: It's recommeneded to call this function each time BAR0 of the virtio
 *      device is changed.
 */
void virtio_device_update_ioport_handlers(struct virtio_device *,
					  uint16_t new_iobase);

#endif /* !_VDEV_VIRTIO_H_ */
