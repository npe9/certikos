#include <debug.h>
#include <stdio.h>
#include <string.h>
#include <syscall.h>
#include <types.h>
#include <x86.h>

#include "mbr.h"
#include "pci.h"
#include "virtio.h"
#include "virtio_blk.h"
#include "../../vmm.h"
#include "../../vmm_dev.h"

#ifdef DEBUG_VIRTIO_BLK

#define virtio_blk_debug(fmt, ...)			\
	do {						\
		DEBUG("VIOBLK: "fmt, ##__VA_ARGS__);	\
	} while (0)

#else

#define virtio_blk_debug(fmt...)		\
	do {					\
	} while (0)

#endif

#ifdef ENABLE_BOOT_CF

static uint32_t drv_nr = 1;
static struct mbr MBR;
static uint8_t empty_sector[512] = { 0 };

static void
prep_mbr(void)
{
	int rc, i;

	if ((rc = sys_disk_read(drv_nr, 0, 1, &MBR)))
		PANIC("Failed to read MBR (errno %d).\n", rc);

	for (i = 0; i < 4; i++) {
		if (MBR.partition[i].id == EMPTY_PARTITION)
			continue;
		printf("%s%d: %d ~ %d %s\n",
		       MBR.partition[i].bootable ==
		       BOOTABLE_PARTITION ? "*" : " ",
		       i,
		       MBR.partition[i].first_lba,
		       MBR.partition[i].first_lba +
		       MBR.partition[i].sectors_count - 1,
		       MBR.partition[i].id == LINUX_PARTITION ? "Linux" :
		       MBR.partition[i].id == EXTENDED_PARTITION ? "Extended" :
		       "(Unknown)");
	}

	/*
	 * Mark the 2nd partition as bootable
	 */
	MBR.partition[0].bootable = INACTIVE_PARTITION;
	MBR.partition[1].bootable = BOOTABLE_PARTITION;
}

#else /* !ENABLE_BOOT_CF */

/* static uint32_t drv_nr = 0; */

#endif /* ENABLE_BOOT_CF */

static uint16_t unsupported_command =
	0xf880 /* reserved bits */ | PCI_COMMAND_MEM_ENABLE |
	PCI_COMMAND_SPECIAL_ENABLE | PCI_COMMAND_INVALIDATE_ENABLE |
	PCI_COMMAND_PALETTE_ENABLE | PCI_COMMAND_PARITY_ENABLE |
	PCI_COMMAND_SERR_ENABLE | PCI_COMMAND_BACKTOBACK_ENABLE;

#define VIRTIO_BLK_MAX_SECTORS	16
static uint8_t virtio_blk_data_buf[ATA_SECTOR_SIZE * VIRTIO_BLK_MAX_SECTORS];

/*
 * Perform the VirtIO block device-specific PCI command, which is recorded in
 * blk->common.header.pci_conf.header.command.
 */
static void
virtio_blk_perform_pci_command(struct virtio_blk *blk)
{
	ASSERT(blk != NULL);

	uint16_t command = blk->common_header.pci_conf.header.command;

	if (command == 0) {
		virtio_blk_debug("logically disconnected.\n");
		blk->vring.desc_guest_addr = 0;
		blk->vring.avail_guest_addr = 0;
		blk->vring.used_guest_addr = 0;
		blk->vring.last_avail_idx = 0;
		blk->vring.need_notify = FALSE;
	}

	if (command & unsupported_command) {
		virtio_blk_debug("ignore unsupported command %08x.\n",
				 command & unsupported_command);
		command &= ~unsupported_command;
		blk->common_header.pci_conf.header.command = command;
	}

	smp_wmb();
}

/*
 * virtio_blk_pci_conf_read()
 * virtio_blk_pci_conf_write()
 *   Default function to read/write the PCI configuration space. (via I/O ports)
 */

static uint32_t
virtio_blk_pci_conf_read(void *opaque, uint32_t addr, data_sz_t size)
{
	ASSERT(opaque != NULL);

	struct virtio_device *dev;
	int len;
	uint8_t reg, *pci_conf;

	dev = (struct virtio_device *) opaque;

	reg = addr & 0xfc;
	len = sizeof(dev->pci_conf);

	if (reg >= len)
		goto err;

	pci_conf = (uint8_t *) &dev->pci_conf;

	if (size == SZ8) {
		return pci_conf[reg];
	} else if (size == SZ16) {
		uint8_t data[2];
		data[0] = pci_conf[reg];
		data[1] = (reg >= len - 1) ? 0x00 : pci_conf[reg+1];
		return ((uint16_t) data[1] << 8) | data[0];
	} else if (size == SZ32) {
		uint8_t data[4];
		data[0] = pci_conf[reg];
		data[1] = (reg >= len - 1) ? 0x00 : pci_conf[reg+1];
		data[2] = (reg >= len - 2) ? 0x00 : pci_conf[reg+2];
		data[3] = (reg >= len - 3) ? 0x00 : pci_conf[reg+3];
		return ((uint32_t) data[3] << 24) | ((uint32_t) data[2] << 16) |
			((uint32_t) data[1] << 8) | data[0];
	}

 err:
	return ((size == SZ8) ? 0x000000ff :
		(size == SZ16) ? 0x0000ffff : 0xffffffff);
}

static void
virtio_blk_pci_conf_write(void *opaque,
			  uint32_t addr, uint32_t val, data_sz_t size)
{
	ASSERT(opaque != NULL);

	struct virtio_device *dev;
	int len;
	uint8_t reg, *pci_conf;

	dev = (struct virtio_device *) opaque;

	reg = addr & 0xfc;
	len = sizeof(dev->pci_conf);

	/* invaild/read-only area */
	if (reg >= len || reg == PCI_ID_REG || reg == PCI_CLASS_REG ||
	    (PCI_MAPREG_START+4 <= reg && reg < PCI_MAPREG_END) ||
	    (0x2c <= reg && reg <= 0x3c))
		return;

	pci_conf = (uint8_t *) &dev->pci_conf;

	pci_conf[reg] = (uint8_t) val;
	if (size <= SZ32 && reg < len - 1)
		pci_conf[reg+1] = (uint8_t) (val >> 8);
	if (size == SZ32) {
		if (reg < len - 2)
			pci_conf[reg+2] = (uint8_t) (val >> 16);
		if (reg < len - 3)
			pci_conf[reg+3] = (uint8_t) (val >> 24);
	}

	if (reg == PCI_COMMAND_STATUS_REG) {
		virtio_blk_perform_pci_command((struct virtio_blk *) dev);
	} else if (reg == PCI_MAPREG_START) {
		if (dev->pci_conf.bar[0] == 0xffffffff) {
			/* calculate BAR0 size */
			uint16_t size;
			int bytes;
			size = sizeof(struct virtio_header) +
				sizeof(struct virtio_blk_config);
			for (bytes = 0; size > 0; bytes++)
				size >>= 1;
			dev->iosize = (1 << bytes);
			dev->pci_conf.bar[0] ^= (1 << bytes) - 1;
			dev->pci_conf.bar[0] |= 0x1;

			virtio_blk_debug("BAR0=%08x.\n", dev->pci_conf.bar[0]);
		} else if (dev->pci_conf.bar[0] != 0) {
			/* set BAR0 address */
			dev->pci_conf.bar[0] =
				(dev->pci_conf.bar[0] & ~(uint32_t) 0x3) | 0x1;
			virtio_device_update_ioport_handlers
				(dev, (uint16_t) dev->pci_conf.bar[0] & 0xfffc);
		}
	} else if (reg == PCI_INTERRUPT_REG) {
		pci_conf[PCI_INTERRUPT_REG] &= 0x000000ff;
	}

	smp_wmb();
}

/*
 * virtio_blk_conf_readb()
 * virtio_blk_conf_readw()
 * virtio_blk_conf_readl()
 *   default functions to read (byte/word/double words) from the device
 *   configuration, the base address of which is indicated by BAR0. (via I/O
 *   ports)
 */

static void
virtio_blk_conf_readb(void *dev, uint32_t port, void *data)
{
	ASSERT(dev != NULL && data != NULL);

	uint32_t iobase;
	uint8_t *conf;
	struct virtio_blk *blk;

	blk = (struct virtio_blk *) dev;
	iobase = blk->common_header.iobase + sizeof(struct virtio_header);
	ASSERT(iobase <= port &&
	       port < iobase + sizeof(struct virtio_blk_config));
	conf = (uint8_t *) &blk->blk_header;

	*(uint8_t *) data = conf[port-iobase];

	virtio_blk_debug("readb blk reg %x, val %02x.\n",
			 port - iobase, *(uint8_t *) data);

	smp_wmb();
}

static void
virtio_blk_conf_readw(void *dev, uint32_t port, void *data)
{
	ASSERT(dev != NULL && data != NULL);

	uint32_t iobase;
	uint8_t *conf;
	struct virtio_blk *blk;

	blk = (struct virtio_blk *) dev;
	iobase = blk->common_header.iobase + sizeof(struct virtio_header);
	ASSERT(iobase <= port &&
	       port < iobase + sizeof(struct virtio_blk_config) - 1);
	conf = (uint8_t *) &blk->blk_header;

	*(uint16_t *) data =
		conf[port-iobase] | ((uint16_t) conf[port-iobase+1] << 8);

	virtio_blk_debug("readw blk reg %x, val %04x.\n",
			 port - iobase, *(uint16_t *) data);

	smp_wmb();
}

static void
virtio_blk_conf_readl(void *dev, uint32_t port, void *data)
{
	ASSERT(dev != NULL && data != NULL);

	uint32_t iobase;
	uint8_t *conf;
	struct virtio_blk *blk;

	blk = (struct virtio_blk *) dev;
	iobase = blk->common_header.iobase + sizeof(struct virtio_header);
	ASSERT(iobase <= port &&
	       port < iobase + sizeof(struct virtio_blk_config) - 3);
	conf = (uint8_t *) &blk->blk_header;

	*(uint32_t *) data =
		conf[port-iobase] | ((uint32_t) conf[port-iobase+1] << 8) |
		((uint32_t) conf[port-iobase+2] << 16) |
		((uint32_t) conf[port-iobase+3] << 24);

	virtio_blk_debug("readw blk reg %x, val %08x.\n",
			 port - iobase, *(uint32_t *) data);

	smp_wmb();
}

static int _virtio_blk_handle_guest_in(void *, uint16_t, data_sz_t, void *);
static int _virtio_blk_handle_guest_out(void *, uint16_t, data_sz_t, uint32_t);

/*
 * Register the caller process for handling reading the device header.
 */
static void
virtio_blk_update_ioport_handlers(struct virtio_device *dev)
{
	ASSERT(dev != NULL);

	struct virtio_blk *blk = (struct virtio_blk *) dev;
	uint16_t base, end, port;

	base = dev->iobase + sizeof(struct virtio_header);
	end = base + sizeof(struct virtio_blk_config);

	for (port = base; port < end; port++) {
		vdev_unregister_ioport(dev->vdev, blk, port);
		vdev_register_ioport(dev->vdev, blk, port,
				     _virtio_blk_handle_guest_in,
				     _virtio_blk_handle_guest_out);
	}
}

static uint8_t
virtio_blk_vrings_amount(struct virtio_device *dev)
{
	/* only 1 virtqueue is used by the VirtIO block device */
	return 1;
}

static struct vring *
virtio_blk_get_vring(struct virtio_device *dev, uint8_t idx)
{
	ASSERT(dev != NULL);

	if (idx != 0)
		return NULL;
	else
		return &((struct virtio_blk *) dev)->vring;
}

/*
 * virtio_blk_disk_read() / virtio_blk_disk_write()
 *   forward the read/write operations on the VirtIO block device to the host
 *   disk drive.
 */

static int
virtio_blk_disk_read(struct vm *vm,
		     uint64_t lba, uint64_t nsectors, uintptr_t gpa)
{
	int rc;
	uint64_t cur_lba, remaining;
	uintptr_t cur_gpa;
	uint8_t *buf;

	cur_lba = lba;
	remaining = nsectors;
	cur_gpa = gpa;

	while (remaining > 0) {
		uint64_t n = MIN(remaining, VIRTIO_BLK_MAX_SECTORS);

#ifdef ENABLE_BOOT_CF
		if (cur_lba == 0)
			buf = (uint8_t *) &MBR;
		else if (cur_lba < MBR.partition[0].first_lba +
			 MBR.partition[0].sectors_count &&
			 cur_lba >= MBR.partition[0].first_lba)
			buf = empty_sector;
		else
			buf = virtio_blk_data_buf;

		if (buf != virtio_blk_data_buf) {
			n = 1;
			goto read_done;
		}
#else /* !ENABLE_BOOT_CF */
		buf = virtio_blk_data_buf;
#endif /* ENABLE_BOOT_CF */

		rc = sys_disk_read(cur_lba, n, virtio_blk_data_buf);
		if (rc) {
			virtio_blk_debug("Failed to read host disk. "
					 "(lba %lld, %lld sectors)\n",
					 cur_lba, n);
			return 1;
		}

#ifdef ENABLE_BOOT_CF
	read_done:
#endif
		rc = vmm_write_guest_memory(vm, cur_gpa, (uintptr_t) buf,
					    n * ATA_SECTOR_SIZE);
		if (rc) {
			virtio_blk_debug("Failed to copy to guest. "
					 "(lba %lld, %lld sectors)\n",
					 cur_lba, n);
			return 2;
		}

		cur_lba += n;
		remaining -= n;
		cur_gpa += n * ATA_SECTOR_SIZE;
	}

	virtio_blk_debug("Succeed reading guest disk. "
			 "(lba %lld, %lld sectors)\n", lba, nsectors);
	return 0;
}

static int
virtio_blk_disk_write(struct vm *vm,
		      uint64_t lba, uint64_t nsectors, uintptr_t gpa)
{
	int rc;
	uint64_t cur_lba, remaining;
	uintptr_t cur_gpa;

	cur_lba = lba;
	remaining = nsectors;
	cur_gpa = gpa;

	while (remaining > 0) {
		uint64_t n = MIN(remaining, VIRTIO_BLK_MAX_SECTORS);

#ifdef ENABLE_BOOT_CF
		if (lba < MBR.partition[0].first_lba +
		    MBR.partition[0].sectors_count) {
			n = 1;
			goto write_done;
		}
#endif

		rc = vmm_read_guest_memory(vm, cur_gpa,
					   (uintptr_t) virtio_blk_data_buf,
					   n * ATA_SECTOR_SIZE);
		if (rc) {
			virtio_blk_debug("Failed to copy from guest. "
					 "(lba %lld, %lld sectors)\n",
					 cur_lba, n);
			return 2;
		}

		rc = sys_disk_write(cur_lba, n, virtio_blk_data_buf);
		if (rc) {
			virtio_blk_debug("Failed to write host disk. "
					 "(lba %lld, %lld sectors)\n",
					 cur_lba, n);
			return 1;
		}

#ifdef ENABLE_BOOT_CF
	write_done:
#endif
		cur_lba += n;
		remaining -= n;
		cur_gpa += n * ATA_SECTOR_SIZE;
	}

	virtio_blk_debug("Succeed writing guest disk. "
			 "(lba %lld, %lld sectors)\n", lba, nsectors);
	return 0;
}

static gcc_inline int
virtio_blk_get_id(struct vm *vm, uintptr_t gpa, uint32_t len)
{
	uint32_t size;
	char id[VIRTIO_BLK_DEVICE_NAME_LEN+1];

	if (len == 0)
		return 1;

	size = MIN(VIRTIO_BLK_DEVICE_NAME_LEN, len-1);
	strncpy(id, VIRTIO_BLK_DEVICE_NAME, size);
	id[size] = '\0';

	return vmm_write_guest_memory(vm, gpa, (uintptr_t) id, size);
}

static gcc_inline int
virtio_blk_set_status(struct vm *vm, uintptr_t gpa, uint8_t status)
{
	return vmm_write_guest_memory(vm, gpa, (uintptr_t) &status,
				      sizeof(status));
}

static int
virtio_blk_handle_req(struct virtio_device *dev,
		      uint8_t vq_idx, uint16_t desc_idx)
{
	ASSERT(dev != NULL);

	struct virtio_blk *blk;
	struct vring_desc req_desc, buf_desc, status_desc;
	struct vring_avail avail;
	struct vring_used used;
	struct vring_used_elem used_elem;
	uint16_t last_used_idx;
	struct virtio_blk_outhdr req;
	uintptr_t buf, status;
	uint32_t nsectors;

	if (vq_idx != 0)
		return 1;

	blk = (struct virtio_blk *) dev;

#ifdef DEBUG_VIRTIO_BLK
	printf("=== Desc %d ~ Desc %d ===\n", desc_idx, desc_idx + 2);
#endif

	/* get the request from the 1st descriptor on the virtqueue */
	if (vring_get_desc(&blk->vring, desc_idx, &req_desc)) {
		virtio_blk_debug("Cannot get the request descriptor %d.\n",
				 desc_idx);
		return 1;
	}
	ASSERT(!(req_desc.flags & VRING_DESC_F_WRITE));
	ASSERT(req_desc.flags & VRING_DESC_F_NEXT);

#ifdef DEBUG_VIRTIO_BLK
	printf("Desc %d, addr %llx, len %d, flags %04x, next %04x.\n",
	       desc_idx, req_desc.addr, req_desc.len,
	       req_desc.flags, req_desc.next);
#endif

	if (vmm_read_guest_memory(dev->vdev->vm, req_desc.addr,
				  (uintptr_t) &req, sizeof(req))) {
		virtio_blk_debug("Cannot get the request.\n");
		return 1;
	}

#ifdef DEBUG_VIRTIO_BLK
	if (req.type == VIRTIO_BLK_T_IN)
		printf("  read sector 0x%x", req.sector);
	else if (req.type == VIRTIO_BLK_T_OUT)
		printf("  write sector 0x%x", req.sector);
	else if (req.type == VIRTIO_BLK_T_FLUSH)
		printf("  flush");
	else if (req.type == VIRTIO_BLK_T_GET_ID)
		printf("  get id");
	else if (req.type == VIRTIO_BLK_T_BARRIER)
		printf("  barrier");
	else
		printf("  command %08x", req.type);
	printf(".\n");
#endif

	/* the address of the guest buffer is in the 2nd descriptor */
	if (vring_get_desc(&blk->vring, req_desc.next, &buf_desc)) {
		virtio_blk_debug("Cannot get the buffer descriptor %d.\n",
				 req_desc.next);
		return 1;
	}
	ASSERT(buf_desc.flags & VRING_DESC_F_NEXT);

#ifdef DEBUG_VIRTIO_BLK
	printf("Desc %d, addr %llx, len %08x, flags %04x, next %04x.\n",
	       req_desc.next, buf_desc.addr, buf_desc.len,
	       buf_desc.flags, buf_desc.next);
#endif

	buf = buf_desc.addr;
	if (req.type == VIRTIO_BLK_T_IN || req.type == VIRTIO_BLK_T_OUT)
		ASSERT(buf_desc.len >= ATA_SECTOR_SIZE);
	nsectors = buf_desc.len / ATA_SECTOR_SIZE;
#ifdef DEBUG_VIRTIO_BLK
	printf("  buf addr %llx, len %d, %d sectors.\n",
	       buf_desc.addr, buf_desc.len, nsectors);
#endif

	/* the address of the guest status is in the 3rd descriptor */
	if (vring_get_desc(&blk->vring, buf_desc.next, &status_desc)) {
		virtio_blk_debug("Cannot get the status descriptor %d.\n",
				 buf_desc.next);
		return 1;
	}
	status = status_desc.addr;
#ifdef DEBUG_VIRTIO_BLK
	printf("Desc %d, addr %llx, len %08x, flags %04x, next %04x.\n",
	       buf_desc.next, status_desc.addr, status_desc.len,
	       status_desc.flags, status_desc.next);
	printf("  status addr %llx.\n", status_desc.addr);
	printf("================\n");
#endif

	/* handle the request */
	switch (req.type) {
	case VIRTIO_BLK_T_IN:
		if (virtio_blk_disk_read(dev->vdev->vm,
					 req.sector, nsectors, buf))
			virtio_blk_set_status(dev->vdev->vm,
					      status, VIRTIO_BLK_S_IOERR);
		else
			virtio_blk_set_status(dev->vdev->vm,
					      status, VIRTIO_BLK_S_OK);
		break;
	case VIRTIO_BLK_T_OUT:
		if (virtio_blk_disk_write(dev->vdev->vm,
					  req.sector, nsectors, buf))
			virtio_blk_set_status(dev->vdev->vm,
					      status, VIRTIO_BLK_S_IOERR);
		else
			virtio_blk_set_status(dev->vdev->vm,
					      status, VIRTIO_BLK_S_OK);
		break;
	case VIRTIO_BLK_T_FLUSH:
		virtio_blk_set_status(dev->vdev->vm, status, VIRTIO_BLK_S_OK);
		break;
	case VIRTIO_BLK_T_GET_ID:
		virtio_blk_get_id(dev->vdev->vm, buf, buf_desc.len);
		virtio_blk_set_status(dev->vdev->vm,
				      status, VIRTIO_BLK_S_OK);
		break;
	case VIRTIO_BLK_T_BARRIER:
		virtio_blk_set_status(dev->vdev->vm,
				      status, VIRTIO_BLK_S_OK);
		break;
	default:
		virtio_blk_debug("unsupported command %x.\n", req.type);
		virtio_blk_set_status(dev->vdev->vm,
				      status, VIRTIO_BLK_S_UNSUPP);
	}

	/* notify the guest? */
	if (vring_get_avail(&blk->vring, &avail)) {
		virtio_blk_debug("Cannot get the availabe ring.\n");
		return 1;
	}
	blk->vring.need_notify =
		(avail.flags & VRING_AVAIL_F_NO_INTERRUPT) ? FALSE : TRUE;

	/* update used ring info */
	if (vring_get_used(&blk->vring, &used))	{
		virtio_blk_debug("Cannot get the used ring.\n");
		return 1;
	}
	last_used_idx = used.idx % blk->vring.queue_size;
	if (vring_get_used_elem(&blk->vring, last_used_idx, &used_elem)) {
		virtio_blk_debug("Cannot get the used ring element %d.\n",
				 last_used_idx);
		return 1;
	}
	used_elem.id = desc_idx;
	used_elem.len =
		(req.type == VIRTIO_BLK_T_IN) ? nsectors * ATA_SECTOR_SIZE :
		(req.type == VIRTIO_BLK_T_GET_ID) ? VIRTIO_BLK_DEVICE_NAME_LEN
		: 0;
	vring_set_used_elem(&blk->vring, last_used_idx, &used_elem);
	used.idx += 1;
	vring_set_used(&blk->vring, &used);

	smp_wmb();

	return 0;
}

static struct virtio_device_ops virtio_blk_ops =
	{
		.pci_conf_read		= virtio_blk_pci_conf_read,
		.pci_conf_write		= virtio_blk_pci_conf_write,
		.update_ioport_handlers	= virtio_blk_update_ioport_handlers,
		.get_vrings_amount	= virtio_blk_vrings_amount,
		.get_vring		= virtio_blk_get_vring,
		.handle_req		= virtio_blk_handle_req,
	};

static gcc_inline void
virtio_blk_handle_ioport(struct virtio_blk *blk,
			 uint16_t port, data_sz_t width, void *data, int write)
{
	struct virtio_device *device;
	uint16_t io_end;

	device = &blk->common_header;
	io_end = device->iobase +
		sizeof(struct virtio_header) + sizeof(struct virtio_header);

	if (write)
		return;

	switch (width) {
	case SZ8:
		virtio_blk_conf_readb(blk, port, data);
		break;
	case SZ16:
		if (port < io_end - 1)
			virtio_blk_conf_readw(blk, port, data);
		break;
	case SZ32:
		if (port < io_end - 3)
			virtio_blk_conf_readl(blk, port, data);
		break;
	default:
		*(uint32_t *) data = 0xffffffff;
		break;
	}
}

static void
virtio_blk_handle_guest_in(struct virtio_blk *blk,
			   uint16_t port, data_sz_t width, void *data)
{
	ASSERT(blk != NULL);
	ASSERT(blk->common_header.iobase <= port &&
	       port < blk->common_header.iobase + blk->common_header.iosize);
	ASSERT(data != NULL);

	struct virtio_device *device;
	uint16_t iobase, blkbase;

	device = &blk->common_header;

	iobase = device->iobase;
	blkbase = iobase + sizeof(struct virtio_header);

	if (iobase <= port && port < blkbase)
		virtio_handle_guest_in(device, port, width, data);
	else if (blkbase <= port &&
		 port < blkbase + sizeof(struct virtio_blk_config))
		virtio_blk_handle_ioport(blk, port, width, data, 0);
	else if (port < iobase + device->iosize)
		virtio_handle_guest_in(device, port, width, data);
	else
		*(uint32_t *) data = 0xffffffff;
}

static int
_virtio_blk_handle_guest_in(void *dev, uint16_t port, data_sz_t width, void *data)
{
	if (dev == NULL || data == NULL)
		return -1;
	virtio_blk_handle_guest_in(dev, port, width, data);
	return 0;
}

static void
virtio_blk_handle_guest_out(struct virtio_blk *blk,
			    uint16_t port, data_sz_t width, uint32_t data)
{
	ASSERT(blk != NULL);
	ASSERT(blk->common_header.iobase <= port &&
	       port < blk->common_header.iobase + blk->common_header.iosize);

	struct virtio_device *device;
	uint16_t iobase, blkbase;

	device = &blk->common_header;

	iobase = device->iobase;
	blkbase = iobase + sizeof(struct virtio_header);

	if (iobase <= port && port < blkbase)
		virtio_handle_guest_out(device, port, width, data);
	else if (blkbase <= port &&
		 port < blkbase + sizeof(struct virtio_blk_config))
		virtio_blk_handle_ioport(blk, port, width, &data, 1);
	else if (port < iobase + device->iosize)
		virtio_handle_guest_out(device, port, width, data);
}

static int
_virtio_blk_handle_guest_out(void *dev,
			     uint16_t port, data_sz_t width, uint32_t data)
{
	if (dev == NULL)
		return -1;
	virtio_blk_handle_guest_out(dev, port, width, data);
	return 0;
}

int
virtio_blk_init(struct vdev *vdev, void *opaque1, void *opaque2)
{
	if (vdev == NULL || opaque1 == NULL || opaque2 == NULL)
		return -1;

	struct vpci_host *vpci_host = opaque1;
	struct virtio_blk *blk = opaque2;

	vpci_init(vdev, vpci_host);

	memset(blk, 0, sizeof(struct virtio_blk));

	struct virtio_device *dev = &blk->common_header;

	if (virtio_device_init(dev, &virtio_blk_ops, vpci_host, vdev)) {
		virtio_blk_debug("failed to initialize virtio device.\n");
		return 1;
	}

	dev->pci_conf.header.device = VIRTIO_PCI_DEVICE_BLK;
	dev->pci_conf.header.class = PCI_CLASS_MASS_STORAGE;
	dev->pci_conf.header.subclass = PCI_SUBCLASS_MASS_STORAGE_IDE;
	dev->pci_conf.header.header_type = PCI_HDRTYPE_DEVICE;
	dev->pci_conf.sub_id = VIRTIO_PCI_SUBDEV_BLK;
	dev->pci_conf.intr_line = 14;
	dev->pci_conf.intr_pin = PCI_INTERRUPT_PIN_A;

	blk->common_header.virtio_header.device_features =
		VIRTIO_BLK_F_SIZE_MAX |
		VIRTIO_BLK_F_SEG_MAX |
		VIRTIO_BLK_F_BLK_SIZE;
	blk->blk_header.capacity = sys_disk_capacity();
	blk->blk_header.size_max = 4096;
	blk->blk_header.seg_max = 1;
	blk->blk_header.blk_size = 512;

	blk->vring.queue_size = VIRTIO_BLK_QUEUE_SIZE;
	blk->vring.vdev = vdev;

	smp_wmb();

#ifdef ENABLE_BOOT_CF
	prep_mbr();
#endif

	return 0;
}
