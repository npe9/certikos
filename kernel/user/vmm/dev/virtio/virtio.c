#include <debug.h>
#include <gcc.h>
#include <string.h>
#include <syscall.h>
#include <types.h>
#include <x86.h>

#include "pci.h"
#include "virtio.h"
#include "../../vmm.h"

#ifdef DEBUG_VIRTIO

#define virtio_debug(fmt, ...)				\
	do {						\
		DEBUG("VIO: "fmt, ##__VA_ARGS__);	\
	} while (0)

#else

#define virtio_debug(fmt...)			\
	do {					\
	} while (0)

#endif

static void
vring_init(struct vring *vring, uintptr_t guest_addr)
{
	ASSERT(vring != NULL);

	vring->desc_guest_addr = guest_addr;
	vring->avail_guest_addr =
		guest_addr + sizeof(struct vring_desc) * vring->queue_size;
	vring->used_guest_addr = ROUNDUP
		(vring->avail_guest_addr + sizeof(struct vring_avail) +
		 sizeof(uint16_t) * vring->queue_size, 4096);

	vring->last_avail_idx = 0;
	vring->need_notify = FALSE;

	smp_wmb();

	virtio_debug("vring_init: desc %08x, avail %08x, used %08x.\n",
		     vring->desc_guest_addr,
		     vring->avail_guest_addr,
		     vring->used_guest_addr);
}

/*
 * Helper functions for manipulating virtqueues/vrings.
 */

gcc_inline int
vring_get_desc(struct vring *vring, uint16_t idx, struct vring_desc *desc)
{
	ASSERT(vring != NULL);
	ASSERT(idx < vring->queue_size);
	ASSERT(desc != NULL);

	return vmm_read_guest_memory(vring->vdev->vm, vring->desc_guest_addr +
				     sizeof(struct vring_desc) * idx,
				     (uintptr_t) desc,
				     sizeof(struct vring_desc));
}

gcc_inline int
vring_get_avail(struct vring *vring, struct vring_avail *avail)
{
	ASSERT(vring != NULL);
	ASSERT(avail != NULL);

	return vmm_read_guest_memory(vring->vdev->vm, vring->avail_guest_addr,
				     (uintptr_t) avail,
				     sizeof(struct vring_avail));
}

gcc_inline int
vring_get_avail_ring(struct vring *vring, int idx, uint16_t *ring)
{
	ASSERT(vring != NULL);
	ASSERT(ring != NULL);

	return vmm_read_guest_memory(vring->vdev->vm, vring->avail_guest_addr +
				     offsetof(struct vring_avail, ring) +
				     sizeof(uint16_t) * idx, (uintptr_t) ring,
				     sizeof(uint16_t));
}

gcc_inline int
vring_get_used(struct vring *vring, struct vring_used *used)
{
	ASSERT(vring != NULL);
	ASSERT(used != NULL);

	return vmm_read_guest_memory(vring->vdev->vm, vring->used_guest_addr,
				     (uintptr_t) used, sizeof(struct vring_used));
}

gcc_inline int
vring_get_used_elem(struct vring *vring, int idx, struct vring_used_elem *elem)
{
	ASSERT(vring != NULL);
	ASSERT(elem != NULL);

	uintptr_t addr = vring->used_guest_addr +
		offsetof(struct vring_used, ring) +
		sizeof(struct vring_used_elem) * idx;

	return vmm_read_guest_memory(vring->vdev->vm, addr, (uintptr_t) elem,
				     sizeof(struct vring_used_elem));
}

gcc_inline int
vring_set_used(struct vring *vring, struct vring_used *used)
{
	ASSERT(vring != NULL);
	ASSERT(used != NULL);

	return vmm_write_guest_memory(vring->vdev->vm, vring->used_guest_addr,
				      (uintptr_t) used, sizeof(struct vring_used));
}

gcc_inline int
vring_set_used_elem(struct vring *vring, int idx, struct vring_used_elem *elem)
{
	ASSERT(vring != NULL);
	ASSERT(elem != NULL);

	uintptr_t addr = vring->used_guest_addr +
		offsetof(struct vring_used, ring) +
		sizeof(struct vring_used_elem) * idx;
	return vmm_write_guest_memory(vring->vdev->vm, addr, (uintptr_t) elem,
				      sizeof(struct vring_used_elem));
}

/*
 * Helper functions for handling requests in virtqueues/vrings.
 */

static int
vring_dequeue_req(struct vring *vring)
{
	ASSERT(vring != NULL);

	struct vring_avail avail;
	uint16_t idx, ring;

	if (vring_get_avail(vring, &avail))
		return -1;

	if (vring->last_avail_idx == avail.idx) {
		virtio_debug("queue is empty.\n");
		return -1;
	}

	idx = vring->last_avail_idx;
	vring->last_avail_idx++;

	smp_wmb();

	if (vring_get_avail_ring(vring, idx % vring->queue_size, &ring))
		return -1;

	virtio_debug("avail.ring[%d]=%d, flags %04x, avail %d, last avail %d.\n",
		     idx % vring->queue_size, ring, avail.flags, avail.idx, idx);

	return ring;
}

static void
virtio_notify_guest(struct virtio_device *dev)
{
	ASSERT(dev != NULL);

	virtio_debug("notify: raise IRQ 0x%x.\n", dev->pci_conf.intr_line);

	/* set interrupt bits */
	dev->pci_conf.header.status |= (1 << 3);
	dev->virtio_header.isr_status |= 1;

	smp_wmb();

	/* edge-triggered interrupt */
	vdev_set_irq(dev->vdev, dev->pci_conf.intr_line, 2);
}

static int
virtio_handle_req(struct virtio_device *dev, int vq_idx)
{
	ASSERT(dev != NULL);

	struct vring *vring;
	uint16_t desc_idx;
	int rc;

	vring = dev->ops->get_vring(dev, vq_idx);

	if (vring == NULL) {
		virtio_debug("queue %d is not usable.\n", vq_idx);
		return 1;
	}

	if ((rc = vring_dequeue_req(vring)) == -1) {
		virtio_debug("no request in queue %d.\n", vq_idx);
		return 1;
	}

	desc_idx = (uint16_t) rc;

	rc = dev->ops->handle_req(dev, vq_idx, desc_idx);

	smp_rmb();

	if (vring->need_notify == TRUE)
		virtio_notify_guest(dev);

	return rc;
}

/*
 * Helper functions for reading/writing virtio device I/O spaces.
 */

static void
virtio_get_dev_features(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, device_features));

	*(uint32_t *) data = dev->virtio_header.device_features;

	virtio_debug("read device features %08x.\n", *(uint32_t *) data);
}

static void
virtio_get_guest_features(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, guest_features));

	*(uint32_t *) data = dev->virtio_header.guest_features;

	virtio_debug("read guest features %08x.\n", *(uint32_t *) data);
}

static void
virtio_set_guest_features(struct virtio_device *dev, uint16_t reg, void *data)
{
	ASSERT(dev != NULL && data != NULL);

	virtio_debug("write guest features %08x.\n", *(uint32_t *) data);

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, guest_features));

	dev->virtio_header.guest_features = *(uint32_t *) data;

	smp_wmb();
}

static void
virtio_get_queue_addr(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, queue_addr));

	*(uint32_t *) data = dev->virtio_header.queue_addr;

	virtio_debug("read queue address %08x.\n", *(uint32_t *) data * 4096);
}

static void
virtio_set_queue_addr(struct virtio_device *dev, uint16_t reg, void *data)
{
	ASSERT(dev != NULL && data != NULL);

	virtio_debug("write queue address %08x.\n", *(uint32_t *) data * 4096);

	struct vring *ring;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, queue_addr));

	ring = dev->ops->get_vring(dev, dev->virtio_header.queue_select);

	if (ring == NULL) {
		virtio_debug("queue %d is not usable.\n",
			     dev->virtio_header.queue_select);
		return;
	}

	vring_init(ring, *(uint32_t *) data * 4096);

	smp_wmb();
}

static void
virtio_get_queue_size(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, queue_size));

	*(uint16_t *) data = dev->virtio_header.queue_size;

	virtio_debug("read queue size %d.\n", *(uint16_t *) data);
}

static void
virtio_get_queue_select(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, queue_select));

	*(uint16_t *) data = dev->virtio_header.queue_select;

	virtio_debug("read queue selected %d.\n", *(uint16_t *) data);
}

static void
virtio_set_queue_select(struct virtio_device *dev, uint32_t reg, void *data)
{
	ASSERT(dev != NULL && data != NULL);

	virtio_debug("select queue %d.\n", *(uint16_t *) data);

	struct vring *ring;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, queue_select));

	ring = dev->ops->get_vring(dev, *(uint16_t *) data);

	if (ring == NULL) {
		virtio_debug("queue %d is not usable.\n", *(uint16_t *) data);
		dev->virtio_header.queue_addr = 0;
		dev->virtio_header.queue_size = 0;
		goto ret;
	}

	dev->virtio_header.queue_addr = ring->desc_guest_addr / 4096;
	dev->virtio_header.queue_size = ring->queue_size;

 ret:
	smp_wmb();
}

static void
virtio_get_queue_notify(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, queue_notify));

	*(uint16_t *) data = dev->virtio_header.queue_notify;

	virtio_debug("read queue notify %d.\n", *(uint16_t *) data);
}

static void
virtio_set_queue_notify(struct virtio_device *dev, uint32_t reg, void *data)
{
	ASSERT(dev != NULL && data != NULL);

	virtio_debug("notify queue %d.\n", *(uint16_t *) data);

	struct vring *vring;
	struct vring_avail avail;
	uint8_t queue_idx;
	int rc;

	queue_idx = *(uint16_t *) data;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, queue_notify));

	dev->virtio_header.queue_notify = queue_idx;

	smp_wmb();

	if ((vring = dev->ops->get_vring(dev, queue_idx)) == NULL)
		return;

	if ((rc = vring_get_avail(vring, &avail))) {
		WARN("Cannot get the available ring. (errno %d)\n", rc);
		return;
	}

	do {
		virtio_handle_req(dev, queue_idx);
	} while (vring->last_avail_idx != avail.idx);
}

static void
virtio_get_device_status(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, device_status));

	*(uint8_t *) data = dev->virtio_header.device_status;

	virtio_debug("read device status %01x.\n", *(uint8_t *) data);
}

static void
virtio_set_device_status(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	virtio_debug("write device status %01x.\n", *(uint8_t *) data);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, device_status));

	dev->virtio_header.device_status = *(uint8_t *) data;
}

static void
virtio_get_isr_status(void *opaque, uint32_t reg, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	struct virtio_device *dev = (struct virtio_device *) opaque;

	ASSERT(reg == dev->iobase +
	       offsetof(struct virtio_header, isr_status));

	*(uint8_t *) data = dev->virtio_header.isr_status;

	virtio_debug("read ISR status %01x.\n", *(uint8_t *) data);
}

static void
virtio_default_ioport_readb(void *opaque, uint32_t port, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	*(uint8_t *) data = 0;

	virtio_debug("readb reg %x, nop.\n",
		     port - ((struct virtio_device *) opaque)->iobase);
}

static void
virtio_default_ioport_readw(void *opaque, uint32_t port, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	*(uint16_t *) data = 0;

	virtio_debug("readw reg %x, nop.\n",
		     port - ((struct virtio_device *) opaque)->iobase);
}

static void
virtio_default_ioport_readl(void *opaque, uint32_t port, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	*(uint32_t *) data = 0;

	virtio_debug("readl reg %x, nop.\n",
		     port - ((struct virtio_device *) opaque)->iobase);
}

static void
virtio_default_ioport_writeb(void *opaque, uint32_t port, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	virtio_debug("writeb reg %x, val %02x, nop.\n",
		     port - ((struct virtio_device *) opaque)->iobase,
		     *(uint8_t *) data);
}

static void
virtio_default_ioport_writew(void *opaque, uint32_t port, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	virtio_debug("writew reg %x, val %04x, nop.\n",
		     port - ((struct virtio_device *) opaque)->iobase,
		     *(uint16_t *) data);
}

static void
virtio_default_ioport_writel(void *opaque, uint32_t port, void *data)
{
	ASSERT(opaque != NULL && data != NULL);

	virtio_debug("writel reg %x, val %08x, nop.\n",
		     port - ((struct virtio_device *) opaque)->iobase,
		     *(uint32_t *) data);
}

/* Helper functions to unregister and register I/O port handlers. */

static void
unregister_ioport_handlers(struct vdev *vdev, void *dev,
			   uint16_t iobase, uint16_t iosize)
{
	uint32_t port;

	for (port = iobase; port < iobase + iosize; port++)
		vdev_unregister_ioport(vdev, dev, port);
}

/*
 * Initialize a virtio device. The devcie-specific initialization is called at
 * the end.
 *
 * @param dev the virtio device to be initialized
 * @param ops the device-specific operations
 *
 * @return 0 if no errors happen
 */
int
virtio_device_init(struct virtio_device *dev, struct virtio_device_ops *ops,
		   struct vpci_host *vpci_host, struct vdev *vdev)
{
	ASSERT(dev != NULL && ops != NULL && vpci_host != NULL && vdev != NULL);

	int rc;

	memset(dev, 0, sizeof(struct virtio_device));

	/* device-independent PCI initialization */
	dev->pci_conf.header.vendor = VIRTIO_PCI_VENDOR_ID;
	dev->pci_conf.header.revision = VIRTIO_PCI_REVISION;
	dev->pci_conf.sub_vendor = VIRTIO_PCI_VENDOR_ID;

	/* attach the virtio device to the virtual PCI host */
	dev->pci_dev.dev = dev;
	dev->pci_dev.conf_read = ops->pci_conf_read;
	dev->pci_dev.conf_write = ops->pci_conf_write;
	if ((rc = vpci_attach_device(vpci_host, &dev->pci_dev)) != 0) {
		virtio_debug("failed to attach the device to PCI bus.\n");
		return 1;
	}

	/* invalid I/O ports base address */
	dev->iobase = 0xffff;
	dev->iosize = 0;

	dev->ops = ops;
	dev->vdev = vdev;

	return 0;
}

void
virtio_handle_guest_in(struct virtio_device *dev,
		       uint16_t port, data_sz_t width, void *data)
{
	ASSERT(dev != NULL);
	ASSERT(dev->iobase <= port && port < dev->iobase + dev->iosize);
	ASSERT(data != NULL);

	uint16_t iobase = dev->iobase;

	if (port == iobase +
	    offsetof(struct virtio_header, device_features) &&
	    width == SZ32) {
		virtio_get_dev_features(dev, port, data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, guest_features) &&
		   width == SZ32) {
		virtio_get_guest_features(dev, port, data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, queue_addr) &&
		   width == SZ32) {
		virtio_get_queue_addr(dev, port, data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, queue_size) &&
		   width == SZ16) {
		virtio_get_queue_size(dev, port, data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, queue_select) &&
		   width == SZ16) {
		virtio_get_queue_select(dev, port, data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, queue_notify) &&
		   width == SZ16) {
		virtio_get_queue_notify(dev, port, data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, device_status) &&
		   width == SZ8) {
		virtio_get_device_status(dev, port, data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, isr_status) &&
		   width == SZ8) {
		virtio_get_isr_status(dev, port, data);
	} else if (port < iobase + dev->iosize) {
		uint16_t delta = iobase + dev->iosize - port;
		if (width == SZ8)
			virtio_default_ioport_readb(dev, port, data);
		else if (width == SZ16 && delta > 1)
			virtio_default_ioport_readw(dev, port, data);
		else if (width == SZ32 && delta > 3)
			virtio_default_ioport_readl(dev, port, data);
		else
			*(uint32_t *) data = 0xffffffff;
	}
}

static int
_virtio_handle_guest_in(void *dev, uint16_t port, data_sz_t width, void *data)
{
	if (dev == NULL || data == NULL)
		return -1;
	virtio_handle_guest_in(dev, port, width, data);
	return 0;
}

void
virtio_handle_guest_out(struct virtio_device *dev,
			uint16_t port, data_sz_t width, uint32_t data)
{
	ASSERT(dev != NULL);
	ASSERT(dev->iobase <= port && port < dev->iobase + dev->iosize);

	uint16_t iobase = dev->iobase;

	if (port == iobase +
	    offsetof(struct virtio_header, guest_features) &&
	    width == SZ32) {
		virtio_set_guest_features(dev, port, &data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, queue_addr) &&
		   width == SZ32) {
		virtio_set_queue_addr(dev, port, &data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, queue_select) &&
		   width == SZ16) {
		virtio_set_queue_select(dev, port, &data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, queue_notify) &&
		   width == SZ16) {
		virtio_set_queue_notify(dev, port, &data);
	} else if (port == iobase +
		   offsetof(struct virtio_header, device_status) &&
		   width == SZ8) {
		virtio_set_device_status(dev, port, &data);
	} else if (port < iobase + dev->iosize) {
		uint16_t delta = iobase + dev->iosize - port;
		if (width == SZ8)
			virtio_default_ioport_writeb(dev, port, &data);
		else if (width == SZ16 && delta > 1)
			virtio_default_ioport_writew(dev, port, &data);
		else if (width == SZ32 && delta > 3)
			virtio_default_ioport_writel(dev, port, &data);
	}
}

static int
_virtio_handle_guest_out(void *dev, uint16_t port, data_sz_t width, uint32_t data)
{
	if (dev == NULL)
		return -1;
	virtio_handle_guest_out(dev, port, width, data);
	return 0;
}

/*
 * Register the I/O port handlers for the virtio device. It should be called
 * whenever the BAR0 of the virtio device is changed. The device-specific
 * registration is called at the end.
 *
 * @param dev the virtio device
 * @param iobase the new base address of I/O ports
 */
void
virtio_device_update_ioport_handlers(struct virtio_device *dev,
				     uint16_t new_iobase)
{
	ASSERT(dev != NULL);

	uint16_t iobase, iosize, port;

	iobase = dev->iobase;
	iosize = dev->iosize;

	ASSERT(iobase == 0xffff || 0xffff - iobase + 1 >= iosize);

	if (iobase != 0xffff) {
		virtio_debug("unregister handlers for I/O ports %x ~ %x.\n",
			     iobase, iobase + iosize - 1);
		unregister_ioport_handlers(dev->vdev, dev, iobase, iosize);
	}

	iobase = dev->iobase = new_iobase;

	virtio_debug("register handlers for I/O ports %x ~ %x.\n",
		     iobase, iobase + iosize - 1);

	for (port = iobase; port < iobase + iosize; port++) {
		if (port < iobase + sizeof(struct virtio_header)) {
			vdev_unregister_ioport(dev->vdev, dev, port);
			vdev_register_ioport(dev->vdev, dev, port,
					     _virtio_handle_guest_in,
					     _virtio_handle_guest_out);
		} else {
			dev->ops->update_ioport_handlers(dev);
		}
	}
}
