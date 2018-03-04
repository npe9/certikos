#include <preinit/lib/debug.h>
#include <preinit/lib/string.h>
#include <preinit/lib/types.h>

#include <preinit/dev/disk.h>

#ifdef DEBUG_DISK

#define DISK_DEBUG(fmt, ...)				\
	do {						\
		KERN_DEBUG("DISK: "fmt, ##__VA_ARGS__);	\
	} while (0)

#else

#define DISK_DEBUG(fmt, ...)			\
	do {					\
	} while (0)

#endif

static bool disk_mgmt_inited = FALSE;

static SLIST_HEAD(all_disk_dev, disk_dev) all_disk_devices;

int
disk_init(void)
{
	if (disk_mgmt_inited == TRUE)
		return 0;

	SLIST_INIT(&all_disk_devices);
	disk_mgmt_inited = TRUE;

	return 0;
}

/*
 * XXX: disk_add_device() should always be invoked by the kernel. No user
 *      behavior can invoke this function. Therefore, it's safe to use
 *      spinlock_acquire(&existing_dev->lk) without worring about the dead
 *      lock.
 */
int
disk_add_device(struct disk_dev *dev)
{
	KERN_ASSERT(disk_mgmt_inited == TRUE);
	KERN_ASSERT(dev != NULL);

	struct disk_dev *existing_dev;

	SLIST_FOREACH(existing_dev, &all_disk_devices, entry) {
		if (existing_dev == dev) {
			DISK_DEBUG("Cannot add existing devices.\n");
			return E_DISK_DUPDEV;
		}
	}

	dev->status = XFER_SUCC;
	memzero(&dev->last_req, sizeof(dev->last_req));
	SLIST_INSERT_HEAD(&all_disk_devices, dev, entry);
	DISK_DEBUG("Add a disk device 0x%08x.\n", dev);

	return E_DISK_SUCC;
}

static int
disk_xfer_helper(struct disk_dev *dev,
		 uint64_t lba, uintptr_t pa, uint16_t nsect, bool write)
{
	KERN_ASSERT(dev->status != XFER_PROCESSING);

	int rc;

	if (dev->last_req.retry > 1) {
		DISK_DEBUG("Exceed maximum retries.\n");
		return 1;
	}

	dev->last_req.write = write;
	dev->last_req.lba = lba;
	dev->last_req.buf_pa = pa;
	dev->last_req.nsect = nsect;

	rc = (write == TRUE) ? dev->dma_write(dev, lba, nsect, pa) :
		dev->dma_read(dev, lba, nsect, pa);
	if (rc)
		return 1;

	/* sleep to wait for the completion of the transfer */
	dev->status = XFER_PROCESSING;

	return 0;
}

static void
disk_poll_complete(struct disk_dev *dev)
{
	KERN_ASSERT(disk_mgmt_inited == TRUE);
	KERN_ASSERT(dev->poll_complete);

	dev->poll_complete(dev);

	if (dev->status == XFER_FAIL) {
		DISK_DEBUG("Retry request (%s, lba 0x%llx, "
			   "nsect %d, buf 0x%08x) ... \n",
			   dev->last_req.write == TRUE ? "write" : "read",
			   dev->last_req.lba,
			   dev->last_req.nsect,
			   dev->last_req.buf_pa);
		dev->last_req.retry++;
		if (disk_xfer_helper(dev, dev->last_req.lba,
				     dev->last_req.buf_pa,
				     dev->last_req.nsect,
				     dev->last_req.write))
			dev->status = XFER_FAIL;
		else
			dev->poll_complete(dev);
	}
}

int
disk_xfer(struct disk_dev *dev, uint64_t lba, uintptr_t pa, uint16_t nsect,
	  bool write)
{
	KERN_ASSERT(disk_mgmt_inited == TRUE);
	KERN_ASSERT(dev != NULL);
	KERN_ASSERT((write == TRUE && dev->dma_write != NULL) ||
		    (write == FALSE && dev->dma_read != NULL));

	int rc;

	if ((rc = disk_xfer_helper(dev, lba, pa, nsect, write))) {
		DISK_DEBUG("disk_xfer() error %d.\n", rc);
		dev->status = XFER_FAIL;
		memzero(&dev->last_req, sizeof(dev->last_req));
		return E_DISK_XFER;
	}

	disk_poll_complete(dev);

	KERN_ASSERT(dev->status != XFER_PROCESSING);

	memzero(&dev->last_req, sizeof(dev->last_req));

	/* transfer is accomplished */
	if (dev->status == XFER_SUCC)
		return E_DISK_SUCC;
	else
		return E_DISK_XFER;
}

size_t
disk_capacity(struct disk_dev *dev)
{
	KERN_ASSERT(disk_mgmt_inited == TRUE);
	KERN_ASSERT(dev != NULL);
	return dev->capacity;
}

struct disk_dev *
disk_get_dev(int nr)
{
	int i = 0;
	struct disk_dev *dev = NULL;

	if (nr < 0)
		return NULL;

	SLIST_FOREACH(dev, &all_disk_devices, entry) {
		if (i == nr)
			return dev;
		i++;
	}

	return NULL;
}
