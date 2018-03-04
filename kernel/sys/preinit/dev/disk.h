#ifndef _KERN_DEV_DISK_H_
#define _KERN_DEV_DISK_H_

#ifdef _KERN_

#include <preinit/lib/queue.h>
#include <preinit/lib/types.h>

struct disk_dev {
	/*
	 * Following fields should not be modified after disk_add_device().
	 */
	void		*dev;		/* the opaque device */
	size_t		capacity;	/* the capacity in sectors */

	int (*dma_read)(struct disk_dev *dev,
			uint64_t lba, uint16_t nsect, uintptr_t pa);
	int (*dma_write)(struct disk_dev *dev,
			 uint64_t lba, uint16_t nsect, uintptr_t pa);
	int (*poll_complete)(struct disk_dev *dev);

	/*
	 * Following fields are used by drivers to communicate with the disk
	 * management module.
	 */
	volatile enum {XFER_SUCC, XFER_FAIL, XFER_PROCESSING} status;

	struct {
		bool		write;
		uint64_t	lba;
		uintptr_t	buf_pa;
		uint16_t	nsect;
		int		retry;
	} last_req;

	/*
	 * Following fields should only be used within the disk mamangement
	 * module.
	 */
	SLIST_ENTRY(disk_dev) entry;	/* used by disk module */
};

enum __disk_errno {
	E_DISK_SUCC = 0,
	E_DISK_DUPDEV,
	E_DISK_NODEV,
	E_DISK_XFER,
	E_DISK_ERROR,
};

/*
 * Initialize the disk module.
 */
int disk_init(void);

/*
 * Add/Remove a disk device to/from the management of the disk madule.
 *
 * @param device the disk device
 *
 * @return 0 if successful; otherwise, return a non-zero value.
 */
int disk_add_device(struct disk_dev *device);
int disk_remove_device(struct disk_dev *device);

/*
 * Transfer data between the disk device and the physical memory. The caller
 * process will be blocked until the transfer is accomplished.
 *
 * @param dev   the disk device
 * @param lba   the start logic block address of the disk device
 * @param nsect how many sectors will be transferred
 * @param write TRUE indicates transferring from the disk device to the physical
 *              memory; FALSE indicates the inverse direction
 *
 * @return 0 if successful; otherwise, return a non-zero value.
 */
int disk_xfer(struct disk_dev *dev, uint64_t lba, uintptr_t pa, uint16_t nsect,
	      bool write);

/*
 * Get the capacity of the disk.
 *
 * @return the capacity in bytes
 */
size_t disk_capacity(struct disk_dev *dev);

struct disk_dev *disk_get_dev(int nr);

#endif /* _KERN_ */

#endif /* !_KERN_DEV_DISK_H_ */
