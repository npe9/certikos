#ifndef _VDEV_NVRAM_H_
#define _VDEV_NVRAM_H_

/*
 * XXX: Virtualized NVRAM does NOT intend to provide the full simulation of
 *      NVRAM. It does only handle the requests of getting memory size. All
 *      other requests are passed to the physical NVRAM.
 *
 *      The functions handled by virtualized NVRAM include:
 *      - getting physical memory size between 1 MB ~ 16 MB,
 *      - getting physical memory size between 16 MB ~ 4 GB, and
 *      - getting physical memory size above 4 GB.
 */

#include <types.h>
#include "../../vmm_dev.h"

struct vnvram {
	bool		data_valid;
	size_t		extmem_size;
	size_t		extmem2_size;
	uint64_t	highmem_size;

	uint8_t		data;
};

int vnvram_init(struct vdev *vdev, void *opaque, size_t memsize);

#endif /* !_VDEV_NVRAM_H_ */
