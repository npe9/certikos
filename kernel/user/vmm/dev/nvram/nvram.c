#include <debug.h>
#include <string.h>
#include <syscall.h>
#include <types.h>
#include <x86.h>

#include "bios.h"
#include "nvram.h"
#include "../../vmm_dev.h"

#define CMOS_INDEX_PORT		0x70
#define CMOS_DATA_PORT		0x71

/* memory size in KB from 1 MB ~ 16 MB */
#define CMOS_EXTMEM_LOW		0x30	/* Bits 7 ~ 0 */
#define CMOS_EXTMEM_HIGH	0x31	/* Bits 15 ~ 8 */
/* memory size in byte from 16 MB ~ 4 GB */
#define CMOS_EXTMEM2_LOW	0x34	/* Bits 23 ~ 16 */
#define CMOS_EXTMEM2_HIGH	0x35	/* Bits 31 ~ 24 */
/* memory size in byte above 4GB */
#define CMOS_HIGHMEM_LOW	0x5b	/* Bits 23 ~ 16 */
#define CMOS_HIGHMEM_MID	0x5c	/* Bits 31 ~ 24 */
#define CMOS_HIGHMEM_HIGH	0x5d	/* Bits 39 ~ 32 */

#define CMOS_NMI_DISABLE_BIT	(1 << 7)

#ifdef DEBUG_VNVRAM

#define VNVRAM_DEBUG(fmt, ...)			\
	do {					\
		DEBUG(fmt, ##__VA_ARGS__);	\
	} while (0)

#else

#define VNVRAM_DEBUG(fmt...)			\
	do {					\
	} while (0)

#endif

static uint8_t
vnvram_ioport_read(struct vnvram *nvram, uint16_t port)
{
	ASSERT(nvram != NULL);
	ASSERT(port == CMOS_INDEX_PORT || port == CMOS_DATA_PORT);

	if (port == CMOS_INDEX_PORT)
		return inb(port);

	if (nvram->data_valid == TRUE)
		return nvram->data;
	else
		return inb(port);
}

static void
vnvram_ioport_write(struct vnvram *nvram, uint16_t port, uint8_t data)
{
	ASSERT(nvram != NULL);
	ASSERT(port == CMOS_INDEX_PORT || port == CMOS_DATA_PORT);

	if (port == CMOS_DATA_PORT) {
		VNVRAM_DEBUG("Write host I/O port 0x%x.\n", port);
		outb(port, data);
		return;
	}

	uint8_t idx = data & ~(uint8_t) CMOS_NMI_DISABLE_BIT;

	switch (idx) {
	case CMOS_EXTMEM_LOW:
		nvram->data = (nvram->extmem_size >> 10) & 0xFF;
		VNVRAM_DEBUG("Read ExtMem.LOW: %d.\n", nvram->data);
		break;

	case CMOS_EXTMEM_HIGH:
		nvram->data = (nvram->extmem_size >> 18) & 0xFF;
		VNVRAM_DEBUG("Read ExtMem.HIGH: %d.\n", nvram->data);
		break;

	case CMOS_EXTMEM2_LOW:
		nvram->data = (nvram->extmem2_size >> 16) & 0xFF;
		VNVRAM_DEBUG("Read ExtMem2.LOW: %d.\n", nvram->data);
		break;

	case CMOS_EXTMEM2_HIGH:
		nvram->data = (nvram->extmem2_size >> 24) & 0xFF;
		VNVRAM_DEBUG("Read ExtMem2.HIGH: %d.\n", nvram->data);
		break;

	case CMOS_HIGHMEM_LOW:
		nvram->data = (nvram->highmem_size >> 16) & 0xFF;
		VNVRAM_DEBUG("Read HighMem.LOW: %d.\n", nvram->data);
		break;

	case CMOS_HIGHMEM_MID:
		nvram->data = (nvram->highmem_size >> 24) & 0xFF;
		VNVRAM_DEBUG("Read HighMem.MID: %d.\n", nvram->data);
		break;

	case CMOS_HIGHMEM_HIGH:
		nvram->data = (nvram->highmem_size >> 32) & 0xFF;
		VNVRAM_DEBUG("Read HighMem.HIGH: %d.\n", nvram->data);
		break;

	default:
		VNVRAM_DEBUG("Passthrough index 0x%x.\n", idx);
		nvram->data_valid = FALSE;
		outb(port, data);
		return;
	}

	nvram->data_valid = TRUE;
}

static int
_vnvram_ioport_read(void *opaque, uint16_t port, data_sz_t width, void *data)
{
	struct vnvram *nvram = (struct vnvram *) opaque;

	if (nvram == NULL || data == NULL)
		return 1;

	if(port != CMOS_INDEX_PORT && port != CMOS_DATA_PORT)
		return 2;

	*(uint8_t *) data = vnvram_ioport_read(nvram, port);

	VNVRAM_DEBUG("Read I/O port 0x%x, val 0x%x.\n", port, *(uint8_t *) data);
	return 0;
}

static int
_vnvram_ioport_write(void *opaque, uint16_t port, data_sz_t width, uint32_t data)
{
	struct vnvram *nvram = (struct vnvram *) opaque;

	if(nvram == NULL)
		return 1;

	if (port != CMOS_INDEX_PORT && port != CMOS_DATA_PORT)
		return 2;

	VNVRAM_DEBUG("Write I/O port 0x%x, val 0x%08x.\n", port, (uint8_t) data);

	vnvram_ioport_write(nvram, port, (uint8_t) data);
	return 0;
}

int
vnvram_init(struct vdev *vdev, void *opaque, size_t memsize)
{
	if (vdev == NULL || opaque == NULL)
		return -1;

	struct vnvram *vnvram = (struct vnvram *) opaque;
	uint64_t phy_mem_size = memsize;

	memset(vnvram, 0, sizeof(struct vnvram));

	vnvram->data_valid = FALSE;

	if (phy_mem_size > 0x100000000ULL) { /* above 4 GB */
		vnvram->highmem_size = phy_mem_size - 0x100000000ULL;
		phy_mem_size -= vnvram->highmem_size;
	}
	if (phy_mem_size > 0x1000000) { /* 16 MB ~ 4G */
		vnvram->extmem2_size = phy_mem_size - 0x1000000;
		phy_mem_size -= vnvram->extmem2_size;
	}
	if (phy_mem_size > 0x100000) { /* 1 MB ~ 16 MB */
		vnvram->extmem_size = phy_mem_size - 0x100000;
		phy_mem_size -= vnvram->extmem_size;
	}

	VNVRAM_DEBUG("ExtMem %d bytes, ExtMem2 %d bytes, HighMem %lld bytes.\n",
		     vnvram->extmem_size, vnvram->extmem2_size,
		     vnvram->highmem_size);

	if (vdev_register_ioport(vdev, opaque, CMOS_DATA_PORT,
				 _vnvram_ioport_read, _vnvram_ioport_write) ||
	    vdev_register_ioport(vdev, opaque, CMOS_INDEX_PORT,
				 _vnvram_ioport_read, _vnvram_ioport_write))
		return -2;

	return 0;
}
