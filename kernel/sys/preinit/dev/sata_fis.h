#ifndef _KERN_DEV_SATA_FIS_
#define _KERN_DEV_SATA_FIS_

#ifdef _KERN_

#include <preinit/lib/debug.h>
#include <preinit/lib/gcc.h>
#include <preinit/lib/types.h>

#define SATA_FIS_TYPE_REG_H2D	0x27
#define SATA_FIS_TYPE_REG_D2H	0x34
#define SATA_FIS_TYPE_SET_BITS	0xa1

/* for H2D and D2H */
struct sata_fis_reg {
	/* DWORD 0 */
	uint8_t type;
	uint8_t flag;
	union {
		uint8_t command;	/* H2D */
		uint8_t status;		/* D2H */
	};
	union {
		uint8_t featurel;	/* H2D */
		uint8_t error;		/* D2H */
	};

	/* DWORD 1 */
	uint8_t lba0;
	uint8_t lba1;
	uint8_t lba2;
	uint8_t dev;

	/* DWORD 2 */
	uint8_t lba3;
	uint8_t lba4;
	uint8_t lba5;
	uint8_t featureh;

	/* DWORD 3 */
	uint8_t countl;
	uint8_t counth;
	uint8_t rsv0;
	uint8_t control;

	/* DWORD 4 */
	uint8_t rsv1[4];
};

/* for set bits */
struct sata_fis_setbits {
	/* DWORD 0 */
	uint8_t type;
	uint8_t flag;
	uint8_t status;
	uint8_t error;

	/* DWORD 1 */
	uint8_t rsv[4];
};

static gcc_inline void
sata_fis_reg_debug(struct sata_fis_reg *fis)
{
	if (fis == NULL)
		return;

	KERN_DEBUG("SATA_FIS_REG: addr %08x, size %d\n",
		   fis, sizeof(struct sata_fis_reg));
	dprintf("\ttype: %02x\n", fis->type);
	dprintf("\tflag: %02x\n", fis->flag);
	dprintf("\tcmd : %02x\n", fis->command);
	dprintf("\tfeat: %02x%02x\n", fis->featureh, fis->featurel);
	dprintf("\tlba : %02x%02x%02x%02x%02x%02x\n",
		fis->lba5, fis->lba4, fis->lba3,
		fis->lba2, fis->lba1, fis->lba0);
	dprintf("\tcnt : %02x%02x\n", fis->counth, fis->countl);
	dprintf("\tdev : %02x\n", fis->dev);
	dprintf("\tctrl: %02x\n", fis->control);
}

#endif /* _KERN_ */

#endif /* !_KERN_DEV_SATA_FIS_ */
