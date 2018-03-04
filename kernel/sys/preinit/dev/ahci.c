#include <preinit/lib/debug.h>
#include <preinit/lib/gcc.h>
#include <preinit/lib/string.h>
#include <preinit/lib/types.h>
#include <preinit/lib/x86.h>

#include <preinit/dev/ahci.h>
#include <preinit/dev/disk.h>
#include <preinit/dev/pci.h>
#include <preinit/dev/sata_fis.h>
#include <preinit/dev/tsc.h>

#ifdef DEBUG_AHCI

#define AHCI_DEBUG(fmt, ...)				\
	do {						\
		KERN_DEBUG("AHCI: "fmt, ##__VA_ARGS__);	\
	} while (0)

#else

#define AHCI_DEBUG(fmt, ...)			\
	do {					\
	} while (0)

#endif

struct ahci_hba {
	struct pci_func	pci_func;
	uintptr_t	ghc;
	uint32_t	cap;
	uint32_t	x_cap;
	uint32_t	revision;
	uint8_t		nports;
	uint8_t		ncmds;
};

struct ahci_port {
	bool		present;

	bool		atapi;
	bool		lba48;
	uint64_t	nsects;

	struct ahci_cmd_header	*cl;
	struct ahci_r_fis	*rfis;

	volatile enum {PORT_UNINITED, PORT_READY, PORT_XFERRING} status;

	uint32_t	error;
	uint32_t	sig;
};

static bool ahci_inited = FALSE;
static struct ahci_hba hba;
static struct ahci_port ports[AHCI_MAX_PORTS];
static struct disk_dev devices[AHCI_MAX_PORTS];

#define PAGESIZE	4096

/*
 * Preallocate memory space for the command list and rfis of each AHCI port.
 * The size for each port is ROUNDUP(AHCI_CMDH_SIZE+AHCI_RFIS_SIZE, PAGESIZE).
 */
static uint8_t port_cl_rfis[AHCI_MAX_PORTS][PAGESIZE] gcc_aligned(PAGESIZE);
/*
 * Preallocate memory space for the command tables of each AHCI port.
 * The size for each port is ROUNDUP(AHCI_CMDTBL_SIZE*AHCI_MAX_CMDS, PAGESIZE).
 */
static uint8_t port_cmds[AHCI_MAX_PORTS][PAGESIZE*2] gcc_aligned(PAGESIZE);

static int ahci_reset(void);
static int ahci_init(uint8_t irq);
static int ahci_init_port(int port, uint8_t irq);
static int ahci_idle_port(int port);
static int ahci_alloc_port(int port);
static int ahci_spinup_port(int port);
static void ahci_identify_drive(int port);
static void ahci_issue_command(int port, int write, void *buffer, size_t size);
static int ahci_wait_command(int port);
static void ahci_error_recovery(int port);
static int ahci_sata_xfer(int port,
			  uint64_t lba, uint16_t n, uintptr_t pa, int write);
static int ahci_sata_xfer_read(struct disk_dev *dev,
			       uint64_t lba, uint16_t nsects, uintptr_t pa);
static int ahci_sata_xfer_write(struct disk_dev *dev,
				uint64_t lba, uint16_t nsects, uintptr_t pa);
static int ahci_poll_complete(struct disk_dev *dev);
static int ahci_port_poll_complete(int port);

/* wait for n ms until cond is satisfied */
#define wait_until(n, cond)					\
	do {							\
		uint64_t time;					\
		for (time = 0; time < (n) && !(cond); time++) 	\
			udelay(100);				\
	} while (0)

static gcc_inline uint8_t
ahci_readb(uintptr_t offset)
{
	uint8_t val = *(volatile uint8_t *) (hba.ghc + offset);
	return (uint8_t) val;
}

static gcc_inline uint16_t
ahci_readw(uintptr_t offset)
{
	uint16_t val = *(volatile uint16_t *) (hba.ghc + offset);
	return (uint16_t) val;
}

static gcc_inline uint32_t
ahci_readl(uintptr_t offset)
{
	uint32_t val = *(volatile uint32_t *) (hba.ghc + offset);
	return (uint32_t) val;
}

static gcc_inline void
ahci_writeb(uintptr_t offset, uint8_t val)
{
	uintptr_t addr = hba.ghc + offset;
	*(volatile uint8_t *) addr = val;
}

static gcc_inline void
ahci_writew(uintptr_t offset, uint16_t val)
{
	uintptr_t addr = hba.ghc + offset;
	*(volatile uint16_t *) addr = val;
}

static gcc_inline void
ahci_writel(uintptr_t offset, uint32_t val)
{
	uintptr_t addr = hba.ghc + offset;
	*(volatile uint32_t *) addr = val;
}

/* reset AHCI HBA (AHCI Spec sec 10.4.3) */
static int
ahci_reset(void)
{
	uint32_t ghc;

	ghc = ahci_readl(AHCI_GHC);
	ahci_writel(AHCI_GHC, ghc | AHCI_GHC_AE);

	/* reset HBA */
	ahci_writel(AHCI_GHC, ghc | AHCI_GHC_AE | AHCI_GHC_HR);
	wait_until(1000, (ahci_readl(AHCI_GHC) & AHCI_GHC_HR) == 0);

	/* timeout */
	if (ahci_readl(AHCI_GHC) & AHCI_GHC_HR) {
		AHCI_DEBUG("Cannot reset AHCI HBA.\n");
		return 1;
	}

	AHCI_DEBUG("AHCI HBA is reset.\n");

	return 0;
}

static int
ahci_init(uint8_t irq)
{
	int i;
	uint32_t ghc, pi;

	/* enable AHCI mode and HBA interrupt */
	ghc = ahci_readl(AHCI_GHC);
	ahci_writel(AHCI_GHC, ghc | AHCI_GHC_AE | AHCI_GHC_IE);

	/* get basic information */
	hba.cap = ahci_readl(AHCI_CAP);
	hba.x_cap = ahci_readl(AHCI_CAP2);
	hba.nports = (hba.cap & AHCI_CAP_NPMASK) + 1;
	hba.ncmds = ((hba.cap & AHCI_CAP_NCS) >> 8) + 1;
	hba.revision = ahci_readl(AHCI_VS);
	KERN_INFO("AHCI: rev %d.%d, %d ports, %d commands.\n",
		  (int) (hba.revision >> 16),
		  (int) ((hba.revision >> 8) & 0xff),
		  hba.nports, hba.ncmds);
	AHCI_DEBUG("cap1: 0x%08x, cap2: 0x%08x\n", hba.cap, hba.x_cap);

	/* initialize AHCI ports */
	memzero(&ports, sizeof(struct ahci_port) * AHCI_MAX_PORTS);
	pi = ahci_readl(AHCI_PI);
	for (i = 0; i < MIN(AHCI_MAX_PORTS, hba.nports); i++) {
		if ((pi & (1 << i)) == 0)
			continue;
		if (ahci_init_port(i, irq))
			AHCI_DEBUG("Cannot initialize port %d.\n", i);
		else
			AHCI_DEBUG("Port %d is initialzied.\n", i);
	}

	return 0;
}

static int
ahci_init_port(int port, uint8_t irq)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

	uint32_t cmd, sctl, ssts, ipm, det, serr;

	/* place AHCI port into the idle state */
	if (ahci_idle_port(port)) {
		AHCI_DEBUG("Cannot place port %d into the idle state.\n", port);
		return 1;
	}

	/* check where there's devices connected to this port */
	sctl = ahci_readl(AHCI_P_SCTL(port));
	ssts = ahci_readl(AHCI_P_SSTS(port));
	ipm = (ssts & AHCI_P_SSTS_IPM_MASK) >> AHCI_P_SSTS_IPM_SHIFT;
	det = (ssts & AHCI_P_SSTS_DET_MASK) >> AHCI_P_SSTS_DET_SHIFT;
	if ((sctl & AHCI_P_SCTL_DET_MASK) ||
	    ipm != AHCI_P_SSTS_IPM_ACTIVE || det != AHCI_P_SSTS_DET_PRESENT) {
		AHCI_DEBUG("No drive on port %d.\n", port);
		return 2;
	}

	/* allocate memory for the command list and FIS receive area */
	if (ahci_alloc_port(port)) {
		AHCI_DEBUG("Cannot allocate memory for CL and RFIS "
			   "of port %d.\n", port);
		return 3;
	}

	/* enable FIS receive */
	cmd = ahci_readl(AHCI_P_CMD(port));
	ahci_writel(AHCI_P_CMD(port), cmd | AHCI_P_CMD_FRE);

	/* clear PxSERR */
	serr = ahci_readl(AHCI_P_SERR(port));
	if (serr)
		ahci_writel(AHCI_P_SERR(port), serr);

	/* spinup the device */
	if (ahci_spinup_port(port)) {
		KERN_INFO("AHCI: port %d link down.\n", port);
		return 1;
	} else {
		KERN_INFO("AHCI: port %d link up.\n", port);
	}

	/* start the port */
	cmd = ahci_readl(AHCI_P_CMD(port));
	ahci_writel(AHCI_P_CMD(port),  cmd | AHCI_P_CMD_ST);

	/* identify drive on this port */
	ahci_identify_drive(port);

	if (ports[port].present == FALSE)
		return 1;

	/* enable interrupts on this port */
	/* XXX: only interrupt for errors and D2H FIS */
	ahci_writel(AHCI_P_IE(port), AHCI_P_IX_TFES | AHCI_P_IX_HBFS |
		    AHCI_P_IX_HBDS | AHCI_P_IX_IFS | AHCI_P_IX_DHRS);

	ports[port].status = PORT_READY;

	devices[port].dev = &ports[port];
	devices[port].capacity = ports[port].nsects;
	devices[port].dma_read = ahci_sata_xfer_read;
	devices[port].dma_write = ahci_sata_xfer_write;
	devices[port].poll_complete = ahci_poll_complete;
	disk_add_device(&devices[port]);

	return 0;
}

static int
ahci_idle_port(int port)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

	uint32_t cmd, is;

	cmd = ahci_readl(AHCI_P_CMD(port));

	/* clear PxCMD.ST, PxCMD.CR, PxCMD.FR and PxCMD.FRE */
	if (cmd & (AHCI_P_CMD_ST | AHCI_P_CMD_CR |
		   AHCI_P_CMD_FR | AHCI_P_CMD_FRE)) {
		ahci_writel(AHCI_P_CMD(port),
			    cmd & ~(AHCI_P_CMD_ST | AHCI_P_CMD_FRE));
		wait_until(500,
			   (ahci_readl(AHCI_P_CMD(port)) &
			    (AHCI_P_CMD_CR | AHCI_P_CMD_FRE)) == 0);
		cmd = ahci_readl(AHCI_P_CMD(port));
		if (cmd & (AHCI_P_CMD_CR | AHCI_P_CMD_FRE)) {
			AHCI_DEBUG("Cannot clear PxCMD.ST, PxCMD.CR, PxCMD.FR "
				   "and PxCMD.FRE of port %d.\n", port);
			return 1;
		}
	}

	/* disable all interrupts */
	ahci_writel(AHCI_P_IE(port), 0);
	if ((is = ahci_readl(AHCI_P_IS(port))))
		ahci_writel(AHCI_P_IS(port), is);

	AHCI_DEBUG("Port %d is idle.\n", port);
	return 0;
}

static int
ahci_alloc_port(int port)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

	uintptr_t cl, rfis, tb;
	int i;

	cl = (uintptr_t) &port_cl_rfis[port];
	rfis = cl + AHCI_CMDH_SIZE;

	ports[port].cl = (struct ahci_cmd_header *) cl;
	ports[port].rfis = (struct ahci_r_fis *) rfis;

	ahci_writel(AHCI_P_CLB(port), cl & 0xffffffff);
	ahci_writel(AHCI_P_CLBU(port), 0x00000000);
	ahci_writel(AHCI_P_FB(port), rfis & 0xffffffff);
	ahci_writel(AHCI_P_FBU(port), 0x00000000);

	tb = (uintptr_t) &port_cmds[port];
	for (i = 0; i < hba.ncmds; i++, tb += AHCI_CMDTBL_SIZE) {
		ports[port].cl[i].cmdh_cmdtba =	(uint32_t) (tb & 0xffffffff);
		ports[port].cl[i].cmdh_cmdtbau = 0x00000000;
	}

	return 0;
}

static int
ahci_spinup_port(int port)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

	uint32_t cmd, ssts, serr, tfd;

	/* spin-up */
	cmd = ahci_readl(AHCI_P_CMD(port));
	ahci_writel(AHCI_P_CMD(port), cmd | AHCI_P_CMD_SUD);
	wait_until(1000,
		   (ahci_readl(AHCI_P_SSTS(port)) &
		    AHCI_P_SSTS_DET_MASK) == AHCI_P_SSTS_DET_PRESENT ||
		   (ahci_readl(AHCI_P_SSTS(port)) &
		    AHCI_P_SSTS_DET_MASK) == AHCI_P_SSTS_DET_PARTIAL);
	ssts = ahci_readl(AHCI_P_SSTS(port));
	if ((ssts & AHCI_P_SSTS_DET_MASK) != AHCI_P_SSTS_DET_PRESENT) {
		AHCI_DEBUG("PxSTSS.DET of port %d != 0x3.\n", port);
		return 3;
	}

	/* clear PxSERR */
	serr = ahci_readl(AHCI_P_SERR(port));
	if (serr)
		ahci_writel(AHCI_P_SERR(port), serr);

	/* wait until the device is ready */
	wait_until(31000, (ahci_readl(AHCI_P_TFD(port)) &
			   (AHCI_P_TFD_ST_BSY | AHCI_P_TFD_ST_DRQ |
			    AHCI_P_TFD_ST_ERR)) == 0);
	tfd = ahci_readl(AHCI_P_TFD(port));
	if (tfd & (AHCI_P_TFD_ST_BSY | AHCI_P_TFD_ST_DRQ | AHCI_P_TFD_ST_ERR)) {
		AHCI_DEBUG("PxTFD.STS.BSY, PxTFD.STS.DRQ or PxTFD.STS.ERR of "
			   "port %d are not 0.\n", port);
		return 4;
	}

	AHCI_DEBUG("Drive on port %d is spun-up.\n", port);
	return 0;
}

static void
ahci_identify_drive(int port)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

	uint16_t buf[256];
	uint16_t udma_mode, __udma_mode;
	struct ahci_cmd_header *cmdh;
	struct ahci_cmd_tbl *tbl;
	struct sata_fis_reg *fis;

	ports[port].sig = ahci_readl(AHCI_P_SIG(port));
	ports[port].present = FALSE;

	if (ports[port].sig == AHCI_P_SIG_ATAPI) {
		KERN_INFO("AHCI: ATAPI drive on port %d. (not support yet)\n",
			  port);
		return;
	} else if (ports[port].sig != AHCI_P_SIG_ATA) {
		KERN_INFO("AHCI: non-ATA drive (sig = 0x%08x) on port %d. "
			  "(not support yet)\n", ports[port].sig, port);
		return;
	}

	/* identify ATA drive */
	cmdh = &ports[port].cl[0];
	tbl = (struct ahci_cmd_tbl *)(uintptr_t)
		(((uint64_t) cmdh->cmdh_cmdtbau << 32) | (cmdh->cmdh_cmdtba));
	fis = (struct sata_fis_reg *) tbl->cmdt_cfis;
	memzero(fis, sizeof(struct sata_fis_reg));
	fis->command = ATA_ATA_IDENTIFY;

	ahci_issue_command(port, 0, buf, sizeof(buf));

	if (ahci_wait_command(port)) {
		AHCI_DEBUG("Cannot identify the ATA drive on port %d.\n", port);
		return;
	}

	AHCI_DEBUG("rev 0x%04x:0x%04x\n", buf[80], buf[81]);
	AHCI_DEBUG("CAP: 0x%04x 0x%04x\n", buf[49], buf[50]);
	AHCI_DEBUG("DMA: 0x%04x, PIO: 0x%04x\n", buf[63], buf[64]);
	AHCI_DEBUG("CMD: 0x%04x 0x%04x 0x%04x 0x%04x 0x%04x 0x%04x\n",
		   buf[82], buf[83], buf[84], buf[85], buf[86], buf[87]);
	AHCI_DEBUG("UDMA: 0x%04x\n", buf[88]);

	if (buf[83] & (1 << 10)) {
		ports[port].lba48 = TRUE;
		ports[port].nsects = *(uint64_t *) &buf[100];
	} else {
		ports[port].lba48 = FALSE;
		ports[port].nsects = *(uint32_t *) &buf[60];
	}

	/* set the Ultra DMA mode to the highest one */
	udma_mode = 0;
	__udma_mode = buf[88] & 0xff;
	if (__udma_mode == 0)
		goto udma_set_done;
	while (__udma_mode >>= 1)
		udma_mode++;
	memzero(fis, sizeof(struct sata_fis_reg));
	fis->command = ATA_SET_FEATURES;
	fis->featurel = ATA_SET_TRANS_MODE;
	fis->countl = ATA_SET_UDMA_MODE(udma_mode);
	ahci_issue_command(port, 0, buf, sizeof(buf));
	if (ahci_wait_command(port)) {
		AHCI_DEBUG("Cannot set Ultra DMA mode %d.\n", udma_mode);
		return;
	} else {
		AHCI_DEBUG("Set Ultra DMA mode %d.\n", udma_mode);
	}

 udma_set_done:
	ports[port].present = TRUE;

	KERN_INFO("AHCI: ATA drive on port %d, size %lld MBytes%s.\n",
		  port, (ports[port].nsects * ATA_SECTOR_SIZE) >> 20,
		  ports[port].lba48 == TRUE ? ", LBA48" : "");
}

static void
ahci_issue_command(int port, int write, void *buffer, size_t bsize)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

	struct ahci_cmd_header *cmdh;
	struct ahci_cmd_tbl *tbl;
	struct sata_fis_reg *fis;

	cmdh = &ports[port].cl[0];
	tbl = (struct ahci_cmd_tbl *)(uintptr_t)
		(((uint64_t) cmdh->cmdh_cmdtbau << 32) | (cmdh->cmdh_cmdtba));
	fis = (struct sata_fis_reg *) tbl->cmdt_cfis;

	fis->type = SATA_FIS_TYPE_REG_H2D;
	fis->flag = (1 << 7);

	tbl->cmdt_prd[0].prd_dba = (uint32_t) buffer & 0xffffffff;
	tbl->cmdt_prd[0].prd_dbau = 0;
	tbl->cmdt_prd[0].prd_dbc = bsize - 1;

	cmdh->cmdh_flags = (write ? AHCI_CMDH_F_WR : 0) | 5;
	cmdh->cmdh_prdtl = 1;
	cmdh->cmdh_prdbc = 0;

	/* issue the command */
	ahci_writel(AHCI_P_SACT(port), 0x1); /* only for NCQ? */
	ahci_writel(AHCI_P_CI(port), 0x1);

	AHCI_DEBUG("Command 0x%x is issued to port %d.\n", fis->command, port);
}

static int
ahci_wait_command(int port)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

	int i;
	uint32_t ci, is, status;
#ifdef DEBUG_AHCI
	uint32_t error = 0;
#endif
	struct ahci_r_fis *rfis = ports[port].rfis;

	for (i = 0; 1; i++) {
		is = ahci_readl(AHCI_P_IS(port));

		if (is) {
			AHCI_DEBUG("PxIS on port %d = 0x%08x.\n", port, is);
			ahci_writel(AHCI_P_IS(port), is);

			if (is & AHCI_P_IX_PSS) {
				status = rfis->rfis_psfis[2];
#ifdef DEBUG_AHCI
				error = rfis->rfis_psfis[3];
#endif
				if (!(status & ATA_S_BUSY))
					break;
			}

			if (is & AHCI_P_IX_DHRS) {
				status = rfis->rfis_rfis[2];
#ifdef DEBUG_AHCI
				error = rfis->rfis_rfis[3];
#endif
				if (!(status & ATA_S_BUSY))
					break;
			}

			if (is & AHCI_P_IX_SDBS) {
				status = rfis->rfis_sdbfis[2];
#ifdef DEBUG_AHCI
				error = rfis->rfis_sdbfis[3];
#endif
				if (!(status & ATA_S_BUSY))
					break;
			}
		}

		udelay(1);
	}

	if (i > 6200000) {
		AHCI_DEBUG("Command timeout on port %d: PxIS = 0x%08x.\n",
			   port, is);
		return 1;
	}

	/* check status */
	if ((status & ATA_S_READY) &&
	    !(status & (ATA_S_ERROR | ATA_S_DWF | ATA_S_BUSY))) {
		AHCI_DEBUG("Command completes on port %d.\n", port);

		do {
			ci = ahci_readl(AHCI_P_CI(port));
			smp_wmb();
		} while (ci & 0x1);

		return 0;
	} else {
		AHCI_DEBUG("Command failed on port %d, status 0x%x, "
			   "errno 0x%x.\n", port, status, error);
		ahci_error_recovery(port);
		return 2;
	}
}

/* non-queued error recovery */
static void
ahci_error_recovery(int port)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));

#ifdef DEBUG_AHCI
	uint32_t ci, ccs;
#endif
	uint32_t cmd, is, serr, tfd, sctl, ssts;

	cmd = ahci_readl(AHCI_P_CMD(port));
	serr = ahci_readl(AHCI_P_SERR(port));
#ifdef DEBUG_AHCI
	ccs = (cmd & AHCI_P_CMD_CCS_MASK) >> AHCI_P_CMD_CCS_SHIFT;
	ci = ahci_readl(AHCI_P_CI(port));
	AHCI_DEBUG("Error on port %d, PxCI = 0x%08x, PxCMD.CCS = 0x%08x, "
		   "PxSERR = 0x%08x.\n", port, ci, ccs, serr);
#endif

	/* clear PxCMD.ST and wait for PxCMD.CR to clear to 0 */
	ahci_writel(AHCI_P_CMD(port), cmd & ~AHCI_P_CMD_ST);
	while (ahci_readl(AHCI_P_CMD(port)) & AHCI_P_CMD_CR);

	/* clear PxIS */
	is = ahci_readl(AHCI_P_IS(port));
	if (is)
		ahci_writel(AHCI_P_IS(port), is);

	/* clear PxSERR */
	if (serr)
		ahci_writel(AHCI_P_SERR(port), serr);

	/* issue a COMRESET if necessary */
	tfd = ahci_readl(AHCI_P_TFD(port));
	if (tfd & (AHCI_P_TFD_ST_BSY | AHCI_P_TFD_ST_DRQ)) {
		sctl = ahci_readl(AHCI_P_SCTL(port));
		ahci_writel(AHCI_P_SCTL(port), sctl | AHCI_P_SCTL_COMRESET);
		delay(1);
		ahci_writel(AHCI_P_SCTL(port), sctl & ~AHCI_P_SCTL_DET_MASK);
		do {
			ssts = ahci_readl(AHCI_P_SSTS(port));
		} while ((ssts & AHCI_P_SSTS_DET_MASK) != 0x1);
	}

	/* enable PxCMD.ST */
	cmd = ahci_readl(AHCI_P_CMD(port));
	ahci_writel(AHCI_P_CMD(port), cmd | AHCI_P_CMD_ST);

	/* enable interrupts on this port */
	/* XXX: only interrupt for errors and D2H FIS */
	ahci_writel(AHCI_P_IE(port), AHCI_P_IX_TFES | AHCI_P_IX_HBFS |
		    AHCI_P_IX_HBDS | AHCI_P_IX_IFS | AHCI_P_IX_DHRS);

}

static int
ahci_sata_xfer(int port, uint64_t lba, uint16_t nsects, uintptr_t pa, int write)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));
	KERN_ASSERT(ports[port].present == TRUE);
	KERN_ASSERT(ports[port].status == PORT_READY);
	KERN_ASSERT(lba + nsects <= ports[port].nsects);

	struct ahci_cmd_header *cmdh;
	struct ahci_cmd_tbl *tbl;
	struct sata_fis_reg *fis;

	cmdh = &ports[port].cl[0];
	tbl = (struct ahci_cmd_tbl *)(uintptr_t)
		(((uint64_t) cmdh->cmdh_cmdtbau << 32) | (cmdh->cmdh_cmdtba));
	fis = (struct sata_fis_reg *) tbl->cmdt_cfis;

	memzero(fis, sizeof(struct sata_fis_reg));
	if (nsects >= (1 << 8) || lba + nsects >= (1 << 28)) {
		fis->command = write ? ATA_WRITE_DMA48 : ATA_READ_DMA48;
		fis->lba3 = (uint8_t) (lba >> 24) & 0xff;
		fis->lba4 = (uint8_t) (lba >> 32) & 0xff;
		fis->lba5 = (uint8_t) (lba >> 40) & 0xff;
		fis->counth = (uint8_t) (nsects >> 8) & 0xff;
	} else {
		fis->command = write ? ATA_WRITE_DMA : ATA_READ_DMA;
	}
	fis->featurel = 1; /* DMA */
	fis->lba0 = (uint8_t) lba & 0xff;
	fis->lba1 = (uint8_t) (lba >> 8) & 0xff;
	fis->lba2 = (uint8_t) (lba >> 16) & 0xff;
	fis->dev = (uint8_t) ((lba >> 24) & 0xf) | 0x40;
	fis->countl = (uint8_t) nsects & 0xff;

	ports[port].status = PORT_XFERRING;

	ahci_issue_command(port, write, (void *) pa, nsects * ATA_SECTOR_SIZE);

	if (write)
		AHCI_DEBUG("Start transferring %d sectors from PA 0x%08x to "
			   "LBA 0x%llx on port %d.\n", nsects, pa, lba, port);
	else
		AHCI_DEBUG("Start transferring %d sectors from LBA 0x%llx to "
			   "PA 0x%08x on port %d.\n", nsects, lba, pa, port);

	return 0;
}

#define AHCI_CHECK_DEV(dev)						\
	if (dev == NULL || dev->dev == NULL)				\
		return 1;						\
									\
	pdev = (struct ahci_port *) dev->dev;				\
									\
	if (((uintptr_t) pdev - (uintptr_t) ports) %			\
	    sizeof(struct ahci_port) ||					\
	    pdev - ports < 0 ||						\
	    pdev - ports >= MIN(AHCI_MAX_PORTS, hba.nports))		\
		return 2;						\
									\
	if (pdev->present == FALSE)					\
		return 2;

static int
ahci_sata_xfer_read(struct disk_dev *dev,
		    uint64_t lba, uint16_t nsects, uintptr_t pa)
{
	struct ahci_port *pdev;
	int rc;

	AHCI_CHECK_DEV(dev);

	if (pdev->status != PORT_READY)
		return 2;

	if (lba + nsects > pdev->nsects)
		return 3;

	rc = ahci_sata_xfer(pdev - ports, lba, nsects, pa, FALSE);

	return rc;
}

static int
ahci_sata_xfer_write(struct disk_dev *dev,
		     uint64_t lba, uint16_t nsects, uintptr_t pa)
{
	struct ahci_port *pdev;
	int rc;

	AHCI_CHECK_DEV(dev);

	if (pdev->status != PORT_READY)
		return 2;

	if (lba + nsects > pdev->nsects)
		return 3;

	rc = ahci_sata_xfer(pdev - ports, lba, nsects, pa, TRUE);

	return rc;
}

static int
ahci_poll_complete(struct disk_dev *dev)
{
	struct ahci_port *pdev;

	AHCI_CHECK_DEV(dev);

	if (pdev->status != PORT_XFERRING)
		return 1;

	if (ahci_port_poll_complete(pdev - ports))
		dev->status = XFER_FAIL;
	else
		dev->status = XFER_SUCC;

	return 0;
}

#undef AHCI_CHECK_DEV

static int
ahci_port_poll_complete(int port)
{
	KERN_ASSERT(0 <= port && port < MIN(AHCI_MAX_PORTS, hba.nports));
	KERN_ASSERT(ports[port].present == TRUE);

	int rc;
	uint32_t tfd, ci;

	rc = ahci_wait_command(port);

	if (rc == 1)
		ahci_error_recovery(port);

	if (rc) {
		ports[port].status = PORT_READY;
		return 1;
	}

	/* check errors */
	tfd = ahci_readl(AHCI_P_TFD(port));
	if (tfd & (AHCI_P_TFD_ST_ERR | AHCI_P_TFD_ST_DF)) {
		AHCI_DEBUG("Transfer errors on port %d: PxTFD = 0x%08x.\n",
			   port, tfd);

		ahci_error_recovery(port);

		ports[port].status = PORT_READY;
		return 1;
	}

	/* transfer succeeds */
	KERN_ASSERT(ports[port].status == PORT_XFERRING);
	do {
//	    asm volatile (
//	            "1: dec %%ecx\n"
//	            "   jnz 1b\n"
//	            : : "c" (1000)
//	    );
		ci = ahci_readl(AHCI_P_CI(port));
	} while (ci);
	if (ci == 0 && ports[port].status == PORT_XFERRING)
		ports[port].status = PORT_READY;

	smp_wmb();

	return 0;
}

int
ahci_pci_attach(struct pci_func *f)
{
	/* XXX: only attach the first AHCI controller */
	if (ahci_inited == TRUE)
		return 1;

	KERN_ASSERT(f != NULL);

	if (PCI_CLASS(f->dev_class) != PCI_CLASS_MASS_STORAGE ||
	    PCI_SUBCLASS(f->dev_class) != PCI_SUBCLASS_MASS_STORAGE_SATA) {
		KERN_WARN("PCI: %02x:%02x.%d: not SATA controller.\n",
			  f->bus->busno, f->dev, f->func);
		return 0;
	}

	/* enable PCI device */
	pci_func_enable(f);
	memzero(&hba, sizeof(hba));
	memcpy(&hba.pci_func, f, sizeof(struct pci_func));
	hba.ghc = f->reg_base[5];

	/* initialize HBA */
	if (ahci_reset())
		return 0;
	if ((ahci_init(f->irq_line)))
		return 0;

	ahci_inited = TRUE;

	return 1;
}
