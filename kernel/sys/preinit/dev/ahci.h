/*
 * Copyright (c) 2006 Manuel Bouyer.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by Manuel Bouyer.
 * 4. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/*
 * This code is derived from NetBSD.
 * Adapated for CertiKOS by Haozhong Zhang at Yale University.
 */

#ifndef _KERN_DEV_AHCI_H_
#define _KERN_DEV_AHCI_H_

#ifdef _KERN_

#include <preinit/lib/gcc.h>
#include <preinit/lib/types.h>

#include <preinit/dev/pci.h>

/* SATA AHCI v1.0 register defines */

/* misc defines */
#define AHCI_MAX_PORTS 32
#define AHCI_MAX_CMDS 32

/* in-memory structures used by the controller */
/* physical region descriptor: points to a region of data (max 4MB) */
struct ahci_dma_prd {
	uint32_t prd_dba; /* data base address (64 bits) */
	uint32_t prd_dbau;
	uint32_t prd_res; /* reserved */
	uint32_t prd_dbc; /* data byte count */
#define AHCI_PRD_DBC_MASK 0x003fffff
#define AHCI_PRD_DBC_IPC  0x80000000 /* interrupt on completion */
} gcc_packed;

#define PAGE_SIZE	4096
#define	MAXPHYS		(64 * 1024)	/* max raw I/O transfer size */
#define AHCI_PRD_SIZE	PAGE_SIZE
#define AHCI_NPRD ((MAXPHYS/AHCI_PRD_SIZE) + 1)

/* command table: describe a command to send to drive */
struct ahci_cmd_tbl {
	uint8_t cmdt_cfis[64]; /* command FIS */
	uint8_t cmdt_acmd[16]; /* ATAPI command */
	uint8_t cmdt_res[48]; /* reserved */
	struct ahci_dma_prd cmdt_prd[1]; /* extended to AHCI_NPRD */
} gcc_packed;

#define AHCI_CMDTBL_ALIGN 0x7f

#define AHCI_CMDTBL_SIZE ((sizeof(struct ahci_cmd_tbl) + \
    (sizeof(struct ahci_dma_prd) * (AHCI_NPRD - 1)) + (AHCI_CMDTBL_ALIGN)) \
    & ~AHCI_CMDTBL_ALIGN)

/*
 * command header: points to a command table. The command list is an array
 * of theses.
 */
struct ahci_cmd_header {
	uint16_t cmdh_flags;
#define AHCI_CMDH_F_PMP_MASK	0xf000 /* port multiplier port */
#define AHCI_CMDH_F_PMP_SHIFT	12
#define AHCI_CMDH_F_CBSY	0x0400 /* clear BSY on R_OK */
#define AHCI_CMDH_F_BIST	0x0200 /* BIST FIS */
#define AHCI_CMDH_F_RST		0x0100 /* Reset FIS */
#define AHCI_CMDH_F_PRF		0x0080 /* prefectchable */
#define AHCI_CMDH_F_WR		0x0040 /* write */
#define AHCI_CMDH_F_A		0x0020 /* ATAPI */
#define AHCI_CMDH_F_CFL_MASK	0x001f /* command FIS length (in dw) */
#define AHCI_CMDH_F_CFL_SHIFT	0
	uint16_t cmdh_prdtl;	/* number of cmdt_prd */
	uint32_t cmdh_prdbc;	/* physical region descriptor byte count */
	uint32_t cmdh_cmdtba;	/* phys. addr. of cmd_tbl */
	uint32_t cmdh_cmdtbau;	/* (64bits, 128bytes aligned) */
	uint32_t cmdh_res[4];	/* reserved */
} gcc_packed;

#define AHCI_CMDH_SIZE (sizeof(struct ahci_cmd_header) * AHCI_MAX_CMDS)

static gcc_inline void
ahci_cmd_header_debug(struct ahci_cmd_header *cmdh)
{
	if (cmdh == NULL)
		return;

	KERN_DEBUG("AHCI CMD HEADER: addr %08x, size %d.\n",
		   cmdh, sizeof(struct ahci_cmd_header));
	dprintf("\tflags: %04x\n", cmdh->cmdh_flags);
	dprintf("\tnprd : %d\n", cmdh->cmdh_prdtl);
	dprintf("\tcprd : %d\n", cmdh->cmdh_prdbc);
	dprintf("\ttba  : %08x%08x\n", cmdh->cmdh_cmdtbau, cmdh->cmdh_cmdtba);
}

/* received FIS: where the HBA stores various type of FIS it receives */
struct ahci_r_fis {
	uint8_t rfis_dsfis[32]; /* DMA setup FIS */
	uint8_t rfis_psfis[32]; /* PIO setup FIS */
	uint8_t rfis_rfis[24]; /* D2H register FIS */
	uint8_t rfis_sdbfis[8]; /* set device bit FIS */
	uint8_t rfis_ukfis[64]; /* unknown FIS */
	uint8_t rfis_res[96];
} gcc_packed;

#define AHCI_RFIS_SIZE (sizeof(struct ahci_r_fis))

/* PCI registers */
/* class Mass storage, subclass SATA, interface AHCI */
#define PCI_INTERFACE_SATA_AHCI	0x01

#define AHCI_PCI_ABAR	0x24 /* native ACHI registers (memory mapped) */

/*  ABAR registers */
/* Global registers */
#define AHCI_CAP	0x00 /* HBA capabilities */
#define		AHCI_CAP_NPMASK	0x0000001f /* Number of ports */
#define		AHCI_CAP_XS	0x00000020 /* External SATA */
#define		AHCI_CAP_EM	0x00000040 /* Enclosure Management */
#define		AHCI_CAP_CCC	0x00000080 /* command completion coalescing */
#define		AHCI_CAP_NCS	0x00001f00 /* number of command slots */
#define		AHCI_CAP_PS	0x00002000 /* Partial State */
#define		AHCI_CAP_SS	0x00004000 /* Slumber State */
#define		AHCI_CAP_PMD	0x00008000 /* PIO multiple DRQ blocks */
#define		AHCI_CAP_FBS	0x00010000 /* FIS-Based switching */
#define		AHCI_CAP_SPM	0x00020000 /* Port multipliers */
#define		AHCI_CAP_SAM	0x00040000 /* AHCI-only */
#define		AHCI_CAP_NZO	0x00080000 /* Non-zero DMA offset (reserved) */
#define		AHCI_CAP_IS	0x00f00000 /* Interface speed */
#define		AHCI_CAP_IS_GEN1	0x00100000 /* 1.5 GB/s */
#define		AHCI_CAP_IS_GEN2	0x00200000 /* 1.5 and 3 GB/s */
#define		AHCI_CAP_IS_GEN3	0x00300000 /* 6 GB/s */
#define		AHCI_CAP_CLO	0x01000000 /* Command list override */
#define		AHCI_CAP_AL	0x02000000 /* Single Activitly LED */
#define		AHCI_CAP_ALP	0x04000000 /* Agressive link power management */
#define		AHCI_CAP_SSU	0x08000000 /* Staggered spin-up */
#define		AHCI_CAP_MPS	0x10000000 /* Mechanical swicth */
#define		AHCI_CAP_NTF	0x20000000 /* Snotification */
#define		AHCI_CAP_NCQ	0x40000000 /* Native command queuing */
#define		AHCI_CAP_64BIT	0x80000000 /* 64bit addresses */

#define AHCI_GHC	0x04 /* HBA control */
#define 	AHCI_GHC_HR	 0x00000001 /* HBA reset */
#define 	AHCI_GHC_IE	 0x00000002 /* Interrupt enable */
#define 	AHCI_GHC_MRSM	 0x00000004 /* MSI revert to single message */
#define 	AHCI_GHC_AE	 0x80000000 /* AHCI enable */

#define AHCI_IS		0x08 /* Interrupt status register: one bit per port */

#define AHCI_PI		0x0c /* Port implemented: one bit per port */

#define AHCI_VS		0x10 /* AHCI version */
#define 	AHCI_VS_10	0x00010000 /* AHCI spec 1.0 */
#define 	AHCI_VS_11	0x00010100 /* AHCI spec 1.1 */
#define 	AHCI_VS_12	0x00010200 /* AHCI spec 1.2 */

#define AHCI_CC_CTL	0x14 /* command completion coalescing control */
#define 	AHCI_CC_TV_MASK	0xffff0000 /* timeout value */
#define 	AHCI_CC_TV_SHIFT 16
#define 	AHCI_CC_CC_MASK	0x0000ff00 /* command completion */
#define 	AHCI_CC_CC_SHIFT 8
#define 	AHCI_CC_INT_MASK 0x000000f8 /* interrupt */
#define 	AHCI_CC_INT_SHIFT 3
#define 	AHCI_CC_EN	0x000000001 /* enable */

#define AHCI_CC_PORTS	0x18 /* command completion coalescing ports (1b/port */

#define AHCI_EM_LOC	0x1c /* enclosure managemement location */
#define		AHCI_EML_OFF_MASK 0xffff0000 /* offset in ABAR */
#define		AHCI_EML_OFF_SHIFT 16
#define		AHCI_EML_SZ_MASK  0x0000ffff /* offset in ABAR */
#define		AHCI_EML_SZ_SHIFT  0

#define AHCI_EM_CTL	0x20 /* enclosure management control */
#define		AHCI_EMC_PM	0x08000000 /* port multiplier support */
#define		AHCI_EMC_ALHD	0x04000000 /* activity LED hardware driven */
#define		AHCI_EMC_XMIT	0x02000000 /* tramsit messages only */
#define		AHCI_EMC_SMB	0x01000000 /* single message buffer */
#define		AHCI_EMC_SGPIO	0x00080000 /* enclosure management messages */
#define		AHCI_EMC_SES2	0x00040000 /* SeS-2 messages */
#define		AHCI_EMC_SAF	0x00020000 /* SAF_TE messages */
#define		AHCI_EMC_LED	0x00010000 /* LED messages */
#define		AHCI_EMC_RST	0x00000200 /* Reset */
#define		AHCI_EMC_TM	0x00000100 /* Transmit message */
#define		AHCI_EMC_MR	0x00000001 /* Message received */

#define AHCI_CAP2	0x24 /* extended capabilities */
#define		AHCI_CAP2_APST	0x00000004
#define		AHCI_CAP2_NVMP	0x00000002
#define		AHCI_CAP2_BOH	0x00000001

/* Per-port registers */
#define AHCI_P_OFFSET(port) (0x80 * (port))

#define AHCI_P_CLB(p)	(0x100 + AHCI_P_OFFSET(p)) /* command list addr */
#define AHCI_P_CLBU(p)	(0x104 + AHCI_P_OFFSET(p)) /* command list addr */
#define AHCI_P_FB(p)	(0x108 + AHCI_P_OFFSET(p)) /* FIS addr */
#define AHCI_P_FBU(p)	(0x10c + AHCI_P_OFFSET(p)) /* FIS addr */
#define AHCI_P_IS(p)	(0x110 + AHCI_P_OFFSET(p)) /* Interrupt status */
#define AHCI_P_IE(p)	(0x114 + AHCI_P_OFFSET(p)) /* Interrupt enable */
#define		AHCI_P_IX_CPDS	0x80000000 /* Cold port detect */
#define		AHCI_P_IX_TFES	0x40000000 /* Task file error */
#define		AHCI_P_IX_HBFS	0x20000000 /* Host bus fatal error */
#define		AHCI_P_IX_HBDS	0x10000000 /* Host bus data error */
#define		AHCI_P_IX_IFS	0x08000000 /* Interface fatal error */
#define		AHCI_P_IX_INFS	0x04000000 /* Interface non-fatal error */
#define		AHCI_P_IX_OFS	0x01000000 /* Overflow */
#define		AHCI_P_IX_IPMS	0x00800000 /* Incorrect port multiplier */
#define		AHCI_P_IX_PRCS	0x00400000 /* Phy Ready change */
#define		AHCI_P_IX_DMPS	0x00000080 /* Device Mechanical Presence */
#define		AHCI_P_IX_PCS	0x00000040 /* port Connect change */
#define		AHCI_P_IX_DPS	0x00000020 /* dexcriptor processed */
#define		AHCI_P_IX_UFS	0x00000010 /* Unknown FIS */
#define		AHCI_P_IX_SDBS	0x00000008 /* Set device bit */
#define		AHCI_P_IX_DSS	0x00000004 /* DMA setup FIS */
#define		AHCI_P_IX_PSS	0x00000002 /* PIO setup FIS */
#define		AHCI_P_IX_DHRS	0x00000001 /* Device to Host FIS */

#define AHCI_P_CMD(p)	(0x118 + AHCI_P_OFFSET(p)) /* Port command/status */
#define		AHCI_P_CMD_ICC_MASK 0xf0000000 /* Interface Comm. Control */
#define		AHCI_P_CMD_ICC_SL   0x60000000 /* State slumber */
#define		AHCI_P_CMD_ICC_PA   0x20000000 /* State partial */
#define		AHCI_P_CMD_ICC_AC   0x10000000 /* State active */
#define		AHCI_P_CMD_ICC_NO   0x00000000 /* State idle/NOP */
#define		AHCI_P_CMD_ASP	0x08000000 /* Agressive Slumber/Partial */
#define		AHCI_P_CMD_ALPE	0x04000000 /* Agressive link power management */
#define		AHCI_P_CMD_DLAE	0x02000000 /* drive LED on ATAPI */
#define		AHCI_P_CMD_ATAP	0x01000000 /* Device is ATAPI */
#define		AHCI_P_CMD_ESP	0x00200000 /* external SATA port */
#define		AHCI_P_CMD_CPD	0x00100000 /* Cold presence detection */
#define		AHCI_P_CMD_MPSP	0x00080000 /* Mechanical switch attached */
#define		AHCI_P_CMD_HPCP	0x00040000 /* hot-plug capable */
#define		AHCI_P_CMD_PMA	0x00020000 /* port multiplier attached */
#define		AHCI_P_CMD_CPS	0x00010000 /* cold presence state */
#define		AHCI_P_CMD_CR	0x00008000 /* command list running */
#define		AHCI_P_CMD_FR	0x00004000 /* FIS receive running */
#define		AHCI_P_CMD_MPSS	0x00002000 /* mechanical switch state */
#define		AHCI_P_CMD_CCS_MASK 0x00001f00 /* current command slot */
#define		AHCI_P_CMD_CCS_SHIFT 12
#define		AHCI_P_CMD_FRE	0x00000010 /* FIS receive enable */
#define		AHCI_P_CMD_CLO	0x00000008 /* command list override */
#define		AHCI_P_CMD_POD	0x00000004 /* power on device */
#define		AHCI_P_CMD_SUD	0x00000002 /* spin up device */
#define		AHCI_P_CMD_ST	0x00000001 /* start */

#define AHCI_P_TFD(p)	(0x120 + AHCI_P_OFFSET(p)) /* Port task file data */
#define		AHCI_P_TFD_ERR_MASK	0x0000ff00 /* error register */
#define		AHCI_P_TFD_ERR_SHIFT	8
#define		AHCI_P_TFD_ST		0x000000ff /* status register */
#define		AHCI_P_TFD_ST_SHIFT	0
#define		AHCI_P_TFD_ST_BSY	(1<<7)
#define		AHCI_P_TFD_ST_DF	(1<<5)
#define		AHCI_P_TFD_ST_DRQ	(1<<3)
#define		AHCI_P_TFD_ST_ERR	(1<<0)

#define AHCI_P_SIG(p)	(0x124 + AHCI_P_OFFSET(p)) /* device signature */
#define		AHCI_P_SIG_LBAH_MASK	0xff000000
#define		AHCI_P_SIG_LBAH_SHIFT	24
#define		AHCI_P_SIG_LBAM_MASK	0x00ff0000
#define		AHCI_P_SIG_LBAM_SHIFT	16
#define		AHCI_P_SIG_LBAL_MASK	0x0000ff00
#define		AHCI_P_SIG_LBAL_SHIFT	8
#define		AHCI_P_SIG_SC_MASK	0x000000ff
#define		AHCI_P_SIG_SC_SHIFT	8
#define		AHCI_P_SIG_ATA		0x00000101
#define		AHCI_P_SIG_ATAPI	0xeb140101
#define		AHCI_P_SIG_SEMB		0xc33c0101
#define		AHCI_P_SIG_PM		0x96690101

#define AHCI_P_SSTS(p)	(0x128 + AHCI_P_OFFSET(p)) /* Serial ATA status */
#define		AHCI_P_SSTS_IPM_MASK	0x00000f00
#define		AHCI_P_SSTS_IPM_SHIFT	8
#define		AHCI_P_SSTS_IPM_NONE	0x0
#define		AHCI_P_SSTS_IPM_ACTIVE	0x1
#define		AHCI_P_SSTS_SPD_MASK	0x000000f0
#define		AHCI_P_SSTS_SPD_SHIFT	4
#define		AHCI_P_SSTS_SPD_NONE	0x0
#define		AHCI_P_SSTS_SPD_G1	0x1
#define		AHCI_P_SSTS_SPD_G2	0x2
#define		AHCI_P_SSTS_SPD_G3	0x3
#define		AHCI_P_SSTS_DET_MASK	0xf
#define		AHCI_P_SSTS_DET_SHIFT	0
#define		AHCI_P_SSTS_DET_NONE	0x0
#define		AHCI_P_SSTS_DET_PARTIAL	0x1
#define		AHCI_P_SSTS_DET_PRESENT	0x3
#define		AHCI_P_SSTS_DET_OFFLINE	0x4

#define AHCI_P_SCTL(p)	(0x12c + AHCI_P_OFFSET(p)) /* Serial ATA control */
#define		AHCI_P_SCTL_IPM_MASK	0x00000f00
#define		AHCI_P_SCTL_IPM_SHIFT	8
#define		AHCI_P_SCTL_SPD_MASK	0x000000f0
#define		AHCI_P_SCTL_SPD_SHIFT	4
#define		AHCI_P_SCTL_DET_MASK	0x0000000f
#define		AHCI_P_SCTL_DET_SHIFT	0
#define		AHCI_P_SCTL_COMRESET	0x00000001

#define AHCI_P_SERR(p)	(0x130 + AHCI_P_OFFSET(p)) /* Serial ATA error */
#define		AHCI_P_SERR_DIAG_X	(1<<26)
#define		AHCI_P_SERR_DIAG_F	(1<<25)
#define		AHCI_P_SERR_DIAG_T	(1<<24)
#define		AHCI_P_SERR_DIAG_S	(1<<23)
#define		AHCI_P_SERR_DIAG_H	(1<<22)
#define		AHCI_P_SERR_DIAG_C	(1<<21)
#define		AHCI_P_SERR_DIAG_D	(1<<20)
#define		AHCI_P_SERR_DIAG_B	(1<<19)
#define		AHCI_P_SERR_DIAG_W	(1<<18)
#define		AHCI_P_SERR_DIAG_I	(1<<17)
#define		AHCI_P_SERR_DIAG_N	(1<<16)
#define		AHCI_P_SERR_ERR_E	(1<<11)
#define		AHCI_P_SERR_ERR_P	(1<<10)
#define		AHCI_P_SERR_ERR_C	(1<<9)
#define		AHCI_P_SERR_ERR_T	(1<<8)
#define		AHCI_P_SERR_ERR_M	(1<<1)
#define		AHCI_P_SERR_ERR_I	(1<<0)
#define		AHCI_P_SERR_CLEAR	0x07ff0f03

/* Serial ATA active: one bit per tag/command slot */
#define AHCI_P_SACT(p)	(0x134 + AHCI_P_OFFSET(p))

/* Command issued: one bit per tag/command slot */
#define AHCI_P_CI(p)	(0x138 + AHCI_P_OFFSET(p))

/* SNotification: one bit per port */
#define AHCI_P_FNTF(p)	(0x13c + AHCI_P_OFFSET(p))

/* ATA command */
#define ATA_READ_DMA48			0x25	/* read DMA 48bit LBA */
#define ATA_WRITE_DMA48			0x35	/* write DMA 48bit LBA */
#define ATA_ATAPI_IDENTIFY		0xa1	/* get ATAPI params*/
#define ATA_READ_DMA			0xc8	/* read DMA */
#define ATA_WRITE_DMA			0xca	/* write DMA */
#define ATA_ATA_IDENTIFY		0xec	/* get ATA params */
#define ATA_SET_FEATURES		0xef

/* subcommands of ATA_SET_FEATURES */
#define ATA_SET_TRANS_MODE		0x03
# define ATA_SET_MDMA_MODE(m)		((1 << 5) | ((m) & 7))
# define ATA_SET_UDMA_MODE(m)		((1 << 6) | ((m) & 7))

/* ATA status */
#define ATA_STATUS			10	/* (R) status */
#define ATA_ALTSTAT			11	/* (R) alternate status */
#define		ATA_S_ERROR		0x01	/* error */
#define		ATA_S_INDEX		0x02	/* index */
#define		ATA_S_CORR		0x04	/* data corrected */
#define		ATA_S_DRQ		0x08	/* data request */
#define		ATA_S_DSC		0x10	/* drive seek completed */
#define		ATA_S_SERVICE		0x10	/* drive needs service */
#define		ATA_S_DWF		0x20	/* drive write fault */
#define		ATA_S_DMA		0x20	/* DMA ready */
#define		ATA_S_READY		0x40	/* drive ready */
#define		ATA_S_BUSY		0x80	/* busy */

#define ATA_SECTOR_SIZE		512	/* 512 bytes */

int ahci_pci_attach(struct pci_func *);

#endif /* _KERN_ */

#endif /* !_KERN_DEV_AHCI_H_ */
