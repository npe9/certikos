#ifndef _VDEV_BIOS_H_
#define _VDEV_BIOS_H_

#include <gcc.h>
#include <types.h>

#define BDA_BASE	0x400

struct bios_data_area {
	uint16_t	com[4];		/* 0x400:
					   IO ports for COM1 ~ COM4 serial */
	uint16_t	lpt[3];		/* 0x408:
					   IO ports for LPT1 ~ LPT3 parallel */
	uint16_t	ebda;		/* 0x40E:
					   EBDA base address >> 4 */
	uint16_t	hw;		/* 0x410:
					   packed bit flags for detected HW */
	uint8_t		_pad1[5];
	uint8_t		kbd_stat1;	/* 0x417: */
	uint8_t		kbd_stat2;	/* 0x418: */
	uint8_t		_pad2[5];
	uint8_t		kbd_buf[32];	/* 0x41E:
					   keyboard buffer */
	uint8_t		_pad3[11];
	uint8_t		disp_mode;	/* 0x449:
					   display mode */
	uint16_t	columns;	/* 0x44A:
					   numbers of columns in text mode */
	uint8_t		_pad4[23];
	uint16_t	video_port;	/* 0x463:
					   base IO port for video */
	uint8_t		_pad5[7];
	uint16_t	ticks;		/* 0x46C:
					   # of IRQ0 timer ticks since boot */
	uint8_t		_pad6[7];
	uint8_t		hdds;		/* 0x475:
					   # of hard disk devices detected */
	uint8_t		_pad7[10];
	uint16_t	kbd_buf_start;	/* 0x480:
					   keyboard buffer start */
	uint16_t	kbd_buf_end;	/* 0x482:
					   keyboard buffer end */
	uint8_t		_pad8[18];
	uint8_t		kbd_stat3;	/* 0x496: */
	uint8_t		kbd_stat4;	/* 0x497: */
} gcc_packed;

#define BDA_KBD_STAT1_INS	(1<<7)
#define BDA_KBD_STAT1_CAP	(1<<6)
#define BDA_KBD_STAT1_NUM	(1<<5)
#define BDA_KBD_STAT1_SCROLL	(1<<4)
#define BDA_KBD_STAT1_ALT	(1<<3)
#define BDA_KBD_STAT1_CTRL	(1<<2)
#define BDA_KBD_STAT1_LSHIFT	(1<<1)
#define BDA_KBD_STAT1_RSHIFT	(1<<0)

#define BDA_KBD_STAT2_INS	(1<<7)
#define BDA_KBD_STAT2_CAP	(1<<6)
#define BDA_KBD_STAT2_NUM	(1<<5)
#define BDA_KBD_STAT2_SCROLL	(1<<4)
#define BDA_KBD_STAT2_PAUSE	(1<<3)
#define BDA_KBD_STAT2_SYSRQ	(1<<2)
#define BDA_KBD_STAT2_LALT	(1<<1)
#define BDA_KBD_STAT2_RALT	(1<<0)

#define BDA_KBD_STAT3_READING	(1<<7)
#define BDA_KBD_STAT3_FIRST_ID	(1<<6)
#define BDA_KBD_STAT3_FORCE_NUM	(1<<5)
#define BDA_KBD_STAT3_ENH_KBD	(1<<4)
#define BDA_KBD_STAT3_RALT	(1<<3)
#define BDA_KBD_STAT3_RCTRL	(1<<2)
#define BDA_KBD_STAT3_LAST_E0	(1<<1)
#define BDA_KBD_STAT3_LAST_E1	(1<<0)

#define BDA_KBD_STAT4_TRANS_ERR	(1<<7)
#define BDA_KBD_STAT4_UPDATING	(1<<6)
#define BDA_KBD_STAT4_RESEND	(1<<5)
#define BDA_KBD_STAT4_ACK	(1<<4)
#define BDA_KBD_STAT4_CAP_LED	(1<<2)
#define BDA_KBD_STAT4_NUM_LED	(1<<1)
#define BDA_KBD_STAT4_SCR_LED	(1<<0)

#endif /* !_VDEV_BIOS_H_ */
