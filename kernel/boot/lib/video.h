// Text-mode CGA/VGA video output.
// See COPYRIGHT for copyright information.
#ifndef _CERTIKOS_BOOT_VIDEO_H_
#define _CERTIKOS_BOOT_VIDEO_H_

#ifdef BOOT_CONSOLE

#include <types.h>
#include <x86.h>

#define MONO_BASE	0x3B4
#define MONO_BUF	0xB0000
#define CGA_BASE	0x3D4
#define CGA_BUF		0xB8000

#define CRT_ROWS	25
#define CRT_COLS	80
#define CRT_SIZE	(CRT_ROWS * CRT_COLS)

void video_init(void);
void video_putc(int c);

#else /* BOOT_CONSOLE */

void video_init(void)
{
}

void video_putc(int c)
{
}

#endif /* !BOOT_CONSOLE */

#endif /* !_CERTIKOS_BOOT_VIDEO_H_ */
