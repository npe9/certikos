/*
 * QEMU PC keyboard emulation
 *
 * Copyright (c) 2003 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

/*
 * Adapted for CertiKOS by Haozhong Zhang at Yale University.
 */

#ifndef _VDEV_KBD_H_
#define _VDEV_KBD_H_

#include <types.h>

#include "ps2.h"
#include "../../vmm_dev.h"

#define	KBSTATP		0x64	/* kbd controller status port(I) */
#define	KBCMDP		0x64	/* kbd controller port(O) */
#define	KBDATAP		0x60	/* kbd data port(I) */

#define IRQ_KBD		1	/* Keyboard interrupt */
#define IRQ_MOUSE	12	/* Mouse interrupt */

struct vkbd {
	uint8_t		write_cmd;

	uint8_t		status;		/* buffer of command/status port */
	uint8_t		outport;	/* buffer of data port */

	uint8_t		mode;

	uint8_t		pending;	/* KBD/AUX event pending? */

	struct vdev		*vdev;
	struct PS2_kbd		kbd;
	struct PS2_mouse	mouse;
};

int vkbd_init(struct vdev *dev, void *opaque);

#endif /* !_VDEV_KBD_H_ */
