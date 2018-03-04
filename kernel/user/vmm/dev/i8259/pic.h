/*
 * QEMU 8259 interrupt controller emulation
 *
 * Copyright (c) 2003-2004 Fabrice Bellard
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

#ifndef _USER_VIRT_PIC_H_
#define _USER_VIRT_PIC_H_

#include <types.h>
#include "../../vmm_dev.h"

struct i8259 {
	struct vpic	*vpic;

	bool		master;

	bool		single_mode;

	uint8_t		init_state;
	bool		init4;

	uint8_t		lowest_priority;

	uint8_t		irq_base;
	uint8_t		last_irr;
	uint8_t		irr;
	uint8_t		isr;
	uint8_t		imr;
	uint8_t		int_out;

	bool		select_isr;
	bool		poll;
	bool		auto_eoi_mode;
	bool		rotate_on_auto_eoi;
	bool		special_mask_mode;
	bool		fully_nested_mode;
	bool		special_fully_nested_mode;

	uint8_t		elcr;
	uint8_t		elcr_mask;

	bool		ready;
};

struct vpic {
	uint8_t		int_out;
	struct i8259	master;
	struct i8259	slave;
	struct vdev	*vdev;
};

int vpic_init(struct vdev *vdev, struct vpic *vpic);

#endif /* !_USER_VIRT_PIC_H_ */
