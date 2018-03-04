/*
 * QEMU PS/2 keyboard/mouse emulation
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

#ifndef _VDEV_PS2_H_
#define _VDEV_PS2_H_

#include <gcc.h>
#include <types.h>

#define PS2_QUEUE_SIZE 256

struct PS2_queue {
	uint8_t	data[PS2_QUEUE_SIZE];
	int	rptr, wptr, count;
};

struct PS2 {
	struct PS2_queue	queue;
	int32_t			write_cmd;
	void			(*update_irq)(void *, int);
	void			*update_arg;
};

struct PS2_kbd{
	struct PS2 	common;
	int 		scan_enabled;
	/* Qemu uses translated PC scancodes internally.  To avoid multiple
	   conversions we do the translation (if any) in the PS/2 emulation
	   not the keyboard controller.  */
	int 		translate;
	int 		scancode_set; /* 1=XT, 2=AT, 3=PS/2 */
	int 		ledstate;
} gcc_packed;

struct PS2_mouse {
	struct PS2	common;
	uint8_t 	mouse_status;
	uint8_t 	mouse_resolution;
	uint8_t 	mouse_sample_rate;
	uint8_t 	mouse_wrap;
	uint8_t 	mouse_type; /* 0 = PS2, 3 = IMPS/2, 4 = IMEX */
	uint8_t 	mouse_detect_state;
	int 		mouse_dx; /* current values, needed for 'poll' mode */
	int 		mouse_dy;
	int 		mouse_dz;
	uint8_t 	mouse_buttons;
} gcc_packed;

void ps2_queue(struct PS2 *, int b);
uint32_t ps2_read_data(struct PS2 *);

void ps2_write_keyboard(struct PS2_kbd *, int val);
void ps2_keyboard_set_translation(struct PS2_kbd *, int mode);

void ps2_mouse_fake_event(struct PS2_mouse *);
void ps2_write_mouse(struct PS2_mouse *, int);

void ps2_kbd_init(struct PS2_kbd *, void (*update_irq)(void *, int), void *);
void ps2_mouse_init(struct PS2_mouse *, void (*update_irq)(void *, int), void *);

#endif /* !_VDEV_PS2_H_ */
