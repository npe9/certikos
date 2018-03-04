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

#include <debug.h>
#include <types.h>

#include "ps2.h"

/* Keyboard Commands */
#define KBD_CMD_SET_LEDS	0xED	/* Set keyboard leds */
#define KBD_CMD_ECHO     	0xEE
#define KBD_CMD_SCANCODE	0xF0	/* Get/set scancode set */
#define KBD_CMD_GET_ID 	        0xF2	/* get keyboard ID */
#define KBD_CMD_SET_RATE	0xF3	/* Set typematic rate */
#define KBD_CMD_ENABLE		0xF4	/* Enable scanning */
#define KBD_CMD_RESET_DISABLE	0xF5	/* reset and disable scanning */
#define KBD_CMD_RESET_ENABLE   	0xF6    /* reset and enable scanning */
#define KBD_CMD_RESET		0xFF	/* Reset */

/* Keyboard Replies */
#define KBD_REPLY_POR		0xAA	/* Power on reset */
#define KBD_REPLY_ID		0xAB	/* Keyboard ID */
#define KBD_REPLY_ACK		0xFA	/* Command ACK */
#define KBD_REPLY_RESEND	0xFE	/* Command NACK, send the cmd again */

/* Mouse Commands */
#define AUX_SET_SCALE11		0xE6	/* Set 1:1 scaling */
#define AUX_SET_SCALE21		0xE7	/* Set 2:1 scaling */
#define AUX_SET_RES		0xE8	/* Set resolution */
#define AUX_GET_SCALE		0xE9	/* Get scaling factor */
#define AUX_SET_STREAM		0xEA	/* Set stream mode */
#define AUX_POLL		0xEB	/* Poll */
#define AUX_RESET_WRAP		0xEC	/* Reset wrap mode */
#define AUX_SET_WRAP		0xEE	/* Set wrap mode */
#define AUX_SET_REMOTE		0xF0	/* Set remote mode */
#define AUX_GET_TYPE		0xF2	/* Get type */
#define AUX_SET_SAMPLE		0xF3	/* Set sample rate */
#define AUX_ENABLE_DEV		0xF4	/* Enable aux device */
#define AUX_DISABLE_DEV		0xF5	/* Disable aux device */
#define AUX_SET_DEFAULT		0xF6
#define AUX_RESET		0xFF	/* Reset aux device */
#define AUX_ACK			0xFA	/* Command byte ACK. */

#define MOUSE_STATUS_REMOTE     0x40
#define MOUSE_STATUS_ENABLED    0x20
#define MOUSE_STATUS_SCALE21    0x10

/* Table to convert from PC scancodes to raw scancodes.  */
static const unsigned char ps2_raw_keycode[128] = {
	0, 118,  22,  30,  38,  37,  46,  54,  61,  62,  70,  69,  78,  85, 102,  13,
	21,  29,  36,  45,  44,  53,  60,  67,  68,  77,  84,  91,  90,  20,  28,  27,
	35,  43,  52,  51,  59,  66,  75,  76,  82,  14,  18,  93,  26,  34,  33,  42,
	50,  49,  58,  65,  73,  74,  89, 124,  17,  41,  88,   5,   6,   4,  12,   3,
	11,   2,  10,   1,   9, 119, 126, 108, 117, 125, 123, 107, 115, 116, 121, 105,
	114, 122, 112, 113, 127,  96,  97, 120,   7,  15,  23,  31,  39,  47,  55,  63,
	71,  79,  86,  94,   8,  16,  24,  32,  40,  48,  56,  64,  72,  80,  87, 111,
	19,  25,  57,  81,  83,  92,  95,  98,  99, 100, 101, 103, 104, 106, 109, 110
};
static const unsigned char ps2_raw_keycode_set3[128] = {
	0,   8,  22,  30,  38,  37,  46,  54,  61,  62,  70,  69,  78,  85, 102,  13,
	21,  29,  36,  45,  44,  53,  60,  67,  68,  77,  84,  91,  90,  17,  28,  27,
	35,  43,  52,  51,  59,  66,  75,  76,  82,  14,  18,  92,  26,  34,  33,  42,
	50,  49,  58,  65,  73,  74,  89, 126,  25,  41,  20,   7,  15,  23,  31,  39,
	47,   2,  63,  71,  79, 118,  95, 108, 117, 125, 132, 107, 115, 116, 124, 105,
	114, 122, 112, 113, 127,  96,  97,  86,  94,  15,  23,  31,  39,  47,  55,  63,
	71,  79,  86,  94,   8,  16,  24,  32,  40,  48,  56,  64,  72,  80,  87, 111,
	19,  25,  57,  81,  83,  92,  95,  98,  99, 100, 101, 103, 104, 106, 109, 110
};

void
ps2_queue(struct PS2 *ps2, int b)
{
	ASSERT(ps2 != NULL);

	struct PS2_queue *q = &ps2->queue;

	if (q->count >= PS2_QUEUE_SIZE)
		return;
	q->data[q->wptr] = b;
	if (++q->wptr == PS2_QUEUE_SIZE)
		q->wptr = 0;
	q->count++;
	ps2->update_irq(ps2->update_arg, 1);
}

/*
 * keycode is expressed as follow:
 * bit 7    - 0 key pressed, 1 = key released
 * bits 6-0 - translated scancode set 2
 */
static void
ps2_put_keycode(struct PS2_kbd *kbd, int keycode)
{
	ASSERT(kbd != NULL);

	/* XXX: add support for scancode set 1 */
	if (!kbd->translate && keycode < 0xe0 && kbd->scancode_set > 1) {
		if (keycode & 0x80) {
			ps2_queue(&kbd->common, 0xf0);
		}
		if (kbd->scancode_set == 2) {
			keycode = ps2_raw_keycode[keycode & 0x7f];
		} else if (kbd->scancode_set == 3) {
			keycode = ps2_raw_keycode_set3[keycode & 0x7f];
		}
	}
	ps2_queue(&kbd->common, keycode);
}

uint32_t
ps2_read_data(struct PS2 *ps2)
{
	ASSERT(ps2 != NULL);

	struct PS2_queue *q;
	int val, index;

	q = &ps2->queue;
	if (q->count == 0) {
		/* NOTE: if no data left, we return the last keyboard one
		   (needed for EMM386) */
		/* XXX: need a timer to do things correctly */
		index = q->rptr - 1;
		if (index < 0)
			index = PS2_QUEUE_SIZE - 1;
		val = q->data[index];
	} else {
		val = q->data[q->rptr];
		if (++q->rptr == PS2_QUEUE_SIZE)
			q->rptr = 0;
		q->count--;
		/* reading deasserts IRQ */
		ps2->update_irq(ps2->update_arg, 0);
		/* reassert IRQs if data left */
		ps2->update_irq(ps2->update_arg, q->count != 0);
	}
	return val;
}

static void
ps2_set_ledstate(struct PS2_kbd *kbd, int ledstate)
{
	ASSERT(kbd != NULL);

	kbd->ledstate = ledstate;
	/* TODO: implement kbd_put_ledstate() */
	/* kbd_put_ledstate(ledstate); */
}

static void
ps2_reset_keyboard(struct PS2_kbd *kbd)
{
	ASSERT(kbd != NULL);

	kbd->scan_enabled = 1;
	kbd->scancode_set = 2;
	ps2_set_ledstate(kbd, 0);
}

void
ps2_write_keyboard(struct PS2_kbd *kbd, int val)
{
	ASSERT(kbd != NULL);

	switch(kbd->common.write_cmd) {
	default:
	case -1:
		switch(val) {
		case 0x00:
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			break;
		case 0x05:
			ps2_queue(&kbd->common, KBD_REPLY_RESEND);
			break;
		case KBD_CMD_GET_ID:
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			/* We emulate a MF2 AT keyboard here */
			ps2_queue(&kbd->common, KBD_REPLY_ID);
			if (kbd->translate)
				ps2_queue(&kbd->common, 0x41);
			else
				ps2_queue(&kbd->common, 0x83);
			break;
		case KBD_CMD_ECHO:
			ps2_queue(&kbd->common, KBD_CMD_ECHO);
			break;
		case KBD_CMD_ENABLE:
			kbd->scan_enabled = 1;
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			break;
		case KBD_CMD_SCANCODE:
		case KBD_CMD_SET_LEDS:
		case KBD_CMD_SET_RATE:
			kbd->common.write_cmd = val;
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			break;
		case KBD_CMD_RESET_DISABLE:
			ps2_reset_keyboard(kbd);
			kbd->scan_enabled = 0;
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			break;
		case KBD_CMD_RESET_ENABLE:
			ps2_reset_keyboard(kbd);
			kbd->scan_enabled = 1;
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			break;
		case KBD_CMD_RESET:
			ps2_reset_keyboard(kbd);
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			ps2_queue(&kbd->common, KBD_REPLY_POR);
			break;
		default:
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
			break;
		}
		break;
	case KBD_CMD_SCANCODE:
		if (val == 0) {
			if (kbd->scancode_set == 1)
				ps2_put_keycode(kbd, 0x43);
			else if (kbd->scancode_set == 2)
				ps2_put_keycode(kbd, 0x41);
			else if (kbd->scancode_set == 3)
				ps2_put_keycode(kbd, 0x3f);
		} else {
			if (val >= 1 && val <= 3)
				kbd->scancode_set = val;
			ps2_queue(&kbd->common, KBD_REPLY_ACK);
		}
		kbd->common.write_cmd = -1;
		break;
	case KBD_CMD_SET_LEDS:
		ps2_set_ledstate(kbd, val);
		ps2_queue(&kbd->common, KBD_REPLY_ACK);
		kbd->common.write_cmd = -1;
		break;
	case KBD_CMD_SET_RATE:
		ps2_queue(&kbd->common, KBD_REPLY_ACK);
		kbd->common.write_cmd = -1;
		break;
	}
}

/*
 * Set the scancode translation mode.
 * 0 = raw scancodes.
 * 1 = translated scancodes (used by qemu internally).
 */
void
ps2_keyboard_set_translation(struct PS2_kbd *kbd, int mode)
{
	ASSERT(kbd != NULL);
	kbd->translate = mode;
}

static void
ps2_mouse_send_packet(struct PS2_mouse *mouse)
{
	ASSERT(mouse != NULL);

	unsigned int b;
	int dx1, dy1, dz1;

	dx1 = mouse->mouse_dx;
	dy1 = mouse->mouse_dy;
	dz1 = mouse->mouse_dz;
	/* XXX: increase range to 8 bits ? */
	if (dx1 > 127)
		dx1 = 127;
	else if (dx1 < -127)
		dx1 = -127;
	if (dy1 > 127)
		dy1 = 127;
	else if (dy1 < -127)
		dy1 = -127;
	b = 0x08 | ((dx1 < 0) << 4) | ((dy1 < 0) << 5) | (mouse->mouse_buttons & 0x07);
	ps2_queue(&mouse->common, b);
	ps2_queue(&mouse->common, dx1 & 0xff);
	ps2_queue(&mouse->common, dy1 & 0xff);
	/* extra byte for IMPS/2 or IMEX */
	switch(mouse->mouse_type) {
	default:
		break;
	case 3:
		if (dz1 > 127)
			dz1 = 127;
		else if (dz1 < -127)
			dz1 = -127;
		ps2_queue(&mouse->common, dz1 & 0xff);
		break;
	case 4:
		if (dz1 > 7)
			dz1 = 7;
		else if (dz1 < -7)
			dz1 = -7;
		b = (dz1 & 0x0f) | ((mouse->mouse_buttons & 0x18) << 1);
		ps2_queue(&mouse->common, b);
		break;
	}

	/* update deltas */
	mouse->mouse_dx -= dx1;
	mouse->mouse_dy -= dy1;
	mouse->mouse_dz -= dz1;
}

static void
ps2_mouse_event(struct PS2_mouse *mouse,
		int dx, int dy, int dz, int buttons_state)
{
	ASSERT(mouse != NULL);

	/* check if deltas are recorded when disabled */
	if (!(mouse->mouse_status & MOUSE_STATUS_ENABLED))
		return;

	mouse->mouse_dx += dx;
	mouse->mouse_dy -= dy;
	mouse->mouse_dz += dz;
	/* XXX: SDL sometimes generates nul events: we delete them */
	if (mouse->mouse_dx == 0 &&
	    mouse->mouse_dy == 0 &&
	    mouse->mouse_dz == 0 &&
	    mouse->mouse_buttons == buttons_state)
		return;
	mouse->mouse_buttons = buttons_state;

	if (!(mouse->mouse_status & MOUSE_STATUS_REMOTE) &&
	    (mouse->common.queue.count < (PS2_QUEUE_SIZE - 16))) {
		for(;;) {
			/* if not remote, send event. Multiple events are sent
			   if too big deltas */
			ps2_mouse_send_packet(mouse);
			if (mouse->mouse_dx == 0 &&
			    mouse->mouse_dy == 0 &&
			    mouse->mouse_dz == 0)
				break;
		}
	}
}

void
ps2_mouse_fake_event(struct PS2_mouse *mouse)
{
	ASSERT(mouse != NULL);
	ps2_mouse_event(mouse, 1, 0, 0, 0);
}

void
ps2_write_mouse(struct PS2_mouse *mouse, int val)
{
	ASSERT(mouse != NULL);

	switch(mouse->common.write_cmd) {
	default:
	case -1:
		/* mouse command */
		if (mouse->mouse_wrap) {
			if (val == AUX_RESET_WRAP) {
				mouse->mouse_wrap = 0;
				ps2_queue(&mouse->common, AUX_ACK);
				return;
			} else if (val != AUX_RESET) {
				ps2_queue(&mouse->common, val);
				return;
			}
		}
		switch(val) {
		case AUX_SET_SCALE11:
			mouse->mouse_status &= ~MOUSE_STATUS_SCALE21;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_SET_SCALE21:
			mouse->mouse_status |= MOUSE_STATUS_SCALE21;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_SET_STREAM:
			mouse->mouse_status &= ~MOUSE_STATUS_REMOTE;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_SET_WRAP:
			mouse->mouse_wrap = 1;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_SET_REMOTE:
			mouse->mouse_status |= MOUSE_STATUS_REMOTE;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_GET_TYPE:
			ps2_queue(&mouse->common, AUX_ACK);
			ps2_queue(&mouse->common, mouse->mouse_type);
			break;
		case AUX_SET_RES:
		case AUX_SET_SAMPLE:
			mouse->common.write_cmd = val;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_GET_SCALE:
			ps2_queue(&mouse->common, AUX_ACK);
			ps2_queue(&mouse->common, mouse->mouse_status);
			ps2_queue(&mouse->common, mouse->mouse_resolution);
			ps2_queue(&mouse->common, mouse->mouse_sample_rate);
			break;
		case AUX_POLL:
			ps2_queue(&mouse->common, AUX_ACK);
			ps2_mouse_send_packet(mouse);
			break;
		case AUX_ENABLE_DEV:
			mouse->mouse_status |= MOUSE_STATUS_ENABLED;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_DISABLE_DEV:
			mouse->mouse_status &= ~MOUSE_STATUS_ENABLED;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_SET_DEFAULT:
			mouse->mouse_sample_rate = 100;
			mouse->mouse_resolution = 2;
			mouse->mouse_status = 0;
			ps2_queue(&mouse->common, AUX_ACK);
			break;
		case AUX_RESET:
			mouse->mouse_sample_rate = 100;
			mouse->mouse_resolution = 2;
			mouse->mouse_status = 0;
			mouse->mouse_type = 0;
			ps2_queue(&mouse->common, AUX_ACK);
			ps2_queue(&mouse->common, 0xaa);
			ps2_queue(&mouse->common, mouse->mouse_type);
			break;
		default:
			break;
		}
		break;
	case AUX_SET_SAMPLE:
		mouse->mouse_sample_rate = val;
		/* detect IMPS/2 or IMEX */
		switch(mouse->mouse_detect_state) {
		default:
		case 0:
			if (val == 200)
				mouse->mouse_detect_state = 1;
			break;
		case 1:
			if (val == 100)
				mouse->mouse_detect_state = 2;
			else if (val == 200)
				mouse->mouse_detect_state = 3;
			else
				mouse->mouse_detect_state = 0;
			break;
		case 2:
			if (val == 80)
				mouse->mouse_type = 3; /* IMPS/2 */
			mouse->mouse_detect_state = 0;
			break;
		case 3:
			if (val == 80)
				mouse->mouse_type = 4; /* IMEX */
			mouse->mouse_detect_state = 0;
			break;
		}
		ps2_queue(&mouse->common, AUX_ACK);
		mouse->common.write_cmd = -1;
		break;
	case AUX_SET_RES:
		mouse->mouse_resolution = val;
		ps2_queue(&mouse->common, AUX_ACK);
		mouse->common.write_cmd = -1;
		break;
	}
}

static void
ps2_common_reset(struct PS2 *ps2)
{
	ASSERT(ps2 != NULL);

	struct PS2_queue *q;
	ps2->write_cmd = -1;
	q = &ps2->queue;
	q->rptr = 0;
	q->wptr = 0;
	q->count = 0;
	ps2->update_irq(ps2->update_arg, 0);
}

static void
ps2_kbd_reset(struct PS2_kbd *kbd)
{
	ASSERT(kbd != NULL);

	ps2_common_reset(&kbd->common);
	kbd->scan_enabled = 0;
	kbd->translate = 0;
	kbd->scancode_set = 0;
}

static void
ps2_mouse_reset(struct PS2_mouse *mouse)
{
	ASSERT(mouse != NULL);

	ps2_common_reset(&mouse->common);
	mouse->mouse_status = 0;
	mouse->mouse_resolution = 0;
	mouse->mouse_sample_rate = 0;
	mouse->mouse_wrap = 0;
	mouse->mouse_type = 0;
	mouse->mouse_detect_state = 0;
	mouse->mouse_dx = 0;
	mouse->mouse_dy = 0;
	mouse->mouse_dz = 0;
	mouse->mouse_buttons = 0;
}

void
ps2_kbd_init(struct PS2_kbd *kbd,
	     void (*update_irq)(void *, int), void *update_arg)
{
	ASSERT(kbd != NULL && update_irq != NULL && update_arg != NULL);

	kbd->common.update_irq = update_irq;
	kbd->common.update_arg = update_arg;
	kbd->scancode_set = 2;

	ps2_kbd_reset(kbd);
}

void
ps2_mouse_init(struct PS2_mouse *mouse,
	       void (*update_irq)(void *, int), void *update_arg)
{
	ASSERT(mouse != NULL && update_irq != NULL && update_arg != NULL);

	mouse->common.update_irq = update_irq;
	mouse->common.update_arg = update_arg;

	ps2_mouse_reset(mouse);
}
