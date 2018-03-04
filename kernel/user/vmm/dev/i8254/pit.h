/*
 * QEMU 8253/8254 interval timer emulation
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

#ifndef _VDEV_8254_H_
#define _VDEV_8254_H_

#include <spinlock.h>
#include <types.h>

#include "../../vmm_dev.h"

/* virtualized i8254 */

#define PIT_FREQ	1193182
#define IRQ_TIMER	0
/**
 *  i8254 Control Port
 *
 * data - xx control word
 *      \ 11 read back command
 *
 * Control word format:
 * +-----+-----+-----+-----+----+----+----+-----+
 * | SC1 | SC0 | RW1 | RW0 | M2 | M1 | M0 | BCD |
 * +-----+-----+-----+-----+----+----+----+-----+
 *      7|    6|    5|    4|   3|   2|   1|    0|
 *
 * SC1,SC0: 00 - select counter 0
 *          01 - select counter 1
 *          10 - select counter 2
 *          11 - read-back command
 * RW1,RW0: 00 - counter latch command
 *          01 - read/write least significant byte only
 *          10 - read/write most significant byte only
 *          11 - read/write least significant byte first, then
 *               most significant byte
 * M2,M1,M0: 000 - mode 0
 *           001 - mode 1
 *           _10 - mode 2
 *           _11 - mode 3
 *           100 - mode 4
 *           101 - mode 5
 * BSD: 0 - binary counter 16-bits
 *      1 - binary coded decimal (BCD) counter
 *
 *
 * Read-back command format:
 * +----+----+----+----+----+----+----+----+
 * | D7 | D6 | D5 | D4 | D3 | D2 | D1 | D0 |
 * +----+----+----+----+----+----+----+----+
 *
 * D7,D6: always 11
 * D5: 0 - latch count of the selected counter(s), 1 - do not latch
 * D4: 0 - latch status of the selected counter(s), 1 - do not latch
 * D3: 1 - select counter 2
 * D2: 1 - select counter 1
 * D1: 1 - select counter 0
 * D0: always 0
 *
 *
 * Status byte format:
 * +--------+------------+-----+-----+----+----+----+-----+
 * | Output | NULL Count | RW1 | RW0 | M2 | M1 | M0 | BCD |
 * +--------+------------+-----+-----+----+----+----+-----+
 *
 * Output: 1 - out pin is 1
 *         0 - out pin is 0
 * NULL Count: 1 - null count
 *             0 - count available for reading
 * RW1,RW0,M2,M1,BCD: see "Control word format" above
 */

#define PIT_CONTROL_SELECT_CHANNEL(q)   (((q) >> 6) & 0x3)
# define PIT_CONTROL_SC_0     0x0
# define PIT_CONTROL_SC_1     0x1
# define PIT_CONTROL_SC_2     0x2
# define PIT_CONTROL_SC_READBACK     0x3

#define PIT_CONTROL_READ_WRITE(q)       (((q) >> 4) & 0x3)
# define PIT_CONTROL_LATCH_CMD     0x0
# define PIT_CONTROL_RW_LSB   0x1
# define PIT_CONTROL_RW_MSB   0x2
# define PIT_CONTROL_RW_BOTH  0x3

#define PIT_CONTROL_MODE(q)             (((q) >> 1) & 0x7)
# define PIT_CONTROL_MODE_0   0x0
# define PIT_CONTROL_MODE_1   0x1
# define PIT_CONTROL_MODE_2A  0x2
# define PIT_CONTROL_MODE_2B  0x6
# define PIT_CONTROL_MODE_3A  0x3
# define PIT_CONTROL_MODE_3B  0x7
# define PIT_CONTROL_MODE_4   0x4
# define PIT_CONTROL_MODE_5   0x5
#define PIT_CONTROL_IS_MODE_2(q)        ((((q) >> 1) & 0x3) == 0x2)
#define PIT_CONTROL_IS_MODE_3(q)        ((((q) >> 1) & 0x3) == 0x3)

#define PIT_CONTROL_BCD(q)              ((q) & 0x1)
# define PIT_CONTROL_BCD_ENABLED  0x1
# define PIT_CONTROL_BCD_DISABLED 0x0

#define PIT_READBACK_LATCH_COUNT_ENABLED     0
#define PIT_READBACK_LATCH_COUNT_DISABLED    0x20
#define PIT_READBACK_IS_LATCH_COUNT(q)       (!((q) & 0x20))

#define PIT_READBACK_LATCH_STATUS_ENABLED    0
#define PIT_READBACK_LATCH_STATUS_DISABLED   0x10
#define PIT_READBACK_IS_LATCH_STATUS(q)      (!((q) & 0x10))

#define PIT_READBACK_LATCH_SC_2             0x8
#define PIT_READBACK_LATCH_SC_1             0x4
#define PIT_READBACK_LATCH_SC_0             0x2


#define PIT_CHANNEL_MODE_0  0   /* interrupt on terminal count */
#define PIT_CHANNEL_MODE_1  1   /* hardware retriggerable one-shot */
#define PIT_CHANNEL_MODE_2  2   /* rate generator */
#define PIT_CHANNEL_MODE_3  3   /* square wave mode */
#define PIT_CHANNEL_MODE_4  4   /* software triggered strobe */
#define PIT_CHANNEL_MODE_5  5   /* hardware triggered strobe */

#define PIT_RW_STATE_LSB    1
#define PIT_RW_STATE_MSB    2
#define PIT_RW_STATE_WORD0  3
#define PIT_RW_STATE_WORD1  4

#define PIT_CHANNEL0_PORT   0x40
#define PIT_CHANNEL1_PORT   0x41
#define PIT_CHANNEL2_PORT   0x42
#define PIT_CONTROL_PORT    0x43
#define PIT_GATE_PORT       0x61

struct vpit;

/* structures of i8254 counter channles */
struct vpit_channel
{
    spinlock_t lk;
    struct vpit *pit;

    uint8_t id;

    int32_t count; /* XXX: valid value range 0x0 ~ 0x10000 */
    uint16_t latched_count;
    uint8_t count_latched;
    uint8_t status_latched;
    uint8_t status;
    uint8_t read_state;
    uint8_t write_state;
    uint8_t write_latch;
    uint8_t rw_mode;
    uint8_t mode;
    uint8_t bcd; /* XXX: not implemented yet  */
    uint8_t gate;
    uint64_t count_load_time;

    uint64_t last_intr_time;
    bool last_intr_time_valid;

    bool enabled;
};

/* structure of the virtualized i8254 */
struct vpit
{
    struct vpit_channel channels[3];
   	uint64_t		guest_cpufreq;
	struct vdev		*vdev;
};

int vpit_init(struct vdev *vdev, void *opaque, uint64_t cpufreq);

#endif /* !_VDEV_8254_H_ */
