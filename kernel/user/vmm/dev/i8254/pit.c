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

#include <debug.h>
#include <gcc.h>
#include <spinlock.h>
#include <string.h>
#include <syscall.h>
#include <types.h>

#include "pit.h"
#include "../../vmm.h"
#include "../../vmm_dev.h"

#ifdef DEBUG_VPIT

#define vpit_debug(fmt...)			\
	{					\
		DEBUG(fmt);			\
	}

#else

#define vpit_debug(fmt...)			\
	{					\
	}

#endif

static void
vpit_channel_update (uint64_t now, struct vpit_channel * ch);

////////////////////////////////////////////////////////////////////////////////
//    vPIT IO lib part
////////////////////////////////////////////////////////////////////////////////
/**
 * Compute with 96 bit intermediate result: (a*b)/c
 */
static gcc_inline uint64_t
muldiv64 (uint64_t a, uint32_t b, uint32_t c)
{
    union
    {
        uint64_t ll;
        struct
        {
            uint32_t low, high;
        } l;
    } u, res;
    uint64_t rl, rh;

    u.ll = a;
    rl = (uint64_t) u.l.low * (uint64_t) b;
    rh = (uint64_t) u.l.high * (uint64_t) b;
    rh += (rl >> 32);
    res.l.high = rh / c;
    res.l.low = (((rh % c) << 32) + (rl & 0xffffffff)) / c;
    return res.ll;
}

static uint64_t
vpit_get_tsc_by_channel (struct vpit* vpit, unsigned int ch)
{
    uint64_t tsc;

    switch (ch)
    {
    case 0:
        tsc = vdev_guest_tsc (vpit->vdev);
        break;
    case 1:
    case 2:
        tsc = rdtsc ();
        break;
    default:
        tsc = 0;
        PANIC("Invalid PIT channel %x.\n", ch);
    }

    return tsc;
}

/*
 * Get the remaining numbers to count before OUT changes.
 */
static int32_t
vpit_get_count (struct vpit_channel *ch)
{
    ASSERT(ch != NULL);
    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    uint64_t d, count, tsc;
    int32_t counter = 0;
    uint16_t d0, d1;

    tsc = vpit_get_tsc_by_channel (ch->pit, ch->id);

    d = muldiv64 (tsc - ch->count_load_time, PIT_FREQ, ch->pit->guest_cpufreq);
    count = (uint64_t) (uint32_t) ch->count;

    switch (ch->mode)
    {
    case PIT_CHANNEL_MODE_0:
    case PIT_CHANNEL_MODE_1:
    case PIT_CHANNEL_MODE_4:
    case PIT_CHANNEL_MODE_5:
        /* mode 0, 1, 4 and 5 are not repeated */
        if (count > d)
            counter = (count - d) & 0xffff;
        else
            counter = 0;
        break;
    case PIT_CHANNEL_MODE_3:
        /*
         * mode 3: high for N/2, low for N/2, when N is even;
         *         high for (N+1)/2, low for (N-1)/2, when N is odd
         */
        if (count % 2 == 0)
            counter = count - ((2 * d) % count);
        else
        {
            d0 = d % count;
            d1 = (count + 1) / 2;
            if (d0 < d1)
                counter = d1 - d0;
            else
                counter = d0 - d1;
        }
        break;
    case PIT_CHANNEL_MODE_2:
        counter = count - (d % count);
        break;

    default:
        PANIC("Invalid PIT channel mode %x.\n", ch->mode);
    }
    ASSERT(counter >= 0 && counter <= count);
    return counter;
}

/*
 * Get PIT output bit.
 */
static int
vpit_get_out (struct vpit_channel *ch, uint64_t current_time)
{
    ASSERT(ch != NULL);
    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    uint64_t d, count;
    int out = 0;

    d = muldiv64 (current_time - ch->count_load_time, PIT_FREQ,
                  ch->pit->guest_cpufreq);
    count = (uint64_t) (uint32_t) ch->count;
    switch (ch->mode)
    {
    case PIT_CHANNEL_MODE_0:
        out = (d >= count);
        break;
    case PIT_CHANNEL_MODE_1:
        out = (d < count);
        break;
    case PIT_CHANNEL_MODE_2:
        if ((d % count) == 0 && d != 0)
            out = 1;
        else
            out = 0;
        break;
    case PIT_CHANNEL_MODE_3:
        out = (d % count) < ((count + 1) >> 1);
        break;
    case PIT_CHANNEL_MODE_4:
    case PIT_CHANNEL_MODE_5:
        out = (d == count);
        break;

    default:
        PANIC("Invalid PIT channel mode %x.\n", ch->mode);
    }
    return out;
}

/*
 * Get the time of next OUT change. If no OUT change will happen, valid will be
 * FALSE.
 */
static uint64_t
vpit_get_next_transition_time (struct vpit_channel *ch, uint64_t current_time,
                               bool *valid)
{
    ASSERT(ch != NULL);
    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    uint64_t d, count, next_time = 0, base;
    int period2;

    d = muldiv64 (current_time - ch->count_load_time,
    PIT_FREQ,
                  ch->pit->guest_cpufreq);
    count = (uint64_t) (uint32_t) ch->count;
    *valid = TRUE;
    switch (ch->mode)
    {
    case PIT_CHANNEL_MODE_0:
    case PIT_CHANNEL_MODE_1:
        if (d < count)
            next_time = count;
        else
        {
            *valid = FALSE;
            return -1;
        }
        break;
    case PIT_CHANNEL_MODE_2:
        base = (d / count) * count;
        if ((d - base) == 0 && d != 0)
            next_time = base + count;
        else
            next_time = base + count + 1;
        break;
    case PIT_CHANNEL_MODE_3:
        base = (d / count) * count;
        period2 = ((count + 1) >> 1);
        if ((d - base) < period2)
            next_time = base + period2;
        else
            next_time = base + count;
        break;
    case PIT_CHANNEL_MODE_4:
    case PIT_CHANNEL_MODE_5:
        if (d < count)
            next_time = count;
        else if (d == count)
            next_time = count + 1;
        else
        {
            *valid = FALSE;
            return -1;
        }
        break;

    default:
        PANIC("Invalid PIT channel mode %x.\n", ch->mode);
    }
    /* convert to timer units */
    next_time = ch->count_load_time
            + muldiv64 (next_time, ch->pit->guest_cpufreq, PIT_FREQ);
    /* fix potential rounding problems */
    /* XXX: better solution: use a clock at PIT_FREQ Hz */
    if (next_time <= current_time)
        next_time = current_time + 1;
    return next_time;
}

static void
vpit_set_gate (struct vpit *pit, int channel, int val)
{
    ASSERT(pit != NULL);
    ASSERT(0 <= channel && channel < 3);
    ASSERT(val == 0 || val == 1);

    struct vpit_channel *ch = &pit->channels[channel];
    uint64_t load_time;

    load_time = vpit_get_tsc_by_channel (pit, channel);

    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    switch (ch->mode)
    {
    case 0:
    case 4:
        /* XXX: just disable/enable counting */
        break;
    case 1:
    case 5:
        if (ch->gate < val)
        {
            /* restart counting on rising edge */
            ch->count_load_time = load_time;
            vpit_channel_update (ch->count_load_time, ch);
        }
        break;
    case 2:
    case 3:
        if (ch->gate < val)
        {
            /* restart counting on rising edge */
            ch->count_load_time = load_time;
            vpit_channel_update (ch->count_load_time, ch);
        }
        /* XXX: disable/enable counting */
        break;

    default:
        PANIC("Invalid PIT channel mode %x.\n", ch->mode);
    }
    ch->gate = val;
}

static int
vpit_get_gate (struct vpit *pit, int channel)
{
    ASSERT(pit != NULL);
    ASSERT(0 <= channel && channel < 3);

    struct vpit_channel *ch = &pit->channels[channel];

    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    return ch->gate;
}

static int32_t
vpit_get_initial_count (struct vpit *pit, int channel)
{
    ASSERT(pit != NULL);
    ASSERT(0 <= channel && channel < 3);

    struct vpit_channel *ch = &pit->channels[channel];

    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    return ch->count;
}

static int
vpit_get_mode (struct vpit *pit, int channel)
{
    ASSERT(pit != NULL);
    ASSERT(0 <= channel && channel < 3);

    struct vpit_channel *ch = &pit->channels[channel];

    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    return ch->mode;
}

static void
vpit_load_count (struct vpit_channel *ch, uint16_t val)
{
    ASSERT(ch != NULL);
    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    uint64_t now;

    // update count
    if (val == 0)
    {
        ch->count = 0x10000;
    }
    else
    {
        ch->count = (uint32_t) val;
    }

    // update count load time
    now = vpit_get_tsc_by_channel (ch->pit, ch->id);
    ch->count_load_time = now;

    ch->enabled = TRUE;

    // update channel
    vpit_debug("[%llx] Set counter: %x.\n", ch->count_load_time, ch->count);
    vpit_channel_update (ch->count_load_time, ch);
}

static void
vpit_latch_count (struct vpit_channel *ch)
{
    ASSERT(ch != NULL);
    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    if (!ch->count_latched)
    {
        ch->latched_count = vpit_get_count (ch);
        ch->count_latched = ch->rw_mode;
    }
}

////////////////////////////////////////////////////////////////////////////////
//    vPIT IO read part
////////////////////////////////////////////////////////////////////////////////
static gcc_inline int
vpit_ioport_read_latched_status (struct vpit_channel* ch)
{
    /* read latched status byte */
    vpit_debug("Read status of channel %d: %x.\n", ch->id, ch->status);
    ch->status_latched = 0;
    return ch->status;
}

static gcc_inline int
vpit_ioport_read_latched_count (struct vpit_channel* ch)
{
    int ret;
    /* read latched count */
    switch (ch->count_latched)
    {
    case PIT_RW_STATE_LSB:
        /* read LSB only */
        vpit_debug("Read LSB from channel %d: %x.\n", ch->id,
                   ch->latched_count & 0xff)
        ;
        ret = ch->latched_count & 0xff;
        ch->count_latched = 0;
        break;

    case PIT_RW_STATE_MSB:
        /* read MSB only */
        vpit_debug("Read MSB from channel %d: %x.\n", ch->id,
                   ch->latched_count >> 8)
        ;
        ret = ch->latched_count >> 8;
        ch->count_latched = 0;
        break;

    case PIT_RW_STATE_WORD0:
        /* read LSB first */
        vpit_debug("Read LSB from channel %d: %x.\n", ch->id,
                   ch->latched_count & 0xff)
        ;
        ret = ch->latched_count & 0xff;
        ch->count_latched = PIT_RW_STATE_MSB;
        break;

    default:
        ret = 0;
        PANIC("Invalid read state %x of counter %x.\n", ch->count_latched,
              ch->id);
    }
    return ret;
}

static gcc_inline int
vpit_ioport_read_count (struct vpit_channel* ch)
{
    int count, ret;
    /* read un-latched count */
    switch (ch->read_state)
    {
    case PIT_RW_STATE_LSB:
        count = vpit_get_count (ch);
        ret = count & 0xff;
        vpit_debug("Read LSB from channel %d: %x.\n", ch->id, ret)
        ;
        break;

    case PIT_RW_STATE_MSB:
        count = vpit_get_count (ch);
        ret = (count >> 8) & 0xff;
        vpit_debug("Read MSB from channel %d: %x.\n", ch->id, ret)
        ;
        break;

    case PIT_RW_STATE_WORD0:
        count = vpit_get_count (ch);
        ret = count & 0xff;
        vpit_debug("Read LSB from channel %d: %x.\n", ch->id, ret)
        ;
        ch->read_state = PIT_RW_STATE_WORD1;
        break;

    case PIT_RW_STATE_WORD1:
        count = vpit_get_count (ch);
        ret = (count >> 8) & 0xff;
        vpit_debug("Read MSB from channel %d: %x.\n", ch->id, ret)
        ;
        ch->read_state = PIT_RW_STATE_WORD0;
        break;

    default:
        ret = 0;
        PANIC("Invalid read state %x of counter %x.\n", ch->read_state, ch->id);
    }
    return ret;
}

/*
 * Read I/O port 0x61.
 *
 * XXX: I/O port 0x61 has multiple functions, including setting up the speakers
 *      and setting up GATE of i8254 channel 2. CertiKOS only simulates the GATE
 *      setup function, and ignores all speaker setup requests (and does not
 *      pass requests to the physical hardware).
 */
static uint8_t
vpit_ioport_read_gate (struct vpit *pit)
{
    ASSERT(pit != NULL);

    struct vpit_channel *ch = &pit->channels[2];

    uint64_t now = vpit_get_tsc_by_channel (pit, 2);

    spinlock_acquire (&ch->lk);
    uint8_t ret = (vpit_get_out (ch, now) << 5) | vpit_get_gate (pit, 2);
    spinlock_release (&ch->lk);

    vpit_debug("[%llx] Read GATE of channel 2: %x\n", now, ret);

    return ret;
}

static uint8_t
vpit_ioport_read (struct vpit *pit, uint16_t port)
{
    ASSERT(pit != NULL);
    ASSERT(port == PIT_CHANNEL0_PORT || port == PIT_CHANNEL1_PORT || port == PIT_CHANNEL2_PORT || port == PIT_GATE_PORT);

    int ret = 0;
    int channel = port - PIT_CHANNEL0_PORT;
    struct vpit_channel *ch = &pit->channels[channel];

    switch (port)
    {
    case PIT_CHANNEL0_PORT:
    case PIT_CHANNEL1_PORT:
    case PIT_CHANNEL2_PORT:
        spinlock_acquire (&ch->lk);
        /* if status is latched, next read will be always status */
        if (ch->status_latched)
        {
            ret = vpit_ioport_read_latched_status (ch);
        }
        else if (ch->count_latched)
        { /* read latched count */
            ret = vpit_ioport_read_latched_count (ch);
        }
        else
        { /* read un-latched count */
            ret = vpit_ioport_read_count (ch);
        }
        spinlock_release (&ch->lk);
        break;

    case PIT_GATE_PORT:
        ret = vpit_ioport_read_gate (pit);
    }

    return ret;
}

////////////////////////////////////////////////////////////////////////////////
//    vPIT IO write part
////////////////////////////////////////////////////////////////////////////////
static void
vpit_ioport_write_channel_count (uint8_t data, int channel, struct vpit* pit)
{
    /* i8254 Channel Ports */
    struct vpit_channel *ch = &pit->channels[channel];

    spinlock_acquire (&ch->lk);

    switch (ch->write_state)
    {
    case PIT_RW_STATE_LSB:
        /* load LSB only */
        vpit_debug("Load LSB to channel %d: %x.\n", channel, data)
        ;
        vpit_load_count (ch, data);
        break;

    case PIT_RW_STATE_MSB:
        /* load MSB only */
        vpit_debug("Load MSB to channel %d: %x.\n", channel, data)
        ;
        vpit_load_count (ch, data << 8);
        break;

    case PIT_RW_STATE_WORD0:
        /* load LSB first */
        vpit_debug("Load LSB to channel %d: %x.\n", channel, data)
        ;
        ch->write_latch = data;
        ch->write_state = PIT_RW_STATE_WORD1;
        break;

    case PIT_RW_STATE_WORD1:
        /* load MSB then */
        vpit_debug("Load MSB to channel %d: %x.\n", channel, data)
        ;
        vpit_load_count (ch, ch->write_latch | (data << 8));
        ch->write_state = PIT_RW_STATE_WORD0;
        break;

    default:
        PANIC("Invalid write state %x of counter %x.\n", ch->write_state,
              channel);
    }

    spinlock_release (&ch->lk);
}

static void
vpit_ioport_write_readback (uint8_t data, struct vpit* pit)
{
    // D0 is always 0
    ASSERT(!(data & 0x1));
    ASSERT(pit != NULL);

    bool is_latch_count = PIT_READBACK_IS_LATCH_COUNT(data);
    bool is_latch_status = PIT_READBACK_IS_LATCH_STATUS(data);
    unsigned int i;
    for (i = 0u; i < 3u; i++)
    {
        // select D1, D2 and D3
        if ((data & (2 << i)) == 0)
        {
            continue;
        }

        struct vpit_channel *ch = &pit->channels[i];

        spinlock_acquire (&ch->lk);
        /* latch count */
        if (is_latch_count)
        {
            vpit_debug("Latch counter of channel %d.\n", i);
            vpit_latch_count (ch);
        }

        /* latch status */
        if (is_latch_status)
        {
            vpit_debug("Latch status of channel %d.\n", i);

            /* only latch once */
            if (ch->status_latched)
            {
                spinlock_release (&ch->lk);
                continue;
            }

            int out = vpit_get_out (ch, vpit_get_tsc_by_channel (pit, i));

            ch->status = (out << 7) | (ch->rw_mode << 4) | (ch->mode << 1)
                    | ch->bcd;
            ch->status_latched = 1;
        }
        spinlock_release (&ch->lk);
    }
}

void
vpit_ioport_write_channel_control_write_op (int rw, uint8_t data,
                                            struct vpit_channel* ch)
{
    ASSERT(rw != 0);
    vpit_debug("Set channel %d: RW=%x, Mode=%x.\n", ch->id, rw,
               PIT_CONTROL_MODE(data));

    spinlock_acquire (&ch->lk);
    ch->rw_mode = rw;
    ch->read_state = rw;
    ch->write_state = rw;
    ch->mode = PIT_CONTROL_MODE(data);
    ch->bcd = PIT_CONTROL_BCD(data);
    /* XXX: need to update irq timer? */
    spinlock_release (&ch->lk);
}

static void
vpit_ioport_write_channel_control (uint8_t data, struct vpit* pit, int channel)
{
    struct vpit_channel *ch = &pit->channels[channel];
    int rw = PIT_CONTROL_READ_WRITE(data); /* get RW1,RW0 */

    if (rw == PIT_CONTROL_LATCH_CMD)
    {
        spinlock_acquire (&ch->lk);
        vpit_latch_count (ch);
        spinlock_release (&ch->lk);
    }
    else
    {
        vpit_ioport_write_channel_control_write_op (rw, data, ch);
    }
}

static void
vpit_ioport_write_control (uint8_t data, struct vpit* pit)
{
    /* XXX: not suuport BCD yet */
    if (PIT_CONTROL_BCD(data) == PIT_CONTROL_BCD_ENABLED)
        PANIC("PIT not support BCD yet.\n");

    int channel = PIT_CONTROL_SELECT_CHANNEL(data);
    switch (channel)
    {
    case PIT_CONTROL_SC_0:
    case PIT_CONTROL_SC_1:
    case PIT_CONTROL_SC_2:
        vpit_ioport_write_channel_control (data, pit, channel);
        break;

    case PIT_CONTROL_SC_READBACK:
        vpit_ioport_write_readback (data, pit);
        break;
    default:
        PANIC("Invalid channel number %d.\n", channel);
    }
}

/*
 * Write I/O port 0x61.
 *
 * XXX: I/O port 0x61 has multiple functions, including setting up the speakers
 *      and setting up GATE of i8254 channel 2. CertiKOS only simulates the GATE
 *      setup function, and ignores all speaker setup requests (and does not
 *      pass the requests to the physical hardware).
 */
static void
vpit_ioport_write_gate (uint8_t data, struct vpit *pit)
{
    ASSERT(pit != NULL);

    spinlock_acquire (&pit->channels[2].lk);
    vpit_set_gate (pit, 2, data & 0x1);
    spinlock_release (&pit->channels[2].lk);
}

static void
vpit_ioport_write (struct vpit *pit, uint16_t port, uint8_t data)
{
    ASSERT(pit != NULL);
    ASSERT(port == PIT_CHANNEL0_PORT || port == PIT_CHANNEL1_PORT || port == PIT_CHANNEL2_PORT || port == PIT_CONTROL_PORT || port == PIT_GATE_PORT);

    switch (port)
    {
    case PIT_CHANNEL0_PORT:
    case PIT_CHANNEL1_PORT:
    case PIT_CHANNEL2_PORT:
        vpit_ioport_write_channel_count (data, port - PIT_CHANNEL0_PORT, pit);
        break;
    case PIT_CONTROL_PORT:
        vpit_ioport_write_control (data, pit);
        break;

    case PIT_GATE_PORT: // does not be fully supported
        vpit_ioport_write_gate (data, pit);
        break;

    default:
        PANIC("Invalid out port %d.\n", port);
    }
}

////////////////////////////////////////////////////////////////////////////////
//    vPIT update part
////////////////////////////////////////////////////////////////////////////////
static uint64_t gcc_inline
vpit_get_expire_time (struct vpit_channel *ch)
{
    uint64_t expire;
    uint64_t count = (uint64_t) ch->count;

    switch (ch->mode)
    {
    case PIT_CHANNEL_MODE_0:
    case PIT_CHANNEL_MODE_1:
    case PIT_CHANNEL_MODE_2:
    case PIT_CHANNEL_MODE_3:
        expire = ch->count_load_time
                + muldiv64 (count, ch->pit->guest_cpufreq, PIT_FREQ);
        break;
    case PIT_CHANNEL_MODE_4:
    case PIT_CHANNEL_MODE_5:
        expire = ch->count_load_time
                + muldiv64 (count + 1, ch->pit->guest_cpufreq, PIT_FREQ);
        break;

    default:
        expire = 0;
        PANIC("Invalid PIT channle mode %x.\n", ch->mode);
    }

    return expire;
}

void
vpit_reset_counter_one_shot (uint64_t now, uint64_t expire,
                             struct vpit_channel* ch)
{
    if (now >= expire)
        ch->enabled = FALSE;
    else
        ch->enabled = TRUE;
}

void
vpit_reset_counter_perodic (uint64_t count, uint64_t now, uint64_t expire,
                            struct vpit_channel* ch)
{
    if (now >= expire)
    {
        uint64_t d = now - expire;
        uint64_t cycle = muldiv64 (count, ch->pit->guest_cpufreq, PIT_FREQ);
        d /= cycle;
        ch->count_load_time += muldiv64 (count * (d + 1),
                                         ch->pit->guest_cpufreq,
                                         PIT_FREQ);
    }
    ch->enabled = TRUE;
}

/**
 * Trigger virtual IRQ 0 to inform guest OS.
 */
void
vpit_channel_trigger_irq (uint64_t now, uint64_t expire,
                          struct vpit_channel* ch)
{
    ASSERT(ch->enabled == TRUE);
    ASSERT(expire <= now);

    if (ch->last_intr_time_valid == FALSE || ch->last_intr_time < expire)
    {
        ch->last_intr_time_valid = TRUE;
        ch->last_intr_time = expire;

        vpit_debug("Trigger IRQ_TIMER.\n");
        vdev_set_irq (ch->pit->vdev, IRQ_TIMER, 2);
    }
}

static void
vpit_channel_reset_counter (uint64_t now, uint64_t expire,
                            struct vpit_channel* ch)
{
    ASSERT(expire <= now);
    ASSERT(ch != NULL);

    /*
     *  Reload counter if necessary.
     */
    uint64_t count = (uint64_t) ch->count;

    switch (ch->mode)
    {
    // one shot
    case PIT_CHANNEL_MODE_0:
    case PIT_CHANNEL_MODE_1:
    case PIT_CHANNEL_MODE_4:
    case PIT_CHANNEL_MODE_5:
        vpit_reset_counter_one_shot (now, expire, ch);
        break;

        // periodic
    case PIT_CHANNEL_MODE_2:
    case PIT_CHANNEL_MODE_3:
        vpit_reset_counter_perodic (count, now, expire, ch);
        break;

    default:
        PANIC("Invalid PIT channel mode 0x%x.\n", ch->mode);
    }
}

/**
 * Check for timer interrupt.
 * XXX: The trigger of the timer interrupt is asynchronous to the
 *      counter, i.e. the timer interrupt maybe triggered in an
 *      underminated period after the counter countdowns to zero.
 *      Only when this function is called at higher freqency than
 *      i8254, it could be possible to trigger the synchronous timer
 *      interrupt. Therefore, the virtualized PIT is suitable for
 *      those operating systems who count the number of timer interrupt
 *      to get the time.
 *
 * +  : The timer interrupt now is triggered by local APIC, which has
 *      a period of 1ms.
 */
static void
vpit_channel_update (uint64_t now, struct vpit_channel *ch)
{
    ASSERT(ch != NULL);
    ASSERT(spinlock_holding (&ch->lk) == TRUE);

    uint64_t expire = vpit_get_expire_time (ch);

    if (now >= expire)
    {
        // trigger time IRQ
        vpit_channel_trigger_irq (now, expire, ch);

        // reset counter
        vpit_channel_reset_counter (now, expire, ch);

        vpit_debug("vpit_channel_update() done.\n");
    }
}

void
vpit_update (struct vpit* vpit)
{
    unsigned int i;
    for (i = 0u; i < 3u; i++)
    {
        struct vpit_channel *ch = &vpit->channels[i];
        if (ch->enabled == FALSE)
        {
            continue;
        }

        uint64_t tsc = vpit_get_tsc_by_channel (vpit, i);
        spinlock_acquire (&ch->lk);
        if (ch->enabled == TRUE) // make sure that channel is still enabled
        {
            vpit_channel_update (tsc, ch);
        }
        spinlock_release (&ch->lk);
    }
}

////////////////////////////////////////////////////////////////////////////////
//    vPIT vdev framework adapting part
////////////////////////////////////////////////////////////////////////////////

static int
_vpit_ioport_read (void *opaque, uint16_t port, data_sz_t width, void *data)
{
    struct vpit *pit = (struct vpit *) opaque;

    if (pit == NULL || data == NULL)
        return 1;

    if (port != PIT_CONTROL_PORT && port != PIT_CHANNEL0_PORT
            && port != PIT_CHANNEL1_PORT && port != PIT_CHANNEL2_PORT
            && port != PIT_GATE_PORT)
        return 2;

    *(uint8_t *) data = vpit_ioport_read (pit, port);

    vpit_debug("Read: port=%x, data=%x.\n", port, *(uint8_t *) data);
    return 0;
}

static int
_vpit_ioport_write (void *opaque, uint16_t port, data_sz_t width, uint32_t data)
{
    struct vpit *pit = (struct vpit *) opaque;

    if (pit == NULL)
        return 1;

    if (port != PIT_CONTROL_PORT && port != PIT_CHANNEL0_PORT
            && port != PIT_CHANNEL1_PORT && port != PIT_CHANNEL2_PORT
            && port != PIT_GATE_PORT)
        return 2;

    vpit_debug("Write: port=%x, data=%x.\n", port, (uint8_t) data);

    vpit_ioport_write (pit, port, data);

    return 0;
}

static int
_vpit_sync (void *opaque)
{
    struct vpit *pit = (struct vpit *) opaque;

    vpit_update (pit);
    return 0;
}

static int
vpit_register_ioport (struct vpit *vpit, uint16_t port)
{

    return vdev_register_ioport (vpit->vdev, vpit, port, _vpit_ioport_read,
                                 _vpit_ioport_write);
}

int
vpit_init (struct vdev *vdev, void *opaque, uint64_t cpufreq)
{
    if (vdev == NULL || opaque == NULL)
        return -1;

    struct vpit *vpit = (struct vpit *) opaque;

    memset (vpit, 0, sizeof(struct vpit));

    /* initialize channle 0 */
    spinlock_init (&vpit->channels[0].lk);
    vpit->channels[0].id = 0;
    vpit->channels[0].pit = vpit;
    vpit->channels[0].enabled = FALSE;
    vpit->channels[0].last_intr_time_valid = FALSE;

    /* initialize channel 1 */
    spinlock_init (&vpit->channels[1].lk);
    vpit->channels[1].id = 1;
    vpit->channels[1].pit = vpit;
    vpit->channels[1].enabled = FALSE;
    vpit->channels[1].last_intr_time_valid = FALSE;

    /* initialize channel 2 */
    spinlock_init (&vpit->channels[2].lk);
    vpit->channels[2].id = 2;
    vpit->channels[2].pit = vpit;
    vpit->channels[2].enabled = FALSE;
    vpit->channels[2].last_intr_time_valid = FALSE;

    vpit->guest_cpufreq = cpufreq;
    vpit->vdev = vdev;

    /* register virtualized device (handlers of I/O ports & IRQ) */
    if (vpit_register_ioport (vpit, PIT_CONTROL_PORT)
            || vpit_register_ioport (vpit, PIT_CHANNEL0_PORT)
            || vpit_register_ioport (vpit, PIT_CHANNEL1_PORT)
            || vpit_register_ioport (vpit, PIT_CHANNEL2_PORT)
            || vpit_register_ioport (vpit, PIT_GATE_PORT)
            || vdev_register_update (vdev, opaque, _vpit_sync))
    {
        return -2;
    }

    return 0;
}

