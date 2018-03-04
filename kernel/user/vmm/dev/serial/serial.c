#include <debug.h>
#include <syscall.h>
#include <types.h>
#include <x86.h>

#include "serial.h"
#include "../../vmm_dev.h"

#define COM1		0x3F8
#define COM2		0x2F8
#define COM3		0x3E8
#define COM4		0x2E8

#define COM_RX		0	// In:	Receive buffer (DLAB=0)
#define COM_TX		0	// Out: Transmit buffer (DLAB=0)
#define COM_DLL		0	// Out: Divisor Latch Low (DLAB=1)
#define COM_DLM		1	// Out: Divisor Latch High (DLAB=1)
#define COM_IER		1	// Out: Interrupt Enable Register
#define COM_IER_RDI	0x01	//   Enable receiver data interrupt
#define COM_IER_THRI	0x02	//   Enable transmitter holding register empty interrupt
#define COM_IER_RLSI	0x04	//   Enable receiver line status interrupt
#define COM_IER_MSI	0x08	//   Enable modem status interrupt
#define COM_IIR		2	// In:	Interrupt ID Register
#define COM_IIR_NOINT	0x01	//   No pending interrupts
#define COM_IIR_MASK	0x06	//   Mask of interrupt state
#define COM_IIR_MSI	0x00	//   Modem status interrupt
#define COM_IIR_THRI	0x02	//   Transmitter holding register empty interrupt
#define COM_IIR_RDI	0x04	//   Received data available interrupt
#define COM_IIR_RLSI	0x06	//   Receiver line status interrupt
#define COM_FCR		2	// Out: FIFO Control Register
#define COM_LCR		3	// Out: Line Control Register
#define	COM_LCR_DLAB	0x80	//   Divisor latch access bit
#define	COM_LCR_WLEN8	0x03	//   Wordlength: 8 bits
#define COM_MCR		4	// Out: Modem Control Register
#define	COM_MCR_RTS	0x02	// RTS complement
#define	COM_MCR_DTR	0x01	// DTR complement
#define	COM_MCR_OUT2	0x08	// Out2 complement
#define COM_LSR		5	// In:	Line Status Register
#define COM_LSR_DATA	0x01	//   Data available
#define COM_LSR_TXRDY	0x20	//   Transmit buffer avail
#define COM_LSR_TSRE	0x40	//   Transmitter off
#define COM_MSR		6	// In: Modem Status Register
#define COM_SRR		7	// In: Shadow Receive Register

#define IRQ_SERIAL13	4

static int
vserial_read_ioport(void *dev, uint16_t port, data_sz_t width, void *val)
{
	if (!(0x3f8 <= port && port <= 0x3ff))
		return -1;

	struct vserial *com = dev;

	if (port == COM1+COM_IIR && com->iir_valid == 1) {
		*(uint8_t *) val = com->iir;
		com->iir_valid = 0;
		return 0;
	}

	if (width == SZ8)
		*(uint8_t *) val = inb(port);
	else if (width == SZ16)
		*(uint16_t *) val = inw(port);
	else
		*(uint32_t *) val = inl(port);

	return 0;
}

static int
vserial_write_ioport(void *dev, uint16_t port, data_sz_t width, uint32_t val)
{
	if (!(0x3f8 <= port && port <= 0x3ff))
		return -1;

	if (width == SZ8)
		outb(port, (uint8_t) val);
	else if (width == SZ16)
		outb(port, (uint16_t) val);
	else
		outb(port, val);

	return 0;
}

static int
vserial_update(void *dev)
{
	if (dev == NULL)
		return -1;

	uint8_t iir, ier, intr;
	struct vserial *com = dev;

	/* if (sys_read_ioport(COM1+COM_LSR, SZ8, &lsr)) */
	/* 	return -2; */

	/* if (lsr & COM_LSR_DATA) { */
	/* 	vdev_set_irq(com->vdev, IRQ_SERIAL13, 2); */
	/* 	return 0; */
	/* } */

	iir = inb(COM1 + COM_IIR);

	if (iir & COM_IIR_NOINT)
		return 0;

	ier = inb(COM1 + COM_IER);
	intr = iir & COM_IIR_MASK;

	if (((intr & COM_IIR_MSI) && (ier & COM_IER_MSI)) ||
	    ((intr & COM_IIR_THRI) && (ier & COM_IER_THRI)) ||
	    ((intr & COM_IIR_RDI) && (ier & COM_IER_RDI)) ||
	    ((intr & COM_IIR_RLSI) && (ier & COM_IER_RLSI))) {
		com->iir = iir;
		com->iir_valid = 1;
		vdev_set_irq(com->vdev, IRQ_SERIAL13, 2);
	}

	return 0;
}

int
vserial_init(struct vdev *vdev, struct vserial *dev)
{
	uint32_t port;

	dev->vdev = vdev;
	dev->iir_valid = 0;

	for (port = 0x3f8; port <= 0x3ff; port++)
		vdev_register_ioport(vdev, dev, port,
				     vserial_read_ioport, vserial_write_ioport);

	vdev_register_update(vdev, dev, vserial_update);

	return 0;
}
