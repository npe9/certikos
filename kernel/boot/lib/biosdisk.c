#include <gcc.h>
#include <types.h>
#include <debug.h>
#include <bios.h>
#include <x86.h>

typedef
struct disk_address_packet {
	uint8_t  size;
	uint8_t  _reserved;
	uint16_t count;
	uint32_t buf_addr;
	uint64_t start_sect;
} gcc_packed dap_t;

struct bios_int_regs
{
  uint32_t eax;
  uint16_t es;
  uint16_t ds;
  uint16_t flags;
  uint16_t dummy;
  uint32_t ebx;
  uint32_t ecx;
  uint32_t edi;
  uint32_t esi;
  uint32_t edx;
};

void ipanic()
{
	panic("bios int failed.\n");
}

extern void
bios_int (uint8_t intno, struct bios_int_regs *regs) __attribute__ ((regparm(3)));

int
int13x (int ah, int drive, void *dap)
{
	struct bios_int_regs regs;
	regs.eax = ah << 8;
	/* compute the address of disk_address_packet */
	regs.ds = (((uint32_t) dap) & 0xffff0000) >> 4;
	regs.esi = (((uint32_t) dap) & 0xffff);
	regs.edx = drive;
	regs.flags = 0;

	bios_int (0x13, &regs);
	return (regs.eax >> 8) & 0xff;
}

int read_sector(int drive, uint64_t sector, void *buf)
{
//	debug ("read_sector: drive = %x, sector = %x, buf = %x\n", drive,
//		(uint32_t) sector, (uint32_t) buf);

	assert(sector >= 0 && buf != 0);

	dap_t dap = {
		.size = 0x10,
		._reserved = 0x0,
		.count = 1,
		.buf_addr = (uint32_t)buf,
		.start_sect = sector
	};

	return int13x(0x42, drive, &dap);
}
