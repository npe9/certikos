#include <preinit/lib/debug.h>
#include <preinit/lib/types.h>
#include <preinit/lib/x86.h>
#include <preinit/dev/disk.h>
#include <preinit/dev/tsc.h>
#include <preinit/lib/timing.h>
#include <lib/trap.h>
#include <preinit/lib/syscall.h>
#include <preinit/lib/pmap.h>

static char sys_buf[NUM_PROC][PAGESIZE];

static int
__sys_disk_read (unsigned int lba_lo, unsigned int lba_hi,
					unsigned int nsectors, unsigned int buf)
{
	unsigned int remaining;
	unsigned int cur_la;
	unsigned int cur_pid;
	unsigned int n;

	struct disk_dev *drv;
	uint64_t cur_lba;
	uintptr_t sys_buf_pa;

	drv = disk_get_dev (0);

	KERN_ASSERT (drv != NULL);

	cur_pid = get_curid ();

	cur_lba = (((uint64_t) lba_hi) << 32) | lba_lo;
	remaining = nsectors;
	cur_la = buf;

	sys_buf_pa = (uintptr_t) sys_buf[cur_pid];

	while (remaining > 0)
	{
		if (remaining < PAGESIZE / ATA_SECTOR_SIZE)
			n = remaining;
		else
			n = PAGESIZE / ATA_SECTOR_SIZE;

		if (disk_xfer (drv, cur_lba, sys_buf_pa, n, FALSE))
			return E_DISK_OP;
		if (pt_copyout (sys_buf[cur_pid], cur_pid, cur_la, n * ATA_SECTOR_SIZE)
				!= n * ATA_SECTOR_SIZE)
			return E_MEM;

		cur_lba += n;
		remaining -= n;
		cur_la += n * ATA_SECTOR_SIZE;
	}

	return E_SUCC;
}

static int
__sys_disk_write (unsigned int lba_lo, unsigned int lba_hi,
					unsigned int nsectors, unsigned int buf)
{
	unsigned int remaining;
	unsigned int cur_la;
	unsigned int cur_pid;
	unsigned int n;

	struct disk_dev *drv;
	uint64_t cur_lba;
	uintptr_t sys_buf_pa;

	drv = disk_get_dev (0);

	KERN_ASSERT (drv != NULL);

	cur_pid = get_curid ();

	cur_lba = (((uint64_t) lba_hi) << 32) | lba_lo;
	remaining = nsectors;
	cur_la = buf;

	sys_buf_pa = (uintptr_t) sys_buf[cur_pid];

	while (remaining > 0)
	{
		if (remaining < PAGESIZE / ATA_SECTOR_SIZE)
			n = remaining;
		else
			n = PAGESIZE / ATA_SECTOR_SIZE;

		if (pt_copyin (cur_pid, cur_la, sys_buf[cur_pid], n * ATA_SECTOR_SIZE)
				!= n * ATA_SECTOR_SIZE)
			return E_MEM;
		if (disk_xfer (drv, cur_lba, sys_buf_pa, n, TRUE))
			return E_DISK_OP;

		cur_lba += n;
		remaining -= n;
		cur_la += n * ATA_SECTOR_SIZE;
	}

	return E_SUCC;
}

void
sys_disk_op (void)
{
	unsigned int op;
	unsigned int lba_lo;
	unsigned int lba_hi;
	unsigned int nsects;
	unsigned int buf_uva;
	unsigned int rc;

	op = uctx_arg2 ();
	lba_lo = uctx_arg3 ();
	lba_hi = uctx_arg4 ();
	nsects = uctx_arg5 ();
	buf_uva = uctx_arg6 ();

	if (!(VM_USERLO <= buf_uva
			&& buf_uva + nsects * ATA_SECTOR_SIZE <= VM_USERHI))
	{
		uctx_set_errno (E_INVAL_ADDR);
		return;
	}

	if (op == DISK_READ)
		rc = __sys_disk_read (lba_lo, lba_hi, nsects, buf_uva);
	else if (op == DISK_WRITE)
		rc = __sys_disk_write (lba_lo, lba_hi, nsects, buf_uva);
	else
		rc = 1;

	if (rc)
		uctx_set_errno (E_DISK_OP);
	else
		uctx_set_errno (E_SUCC);
}

void
sys_disk_cap(void)
{
	struct disk_dev *drv;
	uint64_t cap;

	drv = disk_get_dev(0);
	cap = disk_capacity(drv);

	uctx_set_retval1(cap & 0xffffffff);
	uctx_set_retval2(cap >> 32);
	uctx_set_errno(E_SUCC);
}

void
sys_get_tsc_per_ms(void)
{
    // KERN_DEBUG("tsc per ms: %llu.\n", tsc_per_ms);
	uctx_set_retval1(tsc_per_ms >> 32);
	uctx_set_retval2(tsc_per_ms & 0xffffffff);
	uctx_set_errno(E_SUCC);
}
