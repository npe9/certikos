#include <lib/trap.h>
#include <lib/x86.h>
#include <lib/sysenter.h>

#include <preinit/dev/console.h>
#include <preinit/dev/disk.h>
#include <preinit/dev/intr.h>
#include <preinit/dev/pci.h>
#include <preinit/dev/tsc.h>
//#include <preinit/dev/vmx_drv.h>

#include <preinit/lib/mboot.h>
#include <preinit/lib/seg.h>
#include <preinit/lib/x86.h>
#include <preinit/lib/types.h>

#include <preinit/lib/debug.h>
#include <preinit/lib/timing.h>

cpu_vendor cpuvendor;

void
set_vendor ()
{
	cpuvendor = vendor ();
}

extern void elf_preload(void);

void
boot_loader (uintptr_t mbi_addr)
{
	//int rv;

	FENCE();
	seg_init ();

	FENCE();
	enable_sse ();

	FENCE();
	cons_init ();
	KERN_DEBUG ("cons initialized.\n");

	FENCE();
	tsc_init ();
	KERN_DEBUG ("tsc initialized.\n");

#ifdef PROFILING
	profiling_init ();
	KERN_DEBUG("profiling initialized.\n");
#endif

	FENCE();
	sysenter_init ();
	KERN_DEBUG ("sysenter initialized.\n");

	FENCE();
	intr_init ();
	KERN_DEBUG ("intr initialized.\n");

	/* 	ide_init(); */
	/* KERN_DEBUG("ide initialized.\n"); */

	FENCE();
	disk_init ();

	FENCE();
	pci_init ();

	FENCE();
	set_vendor ();
	/*if (cpuvendor == INTEL)
	{
		KERN_DEBUG ("vendor detected: INTEL.\n");
        rv = vmx_hw_init ();
        KERN_ASSERT(rv == 0 && "vmx hw init failed!");
	}
	else
	{
		KERN_PANIC ("unknown cpu vendor.\n");
	}*/

	/* enable interrupts */
	FENCE();
	intr_enable (IRQ_TIMER);
	intr_enable (IRQ_KBD);
	intr_enable (IRQ_SERIAL13);

	FENCE();
	pmmap_init (mbi_addr);

	elf_preload();

	KERN_DEBUG("Jump to verified kernel ...\n");
}
