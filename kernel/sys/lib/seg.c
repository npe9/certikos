#include <preinit/lib/seg.h>

#include <lib/x86.h>

void
tss_switch (uint32_t pid)
{
	gdt_LOC[CPU_GDT_TSS >> 3] = SEGDESC16 (STS_T32A, (uint32_t) (&tss_LOC[pid]),
		sizeof(tss_t) - 1, 0);
	gdt_LOC[CPU_GDT_TSS >> 3].sd_s = 0;
	ltr (CPU_GDT_TSS);
}
