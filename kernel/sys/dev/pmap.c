#include <preinit/lib/types.h>
#include <lib/x86.h>

void
set_cr3(char **pdir)
{
	lcr3((uint32_t) pdir);
}

void
set_pg(void)
{
	/* enable global pages (Sec 4.10.2.4, Intel ASDM Vol3) */
	uint32_t cr4 = rcr4();
	cr4 |= CR4_PGE;
	lcr4(cr4);

	/* turn on paging */
	uint32_t cr0 = rcr0();
	cr0 |= CR0_PE | CR0_PG | CR0_AM | CR0_WP | CR0_NE | CR0_MP;
	cr0 &= ~(CR0_EM | CR0_TS);
	lcr0(cr0);
}
