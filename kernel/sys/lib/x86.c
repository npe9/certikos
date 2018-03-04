#include <preinit/lib/types.h>
#include "x86.h"

void
ltr(uint16_t sel)
{
	__asm __volatile("ltr %0" : : "r" (sel));
}

void
lcr0(uint32_t val)
{
	__asm __volatile("movl %0,%%cr0" : : "r" (val));
}

uint32_t
rcr0(void)
{
	uint32_t val;
	__asm __volatile("movl %%cr0,%0" : "=r" (val));
	return val;
}

uint32_t
rcr2(void)
{
	uint32_t val;
	__asm __volatile("movl %%cr2,%0" : "=r" (val));
	return val;
}

void
lcr2(uint32_t val)
{
	__asm __volatile("movl %0,%%cr2" : : "r" (val));
}

void
clear_cr2 (void)
{
	lcr2 (0);
}

void
lcr3(uint32_t val)
{
	__asm __volatile("movl %0,%%cr3" : : "r" (val));
}

void
lcr4(uint32_t val)
{
	__asm __volatile("movl %0,%%cr4" : : "r" (val));
}

uint32_t
rcr4(void)
{
	uint32_t cr4;
	__asm __volatile("movl %%cr4,%0" : "=r" (cr4));
	return cr4;
}

uint8_t
inb(int port)
{
	uint8_t data;
	__asm __volatile("inb %w1,%0" : "=a" (data) : "d" (port));
	return data;
}

void
insl(int port, void *addr, int cnt)
{
	__asm __volatile("cld\n\trepne\n\tinsl"                 :
			 "=D" (addr), "=c" (cnt)                :
			 "d" (port), "0" (addr), "1" (cnt)      :
			 "memory", "cc");
}

void
outb(int port, uint8_t data)
{
	__asm __volatile("outb %0,%w1" : : "a" (data), "d" (port));
}

void
outsw(int port, const void *addr, int cnt)
{
	__asm __volatile("cld\n\trepne\n\toutsw"                :
			 "=S" (addr), "=c" (cnt)                :
			 "d" (port), "0" (addr), "1" (cnt)      :
			 "cc");
}

