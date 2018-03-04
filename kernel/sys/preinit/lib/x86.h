#ifndef _PREINIT_LIB_X86_H_
#define _PREINIT_LIB_X86_H_

#include <preinit/lib/gcc.h>
#include <preinit/lib/types.h>
#include <preinit/lib/string.h>
#include <lib/x86.h>

#ifdef _KERN_

uint32_t
read_ebp (void);

void
lldt (uint16_t sel);

void
cli (void);

void
sti (void);

uint64_t
rdmsr (uint32_t msr);

void
wrmsr (uint32_t msr, uint64_t newval);

void
halt (void);

uint64_t
rdtsc (void);

void
enable_sse (void);

void
cpuid (uint32_t info, uint32_t *eaxp, uint32_t *ebxp, uint32_t *ecxp,
		uint32_t *edxp);

cpu_vendor
vendor ();

uint32_t
rcr3 (void);

void
outl (int port, uint32_t data);

uint32_t
inl (int port);

void
smp_wmb (void);

#endif /* _KERN_ */

#endif /* !_PREINIT_LIB_X86_H_ */
