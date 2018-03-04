#ifndef _KERN_X86_H_
#define _KERN_X86_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

/* CR0 */
#define CR0_PE		0x00000001	/* Protection Enable */
#define CR0_MP		0x00000002	/* Monitor coProcessor */
#define CR0_EM		0x00000004	/* Emulation */
#define CR0_TS		0x00000008	/* Task Switched */
#define CR0_NE		0x00000020	/* Numeric Errror */
#define CR0_WP		0x00010000	/* Write Protect */
#define CR0_AM		0x00040000	/* Alignment Mask */
#define CR0_PG		0x80000000	/* Paging */

/* CR4 */
#define CR4_PGE		0x00000080	/* Page Global Enable */
#define CR4_OSFXSR	0x00000200	/* SSE and FXSAVE/FXRSTOR enable */
#define CR4_OSXMMEXCPT	0x00000400	/* Unmasked SSE FP exceptions */

/* EFER */
#define MSR_EFER	0xc0000080
# define MSR_EFER_SVME	(1<<12)		/* for AMD processors */

/* sysenter */
#define SYSENTER_CS_MSR     0x174u
#define SYSENTER_ESP_MSR    0x175u
#define SYSENTER_EIP_MSR    0x176u

void ltr(uint16_t sel);
void lcr0(uint32_t val);
uint32_t rcr0(void);
uint32_t rcr2(void);
void lcr3(uint32_t val);
void lcr4(uint32_t val);
uint32_t rcr4(void);
uint8_t inb(int port);
void insl(int port, void *addr, int cnt);
void outb(int port, uint8_t data);
void outsw(int port, const void *addr, int cnt);

#define FENCE() asm volatile ("mfence" ::: "memory")

#define LOW8(x)  ((x) & 0xffu)
#define HIGH8(x)  (((x) >> 8) & 0xffu)

#endif /* _KERN_ */

#endif /* !_KERN_X86_H_ */
