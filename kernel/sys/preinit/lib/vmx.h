#ifndef _VIRT_VMX_H_
#define _VIRT_VMX_H_

#ifdef _KERN_

#include <lib/gcc.h>
#include <preinit/lib/types.h>
#include <preinit/lib/string.h>

#include "vmcs.h"

#define PAGESIZE 4096

struct vmx {
	/*
	 * VMCS does not store following registers for guest, so we have
	 * to do that by ourself.
	 */
	uint64_t	g_rax, g_rbx, g_rcx, g_rdx, g_rsi, g_rdi, g_rbp, g_rip;
	uint32_t	g_cr2;
	uint32_t	g_dr0, g_dr1, g_dr2, g_dr3, g_dr6;
	uint32_t	enter_tsc[2], exit_tsc[2];

	struct vmcs	*vmcs;

	uint16_t	vpid;
	uint64_t	*pml4ept;
	char		*msr_bitmap, *io_bitmap;

	uint32_t	exit_reason;
	uint64_t	exit_qualification;
	int32_t		pending_intr;

	int		launched;
	int		failed;
};

struct vmx_info {
    bool        vmx_enabled;
    uint32_t    pinbased_ctls;
    uint32_t    procbased_ctls, procbased_ctls2;
    uint32_t    exit_ctls, entry_ctls;
    uint64_t    cr0_ones_mask, cr0_zeros_mask;
    uint64_t    cr4_ones_mask, cr4_zeros_mask;

    uint32_t    vmx_region[1024] gcc_aligned(PAGESIZE);
};

#define offsetof(type, member)  __builtin_offsetof(type, member)
#define MSR_VMX_BASIC           0x480

void vmx_set_intercept_intwin(unsigned int enable);
void vmx_set_reg(unsigned int reg, unsigned int val);
unsigned int vmx_get_reg(unsigned int reg);
unsigned int vmx_get_exit_reason(void);
unsigned int vmx_get_exit_io_port(void);
unsigned int vmx_get_exit_io_width(void);
unsigned int vmx_get_exit_io_write(void);
unsigned int vmx_get_exit_io_rep(void);
unsigned int vmx_get_exit_io_str(void);
unsigned int vmx_get_exit_io_neip(void);
unsigned int vmx_get_exit_fault_addr(void);
void vmx_set_mmap(unsigned int, unsigned int, unsigned int);
void vmx_set_desc(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);
void vmx_inject_event(unsigned int, unsigned int, unsigned int, unsigned int);
void vmx_set_intercept_intwin(unsigned int);
unsigned int vmx_check_pending_event(void);
unsigned int vmx_check_int_shadow(void);
unsigned int vmx_get_next_eip(void);
void vmx_run_vm(void);

uint64_t vmx_get_tsc_offset(void);
void vmx_set_tsc_offset(uint64_t);

int vmx_set_ctlreg(int, int, uint32_t, uint32_t, uint32_t *);

#ifdef DEBUG_VMX

#define VMX_DEBUG(fmt, ...)				\
	do {						\
		KERN_DEBUG("VMX: "fmt, ##__VA_ARGS__);	\
	} while (0)

#else

#define VMX_DEBUG(fmt, ...)			\
	do {					\
	} while (0)

#endif

#endif /* _KERN_ */

#endif /* !_VIRT_VMX_H_ */
