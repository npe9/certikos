#ifndef _USER_HVM_H_
#define _USER_HVM_H_

#include <types.h>

/*
 * VMEXIT code of SVM.
 */

#define	SVM_EXIT_READ_CR0 	0x000
#define	SVM_EXIT_READ_CR3 	0x003
#define	SVM_EXIT_READ_CR4 	0x004
#define	SVM_EXIT_READ_CR8 	0x008
#define	SVM_EXIT_WRITE_CR0 	0x010
#define	SVM_EXIT_WRITE_CR3 	0x013
#define	SVM_EXIT_WRITE_CR4 	0x014
#define	SVM_EXIT_WRITE_CR8 	0x018
#define	SVM_EXIT_READ_DR0 	0x020
#define	SVM_EXIT_READ_DR1 	0x021
#define	SVM_EXIT_READ_DR2 	0x022
#define	SVM_EXIT_READ_DR3 	0x023
#define	SVM_EXIT_READ_DR4 	0x024
#define	SVM_EXIT_READ_DR5 	0x025
#define	SVM_EXIT_READ_DR6 	0x026
#define	SVM_EXIT_READ_DR7 	0x027
#define	SVM_EXIT_WRITE_DR0 	0x030
#define	SVM_EXIT_WRITE_DR1 	0x031
#define	SVM_EXIT_WRITE_DR2 	0x032
#define	SVM_EXIT_WRITE_DR3 	0x033
#define	SVM_EXIT_WRITE_DR4 	0x034
#define	SVM_EXIT_WRITE_DR5 	0x035
#define	SVM_EXIT_WRITE_DR6 	0x036
#define	SVM_EXIT_WRITE_DR7 	0x037
#define SVM_EXIT_EXCP_BASE      0x040
#define SVM_EXIT_INTR		0x060
#define SVM_EXIT_NMI		0x061
#define SVM_EXIT_SMI		0x062
#define SVM_EXIT_INIT		0x063
#define SVM_EXIT_VINTR		0x064
#define SVM_EXIT_CR0_SEL_WRITE	0x065
#define SVM_EXIT_IDTR_READ	0x066
#define SVM_EXIT_GDTR_READ	0x067
#define SVM_EXIT_LDTR_READ	0x068
#define SVM_EXIT_TR_READ	0x069
#define SVM_EXIT_IDTR_WRITE	0x06a
#define SVM_EXIT_GDTR_WRITE	0x06b
#define SVM_EXIT_LDTR_WRITE	0x06c
#define SVM_EXIT_TR_WRITE	0x06d
#define SVM_EXIT_RDTSC		0x06e
#define SVM_EXIT_RDPMC		0x06f
#define SVM_EXIT_PUSHF		0x070
#define SVM_EXIT_POPF		0x071
#define SVM_EXIT_CPUID		0x072
#define SVM_EXIT_RSM		0x073
#define SVM_EXIT_IRET		0x074
#define SVM_EXIT_SWINT		0x075
#define SVM_EXIT_INVD		0x076
#define SVM_EXIT_PAUSE		0x077
#define SVM_EXIT_HLT		0x078
#define SVM_EXIT_INVLPG		0x079
#define SVM_EXIT_INVLPGA	0x07a
#define SVM_EXIT_IOIO		0x07b
#define SVM_EXIT_MSR		0x07c
#define SVM_EXIT_TASK_SWITCH	0x07d
#define SVM_EXIT_FERR_FREEZE	0x07e
#define SVM_EXIT_SHUTDOWN	0x07f
#define SVM_EXIT_VMRUN		0x080
#define SVM_EXIT_VMMCALL	0x081
#define SVM_EXIT_VMLOAD		0x082
#define SVM_EXIT_VMSAVE		0x083
#define SVM_EXIT_STGI		0x084
#define SVM_EXIT_CLGI		0x085
#define SVM_EXIT_SKINIT		0x086
#define SVM_EXIT_RDTSCP		0x087
#define SVM_EXIT_ICEBP		0x088
#define SVM_EXIT_WBINVD		0x089
#define SVM_EXIT_MONITOR	0x08a
#define SVM_EXIT_MWAIT		0x08b
#define SVM_EXIT_MWAIT_COND	0x08c
#define SVM_EXIT_XSETBV		0x08d
#define SVM_EXIT_NPF  		0x400

#define SVM_EXIT_ERR		-1

/*
 * VMCS exit reasons
 */
#define VMX_EXIT_REASON_EXCEPTION	0
#define VMX_EXIT_REASON_EXT_INTR	1
#define VMX_EXIT_REASON_TRIPLE_FAULT	2
#define VMX_EXIT_REASON_INIT		3
#define VMX_EXIT_REASON_SIPI		4
#define VMX_EXIT_REASON_IO_SMI		5
#define VMX_EXIT_REASON_SMI		6
#define VMX_EXIT_REASON_INTR_WINDOW	7
#define VMX_EXIT_REASON_NMI_WINDOW	8
#define VMX_EXIT_REASON_TASK_SWITCH	9
#define VMX_EXIT_REASON_CPUID		10
#define VMX_EXIT_REASON_GETSEC		11
#define VMX_EXIT_REASON_HLT		12
#define VMX_EXIT_REASON_INVD		13
#define VMX_EXIT_REASON_INVLPG		14
#define VMX_EXIT_REASON_RDPMC		15
#define VMX_EXIT_REASON_RDTSC		16
#define VMX_EXIT_REASON_RSM		17
#define VMX_EXIT_REASON_VMCALL		18
#define VMX_EXIT_REASON_VMCLEAR		19
#define VMX_EXIT_REASON_VMLAUNCH	20
#define VMX_EXIT_REASON_VMPTRLD		21
#define VMX_EXIT_REASON_VMPTRST		22
#define VMX_EXIT_REASON_VMREAD		23
#define VMX_EXIT_REASON_VMRESUME	24
#define VMX_EXIT_REASON_VMWRITE		25
#define VMX_EXIT_REASON_VMXOFF		26
#define VMX_EXIT_REASON_VMXON		27
#define VMX_EXIT_REASON_CR_ACCESS	28
#define VMX_EXIT_REASON_DR_ACCESS	29
#define VMX_EXIT_REASON_INOUT		30
#define VMX_EXIT_REASON_RDMSR		31
#define VMX_EXIT_REASON_WRMSR		32
#define VMX_EXIT_REASON_INVAL_VMCS	33
#define VMX_EXIT_REASON_INVAL_MSR	34
#define VMX_EXIT_REASON_MWAIT		36
#define VMX_EXIT_REASON_MTF		37
#define VMX_EXIT_REASON_MONITOR		39
#define VMX_EXIT_REASON_PAUSE		40
#define VMX_EXIT_REASON_MCE		41
#define VMX_EXIT_REASON_TPR		43
#define VMX_EXIT_REASON_APIC		44
#define VMX_EXIT_REASON_GDTR_IDTR	46
#define VMX_EXIT_REASON_LDTR_TR		47
#define VMX_EXIT_REASON_EPT_FAULT	48
#define VMX_EXIT_REASON_EPT_MISCONFIG	49
#define VMX_EXIT_REASON_INVEPT		50
#define VMX_EXIT_REASON_RDTSCP		51
#define VMX_EXIT_REASON_VMX_PREEMPT	52
#define VMX_EXIT_REASON_INVVPID		53
#define VMX_EXIT_REASON_WBINVD		54
#define VMX_EXIT_REASON_XSETBV		55
#define VMX_EXIT_REASON_RDRAND		57
#define VMX_EXIT_REASON_INVPCID		58
#define VMX_EXIT_REASON_VMFUNC		59

/*
 * Arch-independent VMEXIT reason
 */

typedef enum
{
    EXIT_REASON_NONE = 0, /* no VMEXIT */
    EXIT_REASON_EXTINT, /* exit for the external interrupt */
    EXIT_REASON_INTWIN, /* exit for the interrupt window */
    EXIT_REASON_IOPORT, /* exit for accessing an I/O port */
    EXIT_REASON_PGFLT, /* exit for the page fault */
    EXIT_REASON_RDMSR, /* exit for the rdmsr instruction */
    EXIT_REASON_WRMSR, /* exit for the wrmsr instruction */
    EXIT_REASON_CPUID, /* exit for the cpuid instruction */
    EXIT_REASON_RDTSC, /* exit for the rdtsc/rdtscp instruction */
    EXIT_REASON_INVAL_INSTR,/* exit for the invalid instruction */
    EXIT_REASON_HYPERCALL, /* exit for hypercall */
    EXIT_REASON_INVAL, /* invalid exit */
} exit_reason_t;

/*
 * Convert SVM VMEXIT reason to arch_independent VMEXIT reason
 */

#define svm_to_hvm_exit_reason(reason)				\
	((reason) == SVM_EXIT_INTR ? EXIT_REASON_EXTINT :	\
	 (reason) ==  SVM_EXIT_VINTR ? EXIT_REASON_INTWIN :	\
	 (reason) == SVM_EXIT_IOIO ? EXIT_REASON_IOPORT :	\
	 (reason) == SVM_EXIT_NPF ? EXIT_REASON_PGFLT :		\
	 (reason) == SVM_EXIT_CPUID ? EXIT_REASON_CPUID :	\
	 (reason) == SVM_EXIT_RDTSC ? EXIT_REASON_RDTSC :	\
	 (reason) == SVM_EXIT_ERR ? EXIT_REASON_INVAL :		\
	 EXIT_REASON_INVAL_INSTR)

#define vmx_to_hvm_exit_reason(reason)					\
	((reason) == VMX_EXIT_REASON_EXT_INTR ? EXIT_REASON_EXTINT :	\
	 (reason) == VMX_EXIT_REASON_INTR_WINDOW ? EXIT_REASON_INTWIN :	\
	 (reason) == VMX_EXIT_REASON_INOUT ? EXIT_REASON_IOPORT :	\
	 (reason) == VMX_EXIT_REASON_EPT_FAULT ? EXIT_REASON_PGFLT :	\
	 (reason) == VMX_EXIT_REASON_CPUID ? EXIT_REASON_CPUID :	\
	 (reason) == VMX_EXIT_REASON_RDTSC ? EXIT_REASON_RDTSC :	\
	 (reason) == VMX_EXIT_REASON_VMCALL ? EXIT_REASON_HYPERCALL : \
	 EXIT_REASON_INVAL)

/*
 * VMEXIT info.
 */

typedef union
{
    /* valid when exiting for I/O ports */
    struct
    {
        uint16_t port; /* I/O port */
        uint8_t seg; /* segment */
        addr_sz_t aw; /* address width */
        data_sz_t dw; /* data width */
        bool write;/* is write? */
        bool rep; /* has the prefix rep? */
        bool str; /* is a string operation? */
        uintptr_t neip; /* address of the next instruction */
    } ioport;

    /* valid when exiting for EPT/NPT page faults */
    struct
    {
        uintptr_t addr; /* the fault address */
    } pgflt;
} exit_info_t;

/*
 * Guest segment.
 */

#define GUEST_SEG_TYPE_MASK	0xf
#define GUEST_SEG_ATTR_S	(1 << 4)
#define GUEST_SEG_DPL_SHIFT	(1 << 5)
#define GUEST_SEG_DPL_MASK	0x60
#define GUEST_SEG_ATTR_P	(1 << 7)
#define GUEST_SEG_ATTR_AVL	(1 << 12)
#define GUEST_SEG_ATTR_L	(1 << 13)
#define GUEST_SEG_ATTR_D	(1 << 14)
#define GUEST_SEG_ATTR_B	(1 << 14)
#define GUEST_SEG_ATTR_G	(1 << 15)
#define GUEST_SEG_ATTR_UNUSABLE	(1 << 16)

#define GUEST_SEG_ATTR_A	(1 << 0)
#define GUEST_SEG_ATTR_W	(1 << 1)	/* for data segments */
#define GUEST_SEG_ATTR_R	(1 << 1)	/* for code segments */
#define GUEST_SEG_ATTR_E	(1 << 2)	/* for data segments */
#define GUEST_SEG_ATTR_C	(1 << 2)	/* for code segments */

#define GUEST_SEG_TYPE_CODE	0xa
#define GUEST_SEG_TYPE_DATA	0x2
#define GUEST_SEG_TYPE_LDT	0x2
#define GUEST_SEG_TYPE_TSS_BUSY	0x3
#define GUEST_SEG_TYPE_TSS	0xb

struct guest_seg_desc
{
    uint16_t sel;
    uint32_t base;
    uint32_t lim;
    uint32_t ar;
};

/*
 * SVM inject event type
 */

#define SVM_EVTINJ_TYPE_INTR	0
#define SVM_EVTINJ_TYPE_EXEPT	3

/*
 * Arch-independent inject event type
 */

typedef enum
{
    EVENT_EXTINT, /* external interrupt */
    EVENT_EXCEPTION /* exception */
} guest_event_t;

/*
 * Convert arch-independent inject event type to SVM inject event type
 */

#define hvm_to_svm_event_type(type)					\
	((type == EVENT_EXTINT) ? SVM_EVTINJ_TYPE_INTR : SVM_EVTINJ_TYPE_EXEPT)

/*
 * Instruction type
 */

typedef enum
{
    INSTR_IN,
    INSTR_OUT,
    INSTR_RDMSR,
    INSTR_WRMSR,
    INSTR_CPUID,
    INSTR_RDTSC,
    INSTR_HYPERCALL
} guest_instr_t;

#endif /* !_USER_HVM_H_ */
