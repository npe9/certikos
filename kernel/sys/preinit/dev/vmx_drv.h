#ifndef _SYS_PREINIT_DEV_VMX_DRV_H_
#define _SYS_PREINIT_DEV_VMX_DRV_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

#define MSR_VMX_BASIC           0x480
#define MSR_VMX_EPT_VPID_CAP        0x48C

#define MSR_VMX_PROCBASED_CTLS      0x482
#define MSR_VMX_TRUE_PROCBASED_CTLS 0x48E

#define MSR_VMX_PINBASED_CTLS       0x481
#define MSR_VMX_TRUE_PINBASED_CTLS  0x48D

#define MSR_VMX_PROCBASED_CTLS2     0x48B

#define MSR_VMX_EXIT_CTLS       0x483
#define MSR_VMX_TRUE_EXIT_CTLS      0x48f

#define MSR_VMX_ENTRY_CTLS      0x484
#define MSR_VMX_TRUE_ENTRY_CTLS     0x490
#define MSR_VMX_CR0_FIXED0      0x486
#define MSR_VMX_CR0_FIXED1      0x487

#define MSR_VMX_CR4_FIXED0      0x488
#define MSR_VMX_CR4_FIXED1      0x489


/* CR0 */
#define CR0_PE      0x00000001  /* Protection Enable */
#define CR0_MP      0x00000002  /* Monitor coProcessor */
#define CR0_EM      0x00000004  /* Emulation */
#define CR0_TS      0x00000008  /* Task Switched */
#define CR0_ET      0x00000010  /* Extension Type */
#define CR0_NE      0x00000020  /* Numeric Errror */
#define CR0_WP      0x00010000  /* Write Protect */
#define CR0_AM      0x00040000  /* Alignment Mask */
#define CR0_NW      0x20000000  /* Not Writethrough */
#define CR0_CD      0x40000000  /* Cache Disable */
#define CR0_PG      0x80000000  /* Paging */

/* CR4 */
#define CR4_VME     0x00000001  /* V86 Mode Extensions */
#define CR4_PVI     0x00000002  /* Protected-Mode Virtual Interrupts */
#define CR4_TSD     0x00000004  /* Time Stamp Disable */
#define CR4_DE      0x00000008  /* Debugging Extensions */
#define CR4_PSE     0x00000010  /* Page Size Extensions */
#define CR4_PAE     0x00000020  /* Physical Address Extension */
#define CR4_MCE     0x00000040  /* Machine Check Enable */
#define CR4_PGE     0x00000080  /* Page Global Enable */
#define CR4_PCE     0x00000100  /* Performance counter enable */
#define CR4_OSFXSR  0x00000200  /* SSE and FXSAVE/FXRSTOR enable */
#define CR4_OSXMMEXCPT  0x00000400  /* Unmasked SSE FP exceptions */



/* Pin-Based VM-Execution Controls */
#define PINBASED_EXTINT_EXITING     (1 << 0)
#define PINBASED_NMI_EXITING        (1 << 3)
#define PINBASED_VIRTUAL_NMI        (1 << 5)
#define PINBASED_PREMPTION_TIMER    (1 << 6)

/* Primary Processor-Based VM-Execution Controls */
#define PROCBASED_INT_WINDOW_EXITING    (1 << 2)
#define PROCBASED_TSC_OFFSET        (1 << 3)
#define PROCBASED_HLT_EXITING       (1 << 7)
#define PROCBASED_INVLPG_EXITING    (1 << 9)
#define PROCBASED_MWAIT_EXITING     (1 << 10)
#define PROCBASED_RDPMC_EXITING     (1 << 11)
#define PROCBASED_RDTSC_EXITING     (1 << 12)
#define PROCBASED_CR3_LOAD_EXITING  (1 << 15)
#define PROCBASED_CR3_STORE_EXITING (1 << 16)
#define PROCBASED_CR8_LOAD_EXITING  (1 << 19)
#define PROCBASED_CR8_STORE_EXITING (1 << 20)
#define PROCBASED_USE_TPR_SHADOW    (1 << 21)
#define PROCBASED_NMI_WINDOW_EXITING    (1 << 22)
#define PROCBASED_MOV_DR_EXITING    (1 << 23)
#define PROCBASED_IO_EXITING        (1 << 24)
#define PROCBASED_IO_BITMAPS        (1 << 25)
#define PROCBASED_MTF           (1 << 27)
#define PROCBASED_MSR_BITMAPS       (1 << 28)
#define PROCBASED_MONITOR_EXITING   (1 << 29)
#define PROCBASED_PAUSE_EXITING     (1 << 30)
#define PROCBASED_SECONDARY_CONTROLS    (1 << 31)

/* Secondary Processor-Based VM-Execution Controls */
#define PROCBASED2_VIRTUALIZE_APIC  (1 << 0)
#define PROCBASED2_ENABLE_EPT       (1 << 1)
#define PROCBASED2_DESC_TABLE_EXITING   (1 << 2)
#define PROCBASED2_ENABLE_RDTSCP    (1 << 3)
#define PROCBASED2_VIRTUALIZE_X2APIC    (1 << 4)
#define PROCBASED2_ENABLE_VPID      (1 << 5)
#define PROCBASED2_WBINVD_EXITING   (1 << 6)
#define PROCBASED2_UNRESTRICTED_GUEST   (1 << 7)
#define PROCBASED2_PAUSE_LOOP_EXITING   (1 << 10)
#define PROCBASED2_RDRAND_EXITING   (1 << 11)
#define PROCBASED2_ENABLE_INVPCID   (1 << 12)
#define PROCBASED2_ENABLE_VMFUNC    (1 << 13)

/* VM Exit Controls */
#define VM_EXIT_SAVE_DEBUG_CONTROLS (1 << 2)
#define VM_EXIT_HOST_LMA        (1 << 9)
#define VM_EXIT_LOAD_PERF_GLOBAL_CTRL   (1 << 12)
#define VM_EXIT_ACKNOWLEDGE_INTERRUPT   (1 << 15)
#define VM_EXIT_SAVE_PAT        (1 << 18)
#define VM_EXIT_LOAD_PAT        (1 << 19)
#define VM_EXIT_SAVE_EFER       (1 << 20)
#define VM_EXIT_LOAD_EFER       (1 << 21)
#define VM_EXIT_SAVE_PREEMPTION_TIMER   (1 << 22)

/* VM Entry Controls */
#define VM_ENTRY_LOAD_DEBUG_CONTROLS    (1 << 2)
#define VM_ENTRY_GUEST_LMA      (1 << 9)
#define VM_ENTRY_INTO_SMM       (1 << 10)
#define VM_ENTRY_DEACTIVATE_DUAL_MONITOR (1 << 11)
#define VM_ENTRY_LOAD_PERF_GLOBAL_CTRL  (1 << 13)
#define VM_ENTRY_LOAD_PAT       (1 << 14)
#define VM_ENTRY_LOAD_EFER      (1 << 15)


#define PINBASED_CTLS_ONE_SETTING           \
    PINBASED_EXTINT_EXITING/*   |   \ */
/* PINBASED_NMI_EXITING     |   \ */
/* PINBASED_VIRTUAL_NMI */
#define PINBASED_CTLS_ZERO_SETTING  0

#define PROCBASED_CTLS_WINDOW_SETTING           \
    PROCBASED_INT_WINDOW_EXITING/*  |   \ */
/* PROCBASED_NMI_WINDOW_EXITING */

#define PROCBASED_CTLS_ONE_SETTING      \
    (PROCBASED_IO_BITMAPS       |   \
     PROCBASED_MSR_BITMAPS      |   \
     PROCBASED_CTLS_WINDOW_SETTING  |   \
     PROCBASED_SECONDARY_CONTROLS   |   \
     PROCBASED_TSC_OFFSET       |   \
     /*PROCBASED_RDTSC_EXITING  |*/ \
     /* unsupported instructions */     \
     PROCBASED_HLT_EXITING      |   \
     PROCBASED_MWAIT_EXITING    |   \
     PROCBASED_MONITOR_EXITING)
#define PROCBASED_CTLS_ZERO_SETTING     \
    (PROCBASED_CR3_LOAD_EXITING |   \
     PROCBASED_CR3_STORE_EXITING    |   \
     PROCBASED_CR8_LOAD_EXITING |   \
     PROCBASED_CR8_STORE_EXITING    |   \
     PROCBASED_USE_TPR_SHADOW   |   \
     PROCBASED_MOV_DR_EXITING   |   \
     PROCBASED_MTF)

#define PROCBASED_CTLS2_ONE_SETTING     \
    (PROCBASED2_ENABLE_EPT      |   \
     PROCBASED2_ENABLE_VPID     |   \
     PROCBASED2_UNRESTRICTED_GUEST  |   \
     /* unsupported instructions */     \
     PROCBASED2_WBINVD_EXITING)
#define PROCBASED_CTLS2_ZERO_SETTING        \
    (PROCBASED2_VIRTUALIZE_APIC |   \
     PROCBASED2_DESC_TABLE_EXITING  |   \
     PROCBASED2_VIRTUALIZE_X2APIC   |   \
     PROCBASED2_PAUSE_LOOP_EXITING  |   \
     PROCBASED2_RDRAND_EXITING  |   \
     PROCBASED2_ENABLE_INVPCID  |   \
     PROCBASED2_ENABLE_RDTSCP   |   \
     PROCBASED2_ENABLE_VMFUNC)

#define VM_EXIT_CTLS_ONE_SETTING        \
    (VM_EXIT_SAVE_DEBUG_CONTROLS    |   \
     VM_EXIT_SAVE_PAT       |   \
     VM_EXIT_LOAD_PAT       |   \
     VM_EXIT_SAVE_EFER      |   \
     VM_EXIT_LOAD_EFER)
#define VM_EXIT_CTLS_ZERO_SETTING       \
    (VM_EXIT_HOST_LMA       |   \
     VM_EXIT_LOAD_PERF_GLOBAL_CTRL  |   \
     VM_EXIT_ACKNOWLEDGE_INTERRUPT  |   \
     VM_EXIT_SAVE_PREEMPTION_TIMER)

#define VM_ENTRY_CTLS_ONE_SETTING       \
    (VM_ENTRY_LOAD_DEBUG_CONTROLS   |   \
     VM_ENTRY_LOAD_PAT      |   \
     VM_ENTRY_LOAD_EFER)
#define VM_ENTRY_CTLS_ZERO_SETTING      \
    (VM_ENTRY_GUEST_LMA     |   \
     VM_ENTRY_INTO_SMM      |   \
     VM_ENTRY_DEACTIVATE_DUAL_MONITOR | \
     VM_ENTRY_LOAD_PERF_GLOBAL_CTRL)


int vmx_hw_init(void);

#endif /* _KERN_ */

#endif /* !_SYS_PREINIT_DEV_VMX_DRV_H_ */
