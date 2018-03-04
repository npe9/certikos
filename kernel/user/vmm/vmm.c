#include <debug.h>
#include <hvm.h>
#include <string.h>
#include <stdio.h>
#include <syscall.h>
#include <types.h>
#include <x86.h>
#include <hypercall_vmx.h>

#include "vmm.h"
#include "vmm_dev.h"

#ifdef DEBUG_VMM

#define VMM_DEBUG(fmt, ...)				\
	do {						\
		DEBUG("VMM: "fmt, ##__VA_ARGS__);	\
	} while (0)

#else

#define VMM_DEBUG(fmt...)			\
	do {					\
	} while (0)

#endif

#define CODE_SEG_AR (GUEST_SEG_ATTR_P | GUEST_SEG_ATTR_S |	\
		     GUEST_SEG_TYPE_CODE | GUEST_SEG_ATTR_A)
#define DATA_SEG_AR (GUEST_SEG_ATTR_P | GUEST_SEG_ATTR_S |	\
		     GUEST_SEG_TYPE_DATA | GUEST_SEG_ATTR_A)
#define LDT_AR      (GUEST_SEG_ATTR_P | GUEST_SEG_TYPE_LDT)
#define TSS_AR      (GUEST_SEG_ATTR_P | GUEST_SEG_TYPE_TSS)

static struct guest_seg_desc guest_seg_desc[GUEST_MAX_SEG_DESC] =
    {
    /* 0: code segment */
        { .sel = 0xf000, .base = 0x000f0000, .lim = 0xffff, .ar = CODE_SEG_AR },
    /* 1: data segment */
        { .sel = 0x0000, .base = 0x00000000, .lim = 0xffff, .ar = DATA_SEG_AR },
    /* 2: LDT */
        { .sel = 0, .base = 0, .lim = 0xffff, .ar = LDT_AR },
    /* 3: TSS */
        { .sel = 0, .base = 0, .lim = 0xffff, .ar = TSS_AR },
    /* 4: GDT/IDT */
        { .sel = 0, .base = 0, .lim = 0xffff, .ar = 0 } };

#undef CODE_SEG_AR
#undef DATA_SEG_AR
#undef LDT_AR
#undef TSS_AR

static int
vmm_init_mmap (struct vm *vm)
{
    if (vm == NULL)
        return -1;

    memzero (vm->mmap_bitmap, sizeof(uint32_t) * MMAP_BITMAP_SIZE);

    return 0;
}

static void
vmm_update_guest_tsc (struct vm *vm, uint64_t last_h_tsc, uint64_t cur_h_tsc)
{
    uint64_t tsc_per_ms = sys_get_tsc_per_ms (vm->vmid);
    ASSERT(tsc_per_ms != -1);
    ASSERT(vm != NULL);
    ASSERT(cur_h_tsc >= last_h_tsc);
    uint64_t delta = cur_h_tsc - last_h_tsc;
    vm->tsc += (delta * vm->cpufreq) / (tsc_per_ms * 1000);
}

static void
vmm_update_guest_tsc_offset (struct vm *vm, uint64_t cur_h_tsc)
{
    sys_hvm_set_tsc_offset (vm->vmid, (uint64_t) (vm->tsc - cur_h_tsc));
}

static int
vmm_handle_ioport (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason == EXIT_REASON_IOPORT);

    exit_info_t *exit_info = &vm->exit_info;
    uint16_t port;
    data_sz_t width;
    uint32_t eax, next_eip;

    if (exit_info->ioport.rep == TRUE)
    {
        PANIC("REP I/O instructions is not implemented yet.\n");
        return 1;
    }

    if (exit_info->ioport.str == TRUE)
    {
        PANIC("String operation is not implemented yet.\n");
        return 2;
    }

    port = exit_info->ioport.port;
    width = exit_info->ioport.dw;

    /*
     * XXX: I/O permission check is not necessary when using HVM. If the
     *      check fails, the corresponding exception, instead of an I/O
     *      related VMEXIT, will happen in the guest.
     */

	if (exit_info->ioport.write == TRUE)
	{
		sys_hvm_get_reg (vm->vmid, GUEST_EAX, &eax);
//		DEBUG("Write guest I/O port 0x%x, width %d bytes, "
//			"val 0x%08x.\n", port, 1 << width, eax);
		vdev_write_guest_ioport (&vm->vdev, port, width, eax);
		sys_hvm_get_next_eip (vm->vmid, INSTR_OUT, &next_eip);
	}
	else
	{
		vdev_read_guest_ioport (&vm->vdev, port, width, &eax);
		sys_hvm_set_reg (vm->vmid, GUEST_EAX, eax);
		sys_hvm_get_next_eip (vm->vmid, INSTR_IN, &next_eip);
//		DEBUG("Read guest I/O port 0x%x, width %d bytes, "
//			"val 0x%08x.\n", port, 1 << width, eax);
	}

    sys_hvm_set_reg (vm->vmid, GUEST_EIP, next_eip);

    return 0;
}

static int
vmm_handle_rdmsr (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason == EXIT_REASON_RDMSR);

    struct vmm_ops *vmm_ops = vm->ops;
    uint32_t msr, next_eip;
    uint64_t val;

    sys_hvm_get_reg (vm->vmid, GUEST_EAX, &msr);

    /*
     * XXX: I/O permission check is not necessary when using HVM.
     */
    if (vmm_ops->get_msr (vm, msr, &val))
    {
#ifdef DEBUG_GUEST_MSR
        DEBUG("Guest rdmsr failed: invalid MSR 0x%llx.\n", msr);
#endif
        sys_hvm_inject_event (vm->vmid, EVENT_EXCEPTION, T_GPFLT, 0, TRUE);
        return 0;
    }

#ifdef DEBUG_GUEST_MSR
    DEBUG("Guest rdmsr 0x%08x = 0x%llx.\n", msr, val);
#endif

    sys_hvm_set_reg (vm->vmid, GUEST_EAX, val & 0xffffffff);
    sys_hvm_set_reg (vm->vmid, GUEST_EDX, (val >> 32) & 0xffffffff);

    sys_hvm_get_next_eip (vm->vmid, INSTR_RDMSR, &next_eip);
    sys_hvm_set_reg (vm->vmid, GUEST_EIP, next_eip);

    return 0;
}

static int
vmm_handle_wrmsr (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason == EXIT_REASON_WRMSR);

    struct vmm_ops *vmm_ops = vm->ops;
    uint32_t msr, next_eip, eax, edx;
    uint64_t val;

    sys_hvm_get_reg (vm->vmid, GUEST_ECX, &msr);

    sys_hvm_get_reg (vm->vmid, GUEST_EAX, &eax);
    sys_hvm_get_reg (vm->vmid, GUEST_EDX, &edx);
    val = ((uint64_t) edx << 32) | (uint64_t) eax;

    /*
     * XXX: I/O permission check is not necessary when using HVM.
     */
    if (vmm_ops->set_msr (vm, msr, val))
    {
#ifdef DEBUG_GUEST_MSR
        DEBUG("Guest wrmsr failed: invalid MSR 0x%llx.\n", msr);
#endif
        sys_hvm_inject_event (vm->vmid, EVENT_EXCEPTION, T_GPFLT, 0, TRUE);
        return 0;
    }

#ifdef DEBUG_GUEST_MSR
    DEBUG("Guest wrmsr 0x%08x, 0x%llx.\n", msr, val);
#endif

    sys_hvm_get_next_eip (vm->vmid, INSTR_WRMSR, &next_eip);
    sys_hvm_set_reg (vm->vmid, GUEST_EIP, next_eip);

    return 0;
}

static int
vmm_handle_pgflt (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason == EXIT_REASON_PGFLT);

    exit_info_t *exit_info = &vm->exit_info;
    uint32_t fault_pa = exit_info->pgflt.addr;
    uintptr_t host_va;
    int pfn, line, row;

    if (vm->memsize <= fault_pa && fault_pa < 0xf0000000)
    {
        PANIC("EPT/NPT fault @ 0x%08x: out of range. VM mem size: 0x%08x\n",
              fault_pa, vm->memsize);
        return 1;
    }

    pfn = fault_pa / PAGESIZE;
    line = pfn / 32;
    row = pfn % 32;

    if (vm->mmap_bitmap[line] & (1UL << row))
    {
        PANIC("GPA 0x%08x is already mapped.\n", fault_pa);
    }

    host_va =
            (fault_pa < 0xf0000000) ?
                    (uintptr_t) &vm->memory[ROUNDDOWN(fault_pa, PAGESIZE)] :
                    (uintptr_t) &vm->memory_dev[ROUNDDOWN(fault_pa, PAGESIZE)
                            - 0xf0000000];

    if (fault_pa >= 0xf0000000)
        memzero ((uint8_t *) host_va, PAGESIZE);

    if ((sys_hvm_mmap (vm->vmid, ROUNDDOWN(fault_pa, PAGESIZE), host_va,
    PAT_WRITE_BACK)))
    {
        PANIC("EPT/NPT fault @ 0x%08x: cannot be mapped to "
              "HVA 0x%08x.\n",
              fault_pa, host_va);
        return 3;
    }

    vm->mmap_bitmap[line] |= (1UL << row);

//    DEBUG("EPT/NPT fault @ 0x%08x: mapped to HVA 0x%08x.\n",
//            fault_pa, host_va);

    return 0;
}

static int
vmm_handle_cpuid (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason == EXIT_REASON_CPUID);

    struct vmm_ops *vmm_ops = vm->ops;
    uint32_t func1, func2, eax, ebx, ecx, edx, next_eip;

    sys_hvm_get_reg (vm->vmid, GUEST_EAX, &func1);
    sys_hvm_get_reg (vm->vmid, GUEST_ECX, &func2);

    vmm_ops->get_cpuid (vm, func1, func2, &eax, &ebx, &ecx, &edx);
    sys_hvm_set_reg (vm->vmid, GUEST_EAX, eax);
    sys_hvm_set_reg (vm->vmid, GUEST_EBX, ebx);
    sys_hvm_set_reg (vm->vmid, GUEST_ECX, ecx);
    sys_hvm_set_reg (vm->vmid, GUEST_EDX, edx);

#ifdef DEBUG_GUEST_CPUID
    DEBUG("Guest cpuid eax=0x%08x ecx=0x%08x: "
            "eax=0x%08x, ebx=0x%08x, ecx=0x%08x, edx=0x%08x.\n",
            func1, func2, eax, ebx, ecx, edx);
#endif

    sys_hvm_get_next_eip (vm->vmid, INSTR_CPUID, &next_eip);
    sys_hvm_set_reg (vm->vmid, GUEST_EIP, next_eip);

    return 0;
}

static int
vmm_handle_rdtsc (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason == EXIT_REASON_RDTSC);

    uint32_t next_eip;

    sys_hvm_set_reg (vm->vmid, GUEST_EDX, (vm->tsc >> 32) & 0xffffffff);
    sys_hvm_set_reg (vm->vmid, GUEST_EAX, vm->tsc & 0xffffffff);

#ifdef DEBUG_GUEST_TSC
    DEBUG("Guest rdtsc = 0x%llx.\n", vm->tsc);
#endif

    sys_hvm_get_next_eip (vm->vmid, INSTR_RDTSC, &next_eip);
    sys_hvm_set_reg (vm->vmid, GUEST_EIP, next_eip);

    return 0;
}

static int inline
vmm_hypercall_get_tsc_khz (struct vm *vm, uint32_t * a0, uint32_t * a1)
{
    ASSERT (vm != NULL);
    ASSERT (a0 != NULL);
    ASSERT (a1 != NULL);
    ASSERT (1);

    uint64_t khz = sys_get_tsc_per_ms (vm->vmid);
    *a0 = khz >> 32;
    *a1 = khz & 0xffffffffull;

    return HYPERCALL_SUCCESSFUL;
}

static int
vmm_handle_hypercall (struct vm *vm)
{
    ASSERT (vm != NULL);
    ASSERT (vm->exit_reason == EXIT_REASON_HYPERCALL);

    uint32_t call_nr, a0, a1, a2, a3;
    sys_hvm_get_reg (vm->vmid, GUEST_EAX, &call_nr);
    sys_hvm_get_reg (vm->vmid, GUEST_EBX, &a0);
    sys_hvm_get_reg (vm->vmid, GUEST_ECX, &a1);
    sys_hvm_get_reg (vm->vmid, GUEST_EDX, &a2);
    sys_hvm_get_reg (vm->vmid, GUEST_ESI, &a3);

    uint32_t ret = 0;

    switch (call_nr)
    {
    case HYPERCALL_GET_TSC_KHZ:
        ret = vmm_hypercall_get_tsc_khz (vm, &a0, &a1);
        break;
    default:
#ifdef DEBUG_HYPERCALL
        KERN_DEBUG("Invalid hypercall: nr=%llx.\n", call_nr);
#endif
        ret = 1;
        break;
    }

    sys_hvm_set_reg (vm->vmid, GUEST_EAX, ret);
    sys_hvm_set_reg (vm->vmid, GUEST_EBX, a0);
    sys_hvm_set_reg (vm->vmid, GUEST_ECX, a1);
    sys_hvm_set_reg (vm->vmid, GUEST_EDX, a2);
    sys_hvm_set_reg (vm->vmid, GUEST_ESI, a3);

    uint32_t next_eip;

    sys_hvm_get_next_eip (vm->vmid, INSTR_HYPERCALL, &next_eip);
    sys_hvm_set_reg (vm->vmid, GUEST_EIP, next_eip);

    return 0;
}

static int
vmm_handle_invalid_instr (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason == EXIT_REASON_INVAL_INSTR);

    VMM_DEBUG("Invalid instruction.\n");

    sys_hvm_inject_event (vm->vmid, EVENT_EXCEPTION, T_ILLOP, 0, FALSE);
    return 0;
}

static int
vmm_handle_exit (struct vm *vm)
{
    ASSERT(vm != NULL);
    ASSERT(vm->exit_reason != EXIT_REASON_NONE);

    int rc = 0;

//		uint32_t eip;
//		sys_hvm_get_reg (vm->vmid, GUEST_EIP, &eip);
//		DEBUG("vm exit %d @ 0x%08x\n", vm->exit_reason, eip);

    switch (vm->exit_reason)
    {
    case EXIT_REASON_EXTINT:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_INTR)
        DEBUG("VMEXIT for external interrupt.\n");
#endif
        rc = 0;
        break;

    case EXIT_REASON_INTWIN:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_INTR)
        DEBUG("VMEXIT for interrupt window.\n");
#endif
        rc = sys_hvm_intercept_intr_window (vm->vmid, FALSE);
        break;

    case EXIT_REASON_IOPORT:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_IOPORT)
        DEBUG("VMEXIT for I/O port.\n");
#endif
        rc = vmm_handle_ioport (vm);
        break;

    case EXIT_REASON_RDMSR:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_MSR)
        DEBUG("VMEXIT for rdmsr.\n");
#endif
        //rc = vmm_handle_rdmsr(vm);
        sys_hvm_handle_rdmsr (vm->vmid);
        rc = 0;
        break;

    case EXIT_REASON_WRMSR:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_MSR)
        DEBUG("VMEXIT for wrmsr.\n");
#endif
        //rc = vmm_handle_wrmsr(vm);
        sys_hvm_handle_wrmsr (vm->vmid);
        rc = 0;
        break;

    case EXIT_REASON_PGFLT:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_PGFLT)
        DEBUG("VMEXIT for page fault.\n");
#endif
        rc = vmm_handle_pgflt (vm);
        break;

    case EXIT_REASON_CPUID:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_CPUID)
        DEBUG("VMEXIT for cpuid.\n");
#endif
        rc = vmm_handle_cpuid (vm);
        break;

    case EXIT_REASON_RDTSC:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_GUEST_TSC)
        DEBUG("VMEXIT for rdtsc.\n");
#endif
        rc = vmm_handle_rdtsc (vm);
        break;

    case EXIT_REASON_HYPERCALL:
#if defined (DEBUG_VMEXIT) || defined (DEBUG_HYPERCALL)
        DEBUG("VMEXIT for hypercall.\n");
#endif
        rc = vmm_handle_hypercall (vm);
        break;

    case EXIT_REASON_INVAL_INSTR:
#ifdef DEBUG_VMEXIT
        DEBUG("VMEXIT for invalid instruction.\n");
#endif
        rc = vmm_handle_invalid_instr (vm);
        break;

    default:
#ifdef DEBUG_VMEXIT
        DEBUG("VMEXIT for unknown reason %d.\n", vm->exit_reason);
#endif
        rc = -1;
    }

    return rc;
}

/*
 * @return 0 if no interrupt is injected; otherwise, return the number of
 *         injected interrupts.
 */
static int
vmm_intr_assist (struct vm *vm)
{
    ASSERT(vm != NULL);

    int vector;
    uint32_t eflags;
    int blocked = 0;

    /* no interrupt needs to be injected */
    if ((vector = vdev_peep_intout (&vm->vdev)) == -1)
    {
#if defined (DEBUG_GUEST_INTR) || defined (DEBUG_GUEST_INJECT)
        DEBUG("Found no interrupt.\n");
#endif
        return 0;
    }

    if (sys_hvm_check_pending_event (vm->vmid) == TRUE)
    {
#if defined (DEBUG_GUEST_INTR) || defined (DEBUG_GUEST_INJECT)
        DEBUG("Found pending event.\n");
#endif
        blocked = 1;
        goto after_check;
    }

    /* check if the virtual CPU is able to accept the interrupt */
    sys_hvm_get_reg (vm->vmid, GUEST_EFLAGS, &eflags);
    if (!(eflags & FL_IF))
    {
#if defined (DEBUG_GUEST_INTR) || defined (DEBUG_GUEST_INJECT)
        DEBUG("Guest EFLAGS.IF = 0.\n");
#endif
        blocked = 1;
        goto after_check;
    }
    if (sys_hvm_check_intr_shadow (vm->vmid) == TRUE)
    {
#if defined (DEBUG_GUEST_INTR) || defined (DEBUG_GUEST_INJECT)
        DEBUG("Guest in interrupt shadow.\n");
#endif
        blocked = 1;
    }

    after_check:
    /*
     * If not, enable intercepting the interrupt window so that CertiKOS
     * will be acknowledged once the virtual CPU is able to accept the
     * interrupt.
     */
    if (blocked)
    {
        sys_hvm_intercept_intr_window (vm->vmid, TRUE);
        return 0;
    }

    if ((vector = vdev_read_intout (&vm->vdev)) == -1)
        return 0;

    /* inject the interrupt and disable intercepting the interrupt window */
#if defined (DEBUG_GUEST_INTR) || defined (DEBUG_GUEST_INJECT)
    DEBUG("Inject ExtINTR vec=0x%x.\n", vector);
#endif
    sys_hvm_inject_event (vm->vmid, EVENT_EXTINT, vector, 0, FALSE);
    sys_hvm_intercept_intr_window (vm->vmid, FALSE);

    return 1;
}

//static uint8_t tmp[PAGESIZE];

int
vmm_load_bios (struct vm *vm)
{
    ASSERT(vm != NULL);

    extern uint8_t _binary___misc_bios_bin_start[],
            _binary___misc_bios_bin_size[], _binary___misc_vgabios_bin_start[],
            _binary___misc_vgabios_bin_size[];

    /* load BIOS ROM */
    ASSERT((size_t ) _binary___misc_bios_bin_size % 0x10000 == 0);

    vmm_write_guest_memory(vm,
                           0x100000 - (size_t ) _binary___misc_bios_bin_size,
                           (uintptr_t ) _binary___misc_bios_bin_start,
                           (size_t ) _binary___misc_bios_bin_size);

    /* load VGA BIOS ROM */
    vmm_write_guest_memory(vm, 0xc0000,
                           (uintptr_t ) _binary___misc_vgabios_bin_start,
                           (size_t ) _binary___misc_vgabios_bin_size);

//    /* test load success. */
//    vmm_read_guest_memory(vm, 0x100000 - (size_t ) _binary___misc_bios_bin_size,
//						  (uintptr_t ) tmp, (size_t ) _binary___misc_bios_bin_size);
//
//    int i;
//    unsigned char * addr = (unsigned char *) (0x100000 - (size_t ) _binary___misc_bios_bin_size + 8 * PAGESIZE + vm->memory);
////    unsigned char * addr = _binary___misc_bios_bin_start + PAGESIZE * 8;
//    for (i = 0; i < PAGESIZE; i ++)
//    {
//    	if (i % 16 == 0)
//    		printf("0x%08x: ", addr + i);
//       	printf("%02x ", addr[i]);
//       	if ((i + 1) % 16 == 0)
//       		printf("\n");
//    }

    return 0;
}

extern struct vmm_ops vmm_ops_amd;
extern struct vmm_ops vmm_ops_intel;

int
vmm_init_vm (struct vm *vm, uint64_t cpufreq, size_t memsize)
{
    uint64_t tsc_per_ms = sys_get_tsc_per_ms (vm->vmid);
    ASSERT(tsc_per_ms != -1);

    if (vm == NULL)
        return -1;

    if (cpufreq >= tsc_per_ms * 1000)
    {
        DEBUG(
                "Guest CPU frequency cannot be higher than the host " "CPU frequency.\n");
        return -1;
    }


    vm->vmid = 0;
    vm->cpufreq = cpufreq;
    vm->memsize = memsize;
    vm->tsc = 0;

    vm->exit_reason = EXIT_REASON_NONE;
    vm->exit_handled = TRUE;

    cpu_vendor cpuvendor = vendor ();
    if (cpuvendor == AMD)
        vm->ops = &vmm_ops_amd;
    else if (cpuvendor == INTEL)
        vm->ops = &vmm_ops_intel;
    else
    {
    	DEBUG("Cannot recognize the vendor.\n");
        return -7;
    }

    if (vmm_init_mmap (vm))
    {
    	DEBUG("Cannot initialize EPT/NPT.\n");
        return -5;
    }

    /* setup the segment registers */
    sys_hvm_set_desc (vm->vmid, GUEST_CS, &guest_seg_desc[0]);
    sys_hvm_set_desc (vm->vmid, GUEST_DS, &guest_seg_desc[1]);
    sys_hvm_set_desc (vm->vmid, GUEST_ES, &guest_seg_desc[1]);
    sys_hvm_set_desc (vm->vmid, GUEST_FS, &guest_seg_desc[1]);
    sys_hvm_set_desc (vm->vmid, GUEST_GS, &guest_seg_desc[1]);
    sys_hvm_set_desc (vm->vmid, GUEST_SS, &guest_seg_desc[1]);
    sys_hvm_set_desc (vm->vmid, GUEST_LDTR, &guest_seg_desc[2]);
    sys_hvm_set_desc (vm->vmid, GUEST_TR, &guest_seg_desc[3]);
    sys_hvm_set_desc (vm->vmid, GUEST_GDTR, &guest_seg_desc[4]);
    sys_hvm_set_desc (vm->vmid, GUEST_IDTR, &guest_seg_desc[4]);

    /* setup the general registers */
    sys_hvm_set_reg (vm->vmid, GUEST_EAX, 0x00000000);
    sys_hvm_set_reg (vm->vmid, GUEST_EBX, 0x00000000);
    sys_hvm_set_reg (vm->vmid, GUEST_ECX, 0x00000000);

    uint32_t dummy, eax;
    cpuid (0x1, &eax, &dummy, &dummy, &dummy);
    sys_hvm_set_reg (vm->vmid, GUEST_EDX, eax);

    sys_hvm_set_reg (vm->vmid, GUEST_ESI, 0x00000000);
    sys_hvm_set_reg (vm->vmid, GUEST_EDI, 0x00000000);
    sys_hvm_set_reg (vm->vmid, GUEST_EBP, 0x00000000);
    sys_hvm_set_reg (vm->vmid, GUEST_ESP, 0x00000000);
    sys_hvm_set_reg (vm->vmid, GUEST_EIP, 0x0000fff0);
    sys_hvm_set_reg (vm->vmid, GUEST_EFLAGS, 0x00000002);

    if (cpuvendor == AMD)
    {
        /* setup the control registers */
        sys_hvm_set_reg (vm->vmid, GUEST_CR0, 0x60000010);
        sys_hvm_set_reg (vm->vmid, GUEST_CR2, 0);
        sys_hvm_set_reg (vm->vmid, GUEST_CR3, 0);
        sys_hvm_set_reg (vm->vmid, GUEST_CR4, 0);
    }

    /* load BIOS */
    vmm_load_bios (vm);

    /* setup the virtual device interface */
    vdev_init (&vm->vdev, vm);

    DEBUG("VM (CPU %lld Hz, MEM %d bytes) is created.\n", cpufreq, memsize);

    return 0;
}

int
vmm_run_vm (struct vm *vm)
{
    if (vm == NULL)
        return -1;

    //uint64_t host_cpu_freq;
    uint64_t start_tsc, exit_tsc;
    int rc, injected, exit_code;

    //host_cpu_freq = 1000000000ULL;

    DEBUG("Start running VM ... \n");

    rc = 0;
    while (1)
    {
        ASSERT(vm->exit_handled == TRUE);

        injected = 0;
        start_tsc = rdtscp ();

        // vmm_update_guest_tsc_offset (vm, start_tsc);

//        DEBUG("vm enter ... \n");


        if ((rc = sys_hvm_run_vm (vm->vmid)))
            break;

//        DEBUG("vm exit ... \n");

        exit_tsc = rdtscp ();
        vmm_update_guest_tsc (vm, start_tsc, exit_tsc);

        exit_code = sys_hvm_get_exitinfo (vm->vmid, &vm->exit_reason, &vm->exit_info);

        injected = vmm_intr_assist (vm);

        vdev_update_devices (&vm->vdev);

        /* handle other types of the VM exits */
        if (vmm_handle_exit (vm))
        {
        	DEBUG("Cannot handle a VM exit (exit_reason: %d, code: %d).\n",
                      vm->exit_reason, exit_code);
            rc = -3;
            break;
        }

        vm->exit_handled = TRUE;

        /* post-handling of the interrupts from the virtual machine */
        if (injected == 0)
            vmm_intr_assist (vm);
    }

    if (rc)
    	DEBUG("Virtual machine terminates abnormally: %d.\n", rc);
    return rc;
}

int
vmm_rw_guest_memory (struct vm *vm, uintptr_t gpa, uintptr_t hva, size_t size,
                     int write)
{
    if (vm == NULL)
        return -1;

    uintptr_t from, to, from_la, to_la;
    size_t remaining, copied;

    if (gpa >= vm->memsize)
    {
        DEBUG(
                "Guest physical address 0x%08x is out of range " "(0x00000000 ~ 0x%08x).\n",
                gpa, vm->memsize);
        return 1;
    }

    if (vm->memsize - gpa < size)
    {
    	DEBUG("Size (%d bytes) is out of range (%d bytes).\n", size,
                  vm->memsize - gpa);
        return 1;
    }

    /*
     VMM_DEBUG("%s guest physical address 0x%08x %s "
     "host linear address 0x%08x, size %d bytes.\n",
     write ? "Write" : "Read", gpa, write ? "from" : "to",
     hva, size);
     */

    remaining = size;
    from = write ? hva : gpa;
    from_la = write ? from : vmm_translate_gp2hv (vm, from);
    to = write ? gpa : hva;
    to_la = write ? vmm_translate_gp2hv (vm, to) : to;

    while (remaining)
    {
        copied = MIN(PAGESIZE - (from_la - ROUNDDOWN(from_la, PAGESIZE)),
                     PAGESIZE - (to_la - ROUNDDOWN(to_la, PAGESIZE)));
        copied = MIN(copied, remaining);

        memcpy ((void *) to_la, (void *) from_la, copied);

        from_la += copied;
        from += copied;
        to_la += copied;
        to += copied;
        remaining -= copied;

        if (remaining == 0)
            break;

        if (ROUNDDOWN(from, PAGESIZE) == from)
            from_la = write ? from : vmm_translate_gp2hv (vm, from);
        if (ROUNDDOWN(to, PAGESIZE) == to)
            to_la = write ? vmm_translate_gp2hv (vm, to) : to;
    }

    return 0;
}

uintptr_t
vmm_translate_gp2hv (struct vm *vm, uintptr_t gpa)
{
    if (vm == NULL || gpa >= vm->memsize)
        return 0xffffffff;

    uintptr_t pfn;
    int line, row;

    pfn = gpa / PAGESIZE;
    line = pfn / 32;
    row = pfn % 32;

    if ((vm->mmap_bitmap[line] & (1UL << row)) == 0)
    {
        uintptr_t hva =
                (gpa >= 0xf0000000) ?
                        (uintptr_t) &vm->memory_dev[pfn * PAGESIZE] :
                        (uintptr_t) &vm->memory[pfn * PAGESIZE];
        if (gpa >= 0xf000000)
            memzero ((void *) hva, PAGESIZE);
        if (sys_hvm_mmap (vm->vmid, pfn * PAGESIZE, hva, PAT_WRITE_BACK))
            PANIC("Cannot map GPA 0x%08x to HVA 0x%08x.\n", pfn * PAGESIZE,
                  hva);
        vm->mmap_bitmap[line] |= (1UL << row);
//		DEBUG("EPT @ 0x%08x: mapped to HVA 0x%08x.\n", pfn * PAGESIZE, hva);
    }

    return (uintptr_t) vm->memory + gpa;
}
