#include <types.h>
#include <x86.h>
#include <string.h>
#include <stdio.h>

#include "../vmm.h"

static int
vmx_get_msr(struct vm *vm, uint32_t msr, uint64_t *val)
{
    return -1;
}

static int
vmx_set_msr(struct vm *vm, uint32_t msr, uint64_t val)
{
    return -1;
}

static int
vmx_get_cpuid(struct vm *vm, uint32_t in_eax, uint32_t in_ecx,
	      uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx)
{
	if (vm == NULL ||
	    eax == NULL || ebx == NULL || ecx == NULL || edx == NULL)
		return -1;

    uint32_t func = in_eax;
    static char certikos_id[12] = "CertiKOS\0\0\0\0";
    /*
    struct pcpuinfo *cpuinfo = &pcpu_cur()->arch_info;

    if (cpuinfo->cpuid_exthigh && func >= 0x80000000) {
        if (func > cpuinfo->cpuid_exthigh)
            func = cpuinfo->cpuid_exthigh;
    } else if (func >= 0x40000000) {
        func = 0x40000000;
    } else if (func > cpuinfo->cpuid_high) {
        func = cpuinfo->cpuid_high;
    }
    */

    switch (func) {
    case 0x00000000:
    case 0x00000002:
    case 0x00000003:
    case 0x0000000a:
    case 0x80000000:
    case 0x80000001:
    case 0x80000002:
    case 0x80000003:
    case 0x80000004:
    case 0x80000005:
    case 0x80000006:
    case 0x80000007:
    case 0x80000008:
        cpuid(func, eax, ebx, ecx, edx);
        break;

    case 0x00000001:
        cpuid(func, eax, ebx, ecx, edx);
        /* lapic id = 0, no HTT */
        *ebx &= ~(0x000000ff << 16);
        /* no VMX, SMX, SpeedStep, ...  */
        *ecx &= ~(CPUID_FEATURE_MONITOR | CPUID_FEATURE_VMX |
              CPUID_FEATURE_SMX | CPUID_FEATURE_EIST |
              CPUID_FEATURE_TM2 | CPUID_FEATURE_XTPR |
              CPUID_FEATURE_PCID | CPUID_FEATURE_X2APIC |
              CPUID_FEATURE_TSC_DEADLINE | CPUID_FEATURE_AES |
              CPUID_FEATURE_XSAVE | CPUID_FEATURE_OSXSAVE |
              CPUID_FEATURE_AVX);
        /* no ... */
        *edx &= ~(CPUID_FEATURE_DE | CPUID_FEATURE_MSR |
              CPUID_FEATURE_APIC | CPUID_FEATURE_MCE |
              CPUID_FEATURE_SYSENTREXIT | CPUID_FEATURE_MTRR |
              CPUID_FEATURE_MCA | CPUID_FEATURE_ACPI |
              CPUID_FEATURE_HTT | CPUID_FEATURE_TM);
        break;

    case 0x00000004:
        cpuid(func, eax, ebx, ecx, edx);
        *eax &= 0xffff8000;
        *eax |= 0x04008000;
        break;

    case 0x00000006:
        *eax = *ebx = *ecx = *edx = 0;
        break;

    case 0x0000000b:
        *eax = *ebx = *edx = 0;
        *ecx = in_ecx & 0xff;
        break;

    case 0x40000000:
        *eax = 0x40000000;
        memcpy(ebx, &certikos_id[0], 4);
        memcpy(ecx, &certikos_id[4], 4);
        memcpy(edx, &certikos_id[8], 4);
        break;

    default:
        *eax = *ebx = *ecx = *edx = 0;
    }

	return 0;
}

struct vmm_ops vmm_ops_intel = {
	.get_msr = vmx_get_msr,
	.set_msr = vmx_set_msr,
	.get_cpuid = vmx_get_cpuid,
};
