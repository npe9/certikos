#include <types.h>
#include <x86.h>

#include "../vmm.h"

static int
svm_get_msr(struct vm *vm, uint32_t msr, uint64_t *val)
{
	return -1;
}

static int
svm_set_msr(struct vm *vm, uint32_t msr, uint64_t val)
{
	return -1;
}

static int
svm_get_cpuid(struct vm *vm, uint32_t in_eax, uint32_t in_ecx,
	      uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx)
{
	if (vm == NULL ||
	    eax == NULL || ebx == NULL || ecx == NULL || edx == NULL)
		return -1;

	switch (in_eax) {
	case 0x40000000:
		/* 0x40000000 ~ 0x400000ff are reserved for the hypervisor. */
		*ebx = 0x74726543;	/* "treC" */
		*ecx = 0x534f4b69;	/* "SOKi" */
		break;

	case 0x00000001:
		cpuid(in_eax, eax, ebx, ecx, edx);
		*eax = (6 << 8) | (2 << 4) | (3);
		*ebx = /* only 1 processor/core */
			(*ebx & ~(uint32_t) (0xf << 16)) | (uint32_t) (1 << 16);
		*ecx = *ecx & ~(uint32_t)
			(CPUID_FEATURE_AVX | CPUID_FEATURE_AES |
			 CPUID_FEATURE_MONITOR);
		*edx = *edx & ~(uint32_t)
			(CPUID_FEATURE_HTT | CPUID_FEATURE_MCA |
			 CPUID_FEATURE_MTRR | CPUID_FEATURE_APIC |
			 CPUID_FEATURE_MCE | CPUID_FEATURE_MSR |
			 CPUID_FEATURE_DE);
		break;

	case 0x80000001:
		cpuid(in_eax, eax, ebx, ecx, edx);
		*eax = (6 << 8) | (2 << 4) | (3);
		*ecx = *ecx & ~(uint32_t)
			(CPUID_X_FEATURE_WDT | CPUID_X_FEATURE_SKINIT |
			 CPUID_X_FEATURE_XAPIC | CPUID_X_FEATURE_SVM);
		*edx = *edx & ~(uint32_t)
			(CPUID_X_FEATURE_RDTSCP | CPUID_X_FEATURE_NX |
			 CPUID_X_FEATURE_MCA | CPUID_X_FEATURE_MTRR |
			 CPUID_X_FEATURE_APIC | CPUID_X_FEATURE_MCE |
			 CPUID_X_FEATURE_MSR | CPUID_X_FEATURE_DE);
		break;

	default:
		cpuid(in_eax, eax, ebx, ecx, edx);
		break;
	}

	return 0;
}

struct vmm_ops vmm_ops_amd = {
	.get_msr = svm_get_msr,
	.set_msr = svm_set_msr,
	.get_cpuid = svm_get_cpuid,
};
