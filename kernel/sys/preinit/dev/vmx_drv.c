#include <lib/gcc.h>
#include <lib/string.h>

#include <preinit/lib/debug.h>
#include <preinit/lib/string.h>
#include <preinit/lib/types.h>
#include <preinit/lib/x86.h>
#include <preinit/lib/vmx_x86.h>

#include <preinit/lib/vmx.h>
#include <preinit/lib/ept.h>

#include <preinit/dev/vmx_drv.h>

#define MSR_VMX_BASIC           0x480
#define PAGESIZE 4096

struct vmx_info vmx_info;

static bool
vmx_ctl_allows_one_setting(uint64_t msr_val, int bitpos)
{

    if (msr_val & (1ULL << (bitpos + 32)))
        return (TRUE);
    else
        return (FALSE);
}

static bool
vmx_ctl_allows_zero_setting(uint64_t msr_val, int bitpos)
{

    if ((msr_val & (1ULL << bitpos)) == 0)
        return (TRUE);
    else
        return (FALSE);
}

int
vmx_set_ctlreg (int ctl_reg, int true_ctl_reg, uint32_t ones_mask,
				uint32_t zeros_mask, uint32_t *retval)
{
	int i;
	uint64_t val, trueval;
	bool true_ctls_avail, one_allowed, zero_allowed;

	/* We cannot ask the same bit to be set to both '1' and '0' */
	if ((ones_mask ^ zeros_mask) != (ones_mask | zeros_mask))
	{
		return 1;
	}

	if (rdmsr (MSR_VMX_BASIC) & (1ULL << 55))
		true_ctls_avail = TRUE;
	else
		true_ctls_avail = FALSE;

	val = rdmsr (ctl_reg);


	if (true_ctls_avail)
		trueval = rdmsr (true_ctl_reg); /* step c */
	else
		trueval = val; /* step a */


	for (i = 0; i < 32; i++)
	{
		one_allowed = vmx_ctl_allows_one_setting (trueval, i);
		zero_allowed = vmx_ctl_allows_zero_setting (trueval, i);


		KERN_ASSERT (one_allowed || zero_allowed);

		if (zero_allowed && !one_allowed)
		{ /* b(i),c(i) */
			if (ones_mask & (1 << i))
			{
				return 1;
			}
			*retval &= ~(1 << i);
		}
		else if (one_allowed && !zero_allowed)
		{ /* b(i),c(i) */
			if (zeros_mask & (1 << i))
			{
				return 2;
			}
			*retval |= 1 << i;
		}
		else
		{
			if (zeros_mask & (1 << i)) /* b(ii),c(ii) */
				*retval &= ~(1 << i);
			else if (ones_mask & (1 << i)) /* b(ii), c(ii) */
				*retval |= 1 << i;
			else if (!true_ctls_avail)
				*retval &= ~(1 << i); /* b(iii) */
			else if (vmx_ctl_allows_zero_setting (val, i))/* c(iii)*/
				*retval &= ~(1 << i);
			else if (vmx_ctl_allows_one_setting (val, i)) /* c(iv) */
				*retval |= 1 << i;
			else
			{
				KERN_PANIC ("Cannot determine the value of bit %d "
					"of MSR 0x%08x and true MSR 0x%08x.\n", i, ctl_reg,
					true_ctl_reg);
			}
		}
	}

	return (0);
}

extern struct vmx VMX_LOC;

char msr_bitmap_LOC[PAGESIZE] __attribute__((aligned (PAGESIZE)));
char io_bitmap_LOC[PAGESIZE * 2] __attribute__((aligned (PAGESIZE)));

int
vmx_hw_init (void)
{
	int error;
	uint32_t dummy;
	uint32_t val;
	uint64_t fixed0;
	uint64_t fixed1;

	memset (&VMX_LOC, 0, sizeof(VMX_LOC));

	/* CPUID.1:ECX[bit 5] must be 1 for processor to support VMX */
	cpuid (0x00000001, &dummy, &dummy, &val, &dummy);

	if (!(val & CPUID_FEATURE_VMX))
	{
		KERN_PANIC("the hardware does not support vmx\n");
	}

	KERN_DEBUG("vmx is supported!\n");

	/* setup pin-based control registers */
	error = vmx_set_ctlreg (MSR_VMX_PINBASED_CTLS, MSR_VMX_TRUE_PINBASED_CTLS,
		PINBASED_CTLS_ONE_SETTING, PINBASED_CTLS_ZERO_SETTING,
		&vmx_info.pinbased_ctls);

	if (error)
	{
		return (error);
	}

	/* setup primary processor-based control registrers */
	error = vmx_set_ctlreg (MSR_VMX_PROCBASED_CTLS, MSR_VMX_TRUE_PROCBASED_CTLS,
		PROCBASED_CTLS_ONE_SETTING, PROCBASED_CTLS_ZERO_SETTING,
		&vmx_info.procbased_ctls);

	if (error)
	{
		return (error);
	}
	vmx_info.procbased_ctls &= ~PROCBASED_CTLS_WINDOW_SETTING;

	/* setup secondary processor-based control registers */
	error = vmx_set_ctlreg (MSR_VMX_PROCBASED_CTLS, MSR_VMX_PROCBASED_CTLS2,
		PROCBASED_CTLS2_ONE_SETTING, PROCBASED_CTLS2_ZERO_SETTING,
		&vmx_info.procbased_ctls2);

	if (error)
	{
		return (error);
	}

	/* setup VM exit control registers */
	error = vmx_set_ctlreg (MSR_VMX_EXIT_CTLS, MSR_VMX_TRUE_EXIT_CTLS,
		VM_EXIT_CTLS_ONE_SETTING, VM_EXIT_CTLS_ZERO_SETTING,
		&vmx_info.exit_ctls);
	if (error)
	{
		return (error);
	}

	/* setup VM entry control registers */
	error = vmx_set_ctlreg (MSR_VMX_ENTRY_CTLS, MSR_VMX_TRUE_ENTRY_CTLS,
		VM_ENTRY_CTLS_ONE_SETTING, VM_ENTRY_CTLS_ZERO_SETTING,
		&vmx_info.entry_ctls);

	if (error)
	{
		return (error);
	}


	/* check fixed bits of CR0 */
	fixed0 = rdmsr (MSR_VMX_CR0_FIXED0);
	fixed1 = rdmsr (MSR_VMX_CR0_FIXED1);
	vmx_info.cr0_ones_mask = (fixed0 & fixed1) & ~(CR0_PG | CR0_PE);
	vmx_info.cr0_zeros_mask = (CR0_NW | CR0_CD) | (~fixed0 & ~fixed1);

	/* check fixed bits of CR4 */
	fixed0 = rdmsr (MSR_VMX_CR4_FIXED0);
	fixed1 = rdmsr (MSR_VMX_CR4_FIXED1);
	vmx_info.cr4_ones_mask = fixed0 & fixed1;
	vmx_info.cr4_zeros_mask = ~fixed0 & ~fixed1;


	extern unsigned char VMCS_LOC[PAGESIZE];
    memset (VMCS_LOC, 0, 4096);
    memset (msr_bitmap_LOC, 0, sizeof(msr_bitmap_LOC));
    memset (io_bitmap_LOC, 0, sizeof(io_bitmap_LOC));

    // intercept all io ports
    uint32_t *bitmap = (uint32_t *) io_bitmap_LOC;
    memset (bitmap, 0xff, PAGESIZE * 2);

    // intercept all msrs
    int rw = 0;
    char *rdmsr_bitmap = msr_bitmap_LOC;
    char *wrmsr_bitmap = (char *) ((uintptr_t) msr_bitmap_LOC + 0x800);

    memset (rdmsr_bitmap, (rw & 0x1) ? 0xf : 0x0, 2048);
    memset (wrmsr_bitmap, (rw & 0x2) ? 0xf : 0x0, 2048);


	KERN_DEBUG("vmx initialized!\n");

	return 0;
}

#define OFFSETOF(type, field)    ((unsigned long) &(((type *) 0)->field))

#define VMXINFO_OFS_VMX_ENABLED    OFFSETOF(struct vmx_info, vmx_enabled)
#define VMXINFO_OFS_PINBASED_CTLS    OFFSETOF(struct vmx_info, pinbased_ctls)
#define VMXINFO_OFS_PROCBASED_CTLS    OFFSETOF(struct vmx_info, procbased_ctls)
#define VMXINFO_OFS_PROCBASED_CTLS2    OFFSETOF(struct vmx_info, procbased_ctls2)
#define VMXINFO_OFS_EXIT_CTLS    OFFSETOF(struct vmx_info, exit_ctls)
#define VMXINFO_OFS_ENTRY_CTLS    OFFSETOF(struct vmx_info, entry_ctls)
#define VMXINFO_OFS_CR0_ONES_MASK    OFFSETOF(struct vmx_info, cr0_ones_mask)
#define VMXINFO_OFS_CR0_ZEROS_MASK    OFFSETOF(struct vmx_info, cr0_zeros_mask)
#define VMXINFO_OFS_CR4_ONES_MASK    OFFSETOF(struct vmx_info, cr4_ones_mask)
#define VMXINFO_OFS_CR4_ZEROS_MASK    OFFSETOF(struct vmx_info, cr4_zeros_mask)
#define VMXINFO_OFS_VMX_REGION    OFFSETOF(struct vmx_info, vmx_region)

unsigned long vmxinfo_fields_offset[] = {
	0,
	VMXINFO_OFS_VMX_ENABLED,
	VMXINFO_OFS_PINBASED_CTLS,
	VMXINFO_OFS_PROCBASED_CTLS,
	VMXINFO_OFS_PROCBASED_CTLS2,
	VMXINFO_OFS_EXIT_CTLS,
	VMXINFO_OFS_ENTRY_CTLS,
	VMXINFO_OFS_CR0_ONES_MASK,
	VMXINFO_OFS_CR0_ZEROS_MASK,
	VMXINFO_OFS_CR4_ONES_MASK,
	VMXINFO_OFS_CR4_ZEROS_MASK,
	VMXINFO_OFS_VMX_REGION
};

unsigned int vmxinfo_get (unsigned int idx)
{
	unsigned int offset = vmxinfo_fields_offset[idx];
	unsigned char * pvmx_info = (unsigned char *) &vmx_info;
	unsigned int result = (unsigned int) * (unsigned int *)(pvmx_info + offset);

	KERN_DEBUG("vmxinfo[%d] = 0x%08x\n", idx, result);

	return result;
}







