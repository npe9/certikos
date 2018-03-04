typedef unsigned int	uint32_t;
typedef unsigned long long	uint64_t;

typedef enum
{
	GUEST_EAX = 0,
	GUEST_EBX,
	GUEST_ECX,
	GUEST_EDX,
	GUEST_ESI,
	GUEST_EDI,
	GUEST_EBP,
	GUEST_ESP,
	GUEST_EIP,
	GUEST_EFLAGS,
	GUEST_CR0,
	GUEST_CR2,
	GUEST_CR3,
	GUEST_CR4,
	GUEST_MAX_REG
} guest_reg_t;

extern void uctx_set_errno(unsigned int);

extern unsigned int vmx_get_reg(unsigned int reg);
extern void vmx_set_reg(unsigned int, unsigned int);
extern unsigned int vmx_get_next_eip(void);
extern int wrmsr(uint32_t msr, uint64_t val);

#define pow2to32 (0x100000000ull)

void sys_handle_wrmsr()
{
	uint32_t msr, next_eip, eax, edx;
	uint64_t val;

	msr = vmx_get_reg(GUEST_ECX);
	eax = vmx_get_reg(GUEST_EAX);
	edx = vmx_get_reg(GUEST_EDX);
	val = (((uint64_t) edx) * pow2to32) + (uint64_t) eax;
	wrmsr(msr, val);

	next_eip = vmx_get_next_eip();
    vmx_set_reg(GUEST_EIP, next_eip);

    uctx_set_errno(0);
}
