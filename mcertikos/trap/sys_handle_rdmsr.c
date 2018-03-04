typedef unsigned int	uint32_t;
typedef unsigned long long	uint64_t;

enum
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
extern uint64_t rdmsr(uint32_t msr);

#define pow2to32 (0x100000000ull)

void sys_handle_rdmsr()
{
    uint32_t msr, next_eip;
    uint64_t val;

    msr = vmx_get_reg(GUEST_EAX);

    val = rdmsr(msr);

    vmx_set_reg(GUEST_EAX, (unsigned int)(val % pow2to32));
    vmx_set_reg(GUEST_EDX, (unsigned int)(val / pow2to32));

    next_eip = vmx_get_next_eip();
    vmx_set_reg(GUEST_EIP, next_eip);
    uctx_set_errno(0);
}
