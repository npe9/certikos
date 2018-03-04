extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern void uctx_set_errno(unsigned int);
extern void vmx_set_reg(unsigned int, unsigned int);

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

enum __error_nr
{
	E_SUCC = 0, /* no errors */
	E_MEM, /* memory failure */
	E_IPC,
	E_INVAL_CALLNR, /* invalid syscall number */
	E_INVAL_ADDR, /* invalid address */
	E_INVAL_PID, /* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID, /* general invalid id */
	E_DISK_OP, /* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR /* XXX: always put it at the end of __error_nr */
};

void
sys_set_reg ()
{
	unsigned int reg;
	unsigned int val;

	reg = uctx_arg2 ();
	val = uctx_arg3 ();

	if (GUEST_EAX <= reg && reg < GUEST_MAX_REG)
	{
		vmx_set_reg (reg, val);
		uctx_set_errno (E_SUCC);
	}
	else
	{
		uctx_set_errno (E_INVAL_REG);
	}
}
