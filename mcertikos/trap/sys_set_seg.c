extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern unsigned int uctx_arg6(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_set_desc(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);

typedef enum
{
	GUEST_CS = 0,
	GUEST_DS,
	GUEST_ES,
	GUEST_FS,
	GUEST_GS,
	GUEST_SS,
	GUEST_LDTR,
	GUEST_TR,
	GUEST_GDTR,
	GUEST_IDTR,
	GUEST_MAX_SEG_DESC
} guest_seg_t;

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
sys_set_seg ()
{
	unsigned int seg;
	unsigned int sel;
	unsigned int base;
	unsigned int lim;
	unsigned int ar;
	seg = uctx_arg2 ();
	sel = uctx_arg3 ();
	base = uctx_arg4 ();
	lim = uctx_arg5 ();
	ar = uctx_arg6 ();
	if (GUEST_CS <= seg && seg < GUEST_MAX_SEG_DESC)
	{
		vmx_set_desc (seg, sel, base, lim, ar);
		uctx_set_errno (E_SUCC);
	}
	else
	{
		uctx_set_errno (E_INVAL_SEG);
	}
}
