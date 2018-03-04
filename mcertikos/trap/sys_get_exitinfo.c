extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void uctx_set_retval2(unsigned int);
extern void uctx_set_retval3(unsigned int);
extern void uctx_set_retval4(unsigned int);
extern unsigned int vmx_get_exit_reason(void);
extern unsigned int vmx_get_exit_io_port(void);
extern unsigned int vmx_get_io_width(void);
extern unsigned int vmx_get_io_write(void);
extern unsigned int vmx_get_exit_io_rep(void);
extern unsigned int vmx_get_exit_io_str(void);
extern unsigned int vmx_get_exit_fault_addr(void);

#define EXIT_REASON_INOUT		30
#define EXIT_REASON_EPT_FAULT		48

void
sys_get_exitinfo ()
{
	unsigned int reason = 0;
	unsigned int port = 0;
	unsigned int width = 0;
	unsigned int write = 0;
	unsigned int rep = 0;
	unsigned int str = 0;
	unsigned int fault_addr = 0;
	unsigned int flags;

	flags = 0;
	reason = vmx_get_exit_reason ();
	port = vmx_get_exit_io_port ();
	width = vmx_get_io_width ();
	write = vmx_get_io_write ();
	rep = vmx_get_exit_io_rep ();
	str = vmx_get_exit_io_str ();
	fault_addr = vmx_get_exit_fault_addr ();

	uctx_set_retval1 (reason);

	if (reason == EXIT_REASON_INOUT)
	{
		uctx_set_retval2 (port);
		uctx_set_retval3 (width);
		if (write)
			flags |= (1 << 0);
		if (rep)
			flags |= (1 << 1);
		if (str)
			flags |= (1 << 2);
		uctx_set_retval4 (flags);
	}
	else if (reason == EXIT_REASON_EPT_FAULT)
	{
		uctx_set_retval2 (fault_addr);
	}

	uctx_set_errno (0);
}
