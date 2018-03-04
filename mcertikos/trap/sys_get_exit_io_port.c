extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int svm_get_exit_io_port(void);

void sys_get_exit_io_port()
{
    unsigned int val;
    val = svm_get_exit_io_port();
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
