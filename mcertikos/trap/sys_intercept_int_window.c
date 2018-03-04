extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_set_intercept_intwin(unsigned int);

void sys_set_intercept_intwin()
{
    unsigned int enable;
    enable = uctx_arg1();
    vmx_set_intercept_intwin(enable);
    uctx_set_errno(0);
}
