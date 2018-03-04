extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_inject_event(unsigned int, unsigned int, unsigned int, unsigned int);

void sys_inject_event()
{
    unsigned int type;
    unsigned int vector;
    unsigned int errcode;
    unsigned int ev;
    type = uctx_arg2();
    vector = uctx_arg3();
    errcode = uctx_arg4();
    ev = uctx_arg5();
    vmx_inject_event(type, vector, errcode, ev);
    uctx_set_errno(0);
}
