extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void uctx_set_retval2(unsigned int);
extern unsigned long long vmx_get_tsc_offset(void);

#define pow2to32 (0x100000000ull)

void sys_get_tsc_offset()
{
    unsigned long long tsc;
    unsigned int hi;
    unsigned int lo;
    tsc = vmx_get_tsc_offset();
    hi = (unsigned int) (tsc / pow2to32);
    lo = (unsigned int) (tsc % pow2to32);

    uctx_set_retval1(hi);
    uctx_set_retval2(lo);
    uctx_set_errno(0);
}
