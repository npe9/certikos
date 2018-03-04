extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_set_tsc_offset(unsigned long long tsc_offset);

#define pow2to32 (0x100000000ull)

void sys_set_tsc_offset()
{
    unsigned int hi;
    unsigned int lo;
    unsigned long long tsc;
    hi = uctx_arg2();
    lo = uctx_arg3();
    tsc = ((unsigned long long)hi) * pow2to32 + (unsigned long long)lo;
    vmx_set_tsc_offset(tsc);
    uctx_set_errno(0);
}
