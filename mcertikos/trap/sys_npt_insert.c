extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void npt_insert(unsigned int, unsigned int);
extern unsigned int la2pa_resv(unsigned int);

void sys_npt_insert()
{
    unsigned int gpa;
    unsigned int hpa;
    gpa = uctx_arg1();
    hpa = uctx_arg2();
    hpa = la2pa_resv(hpa);
    npt_insert(gpa, hpa);
    uctx_set_errno(0);
}
