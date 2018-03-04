#define U_EBX 4

extern void uctx_set(unsigned int, unsigned int, unsigned int);
extern unsigned int get_curid(void);

void uctx_set_retval1(unsigned int retval)
{
    unsigned int curid;
    curid = get_curid();
    uctx_set(curid, U_EBX, retval);
}
