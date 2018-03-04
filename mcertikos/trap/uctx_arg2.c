#define U_EBX 4

extern unsigned int uctx_get(unsigned int, unsigned int);
extern unsigned int get_curid(void);

unsigned int uctx_arg2()
{
    unsigned int curid;
    unsigned int arg;
    curid = get_curid();
    arg = uctx_get(curid, U_EBX);
    return arg;
}
