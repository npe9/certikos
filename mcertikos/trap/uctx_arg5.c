#define U_ESI 1

extern unsigned int uctx_get(unsigned int, unsigned int);
extern unsigned int get_curid(void);

unsigned int uctx_arg5()
{
    unsigned int curid;
    unsigned int arg;
    curid = get_curid();
    arg = uctx_get(curid, U_ESI);
    return arg;
}
