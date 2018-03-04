#define U_EAX 7

extern void uctx_set(unsigned int, unsigned int, unsigned int);
extern unsigned int get_curid(void);

void uctx_set_errno(unsigned int errno)
{
    unsigned int curid;
    curid = get_curid();
    uctx_set(curid, U_EAX, errno);
}
