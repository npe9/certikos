extern unsigned int get_curid(void);
extern unsigned int container_get_quota(unsigned int);
extern unsigned int container_get_usage(unsigned int);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);

void sys_get_quota()
{
    unsigned int curid;
    unsigned int quota;
    unsigned int usage;
    curid = get_curid();
    quota = container_get_quota(curid);
    usage = container_get_usage(curid);
    uctx_set_retval1(quota - usage);
    uctx_set_errno(0);
}
