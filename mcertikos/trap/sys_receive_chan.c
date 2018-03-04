extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int syncreceive_chan(unsigned int, unsigned int, unsigned int);

void sys_receive_chan()
{
    unsigned int fromid;
    unsigned int vaddr;
    unsigned int rcount;
    unsigned int val;
    fromid = uctx_arg2();
    vaddr = uctx_arg3();
    rcount = uctx_arg4();
    val = syncreceive_chan(fromid, vaddr, rcount);
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
