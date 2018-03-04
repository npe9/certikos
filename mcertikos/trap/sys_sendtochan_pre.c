extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int syncsendto_chan_pre(unsigned int, unsigned int, unsigned int);

unsigned int trap_sendtochan_pre()
{
    unsigned int chid;
    unsigned int vaddr;
    unsigned int scount;
    unsigned int val;
    chid = uctx_arg2();
    vaddr = uctx_arg3();
    scount = uctx_arg4();
    val = syncsendto_chan_pre(chid, vaddr, scount);
    return val;
}
