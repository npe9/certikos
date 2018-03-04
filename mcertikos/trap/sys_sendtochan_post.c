extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int syncsendto_chan_post(void);

void trap_sendtochan_post()
{
    unsigned int val;
    val = syncsendto_chan_post();
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
