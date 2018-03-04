extern unsigned int get_curid(void);
extern unsigned int get_chan_info(unsigned int);

unsigned int is_chan_ready () 
{
    unsigned int curid, info;
    curid = get_curid ();
    info = get_chan_info(curid);
    if (info == 0)
        return 0;
    else
        return 1;
}
