extern unsigned int get_curid(void);
extern unsigned int get_chan_info(unsigned int);
extern unsigned int get_chan_content(unsigned int);
extern void set_chan_info(unsigned int, unsigned int);
extern void set_chan_content(unsigned int, unsigned int);
extern void thread_wakeup(unsigned int);

unsigned int receive_chan()
{
    unsigned int chan_index;
    unsigned int info;
    unsigned int content;
    chan_index = get_curid();
    info = get_chan_info(chan_index);
    if (info == 1)
    {
        content = get_chan_content(chan_index);
        thread_wakeup(chan_index);
        set_chan_info(chan_index, 0);
        set_chan_content(chan_index, 0);
        return content;
    }
    else
        return 0;
}
