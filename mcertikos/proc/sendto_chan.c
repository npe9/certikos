#define num_chan 64

extern unsigned int get_chan_info(unsigned int);
extern void set_chan_info(unsigned int, unsigned int);
extern void set_chan_content(unsigned int, unsigned int);

unsigned int sendto_chan (unsigned int chan_index, unsigned int content)
{
    unsigned int info;
    if (0 <= chan_index)
    {
        if(chan_index < num_chan)
        {
            info = get_chan_info(chan_index);
            if (info == 0)
            {
                set_chan_info (chan_index, 1);
                set_chan_content (chan_index, content);
                return 1;
            }
            else
                return 0;
        }
        else
            return 0;
    }
    else
        return 0;
}
