#define num_chan 64

struct ChanStruct {
    unsigned int isbusy;
    unsigned int content;
};

extern struct ChanStruct CHPOOL_LOC[num_chan];

void set_chan_info(unsigned int chan_index, unsigned int info)
{
    CHPOOL_LOC[chan_index].isbusy = info; 
}
