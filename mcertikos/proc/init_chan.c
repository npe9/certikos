#define num_chan 64

struct ChanStruct {
    unsigned int isbusy;
    unsigned int content;
};

extern struct ChanStruct CHPOOL_LOC[num_chan];

void init_chan(unsigned int chan_index, unsigned int info, unsigned int content)
{
    CHPOOL_LOC[chan_index].isbusy = info; 
    CHPOOL_LOC[chan_index].content = content;
}
