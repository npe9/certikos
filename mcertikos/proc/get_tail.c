#define num_chan 64

struct TDQ {
    unsigned int head;
    unsigned int tail;
};

extern struct TDQ TDQPool_LOC[num_chan + 1];

unsigned int get_tail(unsigned int chan_index)
{
    return TDQPool_LOC[chan_index].tail;
}
