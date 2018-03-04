#define num_chan 64
#define num_proc 64

struct TDQ {
    unsigned int head;
    unsigned int tail;
};

extern struct TDQ TDQPool_LOC[num_chan + 1];

void tdq_init(unsigned int chan_index)
{
    TDQPool_LOC[chan_index].head = num_proc;
    TDQPool_LOC[chan_index].tail = num_proc;
}
