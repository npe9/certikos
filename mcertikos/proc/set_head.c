#define num_chan 64

struct TDQ {
    unsigned int head;
    unsigned int tail;
};

extern struct TDQ TDQPool_LOC[num_chan + 1];

void set_head(unsigned int chan_index, unsigned int head)
{
    TDQPool_LOC[chan_index].head = head;
}
