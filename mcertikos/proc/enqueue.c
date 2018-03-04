#define num_proc 64

extern void set_prev(unsigned int, unsigned int);
extern void set_next(unsigned int, unsigned int);
extern unsigned int get_tail(unsigned int);
extern void set_head(unsigned int, unsigned int);
extern void set_tail(unsigned int, unsigned int);

void enqueue(unsigned int chan_index, unsigned int proc_index)
{
    unsigned int tail;
    tail = get_tail(chan_index);
    if(tail == num_proc)
    {
        set_prev(proc_index, num_proc);
        set_next(proc_index, num_proc);
        set_head(chan_index, proc_index);
        set_tail(chan_index, proc_index);
    }
    else
    {
        set_next(tail, proc_index);
        set_prev(proc_index, tail);
        set_next(proc_index, num_proc);
        set_tail(chan_index, proc_index);
    }
}
