#define num_proc 64

extern void set_prev(unsigned int, unsigned int);
extern void set_next(unsigned int, unsigned int);
extern unsigned int get_prev(unsigned int);
extern unsigned int get_next(unsigned int);
extern void set_head(unsigned int, unsigned int);
extern void set_tail(unsigned int, unsigned int);

void queue_rmv(unsigned int chan_index, unsigned int proc_index)
{
    unsigned int prev, next;
    prev = get_prev(proc_index);
    next = get_next(proc_index);
    if(prev == num_proc)
    {
        if(next == num_proc)
        {
            set_head(chan_index, num_proc);
            set_tail(chan_index, num_proc);
        }
        else
        {
            set_prev(next, num_proc);
            set_head(chan_index, next);
        }
    }
    else
    {
        if(next == num_proc)
        {
            set_next(prev, num_proc);
            set_tail(chan_index, prev);
        }
        else
        {
            if(prev != next)
                set_next(prev, next);
            set_prev(next, prev);
        }
    }
}
