#define num_proc 64

extern void set_prev(unsigned int, unsigned int);
extern unsigned int get_head(unsigned int);
extern unsigned int get_next(unsigned int);
extern void set_head(unsigned int, unsigned int);
extern void set_tail(unsigned int, unsigned int);

unsigned int dequeue(unsigned int chan_index)
{
    unsigned int head, next, proc_index;
    proc_index = num_proc;
    head = get_head(chan_index);
    if(head != num_proc)
    {
        proc_index = head;
        next = get_next(head);
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
    return proc_index;
}
