#define TSTATE_READY 0
#define num_chan 64
#define num_proc 64

extern unsigned int dequeue(unsigned int);
extern void set_state(unsigned int, unsigned int);
extern void enqueue(unsigned int, unsigned int);

void thread_wakeup(unsigned int chan_index)
{
    unsigned int proc_index;
    proc_index = dequeue(chan_index);
    if(proc_index != num_proc)
    {
        set_state(proc_index, TSTATE_READY);
        enqueue(num_chan, proc_index);
    }
}
