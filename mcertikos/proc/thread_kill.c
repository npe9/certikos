/* #define TSTATE_DEAD 3

extern void set_state(unsigned int, unsigned int);
extern void queue_rmv(unsigned int, unsigned int);
extern void thread_free(unsigned int);

void thread_kill(unsigned int proc_index, unsigned int chan_index)
{
    set_state(proc_index, TSTATE_DEAD);
    queue_rmv(chan_index, proc_index);
    thread_free(proc_index);
} */
