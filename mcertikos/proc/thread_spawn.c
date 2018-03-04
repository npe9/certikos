#define READY 0
#define num_chan 64

extern unsigned int kctxt_new(void *, unsigned int, unsigned int);
extern void set_state(unsigned int, unsigned int);
extern void enqueue(unsigned int, unsigned int);

unsigned int thread_spawn(void * entry, unsigned int id, unsigned int quota)
{
    unsigned int i;
    i = kctxt_new(entry, id, quota);
    set_state(i, READY);
    enqueue(num_chan, i);
    return i;
}

