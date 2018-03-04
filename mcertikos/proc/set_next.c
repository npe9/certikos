#define num_proc 64

struct TCB {
    unsigned int state;
    unsigned int prev;
    unsigned int next;
};

extern struct TCB TCBPool_LOC[num_proc];

void set_next(unsigned int proc_index, unsigned int next)
{
    TCBPool_LOC[proc_index].next = next;
}
