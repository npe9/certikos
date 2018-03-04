#define num_proc 64

struct TCB {
    unsigned int state;
    unsigned int prev;
    unsigned int next;
};

extern struct TCB TCBPool_LOC[num_proc];

void tcb_init(unsigned int proc_index)
{
    TCBPool_LOC[proc_index].state = 3;
    TCBPool_LOC[proc_index].prev = num_proc;
    TCBPool_LOC[proc_index].next = num_proc;
}
