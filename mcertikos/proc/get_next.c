#define num_proc 64

struct TCB {
    unsigned int state;
    unsigned int prev;
    unsigned int next;
};

extern struct TCB TCBPool_LOC[num_proc];

unsigned int get_next(unsigned int proc_index)
{
    return TCBPool_LOC[proc_index].next;
}
