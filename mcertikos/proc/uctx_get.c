#define num_proc 64
#define UCTXT_SIZE 17

extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];

unsigned int uctx_get(unsigned int proc_index, unsigned int ofs)
{
    return UCTX_LOC[proc_index][ofs];
}
