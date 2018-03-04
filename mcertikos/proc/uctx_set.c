#define num_proc 64
#define UCTXT_SIZE 17

extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];

void uctx_set(unsigned int proc_index, unsigned int ofs, unsigned int val)
{
    UCTX_LOC[proc_index][ofs] = val;
}
