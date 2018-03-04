#define num_proc 64
#define UCTXT_SIZE 17
#define U_EIP 12

extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];

void uctx_set_eip(unsigned int proc_index, void * val)
{
    UCTX_LOC[proc_index][U_EIP] = val;
}
