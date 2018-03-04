#define NUM_PROC 64
#define PT_PERM_UP 0

extern char * PTPool_LOC[NUM_PROC][1024];

void rmv_PDE(unsigned int proc_index, unsigned int pde_index)
{
    PTPool_LOC[proc_index][pde_index] = (char *)PT_PERM_UP;
}
