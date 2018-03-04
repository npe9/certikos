#define NUM_PROC 64

extern char * PTPool_LOC[NUM_PROC][1024];

unsigned int get_PDE(unsigned int proc_index, unsigned int pde_index)
{
    unsigned int pde;
    pde = ((unsigned int)PTPool_LOC[proc_index][pde_index]) / 4096;
    return pde;
}
