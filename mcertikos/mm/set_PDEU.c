#define NUM_PROC 64
#define PT_PERM_PTU 7

extern char * PTPool_LOC[NUM_PROC][1024];

void set_PDEU(unsigned int proc_index, unsigned int pde_index, unsigned int pi)
{
    PTPool_LOC[proc_index][pde_index] = (char *)(pi * 4096 + PT_PERM_PTU);
}
