#define NUM_PROC 64
#define PT_PERM_PTU 7

extern char * PTPool_LOC[NUM_PROC][1024];
extern unsigned int IDPMap_LOC[1024][1024];

void set_PDE(unsigned int proc_index, unsigned int pde_index)
{
    PTPool_LOC[proc_index][pde_index] = ((char *)(IDPMap_LOC[pde_index])) + PT_PERM_PTU;
}
