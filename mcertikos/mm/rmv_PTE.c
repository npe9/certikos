#define NUM_PROC 64
#define PT_PERM_PTU 7

extern char * PTPool_LOC[NUM_PROC][1024];
extern void fstore(unsigned int, unsigned int);

void rmv_PTE(unsigned int proc_index, unsigned int pde_index, unsigned int vadr)
{
    unsigned int offset;
    offset = ((unsigned int)PTPool_LOC[proc_index][pde_index] - PT_PERM_PTU) / 4096;
    fstore(offset * 1024 + vadr, 0);
}
