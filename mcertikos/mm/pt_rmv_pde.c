extern void rmv_PDE(unsigned int, unsigned int);

void pt_rmv_pde(unsigned int proc_index, unsigned int vaddr)
{
    unsigned int pdx_index;
    pdx_index = vaddr / (4096 * 1024);
    rmv_PDE(proc_index, pdx_index);
}
