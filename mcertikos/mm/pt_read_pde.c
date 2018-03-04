extern unsigned int get_PDE(unsigned int, unsigned int);

unsigned int pt_read_pde(unsigned int proc_index, unsigned int vaddr)
{
    unsigned int pdx_index;
    unsigned int paddr;
    pdx_index = vaddr / (4096 * 1024);
    paddr = get_PDE(proc_index, pdx_index);
    return paddr;
}
