extern unsigned int get_PTE(unsigned int, unsigned int, unsigned int);

unsigned int pt_read(unsigned int proc_index, unsigned int vaddr)
{
    unsigned int pdx_index;
    unsigned int vaddrl;
    unsigned int paddr;
    pdx_index = vaddr / (4096 * 1024);
    vaddrl = (vaddr / 4096) % 1024;
    paddr = get_PTE(proc_index, pdx_index, vaddrl);
    return paddr;
}
