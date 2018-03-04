extern void set_PTX(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);

void pt_insert_aux(unsigned int proc_index, unsigned int vaddr, unsigned int paddr, unsigned int perm)
{
    unsigned int pdx_index;
    unsigned int vaddrl;
    pdx_index = vaddr / (4096 * 1024);
    vaddrl = (vaddr / 4096) % 1024;
    set_PTX(proc_index, pdx_index, vaddrl, paddr, perm);
}
