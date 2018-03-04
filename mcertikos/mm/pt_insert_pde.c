extern void set_PDEU(unsigned int, unsigned int, unsigned int);

void pt_insert_pde(unsigned int proc_index, unsigned int vaddr, unsigned int pi)
{
    unsigned int pdx_index;
    pdx_index = vaddr / (4096 * 1024);
    set_PDEU(proc_index, pdx_index, pi);
}
