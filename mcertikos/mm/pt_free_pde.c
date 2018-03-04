extern unsigned int pt_read_pde(unsigned int, unsigned int);
extern void pt_rmv_pde(unsigned int, unsigned int);
extern void pfree(unsigned int);

void pt_free_pde(unsigned int proc_index, unsigned int vadr)
{
  unsigned int pi;
  pi = pt_read_pde(proc_index, vadr);
  pt_rmv_pde(proc_index, vadr);
  pfree(pi);
}
