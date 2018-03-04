extern unsigned int container_alloc(unsigned int);
extern void pt_insert_pde(unsigned int, unsigned int, unsigned int);
extern void rmv_PTE(unsigned int, unsigned int, unsigned int);

unsigned int pt_alloc_pde(unsigned int proc_index, unsigned int vadr)
{
  unsigned int i;
  unsigned int pi;
  unsigned int pde_index;
  pi = container_alloc(proc_index);
  if (pi != 0)
  {
    pt_insert_pde(proc_index, vadr, pi);
    pde_index = vadr / (4096 * 1024);
    i = 0;
    while (i < 1024)
    {
      rmv_PTE(proc_index, pde_index, i);
      i ++;
    }
  }
  return pi;
}
