#define PAGESIZE 4096

extern unsigned int pt_read(unsigned int, unsigned int);
extern void pt_rmv_aux(unsigned int, unsigned int);
extern unsigned int at_get_c(unsigned int);
extern void at_set_c(unsigned int, unsigned int);

unsigned int pt_rmv(unsigned int proc_index, unsigned int vadr)
{
  unsigned int padr;
  unsigned int count;
  padr = pt_read(proc_index, vadr);
  if (padr != 0)
  {
    pt_rmv_aux(proc_index, vadr);
    count = at_get_c(padr / PAGESIZE);
    if (count > 0)
      at_set_c(padr / PAGESIZE, count - 1);
  }
  return padr;
}
