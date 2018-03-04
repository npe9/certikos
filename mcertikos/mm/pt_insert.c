#define MagicNumber 1048577

extern unsigned int pt_read_pde(unsigned int, unsigned int);
extern void pt_insert_aux(unsigned int, unsigned int, unsigned int, unsigned int);
extern unsigned int pt_alloc_pde(unsigned int, unsigned int);
extern unsigned int at_get_c(unsigned int);
extern void at_set_c(unsigned int, unsigned int);

unsigned int pt_insert(unsigned int proc_index, unsigned int vadr, unsigned int padr, unsigned int perm)
{
  unsigned int pi;
  unsigned int result;
  unsigned int count;
  pi = pt_read_pde(proc_index, vadr);
  if (pi != 0)
    result = 0;
  else
  {
    result = pt_alloc_pde(proc_index, vadr);
    if (result == 0)
      result = MagicNumber;
  }
  if (result != MagicNumber)
  {
    pt_insert_aux(proc_index, vadr, padr, perm);
    count = at_get_c(padr);
    at_set_c(padr, count + 1);
  }
  return result;
}
