#define num_proc 64

extern void clear_shared_mem(unsigned int, unsigned int);
extern void pmap_init(unsigned int);

void shared_mem_init(unsigned int mbi_adr)
{
  unsigned int i, j;
  pmap_init(mbi_adr);
  i = 0;
  while (i < num_proc)
  {
    j = 0;
    while (j < num_proc)
    {
      clear_shared_mem(i, j);
      j ++;
    }
    i ++;
  }
}
