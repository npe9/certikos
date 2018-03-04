#define PT_PERM_PTKF 3
#define PT_PERM_PTKT 259

extern void contaner_init(unsigned int);
extern void set_IDPTE(unsigned int, unsigned int, unsigned int);

void idpde_init(unsigned int mbi_adr)
{
  unsigned int i, j;
  unsigned int perm;
  container_init(mbi_adr);
  i = 0;
  while(i < 1024)
  {
    if (i < 256)
      perm = PT_PERM_PTKT;
    else if (i >= 960)
      perm = PT_PERM_PTKT;
    else
      perm = PT_PERM_PTKF;
    j = 0;
    while(j < 1024)
    {
      set_IDPTE(i, j, perm);
      j ++;
    }
    i ++;
  }
}
