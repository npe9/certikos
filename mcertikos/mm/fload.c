#define adr_low 1073741823

extern unsigned int FlatMem_LOC[adr_low];

unsigned int fload(unsigned int addr)
{
  return FlatMem_LOC[addr];
}
