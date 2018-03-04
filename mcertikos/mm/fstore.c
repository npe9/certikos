#define adr_low 1073741823

extern unsigned int FlatMem_LOC[adr_low];

void fstore(unsigned int addr, unsigned int val)
{
  FlatMem_LOC[addr] = val;
}
