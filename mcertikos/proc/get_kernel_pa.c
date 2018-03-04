#define PAGESIZE 4096

extern unsigned int pt_read(unsigned int pid, unsigned int vaddr);

unsigned int get_kernel_pa(unsigned int pid, unsigned int va)
{
  unsigned int kpa = pt_read(pid, va);
  kpa = kpa / PAGESIZE * PAGESIZE + va % PAGESIZE;
  return kpa;
}
