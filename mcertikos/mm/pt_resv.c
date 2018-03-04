extern unsigned int container_alloc(unsigned int);
extern unsigned int pt_insert(unsigned int, unsigned int, unsigned int, unsigned int);

#define MagicNumber 1048577

unsigned int pt_resv(unsigned int proc_index, unsigned int vaddr, unsigned int perm)
{
    unsigned int pi;
    unsigned int result;
    pi = container_alloc(proc_index);
    if (pi == 0)
      result = MagicNumber;
    else
      result = pt_insert(proc_index, vaddr, pi, perm);
    return result;
}
