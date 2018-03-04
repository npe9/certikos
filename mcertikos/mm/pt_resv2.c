extern unsigned int container_alloc(unsigned int);
extern unsigned int pt_insert(unsigned int, unsigned int, unsigned int, unsigned int);

#define MagicNumber 1048577

unsigned int pt_resv2(unsigned int proc_index, unsigned int vaddr, unsigned int perm, unsigned int proc_index2, unsigned int vaddr2, unsigned int perm2)
{
    unsigned int pi;
    unsigned int result;
    pi = container_alloc(proc_index);
    if (pi == 0)
      result = MagicNumber;
    else
    {
      result = pt_insert(proc_index, vaddr, pi, perm);
      if (result != MagicNumber)
        result = pt_insert(proc_index2, vaddr2, pi, perm2);
    }
    return result;
}
