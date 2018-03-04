#define PT_PERM_PTU 7
#define addr_low 1073741824
#define addr_high 4026531840

extern unsigned int get_curid(void);
extern void pt_resv(unsigned int, unsigned int, unsigned int);

void ptfault_resv(unsigned int vaddr)
{
    unsigned int curid; 
    curid = get_curid();
    if (addr_low <= vaddr < addr_high)
      pt_resv(curid, vaddr, PT_PERM_PTU);
}
