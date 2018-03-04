#define PT_PERM_PTU 7

extern unsigned int get_curid(void);
extern void pt_resv(unsigned int, unsigned int, unsigned int);
extern void uctx_set_errno(unsigned int);

void ptf_resv(unsigned int vaddr)
{
    unsigned int curid;
    curid = get_curid();
    pt_resv(curid, vaddr, PT_PERM_PTU);
    uctx_set_errno(0);
}
