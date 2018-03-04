extern void set_PDE(unsigned int, unsigned int);
extern void pt_init_comm(unsigned int);

void pt_init_kern(unsigned int mbi_adr)
{
    unsigned int i;
    pt_init_comm(mbi_adr);
    i = 256;
    while(i < 960)
    {
        set_PDE(0, i);
        i ++;
    }
}
