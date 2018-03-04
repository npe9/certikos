extern void pt_init_kern(unsigned int);
extern void set_pg(void);
extern void set_pt(unsigned int);

void pt_init(unsigned int mbi_adr)
{
    pt_init_kern(mbi_adr);
    set_pt(0);
    set_pg();
}
