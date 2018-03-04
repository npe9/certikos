extern void pt_init(unsigned int);

void pmap_init(unsigned int mbi_adr)
{
    pt_init(mbi_adr);
}
