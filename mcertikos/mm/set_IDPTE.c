extern unsigned int IDPMap_LOC[1024][1024];

void set_IDPTE(unsigned int pde_index, unsigned int vadr, unsigned int perm)
{
    IDPMap_LOC[pde_index][vadr] = (pde_index * 1024 + vadr) * 4096 + perm;
}
