extern void set_PDE(unsigned int, unsigned int);
extern void rmv_PDE(unsigned int, unsigned int);
extern void idpde_init(unsigned int);

#define num_proc 64
#define one_k 1024

void pt_init_comm(unsigned int mbi_adr)
{
    unsigned int i, j;
    idpde_init(mbi_adr);
    i = 0;
    while(i < num_proc)
    {
        j = 0;
        while(j < one_k)
        {
            if (j < 256)
              set_PDE(i, j);
            else if(j >= 960)
              set_PDE(i, j);
            else
              rmv_PDE(i, j);
            j++;
        }
        i++;
    }
}

