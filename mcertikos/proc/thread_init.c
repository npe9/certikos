#define num_proc 64

// extern void pmap_init(unsigned int);
extern void sharedmem_init(unsigned int);
extern void tcb_init(unsigned int);

void thread_init(unsigned int mbi_adr)
{
    unsigned int i;
    sharedmem_init(mbi_adr);
    i = 0;
    while (i < num_proc)
    {
        tcb_init(i);
        i++;
    }
}
