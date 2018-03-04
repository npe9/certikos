#define num_chan 64

extern void sched_init(unsigned int);
extern void init_sync_chan(unsigned int);

void proc_init(unsigned int mbi_adr)
{
    unsigned int i;
    sched_init(mbi_adr);
    i = 0;
    while(i < num_chan)
    {
        init_sync_chan(i);
        i++;
    }
}
