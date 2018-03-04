#define num_chan 64

extern void thread_init(unsigned int);
extern void tdq_init(unsigned int);

void tdqueue_init(unsigned int mbi_adr)
{
    unsigned int i;
    thread_init(mbi_adr);
    i = 0;
    while (i <= num_chan)
    {
        tdq_init(i);
        i++;
    }
}
