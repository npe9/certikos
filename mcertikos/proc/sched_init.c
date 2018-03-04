#define TSTATE_RUN 1

extern void tdqueue_init(unsigned int);
extern void set_curid(unsigned int);
extern void set_state(unsigned int, unsigned int);

void sched_init(unsigned int mbi_adr)
{
    tdqueue_init(mbi_adr);
    set_curid(0);
    set_state(0, TSTATE_RUN);
}
