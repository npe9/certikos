#define num_proc 64
#define PgSize 4096

extern unsigned int pt_new(unsigned int, unsigned int);
extern void set_RA(unsigned int, void *);
extern void set_SP(unsigned int, void *);

extern void STACK_LOC[num_proc][PgSize];

unsigned int kctxt_new(void * entry, unsigned int id, unsigned int quota)
{
    unsigned int proc_index;
    proc_index = pt_new(id, quota);
    if (proc_index == num_proc) {
        return num_proc;
    }
    else {
        set_SP(proc_index, & STACK_LOC[proc_index][PgSize - 4]);
        set_RA(proc_index, entry);
        return proc_index;
    }
}
