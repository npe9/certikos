#define PgSize 4096
#define PT_PERM_PTU 7

extern unsigned int get_curid(void);
extern unsigned int pt_read(unsigned int, unsigned int);
extern void pt_resv(unsigned int, unsigned int, unsigned int);

unsigned int la2pa_resv(unsigned int va)
{
    unsigned int cur_pid;
    unsigned int pa;
    cur_pid = get_curid();
    pa = pt_read(cur_pid, va);

    if (pa == 0) {
        pt_resv(cur_pid, va, PT_PERM_PTU);
        pa = pt_read(cur_pid, va);
    }

    pa = pa / PgSize * PgSize + (va % PgSize);

    return pa;
}
