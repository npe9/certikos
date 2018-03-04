#define U_ES 8
#define U_DS 9
#define U_CS 13
#define U_EFLAGS 14
#define U_ESP 15
#define U_SS 16
#define kern_high 983040
#define PgSize 4096

extern unsigned int thread_spawn(void *, unsigned int, unsigned int);
extern unsigned int get_curid(void);
extern void uctx_set(unsigned int, unsigned int, unsigned int);
extern void uctx_set_eip(unsigned int, void * );
extern void proc_start_user(void);
extern void elf_load(void *, unsigned int);

unsigned int proc_create(void * elf_addr, void * fun_adr, unsigned int quota)
{
    unsigned int proc_index, id;
    id = get_curid();
    proc_index = thread_spawn((void * )proc_start_user, id, quota);
    elf_load(elf_addr, proc_index);
    uctx_set(proc_index, U_ES, 35);
    uctx_set(proc_index, U_DS, 35);
    uctx_set(proc_index, U_CS, 27);
    uctx_set(proc_index, U_SS, 35);
    uctx_set(proc_index, U_ESP, kern_high * PgSize);
    uctx_set(proc_index, U_EFLAGS, 512);
    uctx_set_eip(proc_index, fun_adr);

    return proc_index;
}
