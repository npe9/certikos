#define NUM_ID 64
#define MAX_CHILDREN 3

extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int get_curid(void);
extern unsigned int container_get_nchildren(unsigned int);
extern unsigned int container_can_consume(unsigned int, unsigned int);
extern unsigned int proc_create(void *, void * ); 

extern void * ELF_ENTRY_LOC[NUM_ID];
extern void * ELF_LOC;

void sys_proc_create()
{
    unsigned int elf_id;
    unsigned int proc_index;
    unsigned int quota, qok;
    unsigned int nc;

    curid = get_curid();
    quota = uctx_arg3();    
    qok = container_can_consume(curid, quota);
    nc = container_get_nchildren(curid);
    if (qok == 0 || NUM_ID < curid * MAX_CHILDREN + 1 + MAX_CHILDREN 
                 || nc == MAX_CHILDREN) uctx_set_errno(1);
    else {    
        elf_id = uctx_arg2();
        proc_index = proc_create(ELF_LOC, ELF_ENTRY_LOC[elf_id], quota);
        uctx_set_retval1(proc_index);
        uctx_set_errno(0);
    }
}
