extern void set_bit(unsigned int, unsigned int);
extern void pt_rmv(unsigned int, unsigned int);

#define PgSize 4096
#define kern_low 262144
#define kern_high 983040
#define adr_low (kern_low * PgSize)
#define adr_high (kern_high * PgSize)

void pt_free(unsigned int proc_index)
{
    unsigned int i;
    set_bit(proc_index, 0);
    i = adr_low;
    while(i < adr_high)
    {
        pt_rmv(proc_index, i);
        i = i + PgSize;
    }
}
