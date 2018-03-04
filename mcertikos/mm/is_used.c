extern unsigned int PTP_LOC[64];

unsigned int is_used(unsigned int proc_index)
{
    unsigned int val;
    val = PTP_LOC[proc_index];
    return val;
}
