extern unsigned int PTP_LOC[64];

void set_bit(unsigned int proc_index, unsigned int val)
{
    PTP_LOC[proc_index] = val;
}
