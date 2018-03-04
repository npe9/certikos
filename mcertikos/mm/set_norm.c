struct A {
    unsigned int isnorm;
    unsigned int allocated;
    unsigned int c;
};

extern struct A AT_LOC[1048576];

void set_norm (unsigned int set_norm_index, unsigned int norm_val)
{
    unsigned int tisnorm;

    AT_LOC[set_norm_index].isnorm = norm_val;
    AT_LOC[set_norm_index].allocated = 0;
    AT_LOC[set_norm_index].c = 0;
}
