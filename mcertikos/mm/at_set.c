struct A {
    unsigned int isnorm;
    unsigned int allocated;
    unsigned int c;
};

extern struct A AT_LOC[1048576];

void at_set (unsigned int at_set_index, unsigned int allocated_val)
{
    AT_LOC[at_set_index].allocated = allocated_val;
}
