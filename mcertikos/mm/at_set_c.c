struct A {
    unsigned int isnorm;
    unsigned int allocated;
    unsigned int c;
};

extern struct A AT_LOC[1048576];

void at_set_c (unsigned int at_set_c_index, unsigned int c_val)
{
    AT_LOC[at_set_c_index].c = c_val;
}
