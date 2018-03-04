struct A {
    unsigned int isnorm;
    unsigned int allocated;
    unsigned int c;
};

extern struct A AT_LOC[1048576];

unsigned int at_get_c (unsigned int at_get_c_index)
{
    unsigned int c;

    c = AT_LOC[at_get_c_index].c;

    return c;
}
