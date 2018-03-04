struct A {
    unsigned int isnorm;
    unsigned int allocated;
    unsigned int c;
};

extern struct A AT_LOC[1048576];

unsigned int at_get (unsigned int at_get_index)
{
    unsigned int allocated;

    allocated = AT_LOC[at_get_index].allocated;

    return allocated;
}
