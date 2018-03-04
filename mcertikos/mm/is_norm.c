struct A {
    unsigned int isnorm;
    unsigned int allocated;
    unsigned int c;
};

extern struct A AT_LOC[1048576];

unsigned int is_norm (unsigned int t_is_norm_index)
{
    unsigned int tisnorm;

    tisnorm = AT_LOC[t_is_norm_index].isnorm;
    if (tisnorm == 0)
        tisnorm = 0;
    else {
        if (tisnorm == 1)
            tisnorm = 0;
        else
            tisnorm = 1;
    }

    return tisnorm;
}
