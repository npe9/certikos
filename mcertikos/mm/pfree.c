extern void at_set(unsigned int, unsigned int);

void pfree(unsigned int pfree_index)
{
    at_set(pfree_index, 0);
}
