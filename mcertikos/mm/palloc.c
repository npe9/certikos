extern unsigned int get_nps(void);
extern unsigned int is_norm(unsigned int);
extern unsigned int at_get(unsigned int);
extern void at_set(unsigned int, unsigned int);
extern void at_set_c(unsigned int, unsigned int);

unsigned int palloc(unsigned int id)
{
    unsigned int tnps;
    unsigned int palloc_index;
    unsigned int palloc_cur_at;
    unsigned int palloc_is_norm;
    unsigned int palloc_free_index;

    tnps = get_nps();
    palloc_index = 1;
    palloc_free_index = tnps;
    while( palloc_index < tnps && palloc_free_index == tnps )
    {
        palloc_is_norm = is_norm(palloc_index);
        if (palloc_is_norm == 1)
        {
            palloc_cur_at = at_get(palloc_index);
            if (palloc_cur_at == 0)
                palloc_free_index = palloc_index;
        }
        palloc_index ++;
    }
    if (palloc_free_index == tnps)
      palloc_free_index = 0;
    else
    {
      at_set(palloc_free_index, 1);
      at_set_c(palloc_free_index, 0);
    }
    return palloc_free_index;
} 
