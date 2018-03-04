extern unsigned int get_size(void);
extern unsigned int get_mms(unsigned int);
extern unsigned int get_mml(unsigned int);
extern unsigned int is_usable(unsigned int);
extern void set_norm(unsigned int, unsigned int);
extern void set_nps(unsigned int);
extern void boot_loader(unsigned int);

void mem_init(unsigned int mbi_adr)
{
    unsigned int i, j, s, l, isnorm, nps, maxs, size, mm, flag;
    boot_loader(mbi_adr);
    i = 0;
    size = get_size();
    nps = 0;
    while(i < size)
    {
        s = get_mms(i);
        l = get_mml(i);
        maxs = (s + l) / 4096 + 1;
        if(maxs > nps)
            nps = maxs;
        i++;
    }
    set_nps(nps);
    i = 0;
    while(i < nps)
    {
        if(i < 262144 || i >= 786432)
            set_norm(i, 1);
        else
        {
            j = 0;
            flag = 0;
            isnorm = 0;
            while(j < size && flag == 0)
            {
                s = get_mms(j);
                l = get_mml(j);
                isnorm = is_usable(j);
                if(s <= i * 4096 && l + s >= (i + 1) * 4096)
                    flag = 1;
                j++;
            }
            if(flag == 1 && isnorm == 1)
                set_norm(i, 2);
            else
                set_norm(i, 0);
        }
        i++;
    }
}

