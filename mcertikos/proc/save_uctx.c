#define num_proc 64
#define UCTXT_SIZE 17

extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];
extern int get_curid(void);

void save_uctx(int u0, int u1, int u2, int u3, int u4, int u5, int u6, int u7, int u8, int u9, int u10, int u11, int u12, int u13, int u14, int u15, int u16)
{
    int curid;
    curid = get_curid();
    UCTX_LOC[curid][0] = u0;
    UCTX_LOC[curid][1] = u1;
    UCTX_LOC[curid][2] = u2;
    UCTX_LOC[curid][3] = u3;
    UCTX_LOC[curid][4] = u4;
    UCTX_LOC[curid][5] = u5;
    UCTX_LOC[curid][6] = u6;
    UCTX_LOC[curid][7] = u7;
    UCTX_LOC[curid][8] = u8;
    UCTX_LOC[curid][9] = u9;
    UCTX_LOC[curid][10] = u10;
    UCTX_LOC[curid][11] = u11;
    UCTX_LOC[curid][12] = u12;
    UCTX_LOC[curid][13] = u13;
    UCTX_LOC[curid][14] = u14;
    UCTX_LOC[curid][15] = u15;
    UCTX_LOC[curid][16] = u16;
}
