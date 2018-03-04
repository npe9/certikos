#define NUM_PROC 64

extern void set_cr3 (char **); 

extern char * PTPool_LOC[NUM_PROC][1024];

void set_pt(unsigned int index)
{
    set_cr3(PTPool_LOC[index]);
}
