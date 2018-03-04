#define num_proc 64

struct KCtxtStruct {
    void * ESP;
    void * EDI;
    void * ESI;
    void * EBX;
    void * EBP;
    void * RA;
};

extern struct KCtxtStruct KCtxtPool_LOC[num_proc];

void set_RA(unsigned int proc_index, void * entry)
{
    KCtxtPool_LOC[proc_index].RA = entry;
}
