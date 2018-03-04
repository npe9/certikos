extern unsigned int container_split(unsigned int, unsigned int);
 
unsigned int pt_new(unsigned int id, unsigned int quota)
{
    unsigned int child;
    child = container_split(id, quota);   
    return child;
} 
