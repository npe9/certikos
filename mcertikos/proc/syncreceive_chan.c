#define NUM_CHAN 64
#define TCB_STATE_DEAD 3
#define MAX_BUFFSIZE 1024

extern unsigned int get_curid(void);
extern unsigned int get_state(unsigned int pid);

extern unsigned int get_sync_chan_to(unsigned int chanid);
extern unsigned int get_sync_chan_count(unsigned int chanid);
extern unsigned int get_sync_chan_paddr(unsigned int chanid);

extern unsigned int get_kernel_pa(unsigned int pid, unsigned int vaddr);

extern void set_sync_chan_to(unsigned int chanid, unsigned int to);
extern void set_sync_chan_count(unsigned int chanid, unsigned int count);
extern void set_sync_chan_paddr(unsigned int chanid, unsigned int paddr);

extern void flatmem_copy(void *to, void *from, unsigned int len);
extern void thread_wakeup(unsigned int pid);

unsigned int
syncreceive_chan(unsigned int pid, unsigned int vaddr, unsigned int rcount)
{
  unsigned int myid = get_curid();
  unsigned int sender_state = get_state(pid);

  if (sender_state == TCB_STATE_DEAD) return MAX_BUFFSIZE+2;

  unsigned int sender_to = get_sync_chan_to(pid);

  if (sender_to == myid) {
    unsigned int sender_count = get_sync_chan_count(pid);
    unsigned int sbuffpa = get_sync_chan_paddr(pid);

    unsigned int arecvcount = (rcount < sender_count) ? rcount : sender_count;
    unsigned int arecvsize = arecvcount * sizeof(unsigned int);

    unsigned int rbuffva = vaddr;

    unsigned int rbuffpa = get_kernel_pa(myid, rbuffva);

    flatmem_copy((void *)rbuffpa, (void *)sbuffpa, arecvsize);

    set_sync_chan_to(pid, NUM_CHAN);
    set_sync_chan_paddr(pid, 0);
    set_sync_chan_count(pid, arecvcount);

    thread_wakeup(pid);

    return arecvcount;

  } else {
    return MAX_BUFFSIZE+3;
  }
}
