#define MAX_BUFFSIZE 1024
#define NUM_CHAN     64

extern unsigned int get_curid(void);
extern unsigned int get_state(unsigned int pidx);

extern void set_sync_chan_paddr(unsigned int chanid, unsigned int paddr);
extern void set_sync_chan_to(unsigned int chanid, unsigned int to);
extern void set_sync_chan_count(unsigned int chanid, unsigned int count);

extern unsigned int get_sync_chan_to(unsigned int chanid);

extern unsigned int get_kernel_pa(unsigned int pid, unsigned int vaddr);

unsigned int
syncsendto_chan_pre(unsigned int pid, unsigned int vaddr, unsigned int scount)
{
  unsigned int myid = get_curid();
  unsigned int target_state = get_state(pid);

  if (target_state == 3) return MAX_BUFFSIZE+2;

  if (0 <= pid && pid < NUM_CHAN) {
    unsigned int sender_kpa = get_kernel_pa(myid, vaddr);

    if (scount < MAX_BUFFSIZE) {
      set_sync_chan_paddr(myid, sender_kpa);
      set_sync_chan_count(myid, scount);
    } else {
      set_sync_chan_paddr(myid, sender_kpa);
      set_sync_chan_count(myid, MAX_BUFFSIZE);
    }

    if (get_sync_chan_to(myid) == NUM_CHAN) {
      set_sync_chan_to(myid, pid);
    } else {
      // Should Crash
    }

    return 0;
  } else {
    return MAX_BUFFSIZE+1;
  }
}
