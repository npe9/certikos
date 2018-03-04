#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int paddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

void set_sync_chan_paddr(unsigned int cid, unsigned int paddrval)
{
  SYNCCHPOOL_LOC[cid].paddr = paddrval;
}
