#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

void set_sync_chan_count(unsigned int cid, unsigned int countval)
{
  SYNCCHPOOL_LOC[cid].count = countval;
}
