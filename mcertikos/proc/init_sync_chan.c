#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

void init_sync_chan(unsigned int cid)
{
  SYNCCHPOOL_LOC[cid].to = num_proc;
  SYNCCHPOOL_LOC[cid].vaddr = 0;
  SYNCCHPOOL_LOC[cid].count = 0;
}
