struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

struct SyncIPCChan ipc_chan_pool[64];
