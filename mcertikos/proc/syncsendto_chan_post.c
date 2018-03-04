#define NUM_CHAN 64
#define MAX_BUFFSIZE 1024

extern unsigned int get_curid(void);
extern unsigned int get_sync_chan_to(unsigned int chanid);
extern unsigned int get_sync_chan_count(unsigned int chanid);
extern void set_sync_chan_to(unsigned int chanid, unsigned int to);

unsigned int
syncsendto_chan_post(void)
{
  unsigned int myid = get_curid();
  unsigned int to = get_sync_chan_to(myid);

  if (to == NUM_CHAN) {
    return get_sync_chan_count(myid);
  } else {
    set_sync_chan_to(myid, NUM_CHAN);
    return MAX_BUFFSIZE+3;
  }
}
