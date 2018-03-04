#define num_chan 64
#define max_sendcount 32
#define TCB_STATE_DEAD 3

extern void set_sync_chan_count(unsigned int chanid, unsigned int count);
extern void set_sync_chan_to(unsigned int chanid, unsigned int to);
extern void set_sync_chan_vaddr(unsigned int chanid, unsigned int vaddr);
extern unsigned int get_sync_chan_to(unsigned int chanid);
extern unsigned int pt_read(unsigned int pid, unsigned int vaddr);

/*
unsigned int
syncsendto_chan(unsigned int targetid, unsigned int vaddr,
                unsigned int sendcount, unsigned int actualsentva)
{
  unsigned int myid = get_curid();
  
  unsigned int targetstate = get_state(targetid);

  if (targetstate == TCB_STATE_DEAD) return 0;

  if (0 <= targetid && targetid < num_chan) {
    unsigned int actualsentpa = pt_read(myid, actualsentva);
    actualsentpa = (actualsentpa & 0xfffff000) + (actualsentpa % 4096);
    unsigned int *asentpa = (unsigned int*)actualsentpa;
    *asentpa = (sendcount < max_sendcount) ? sendcount : max_sendcount;

    set_sync_chan_count(myid, *asentpa);
    set_sync_chan_vaddr(myid, vaddr);

    if (get_sync_chan_to(myid) == num_chan) {
      set_sync_chan_to(myid, targetid);
    } else {
      return 0;
    }

    thread_wakeup2(targetid);
    thread_sleep2();

    return 1;

  } else {

    return 0;

  }
}
*/

unsigned int 
syncsendto_chan_c_helper(unsigned int myid, unsigned int targetid, 
                         unsigned int vaddr, unsigned int sendcount, 
                         unsigned int actualsentva)
{
  unsigned int actualsentpa = pt_read(myid, actualsentva);
  actualsentpa = (actualsentpa & 0xfffff000) + (actualsentpa % 4096);
  unsigned int *asentpa = (unsigned int*)actualsentpa;
  *asentpa = (sendcount < max_sendcount) ? sendcount : max_sendcount;

  set_sync_chan_count(myid, *asentpa);
  set_sync_chan_vaddr(myid, vaddr);

  if (get_sync_chan_to(myid) == num_chan) {
    set_sync_chan_to(myid, targetid);
    return 1;
  } else {
    return 0;
  } 
}

//extern unsigned int get_state(unsigned int tid);
//extern void thread_sleep2(void);
//extern void thread_wakeup2(unsigned int pid);
//extern unsigned int get_curid(void);

/*
 * .global syncsendto_chan
 * syncsendto_chan:
 *
 * movl 0(%esp), %esi // esi holds actualsentva
 * movl 4(%esp), %edi // edi holds sendcount
 * movl 8(%esp), %ecx // ecx holds vaddr
 * movl 12(%esp), %edx // edx holds targetid
 *
 * alloc_stack_frame
 *
 * call get_curid
 * movl %eax, %ebx // ebx holds myid
 *
 * movl %edx, 0(%esp)
 * call get_state
 * cmpl %eax, $3
 * je done0
 *
 * cmpl $0, %edx
 * jl done0
 * cmpl $64, %edx // num_chan
 * jge done0
 *
 * movl %esi, 0(%esp)
 * movl %edi, 4(%esp)
 * movl %ecx, 8(%esp)
 * movl %edx, 12(%esp)
 * movl %ebx, 16(%esp)
 * call syncsendto_chan_c_helper
 *
 * cmpl $0, %eax
 * je done0
 *
 * movl %edx, 0(%esp)
 * call thread_wakeup2
 *
 * call thread_sleep2
 * jmp done1
 *
 * done0:
 * movl $0, %eax
 * jmp done
 *
 * done1:
 * movl $1, %eax
 * 
 * done:
 * 
 */
