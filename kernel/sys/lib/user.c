#include <preinit/lib/debug.h>
#include <preinit/lib/x86.h>

#define PAGESIZE	4096
#define NUM_PROC	64
#define UCTX_SIZE	17

#define SYSENTER_ESP_MSR    0x175u

#define NUM_CHAN 64
#define TD_STATE_RUN		1

#define ROOT_QUOTA 720896

extern void proc_start_user (void);
extern unsigned int proc_create(void * elf_addr, void * fun_adr, unsigned int quota);
extern void set_curid(unsigned int curid);
extern void dequeue(unsigned int);
extern void queue_rmv(unsigned int chan_index, unsigned int proc_index);
extern void set_state(unsigned int proc_index, unsigned int state);

void
start_user (void)
{
	extern char STACK_LOC[NUM_PROC][PAGESIZE];

	unsigned int pid;

    KERN_DEBUG("In start user.\n");

	extern void *ELF_LOC[];
	extern unsigned int ELF_ENTRY_LOC[];
	pid = proc_create(ELF_LOC[0], (void *) ELF_ENTRY_LOC[0], ROOT_QUOTA);

	KERN_DEBUG("Process %d is created (elf = 0x%08x, start = 0x%08x).\n", pid,
		ELF_LOC[0], ELF_ENTRY_LOC[0]);

    KERN_INFO("Start user-space ... \n");

    queue_rmv (NUM_CHAN, pid);
    set_state (pid, TD_STATE_RUN);
	set_curid(pid);

	wrmsr (SYSENTER_ESP_MSR, (unsigned int ) (&STACK_LOC[pid][PAGESIZE - 4]));
	proc_start_user();

	KERN_PANIC("We should not be here!\n");
}
