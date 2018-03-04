#include <preinit/lib/debug.h>
#include <preinit/lib/vmx_x86.h>

extern void * memmove(void *dst, const void *src, unsigned int len);

void
flatmem_copy (unsigned int len, unsigned int from, unsigned int to)
{
	unsigned int * src = (unsigned int *) (from * 4);
	unsigned int * dst = (unsigned int *) (to * 4);
	memmove (dst, src, len * 4);
}

unsigned int
fload (unsigned int addr)
{
	return *((unsigned int *) (addr * 4));
}

void
fstore (unsigned int addr, unsigned int val)
{
	*((unsigned int *) (addr * 4)) = val;
}

extern unsigned int * VMCS_LOC;

#include <preinit/lib/ept.h>

#include <preinit/lib/types.h>

#define PAGESHIFT 12
extern void proc_init(unsigned int);
#include <sys/lib/string.h>

void
go_to_panic()
{
	KERN_PANIC("kernel panic from the verified code.\n");
}

#include <preinit/lib/x86.h>
#include <preinit/lib/vmx_x86.h>
#include <preinit/lib/vmx.h>


#define VM_USERHI			0xf0000000
#define VM_USERLO			0x40000000

#define PTE_P				0x001	/* Present */
#define PTE_W				0x002	/* Writeable */
#define PTE_U				0x004	/* User-accessible */

extern unsigned int get_curid(void);

enum __error_nr {
	E_SUCC,		/* no errors */
	E_MEM,		/* memory failure */
	E_IPC,
	E_INVAL_CALLNR,	/* invalid syscall number */
	E_INVAL_ADDR,	/* invalid address */
	E_INVAL_PID,	/* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID,     /* general invalid id */
	E_DISK_OP,	/* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR	/* XXX: always put it at the end of __error_nr */
};

void pin(){
	KERN_DEBUG("initialization completed.\n");
}

void device_output (int from, int to, int content) {
	KERN_DEBUG("from: %d, to: %d, content: %d.\n", from, to, content);
}
// XXX: function to support printf in user space
#include <preinit/lib/pmap.h>


#define NUM_PROC			64
#define VM_USERHI			0xf0000000
#define VM_USERLO			0x40000000

static char sys_buf[NUM_PROC][PAGESIZE];

extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);

void
sys_puts(void)
{
	unsigned int cur_pid;
	unsigned int str_uva, str_len;
	unsigned int remain, cur_pos, nbytes;

	cur_pid = get_curid();
	str_uva = uctx_arg2();
	str_len = uctx_arg3();

	if (!(VM_USERLO <= str_uva && str_uva + str_len <= VM_USERHI)) {
		uctx_set_errno(E_INVAL_ADDR);
		return;
	}

	remain = str_len;
	cur_pos = str_uva;

	while (remain) {
		if (remain < PAGESIZE - 1)
			nbytes = remain;
		else
			nbytes = PAGESIZE - 1;

		if (pt_copyin(cur_pid,
			      cur_pos, sys_buf[cur_pid], nbytes) != nbytes) {
			uctx_set_errno(E_MEM);
			return;
		}

		sys_buf[cur_pid][nbytes] = '\0';
		KERN_INFO("%s", sys_buf[cur_pid]);

		remain -= nbytes;
		cur_pos += nbytes;
	}

	uctx_set_errno(E_SUCC);
}

#include <lib/trap.h>

typedef struct ef_t
{
	/* registers and other info we push manually in trapasm.S */
	pushregs regs;
	uint16_t es;
	uint16_t padding_es;
	uint16_t ds;
	uint16_t padding_ds;
} ef_t;

void
sysexit (ef_t * ef)
{
}

void
sysenter_handler (ef_t * ef)
{
	sysexit (ef);
}

void
sysenter_init ()
{
}
