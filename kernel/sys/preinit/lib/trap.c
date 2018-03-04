#include <lib/string.h>
#include <lib/trap.h>
#include <preinit/lib/debug.h>
#include <sys/lib/x86.h>
#include <preinit/dev/intr.h>
#include <preinit/lib/syscall.h>


extern unsigned int UCTX_LOC[NUM_PROC][UCTX_SIZE];

extern void set_pt (unsigned int index);
extern unsigned int get_curid ();
extern unsigned int uctx_get (unsigned int proc_index, unsigned int ofs);
extern unsigned int pt_resv(unsigned int proc_index, unsigned int vaddr, unsigned int perm);
extern unsigned int uctx_arg1();
extern void syscall_dispatch_C();
extern void proc_start_user(void);


static int
spurious_intr_handler (void)
{
    return 0;
}

static int
timer_intr_handler (void)
{
    intr_eoi ();

    return 0;
}

static int
default_intr_handler (void)
{
    intr_eoi ();
    return 0;
}

void
interrupt_handler (void)
{
    unsigned int cur_pid;
    unsigned int trapno;

    cur_pid = get_curid ();
    trapno = uctx_get (cur_pid, U_TRAPNO);

    switch (trapno)
    {
    case T_IRQ0 + IRQ_SPURIOUS:
        spurious_intr_handler ();
        break;
    case T_IRQ0 + IRQ_TIMER:
        timer_intr_handler ();
        break;
    default:
        default_intr_handler ();
    }
}


static void
trap_dump(tf_t *tf)
{
	if (tf == NULL)
		return;

	uintptr_t base = (uintptr_t) tf;

	KERN_DEBUG("trapframe at %x\n", base);
	KERN_DEBUG("\t%08x:\tedi:   \t\t%08x\n", &tf->regs.edi, tf->regs.edi);
	KERN_DEBUG("\t%08x:\tesi:   \t\t%08x\n", &tf->regs.esi, tf->regs.esi);
	KERN_DEBUG("\t%08x:\tebp:   \t\t%08x\n", &tf->regs.ebp, tf->regs.ebp);
	KERN_DEBUG("\t%08x:\tesp:   \t\t%08x\n", &tf->regs.oesp, tf->regs.oesp);
	KERN_DEBUG("\t%08x:\tebx:   \t\t%08x\n", &tf->regs.ebx, tf->regs.ebx);
	KERN_DEBUG("\t%08x:\tedx:   \t\t%08x\n", &tf->regs.edx, tf->regs.edx);
	KERN_DEBUG("\t%08x:\tecx:   \t\t%08x\n", &tf->regs.ecx, tf->regs.ecx);
	KERN_DEBUG("\t%08x:\teax:   \t\t%08x\n", &tf->regs.eax, tf->regs.eax);
	KERN_DEBUG("\t%08x:\tes:    \t\t%08x\n", &tf->es, tf->es);
	KERN_DEBUG("\t%08x:\tds:    \t\t%08x\n", &tf->ds, tf->ds);
	KERN_DEBUG("\t%08x:\ttrapno:\t\t%08x\n", &tf->trapno, tf->trapno);
	KERN_DEBUG("\t%08x:\terr:   \t\t%08x\n", &tf->err, tf->err);
	KERN_DEBUG("\t%08x:\teip:   \t\t%08x\n", &tf->eip, tf->eip);
	KERN_DEBUG("\t%08x:\tcs:    \t\t%08x\n", &tf->cs, tf->cs);
	KERN_DEBUG("\t%08x:\teflags:\t\t%08x\n", &tf->eflags, tf->eflags);
	KERN_DEBUG("\t%08x:\tesp:   \t\t%08x\n", &tf->esp, tf->esp);
	KERN_DEBUG("\t%08x:\tss:    \t\t%08x\n", &tf->ss, tf->ss);
}

void
exception_handler(void)
{
	unsigned int cur_pid;

	cur_pid = get_curid();
	trap_dump((tf_t *) UCTX_LOC[cur_pid]);

	KERN_PANIC("Trap %d @ 0x%08x.\n",
		   uctx_get(cur_pid, U_TRAPNO), uctx_get(cur_pid, U_EIP));
}


extern void sys_puts(void);
extern void sys_yield(void);
extern void sys_run_vm(void);

static void
syscall_handler(void)
{
	unsigned int nr = uctx_arg1();

	if (nr == SYS_puts)
	{
		sys_puts();
	}
	else if (nr == SYS_get_tsc_per_ms)
	{
		sys_get_tsc_per_ms();
	}
	else if (nr == SYS_disk_op)
	{
		sys_disk_op();
	}
	else if (nr == SYS_disk_cap)
	{
		sys_disk_cap();
	}
	else
	{
		KERN_PANIC("unhandled syscall: %d", nr);
	}

	unsigned errno = uctx_arg1();
	if (errno != E_SUCC)
	{
		KERN_DEBUG("syscall %d return with error no %d\n", nr, errno);
	}

}

void
trap (tf_t *tf)
{
	unsigned int cur_pid;
	cur_pid = get_curid ();
	memcpy (UCTX_LOC[cur_pid], tf, sizeof(tf_t));

	set_pt (0);

	if (T_DIVIDE <= tf->trapno && tf->trapno <= T_SECEV)
	{
		exception_handler ();
	}
	else if (T_IRQ0 + IRQ_TIMER <= tf->trapno && tf->trapno <= T_IRQ0 + IRQ_IDE2)
		interrupt_handler ();
	else if (tf->trapno == T_SYSCALL)
	{
		syscall_handler ();
	}

	proc_start_user ();
}

uint32_t
trap_get()
{
	uint32_t cr2 = rcr2();
	return (cr2 & ~0xFFFUL);
}
