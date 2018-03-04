/* Trap handler entry and exit code. */
/* See COPYRIGHT for copyright information. */

#include <preinit/lib/seg.h>
#include <lib/trap.h>

.text

.globl	_asm_sysenter_hdl
.type	_asm_sysenter_hdl, @function
.p2align 4, 0x90		/* 16-byte alignment, nop filled */
_asm_sysenter_hdl:
	cli
	cld

	pushl %ds		# build context
	pushl %es
	pushal

	movl $CPU_GDT_KDATA,%eax # load kernel's data segment
	movw %ax,%ds
	movw %ax,%es

	pushl %esp		# pass pointer to this trapframe
	call sysenter_handler		# and call trap (does not return)

1:	hlt			# should never get here; just spin...


.globl	_asm_sysexit
.type	_asm_sysexit, @function
.p2align 4, 0x90		/* 16-byte alignment, nop filled */
_asm_sysexit:
	movl	4(%esp),%esp	// reset stack pointer to point to trap frame
	popal			// restore general-purpose registers except esp
	popl	%es		// restore data segment registers
	popl	%ds

	sti
	sysexit
