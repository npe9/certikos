	.set CR0_PE_ON, 0x1
	.set CR0_PE_OFF, 0xfffffffe

	.set PROT_MODE_CSEG, 0x8
	.set PROT_MODE_DSEG, 0x10
	.set REAL_MODE_CSEG, 0x18
	.set REAL_MODE_DSEG, 0x20

/*
 * Swtich back from real mode to the protected mode.
 */
	.globl real_to_prot
real_to_prot:
	.code16

	/* load GDT */
	lgdt	gdtdesc
	movl	%cr0, %eax

	/* enable protection */
	orl	$CR0_PE_ON, %eax
	movl	%eax, %cr0

	/* switch to the protected-mode */
	ljmp	$PROT_MODE_CSEG, $protcseg

	.code32
protcseg:
	/* set segment registers */
	movw	$PROT_MODE_DSEG, %ax
	movw	%ax, %ds
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movw	%ax, %ss

	/* store the return address */
	movl	(%esp), %eax

	/* set up the protected mode stack */
	movl	protstack, %esp

	/* set up the reture address */
	movl	%eax, (%esp)
	xorl	%eax, %eax

	/* king returns */
	ret

/*
 * Switch from the protected mode to the real mode.
 */
	.globl prot_to_real
prot_to_real:
	.code32

	/* load GDT */
	lgdt	gdtdesc

	/* backup the protected mode stack */
	movl	%esp, protstack

	/* set up segment registers */
	movw	$REAL_MODE_DSEG, %ax
	movw	%ax, %ds
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movw	%ax, %ss

	ljmp	$REAL_MODE_CSEG, $prerealcseg

prerealcseg:
	.code16
	/* disable protection */
	movl	%cr0, %eax
	andl	$CR0_PE_OFF, %eax
	movl	%eax, %cr0

	/* switch to the real mode */
	ljmp	$0, $realcseg

realcseg:
	.code16
	xorw	%ax, %ax
	movw	%ax, %ds
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movw	%ax, %ss

	ret

	.code32

	.p2align	2	/* force 4-byte alignment */
gdt_LOC:
	.word	0, 0
	.byte	0, 0, 0, 0

	/* code segment */
	.word	0xFFFF, 0
	.byte	0, 0x9A, 0xCF, 0

	/* data segment */
	.word	0xFFFF, 0
	.byte	0, 0x92, 0xCF, 0

	/* 16 bit real mode CS */
	.word	0xFFFF, 0
	.byte	0, 0x9E, 0, 0

	/* 16 bit real mode DS */
	.word	0xFFFF, 0
	.byte	0, 0x92, 0, 0

gdtdesc:
	.word	0x27		/* limit */
	.long	gdt_LOC		/* addr */

protstack:
	.word	0, 0
