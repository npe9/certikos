#ifdef ENABLE_BOOT_CF

/*
 * void chainload(void *vbs);
 */
	.set CR0_PE_OFF, 0xfffffffe

	.set REAL_MODE_CSEG, 0x18
	.set REAL_MODE_DSEG, 0x20

	.globl chainload
chainload:
	.code32

	movl	0x4(%esp), %esi
	movl	$0x7c00, %edi
	movl	$128, %ecx
	rep
	movsl

	lgdt	gdtdesc
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

	jmp	0x7c00


	.code32

	.p2align	2	/* force 4-byte alignment */
gdt:
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
	.long	gdt		/* addr */

#endif /* ENABLE_BOOT_CF*/
