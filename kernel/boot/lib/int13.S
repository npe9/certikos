	.set PROT_MODE_DSEG, 0x10

/*
 * int int13x(int ax, int driver, void *dap)
 */
#	.globl int13x
#int13x:
#	.code32
#
#	pushl	%ebp
#	movl	%esp, %ebp
#
#	pushl	%esi
#	pushl	%ebx
#
#	/* save dap in cx:si */
#	movl	0x10(%ebp), %eax
#	movw	%ax, %si
#	xorw	%ax, %ax
#	movw	%ax, %cx
#	/* save driver in dl */
#	movb	0xc(%ebp), %dl
#	/* save ax in bx */
#	movb	0x8(%ebp), %bl
#
#	/* switch to the real mode */
#	call	prot_to_real
#
#	.code16
#
#	/* set up ah */
#	movb	%bl, %ah
#	/* set up ds:si */
#	movw	%cx, %ds
#	/* int 13h */
#	int	$0x13
#
#	jc	dpanic
#	/* save the return code */
#	movb	%ah, %dl
#
#	xorw	%ax, %ax
#	movw	%ax, %ds
#
#	/* switch back to the protected mode */
#	call	real_to_prot
#
#	.code32
#
#	movb	%dl, %al
#
#	popl	%ebx
#	popl	%esi
#	popl	%ebp
#
#	ret


	.globl	bios_int
bios_int:
	.code32
	pushf
	cli
	popf
	pushl    %ebp
	pushl    %ecx
	pushl    %eax
	pushl    %ebx
	pushl    %esi
	pushl    %edi
	pushl    %edx

	movb     %al, intno
	movl	 (%edx), %eax
	movl	 %eax, L_bios_register_eax
	movw	 4(%edx), %ax
	movw	 %ax, L_bios_register_es
	movw	 6(%edx), %ax
	movw	 %ax, L_bios_register_ds
	movw	 8(%edx), %ax
	movw	 %ax, L_bios_register_flags

	movl 	12(%edx), %ebx
	movl 	16(%edx), %ecx
	movl 	20(%edx), %edi
	movl 	24(%edx), %esi
	movl 	28(%edx), %edx


	call	prot_to_real
	.code16
	pushf
	cli

	mov	%ds, %ax
	push	%ax

	/* movw imm16, %ax*/
	.byte	0xb8
L_bios_register_es:
	.short 	0
	movw	%ax, %es
	/* movw imm16, %ax*/
	.byte	0xb8
L_bios_register_ds:
	.short 	0
	movw	%ax, %ds

	/* movw imm16, %ax*/
	.byte	0xb8
L_bios_register_flags:
	.short 	0
	push	%ax
	popf

	/* movl imm32, %eax*/
	.byte	0x66, 0xb8
L_bios_register_eax:
	.long 	0

	/* int imm8.  */
	.byte   0xcd
intno:
	.byte   0

	movl 	%eax, %cs:L_bios_register_eax
	movw	%ds, %ax
	movw 	%ax, %cs:L_bios_register_ds
	pop 	%ax
	mov	%ax, %ds
	pushf
	pop	%ax
	movw	%ax, L_bios_register_flags
	mov 	%es, %ax
	movw	%ax, L_bios_register_es

	popf
	call	real_to_prot
	.code32

	popl    %eax

	movl 	%ebx, 12(%eax)
	movl 	%ecx, 16(%eax)
	movl 	%edi, 20(%eax)
	movl 	%esi, 24(%eax)
	movl 	%edx, 28(%eax)

	movl     %eax, %edx

	movl	 L_bios_register_eax, %eax
	movl	 %eax, (%edx)
	movw	 L_bios_register_es, %ax
	movw	 %ax, 4(%edx)
	movw	 L_bios_register_ds, %ax
	movw	 %ax, 6(%edx)
	movw	 L_bios_register_flags, %ax
	movw	 %ax, 8(%edx)

	popl 	%edi
	popl 	%esi
	popl    %ebx
	popl    %eax
	popl    %ecx
	popl    %ebp

	ret
