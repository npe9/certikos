/*
 * boot1
 *
 * - boot1 is put just after MBR and before the first partition, i.e. from
 *   sector 2 to sector 63.
 *
 * - boot1 is loaded at 0x7c00 by boot0. boot0 passes two parameters to boot1,
 *   the first of which is the booting device id and the second of which is LBA
 *   of the first bootable partition.
 *
 * - boot1 loads /boot/loader on the first bootable partition.
 */

	.set PROT_MODE_CSEG, 0x8	# kernel code segment selector
	.set PROT_MODE_DSEG, 0x10	# kernel data segment selector
	.set CR0_PE_ON, 0x1		# protected mode enable flag

	.set LOAD, 0x7e00

	.set SMAP_SIG, 0x0534D4150	# "SMAP"

	.globl start
start:
	.code16
	cli
	cld

	/*
	 * clear segment registers
	 */
	xorw	%ax, %ax
	movw    %ax, %ds
	movw    %ax, %es
	movw    %ax, %ss

	/*
	 * XXX: remember that the first 8 bytes below LOAD are reserverd to
	 *      store the information of the booting device
	 */

	/* set up the stack */
	movw	$(LOAD - 8), %bp
	movw	$(LOAD - 8), %sp

	/*
	 * set to normal (80x25 text) video mode
	 */
set_video_mode:
	movw	$0x0F00, %ax
	int	$0x10			# get the video mode
	cmpb	$0x03, %al
	je	set_video_mode.2	# video mode is already set
set_video_mode.1:
	movw	$0x0003, %ax
	int	$0x10

	/*
	 * print starting message
	 */
set_video_mode.2:
	movw	$STARTUP_MSG, %si
	call	putstr

	/*
	 * detect the physical memory map
	 */
e820:
	xorl	%ebx, %ebx		# ebx must be 0 when first calling e820
	movl	$SMAP_SIG, %edx		# edx must be 'SMAP' when calling e820
	movw	$(smap+4), %di		# set the address of the output buffer
e820.1:
	movl	$20, %ecx		# set the size of the output buffer
	movl	$0xe820, %eax		# set the BIOS service code
	int	$0x15			# call BIOS service e820h
e820.2:
	jc	e820.fail		# error during e820h
	cmpl	$SMAP_SIG, %eax		# check eax, which should be 'SMAP'
	jne	e820.fail
e820.3:
	movl	$20, -4(%di)
	addw	$24, %di
	cmpl	$0x0, %ebx		# whether it's the last descriptor
	je	e820.4
	jmp	e820.1
e820.4:					# zero the descriptor after the last one
	xorb	%al, %al
	movw	$20, %cx
	rep	stosb
	jmp	switch_prot
e820.fail:
	movw	$E820_FAIL_MSG, %si
	call	putstr
	jmp	spin16

spin16:
	hlt

	/*
	 * load the bootstrap GDT
	 */
switch_prot:
	lgdt	gdtdesc
	movl	%cr0, %eax
	orl	$CR0_PE_ON, %eax
	movl	%eax, %cr0
	/*
	 * switch to the protected mode
	 */
	ljmp	$PROT_MODE_CSEG, $protcseg

	.code32
protcseg:
	movw	$PROT_MODE_DSEG, %ax
	movw	%ax, %ds
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movw	%ax, %ss

	/*
	 * jump to the C part
	 */
	pushl	$smap
	movl	(LOAD-4), %eax
	pushl	%eax
	movl	(LOAD-8), %eax
	pushl	%eax
	call	boot1main

spin:
	hlt

/*
 * print a string (@ %si) to the screen
 */
	.globl putstr
putstr:
	pusha
	movb	$0xe, %ah
putstr.1:
	lodsb
	cmp	$0, %al
	je	putstr.2
	int	$0x10
	jmp	putstr.1
putstr.2:
	popa
	ret

STARTUP_MSG:
	.ascii	"Start boot1 ...\r\n\0"
E820_FAIL_MSG:
	.ascii	"error when detecting memory map\r\n\0"


	.p2align	2	/* force 4-byte alignment */
/* bootstrap GDT */
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

/* GDT descriptor */
gdtdesc:
	.word	0x27			/* limit */
	.long	gdt_LOC			/* addr */

/* reserve space for memory map */
smap:
	.space 0xc00
