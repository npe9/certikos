/*
 * boot0
 *
 * - boot0 is put in the MBR and therefore should be smaller than 446 bytes.
 *
 * - boot0 is loaded to physical memory address 0x7c00 and the invoked by BIOS.
 *
 * - boot0 relocates itself at 0x600 to free the space at 0x7c00 for the second
 *   second stage bootloader boot1. boot1 is put in the sectors after MBR and
 *   before the first partition, which are usually from sector 2 to sector 63.
 *
 * - boot0 puts the booting device id and lower 32 bits of LBA of the first
 *   bootable partiion below 0x7c00.
 *
 * - boot0 requires
 *   1. boot0, boot1, /boot/loader and OS kernel are on the same disk;
 *   2. the first 63 sectors of the disk is out of the filesystem;
 *   3. the filesystem on the first bootable partition is EXT2;
 *   4. /boot/loader is on the first bootable partition.
 *
 * - boot0 is running in the real mode and does not switch to the
 *   protected mode.
 */

	.set LOAD, 0x7c00		# load address
	.set BOOT1, 0x7e00		# start address of boot1
	.set RELOC, 0x600		# relocated address

	.set PR_TABLE, RELOC+0x1be	# address of the partition table

	.set PR_BOOTABLE, 0x80		# bootable partition

	.globl start
start:
	.code16
	cli
	cld

	/* clear segment registers */
	xorw	%ax, %ax
	movw    %ax, %ds
	movw    %ax, %es
	movw    %ax, %ss

	/* store the booting device id */
	xorl	%eax, %eax
	movb	%dl, %al
	movl	%eax, (RELOC - 4)

	/* set up the stack */
	movw	$(RELOC - 4), %bp
	movw	$(RELOC - 4), %sp

	/*
	 * relocate at $RELOC (0x600) in order to free the space at 0x7c00
	 * for boot1
	 */
	movw	$LOAD, %si
	movw	$RELOC, %di
	movw	$0x100, %cx		# copy 256 words (512 bytes)
	rep
	movsw

	/* jump to the relocated code */
	jmp	reloc-LOAD+RELOC

	/* relocated code starts from here */
reloc:
	/* set to normal (80x25 text) video mode */
set_video_mode:
	movw	$0x0003, %ax
	int	$0x10

	/* print starting message */
	movw	$STARTUP_MSG, %si
	call	putstr

	/* enable A20 */
seta20.1:
	inb     $0x64, %al
	testb   $0x2, %al
	jnz     seta20.1
	movb    $0xd1, %al
	outb    %al, $0x64
seta20.2:
	inb     $0x64, %al
	testb   $0x2, %al
	jnz     seta20.2
	movb    $0xdf, %al
	outb    %al, $0x60
seta20.3:

	/*
	 * search for the first bootable partition, the address of the partition
	 * table entry for the bootable partition is stored in %si
	 */
	movb	$0x4, %cl
	xorl	%esi, %esi
	movw	$PR_TABLE, %si
search_bootable:
	test	%cl, %cl
	jz	no_bootable
	cmpb	$PR_BOOTABLE, (%si)
	je	load_boot1
	add	$0x10, %si
	dec	%cl
	jmp	search_bootable

	/*
	 * find no bootable partition, go to spin
	 */
no_bootable:
	movw	$NO_BOOTABLE_MSG, %si
	call	putstr
	jmp	spin

	/*
	 * load boot1 from sector 2 to sector 63
	 */
load_boot1:
	/*
	 * the first 8 bytes below BOOT1 are reserved to store the information
	 * about the boot device, as described in following figure:
	 *    +------------------------------+ <-- BOOT1
	 *    | lower 32 bits of LBA of the  |
	 *    | first bootable partition     |
	 *    |------------------------------| <-- BOOT1 - 4
	 *    | the booting device id
	 *    |------------------------------| <-- BOOT1 - 8
	 *    :                              :     (stack starts from here)
	 *    :                              :
	 */
	movl	0x8(%si), %eax
	movl	%eax, (BOOT1 - 4)
	movl	(RELOC - 4), %eax
	movl	%eax, (BOOT1 - 8)

	/* read disk */
	pushl	$0x0			# set the start
	pushl	$0x1			# LBA address
	pushw	%es			# set the buffer address
	pushw	$BOOT1			# to 0x7e00
	pushw	$62			# set the number of sectors to be read
	pushw	$0x10			# set the size of DAP
	movw	%sp, %si		# set the DAP address
	movw	$0x4200, %ax		# ah = 0x42, al = 0x00
	int	$0x13			# read sectors
	jc	load_fail		# encouter errors

	jmp	BOOT1			# jump to boot1

load_fail:
	movw	$LOAD_FAIL_MSG, %si
	call	putstr

spin:
	hlt


/*
 * print a string (@ %si) to the screen
 */
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
	.ascii	"Start boot0 ...\r\n\0"
NO_BOOTABLE_MSG:
	.ascii	"No bootable partition.\r\n\0"
LOAD_FAIL_MSG:
	.ascii	"Error during loading boot1.\r\n\0"
