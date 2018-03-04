#define offsetof(type, member)	__builtin_offsetof(type, member)

/* void host_out(void) */
	.text
	.align	16
	.globl	host_out
	.p2align 4, 0x90
host_out:
	.cfi_startproc
	movl	$VMX_LOC, %ecx
	cmpl	$0, 124(%ecx); jz .Lvmx_launch
	movl	16(%ecx), %ecx
	vmresume
	jmp		vmx_return_from_guest

.Lvmx_launch:
	movl	16(%ecx), %ecx

	vmlaunch

	jmp		vmx_return_from_guest

	.cfi_endproc
	.type	host_out, @function
	.size	host_out, . - host_out

/* void host_in(void) */
	.text
	.align	16
	.globl	host_in
	.p2align 4, 0x90
host_in:
	.cfi_startproc
	ret
	.cfi_endproc
	.type	host_in, @function
	.size	host_in, . - host_in

/*__vmx_load_guest*/
	.text
	.align	16
	.global __vmx_load_guest
	.p2align 4, 0x90		/* 16-byte alignment, nop filled */
__vmx_load_guest:
	.cfi_startproc

	# save the address of vmx on the stack

	movl $27668, %edi
	vmwrite %esp, %edi

	/* load guest registers */
	movl $VMX_LOC, %ecx
	movl 0x40(%ecx), %edi
	movl %edi, %cr2
	movl 0x44(%ecx), %edi
	movl %edi, %dr0
	movl 0x48(%ecx), %edi
	movl %edi, %dr1
	movl 0x4c(%ecx), %edi
	movl %edi, %dr2
	movl 0x50(%ecx), %edi
	movl %edi, %dr3

	jmp vmx_enter_bottom_half

	.cfi_endproc
	.type	__vmx_load_guest, @function
	.size	__vmx_load_guest, . - __vmx_load_guest


/*__vmx_store_guest*/
	.text
	.align	16
	.global __vmx_store_guest
	.p2align 4, 0x90		/* 16-byte alignment, nop filled */
__vmx_store_guest:
	.cfi_startproc
	movl	%ecx, (VMX_LOC + 16)
	movl $VMX_LOC, %ecx
	# check error first
	jnc 1f
	movl $1, 144(%ecx)
	jmp 3f
	1: jnz 2f
	movl $2, 144(%ecx)
	jmp 3f
	2: movl $0, 144(%ecx)
	3: nop

	movl %cr2, %edi
	movl %edi, 0x40(%ecx)
	movl %dr0, %edi
	movl %edi, 0x44(%ecx)
	movl %dr1, %edi
	movl %edi, 0x48(%ecx)
	movl %dr2, %edi
	movl %edi, 0x4c(%ecx)
	movl %dr3, %edi
	movl %edi, 0x50(%ecx)

	jmp vmx_exit_bottom_half

	.cfi_endproc
	.type	__vmx_store_guest, @function
	.size	__vmx_store_guest, . - __vmx_store_guest



