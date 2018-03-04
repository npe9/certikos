	.globl enter_guest
/* void enter_guest(struct vmcb *vmcb,
                    uint32_t *g_ebx, uint32_t *g_ecx, uint32_t *g_edx,
                    uint32_t *g_esi, uint32_t *g_edi, uint32_t *g_ebp,
                    uint32_t *h_ebx, uint32_t *h_ecx, uint32_t *h_edx,
                    uint32_t *h_esi, uint32_t *h_edi, uint32_t *h_ebp) */
enter_guest:
	clgi

	/* save other host general-purpose registers */
	movl	32(%esp), %eax
	movl	%ebx, (%eax)
	movl	36(%esp), %eax
	movl	%ecx, (%eax)
	movl	40(%esp), %eax
	movl	%edx, (%eax)
	movl	44(%esp), %eax
	movl	%esi, (%eax)
	movl	48(%esp), %eax
	movl	%edi, (%eax)
	movl	52(%esp), %eax
	movl	%ebp, (%eax)

	/* restore guest registers */
	movl	8(%esp), %eax	/* guest %ebx */
	movl	(%eax), %ebx
	movl	12(%esp), %eax	/* guest %ecx */
	movl	(%eax), %ecx
	movl	16(%esp), %eax	/* guest %edx */
	movl	(%eax), %edx
	movl	20(%esp), %eax	/* guest %esi */
	movl	(%eax), %esi
	movl	24(%esp), %eax	/* guest %edi */
	movl	(%eax), %edi
	movl	28(%esp), %eax	/* guest %ebp */
	movl	(%eax), %ebp

	/* setup interrupt flags */
	sti
	nop

	/* load VMCB */
	movl	4(%esp), %eax
	vmload

	/* switch to guest */
	vmrun

__exit_guest:
	/* when returning from the guest... */
	vmsave

	/* reset interrupt flags */
	cli

	/* save guest registers */
	movl	8(%esp), %eax	/* guest %ebx */
	movl	%ebx, (%eax)
	movl	12(%esp), %eax	/* guest %ecx */
	movl	%ecx, (%eax)
	movl	16(%esp), %eax	/* guest %edx */
	movl	%edx, (%eax)
	movl	20(%esp), %eax	/* guest %esi */
	movl	%esi, (%eax)
	movl	24(%esp), %eax	/* guest %edi */
	movl	%edi, (%eax)
	movl	28(%esp), %eax	/* guest %ebp */
	movl	%ebp, (%eax)

	/* restore host general-purpose registers */
	movl	32(%esp), %eax
	movl	(%eax), %ebx
	movl	36(%esp), %eax
	movl	(%eax), %ecx
	movl	40(%esp), %eax
	movl	(%eax), %edx
	movl	44(%esp), %eax
	movl	(%eax), %esi
	movl	48(%esp), %eax
	movl	(%eax), %edi
	movl	52(%esp), %eax
	movl	(%eax), %ebp

	stgi

	ret
