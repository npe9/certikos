/*
 * Derived from BHyVe (svn 237539).
 * Adapted for CertiKOS by Haozhong Zhang at Yale.
 *
 * XXX: BHyVe is a 64-bit hypervisor, while CertiKOS is 32-bit.
 */

/*-
 * Copyright (c) 2011 NetApp, Inc.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY NETAPP, INC ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL NETAPP, INC OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * $FreeBSD$
 */

#include <preinit/lib/debug.h>
#include <preinit/lib/gcc.h>
#include <preinit/lib/types.h>
#include <preinit/lib/vmx_x86.h>

int
vmxon (char *region)
{
	int error;
	uint64_t addr;

	addr = (uintptr_t) region | 0ULL;

	__asm __volatile("vmxon %0" : : "m" (addr) : "cc", "memory");

	VMX_SET_ERROR_CODE(error);
	return (error);
}

void
vmclear (struct vmcs *vmcs)
{
	int error;
	uint64_t addr;

	addr = (uintptr_t) vmcs | 0ULL;

	__asm __volatile("vmclear %0" : : "m" (addr) : "cc", "memory");

	VMX_SET_ERROR_CODE(error);
	if (error)
		KERN_PANIC("vmclear error %d", error);
}

void
vmxoff (void)
{
	__asm __volatile("vmxoff");
}

void
vmptrst (uintptr_t *addr)
{
	__asm __volatile("vmptrst %0" : : "m" (*addr) : "cc", "memory");
}

void
_vmptrld (struct vmcs *vmcs)
{
	int error;
	uint64_t addr;

	addr = (uintptr_t) vmcs;

	__asm __volatile("vmptrld %0" : : "m" (addr)
			: "cc", "memory");

	VMX_SET_ERROR_CODE(error);
	if (error)
		KERN_PANIC("vmptrld error %d", error);
}

uint32_t
vmread (uint32_t encoding)
{
	uint32_t val;
	__asm __volatile("vmread %1, %0" : "=r" (val) : "r" (encoding) : "cc");
	return val;
}

void
vmwrite (uint32_t encoding, uint32_t val)
{
	uint8_t error;
	__asm __volatile("vmwrite %1, %2; setna %0"
			: "=q" (error)
			: "r" (val), "r" (encoding)
			: "cc");
	if (unlikely(error))
		KERN_PANIC("vmwrite encoding = 0x%08x, val = 0x%08x. error %d\n",
			encoding, val, error);
}

void
invvpid (uint32_t type, uint16_t vpid, uint64_t la)
{
	int error;

	struct
	{
		uint16_t vpid;
		uint16_t res[3];
		uint64_t la;
	}gcc_packed desc =
		{ vpid,
			{ 0, 0, 0 }, la };

	KERN_ASSERT(sizeof(desc) == 16);

	__asm __volatile("invvpid %0, %1" :: "m" (desc), "r" (type)
			: "cc", "memory");

	VMX_SET_ERROR_CODE(error);
	if (error)
		KERN_PANIC("invvpid error %d", error);
}

void
invept (uint32_t type, uint64_t eptp)
{
	int error;

	struct
	{
		uint64_t eptp;
		uint64_t res;
	}gcc_packed desc =
		{ eptp, 0 };

	KERN_ASSERT(sizeof(desc) == 16);

	__asm __volatile("invept %0, %1" :: "m" (desc), "r" (type)
			: "cc", "memory");

	VMX_SET_ERROR_CODE(error);
	if (error)
		KERN_PANIC("invept error %d", error);
}
