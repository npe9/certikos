/*
 * Derived from BHyVe (svn 237539).
 * Adapted for CertiKOS by Haozhong Zhang at Yale.
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

#ifndef _VIRT_VMX_EPT_H_
#define _VIRT_VMX_EPT_H_

#ifdef _KERN_

#include <preinit/lib/types.h>
#include <lib/gcc.h>

#define	EPT_PWLEVELS	4		/* page walk levels */
#define PAT_WRITE_BACK      0x06
#define	EPTP(pml4)	((pml4) | (EPT_PWLEVELS - 1) << 3 | PAT_WRITE_BACK)

/* Round down to the nearest multiple of n */
#define ROUNDDOWN(a, n)             \
        ({                  \
                 typeof(a) _a = (a);     \
                 typeof(n) _n = (n);     \
                 (typeof(a)) (_a - _a % _n); \
             })

/* Round up to the nearest multiple of n */
#define ROUNDUP(_a, _n)                     \
        ({                          \
                 typeof(_a) __a = (_a);              \
                 typeof(_n) __n = (_n);              \
                 (typeof(_a)) (ROUNDDOWN(__a + __n - 1, __n));   \
             })

#define PAGESIZE 4096

struct eptStruct {
    uint64_t pml4[512] gcc_aligned(PAGESIZE);
    uint64_t pdpt[512] gcc_aligned(PAGESIZE);
    uint64_t pdt[4][512] gcc_aligned(PAGESIZE);
    uint64_t ptab[4][512][512] gcc_aligned(PAGESIZE);
};

void      ept_init(unsigned int mbi_adr);
int       ept_create_mappings(uint64_t *pml4ept, size_t);
int       ept_add_mapping(uintptr_t gpa, uintptr_t hpa, uint32_t mem_type);
void      ept_invalidate_mappings();
uint64_t  ept_gpa_to_hpa(uintptr_t gpa);
void       ept_set_permission(uintptr_t gpa, uint8_t perm);
int       ept_mmap(uintptr_t gpa, uint64_t hpa, uint8_t mem_type);

#endif /* _KERN_ */

#endif /* !_VIRT_VMX_EPT_H_ */
