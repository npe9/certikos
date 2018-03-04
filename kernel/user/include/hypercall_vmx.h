#ifndef _USER_HYPERCALL_VMX_H_
#define _USER_HYPERCALL_VMX_H_

#include "hypercall.h"

#define gcc_inline  __inline __attribute__((always_inline))
typedef unsigned int uint32_t;

typedef enum
{
    HYPERCALL_GET_TSC_KHZ = 1, HYPERCALL_NULL, /* NOTICE: this should be the last one */
} hypercall_t;

static uint64_t gcc_inline
hyp_get_tsc_khz (void)
{
    uint32_t high, low;
    uint32_t c;
    asm volatile("vmcall"
            : "=a" (c), "=b"(high), "=c"(low)
            : "a" (HYPERCALL_GET_TSC_KHZ)
            : "cc", "memory");
    return ((uint64_t) high << 32) | (uint64_t) low;
}

#endif /* _USER_HYPERCALL_VMX_H_ */
