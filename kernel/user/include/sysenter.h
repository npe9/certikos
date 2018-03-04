#ifndef _USER_SYSENTER_H_
#define _USER_SYSENTER_H_

#include <gcc.h>
#include <types.h>

typedef enum fast_syscall {
    N_fsys_yield = 0,
    N_fsys_ssend = 1,
    N_fsys_srecv = 2,
} fast_syscall;


static gcc_inline uint32_t
sysenter (void)
{
    uint32_t rv;

    __asm __volatile(
            "movl %%esp, %%ecx;"
            "leal 1f, %%edx;"
            "sysenter;"
            "1:;"
            "movl %%eax, %0"
            : "=g" (rv)
            :
            : "cc", "memory", "eax", "ebx", "edx", "ecx", "esi", "edi"
    );

    return rv;
}


static gcc_inline uint32_t
fast_sys_yield (void)
{
    uint32_t rv;

    __asm __volatile(
            "pushl %%ebp;"
            "movl %%ecx, %%ebp;"
            "movl %%esp, %%ecx;"
            "leal 1f, %%edx;"
            "sysenter;"
            "1:;"
            "popl %%ebp"
            : "=a" (rv)
            : "a" (N_fsys_yield)
            : "cc", "memory", "edx", "ecx"
    );

    return rv;
}

static gcc_inline int
fast_sys_ssend (uint32_t chid, unsigned int *buffer, uint32_t scount)
{
    int rv;

    asm volatile(
            "movl %%esp, %%ecx;"
            "leal 1f, %%edx;"
            "sysenter;"
            "1:;"
            "movl %%eax, %0"
            : "=a" (rv)
            : "a" (N_fsys_ssend),
              "b" (chid),
              "S" (buffer),
              "D" (scount)
            : "cc", "memory", "edx", "ecx"
    );

    return rv;
}

static gcc_inline int
fast_sys_srecv (uint32_t pid, unsigned int *buffer, uint32_t rcount)
{
    int rv;

    asm volatile(
            "movl %%esp, %%ecx;"
            "leal 1f, %%edx;"
            "sysenter;"
            "1:;"
            "movl %%eax, %0"
            : "=a" (rv)
            : "a" (N_fsys_srecv),
              "b" (pid),
              "S" (buffer),
              "D" (rcount)
            : "cc", "memory", "edx", "ecx"
    );

    return rv;
}

#endif
