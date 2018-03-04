#ifndef _KERN_TRAP_SYSENTER_H_
#define _KERN_TRAP_SYSENTER_H_

#include <lib/trap.h>

typedef
struct ef_t {
    /* registers and other info we push manually in trapasm.S */
    pushregs regs;
    uint16_t es;        uint16_t padding_es;
    uint16_t ds;        uint16_t padding_ds;
} ef_t;

typedef enum fast_syscall {
    N_fsys_yield = 0,
    N_fsys_ssend = 1,
    N_fsys_srecv = 2,
} fast_syscall;

void sysenter(ef_t * ef);
void sysexit(ef_t * ef);

void sysenter_init();

#endif /* !_KERN_TRAP_SYSENTER_H_ */
