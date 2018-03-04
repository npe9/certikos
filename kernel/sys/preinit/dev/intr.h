#ifndef _SYS_PREINIT_DEV_INTR_H_
#define _SYS_PREINIT_DEV_INTR_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

void intr_init(void);
void intr_enable(uint8_t irq);
void intr_local_enable(void);
void intr_local_disable(void);
void intr_eoi(void);

#endif /* _KERN_ */

#endif /* !_SYS_PREINIT_DEV_INTR_H_ */
