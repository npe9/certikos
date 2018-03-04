#ifndef _KERN_PREINIT_H_
#define _KERN_PREINIT_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

void set_vendor(void);

void preinit(uintptr_t);

#endif /* _KERN_ */

#endif /* !_KERN_PREINIT_H_ */
