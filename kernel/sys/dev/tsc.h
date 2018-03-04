#ifndef _SYS_DEV_TSC_H_
#define _SYS_DEV_TSC_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

uint32_t tsc_freq_lo(void);
uint32_t tsc_freq_hi(void);

#endif /* _KERN_ */

#endif /* !_SYS_DEV_TSC_H_ */
