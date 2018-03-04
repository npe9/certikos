#ifndef _SYS_LIB_GCC_H_
#define _SYS_LIB_GCC_H_

#ifdef _KERN_

#define gcc_aligned(mult)	__attribute__((aligned (mult)))
#define gcc_packed		__attribute__((packed))

#endif /* _KERN_ */

#endif /* !_SYS_LIB_GCC_H_ */
