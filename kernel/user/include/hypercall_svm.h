#ifndef _USER_HYPERCALL_SVM_H_
#define _USER_HYPERCALL_SVM_H_

#include "hypercall.h"

#define gcc_inline	__inline __attribute__((always_inline))
typedef unsigned int	uint32_t;

typedef enum {
	HYPERCALL_BITAND,
	HYPERCALL_BITOR,
	HYPERCALL_BITXOR,
	HYPERCALL_BITNOT,
	HYPERCALL_GETC,
} hypercall_t;

/*
 * Define hypercalls.
 *
 * DEF_HYPERCALL_#(name, nr) defines such a function
 * - it's for the hypercall nr (defined as hypercall_t)
 * - its name is hypercall_##name
 * - it requires # parameters
 */
DEF_HYPERCALL_2(bitand, HYPERCALL_BITAND)
DEF_HYPERCALL_2(bitor, HYPERCALL_BITOR)
DEF_HYPERCALL_2(bitxor, HYPERCALL_BITXOR)
DEF_HYPERCALL_1(bitnot, HYPERCALL_BITNOT)
DEF_HYPERCALL_0(getc, HYPERCALL_GETC)

#endif /* _USER_HYPERCALL_SVM_H_ */
