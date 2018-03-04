#ifndef _CERTIKOS_BOOT_TYPES_H_
#define _CERTIKOS_BOOT_TYPES_H_

#ifndef __ASSEMBLER__

#ifndef NULL
#define NULL ((void*) 0)
#endif

// Represents true-or-false values
typedef int bool;
#define true (~0)
#define false 0


// Explicitly-sized versions of integer types
typedef __signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef long long int64_t;
typedef unsigned long long uint64_t;

/*
//temp data types for svm
typedef signed char s8;
typedef unsigned char u8;

typedef signed short s16;
typedef unsigned short u16;

typedef signed int s32;
typedef unsigned int u32;

typedef signed long long s64;
typedef unsigned long long u64;
*/
// Pointers and addresses are 32 bits long.
// We use pointer types to represent virtual addresses,
// and [u]intptr_t to represent the numerical values of virtual addresses.
typedef int32_t intptr_t;
typedef uint32_t uintptr_t;

// size_t is used for memory object sizes.
typedef uint32_t size_t;
// ssize_t is a signed version of ssize_t, used in case there might be an
// error return.
typedef int32_t ssize_t;

// off_t is used for file offsets and lengths.
typedef int32_t off_t;

// Random Unix API compatibility types
typedef int pid_t;
typedef int dev_t;
typedef int ino_t;
typedef int mode_t;
typedef int nlink_t;

// Efficient min and max operations
#define MIN(_a, _b)						\
({								\
	typeof(_a) __a = (_a);					\
	typeof(_b) __b = (_b);					\
	__a <= __b ? __a : __b;					\
})
#define MAX(_a, _b)						\
({								\
	typeof(_a) __a = (_a);					\
	typeof(_b) __b = (_b);					\
	__a >= __b ? __a : __b;					\
})

// Rounding operations (efficient when n is a power of 2)
// Round down to the nearest multiple of n
#define ROUNDDOWN(a, n)						\
({								\
	uint32_t __a = (uint32_t) (a);				\
	(typeof(a)) (__a - __a % (n));				\
})
// Round up to the nearest multiple of n
#define ROUNDUP(a, n)						\
({								\
	uint32_t __n = (uint32_t) (n);				\
	(typeof(a)) (ROUNDDOWN((uint32_t) (a) + __n - 1, __n));	\
})

// Return the offset of 'member' relative to the beginning of a struct type
#define offsetof(type, member)  ((size_t) (&((type*)0)->member))

// Make the compiler think a value is getting used, even if it isn't.
#define USED(x)		(void)(x)

#if 0
#define __init          __attribute__ ((__section__ (".init.text")))
#else
#define __init
#endif



#endif /* !__ASSEMBLER__ */
#endif /* !_CERTIKOS_BOOT_TYPES_H_ */
