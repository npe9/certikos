// Kernel debugging code.
// See COPYRIGHT for copyright information.

#ifndef _CERTIKOS_BOOT_DEBUG_H_
#define _CERTIKOS_BOOT_DEBUG_H_

#ifdef BOOT_DEBUG

#include <types.h>
#include <gcc.h>

#define DEBUG_TRACEFRAMES	10

void debug_normal(const char *, int, const char *, ...);
void debug_warn(const char *, int, const char *, ...);
void debug_panic(const char *, int, const char *, ...);

#define debug(...)	debug_normal(__FILE__, __LINE__, __VA_ARGS__)
#define warn(...)	debug_warn(__FILE__, __LINE__, __VA_ARGS__)
#define panic(...)	debug_panic(__FILE__, __LINE__, __VA_ARGS__)

#define bochs_bp()				\
	do {					\
		asm volatile("xchg %bx, %bx");	\
	} while (0)

#define assert(x)		\
	do { if (!(x)) panic("assertion failed: %s", #x); } while (0)

#else /* BOOT_DEBUG */

#define debug(...)     	do {} while (0)
#define warn(...)      	do {} while (0)
#define panic(...)    	do {__asm __volatile("hlt");} while (0)

#define bochs_bp()	do {} while (0)

#define assert(x)	do {} while (0)

#endif /* !BOOT_DEBUG */

#endif /* !_CERTIKOS_BOOT_DEBUG_H_ */
