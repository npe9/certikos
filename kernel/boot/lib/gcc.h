#ifndef _CERTIKOS_BOOT_GCC_H_
#define _CERTIKOS_BOOT_GCC_H_

// Use this to align a variable or struct member at a given boundary.
#define gcc_aligned(mult)	__attribute__((aligned (mult)))

// Use this to _prevent_ GCC from naturally aligning a structure member.
#define gcc_packed		__attribute__((packed))

// Functions declared always_inline will always be inlined,
// even in code compiled without optimization.  In contrast,
// the regular "inline" attribute is just a hint and may not be observed.
#define gcc_inline		__inline __attribute__((always_inline))

// Conversely, this ensures that GCC does NOT inline a function.
#define gcc_noinline		__attribute__((noinline))

// Functions declared noreturn are not expected to return
// (and GCC complains if you write a noreturn function that does).
#define gcc_noreturn		__attribute__((noreturn))

#endif /* !_CERTIKOS_BOOT_GCC_H_ */
