#ifndef _PREINIT_LIB_STRING_H_
#define _PREINIT_LIB_STRING_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

int	strncmp(const char *p, const char *q, size_t n);
int	strnlen(const char *s, size_t size);
void	*memzero(void *dst, size_t len);
void	*memcpy(void *dst, const void *src, size_t len);
void	*memmove(void *dst, const void *src, size_t len);

#endif /* _KERN_ */

#endif /* !_PREINIT_LIB_STRING_H_ */
