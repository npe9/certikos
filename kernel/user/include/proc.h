#ifndef _USER_PROC_H_
#define _USER_PROC_H_

#include <types.h>

pid_t spawn(uint32_t elf_id, uint32_t quota);
void  yield(void);
unsigned int get_quota(void);

#endif /* !_USER_PROC_H_ */
