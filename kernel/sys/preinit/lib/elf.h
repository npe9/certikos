#ifndef _KERN_PROC_ELF_H_
#define _KERN_PROC_ELF_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

void elf_load(void *user_elf_addr, int pmap_id);
uintptr_t elf_entry(void *user_elf_addr);

#endif /* _KERN_ */

#endif /* _KERN_PROC_ELF_H_ */
