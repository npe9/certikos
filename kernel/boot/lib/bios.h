#ifndef _CERTIKOS_BOOT_BOIS_H_
#define _CERTIKOS_BOOT_BOIS_H_

#include <gcc.h>
#include <types.h>

typedef
struct bios_smap {
	uint32_t size;
	uint64_t base_addr;
	uint64_t length;
	uint32_t type;
} gcc_packed bios_smap_t;

int read_sector(int drive, uint64_t sector, void *buf);
int int13x(int, int, void *);

#endif /* !_CERTIKOS_BOOT_BOIS_H_ */
