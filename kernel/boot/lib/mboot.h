#ifndef _CERTIKOS64_BOOT_MBOOT_H_
#define _CERTIKOS64_BOOT_MBOOT_H_

#include <types.h>

/* Provided by OS */
typedef
struct mboot_hdr {
	uint32_t magic;
#define MBOOT_HDR_MAGIC			0x1badb002

	uint32_t flags;
#define MBOOT_HDR_PAGE_ALIGNED		0x1
#define MBOOT_HDR_MEM_INFO		0x2
#define MBOOT_HDR_VIDEO_MODE		0x4
#define MBOOT_HDR_XINFO_VALID	    	0x10000

	uint32_t checksum;

	uint32_t header_addr;
	uint32_t load_addr;
	uint32_t load_end_addr;
	uint32_t bss_end_addr;
	uint32_t entry_addr;
	uint32_t mode_type;
#define MBOOT_VIDEO_LINEAR_MODE		0x0
#define MBOOT_VIDEO_EGA_MODE		0x1

	uint32_t width;
	uint32_t height;
	uint32_t depth;
} mboot_hdr_t;

/* Provided by bootloader */
typedef
struct mboot_info {
	uint32_t flags;

	/* if bit 0 of flags is set */
	uint32_t mem_lower;		/* the amount of the loer memory */
	uint32_t mem_upper;		/* the amount of the higher memory */

	/* if bit 1 of flags is set */
	struct {
		uint8_t driver;		/* BIOS disk device number */
		uint8_t part1;		/* top-level partition number */
		uint8_t part2;		/* second-level partition number */
		uint8_t part3;		/* third-level partition number */
	} boot_device;

	/* if bit 2 of flags is set */
	uint32_t cmdline;		/* the address of a zerom terminated
					   command string passed to kernel */

	/* if bit 3 of flags is set */
	uint32_t mods_count;
	uint32_t mods_addr;

	/* if bit 4/5 of flags is set */
	union {
		struct {
			uint32_t tabsize;
			uint32_t strsize;
			uint32_t addr;
			uint32_t _reserved;
		} aout;
		struct {
			uint32_t num;
			uint32_t size;
			uint32_t addr;
			uint32_t shndx;
		} elf;
	} syms;

	/* if bit 6 of flags is set */
	uint32_t mmap_length;		/* length of the buffer containing
					   the memory map */
	uint32_t mmap_addr;		/* address of the buffer containing
					   the memory map */

	/* if bit 7 of flags is set */
	uint32_t drives_length;
	uint32_t drives_addr;

	/* if bit 8 of flags is set */
	uint32_t config_table;

	/* if bit 9 of flags is set */
	uint32_t boot_loader_name;

	/* if bit 10 of flags is set */
	uint32_t apm_table;

	/* if bit 11 of flags is set */
	uint32_t vbe_control_info;
	uint32_t vbe_mode_info;
	uint32_t vbe_mode;
	uint32_t vbe_interface_seg;
	uint32_t vbe_interface_off;
	uint32_t vbe_interface_len;
} mboot_info_t;

#define MBOOT_INFO_MAGIC	0x2badb002

#endif /* !_CERTIKOS64_BOOT_MBOOT_H_ */
