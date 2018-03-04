#include <x86.h>
#include <types.h>
#include <stdio.h>
#include <debug.h>
#include <mboot.h>
#include <elf.h>
#include <bios.h>
#include <console.h>
#include <fs.h>
#include <ext2.h>

mboot_info_t mboot_info =
	{
		.flags = (1 << 6),
	};

static uint32_t load_kernel(const char *kernel_path);

extern void exec_kernel(uint32_t, mboot_info_t *);

void loader(uint32_t dev, uint32_t start_sect_idx, bios_smap_t *smap)
{
	cons_init();

	cprintf("Start /boot/loader ...\n");

	bios_smap_t *p = smap;
	uint32_t smap_length = 0;
	cprintf("* E820 Memory Map (%08x)\n", p);
	while (p->base_addr != 0 || p->length != 0 || p->type != 0) {
		cprintf("    base addr = %08x, ", p->base_addr);
		cprintf("    length = %08x, ", p->length);
		cprintf("    type = %x\n", p->type);
		p += 1;
		smap_length += sizeof(bios_smap_t);
	}
	mboot_info.mmap_addr = (uint32_t)smap;
	mboot_info.mmap_length = smap_length;

	ext2_fs_init(dev, start_sect_idx);

	cprintf("Load kernel ...\n");
	uint32_t kern_addr = load_kernel("/boot/kernel");

	cprintf("Start kernel (%x) ...\n", kern_addr);
	exec_kernel(kern_addr, &mboot_info);

	panic("Fail to load kernel.");
}

static uint32_t load_kernel(const char *kernel_path)
{
	uint8_t elf_buf[SECTOR_SIZE * 8];
	elfhdr *ELFHDR = (elfhdr *)elf_buf;

	ext2_inode_t inode;
	uint32_t inode_idx;

	inode_idx = find_file(kernel_path);
	if (inode_idx == EXT2_BAD_INO)
		panic("Cannot find the kernel.\n");
	read_inode(inode_idx, &inode);

	ext2_fsread(&inode, (uint8_t *)ELFHDR, 0, SECTOR_SIZE * 8);

	if (ELFHDR->e_magic != ELF_MAGIC)
		panic("/boot/certikos is not a valid ELF file.\n");

	/* debug("Load sections\n"); */
	proghdr *ph = (proghdr *) ((uint8_t *) ELFHDR + ELFHDR->e_phoff);
	int i;
	for (i = 0; i < ELFHDR->e_phnum; i++, ph++) {
		/* debug("load %x bytes from %x to %x (%x)\n", */
		/*       ph->p_filesz, ph->p_offset, ph->p_pa, ph->p_va); */
		ext2_fsread(&inode, (uint8_t *)ph->p_pa, ph->p_offset, ph->p_filesz);
	}

	return (ELFHDR->e_entry & 0xFFFFFFFF);
}
