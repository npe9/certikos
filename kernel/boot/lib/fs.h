#ifndef _CERTIKOS_BOOT_FS_H_
#define _CERTIKOS_BOOT_FS_H_

#include <types.h>
#include <ext2.h>

void ext2_fs_init(uint8_t dev, uint64_t start_sect);
void read_block(uint32_t blk_idx, uint8_t *buf);
void read_block_group_descriptor(uint32_t bg_idx,
				 ext2_block_group_descriptor_t *bg_desc);
void read_inode(uint32_t inode_idx, ext2_inode_t *);
uint32_t search_in_dir(ext2_inode_t *, const char*, const int);
uint32_t find_file(const char *fullname);
void ext2_fsread(ext2_inode_t *, uint8_t *, uint32_t, uint32_t);

#endif /* !_CERTIKOS_BOOT_FS_H_ */
