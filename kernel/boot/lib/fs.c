#include <types.h>
#include <string.h>
#include <x86.h>
#include <ext2.h>
#include <debug.h>
#include <fs.h>
#include <bios.h>

#define BOOT_ASSERT(a)		assert(a)

struct {
	uint8_t dev;
#define EXT2_FS_DEV		(ext2_fs_param.dev)

	uint64_t start_sector;
#define EXT2_FS_START_SECTOR	(ext2_fs_param.start_sector)

	uint32_t rev;
#define EXT2_FS_REV		(ext2_fs_param.rev)

	uint32_t block_size;
#define EXT2_FS_BLK_SIZE	(ext2_fs_param.block_size)
	uint32_t blocks_per_group;
#define EXT2_FS_BLK_PER_GRP	(ext2_fs_param.blocks_per_group)
	uint32_t inodes_per_group;
#define EXT2_FS_INO_PER_GRP	(ext2_fs_param.inodes_per_group)

/*	uint32_t sector_offset; */
/* #define EXT2_FS_SEC_OFF		(ext2_fs_param.sector_offset) */
/*	uint32_t group_desc_table_sect_idx; */
/* #define EXT2_FS_GPT_SECT_IDX	(ext2_fs_param.group_desc_table_sect_idx) */

	uint32_t sectors_per_block;
#define EXT2_FS_SEC_PER_BLK	(ext2_fs_param.sectors_per_block)
	uint32_t blocks_per_block;
#define EXT2_FS_BLK_PER_BLK	(ext2_fs_param.blocks_per_block)

	/* EXT2_DYNAMIC_REV specific */
	uint32_t inode_size;
#define EXT2_FS_INO_SIZE	(ext2_fs_param.inode_size)
	uint32_t first_ino;
#define EXT2_FS_FIRST_INO	(ext2_fs_param.first_ino)
} ext2_fs_param;

/*
 * Initialze ext2_fs_param
 */
void ext2_fs_init(uint8_t dev, uint64_t sect_idx)
{
	/* debug("ext2_fs_init(%x, %x)\n", dev, sect_idx); */
	memset(&ext2_fs_param, 0x0, sizeof(ext2_fs_param));

	EXT2_FS_DEV = dev;

	EXT2_FS_START_SECTOR = sect_idx;

	uint8_t super_block_buf[1024];
	/* the first 2 sectors of the partition is reserved for VBR */
	read_sector(dev, sect_idx+2, &super_block_buf[0]);
	read_sector(dev, sect_idx+3, &super_block_buf[512]);

	ext2_super_block_t *super_block = (ext2_super_block_t *)super_block_buf;

	if (super_block->s_magic != EXT2_SUPER_MAGIC)
		panic("Not ext2 super block (magic = %x)\n", super_block->s_magic);

	EXT2_FS_REV = super_block->s_rev_level;

	EXT2_FS_BLK_SIZE = 1024 << (super_block->s_log_block_size);
	EXT2_FS_BLK_PER_GRP = super_block->s_blocks_per_group;
	EXT2_FS_INO_PER_GRP = super_block->s_inodes_per_group;

	/* EXT2_FS_SEC_OFF = sect_idx + */
	/*	((EXT2_FS_BLK_SIZE > 1024) ? (EXT2_FS_BLK_SIZE/SECTOR_SIZE) : 0); */
	/* EXT2_FS_GPT_SECT_IDX = sect_idx + 2 + EXT2_FS_BLK_SIZE/SECTOR_SIZE; */

	EXT2_FS_SEC_PER_BLK = EXT2_FS_BLK_SIZE / SECTOR_SIZE;
	EXT2_FS_BLK_PER_BLK = EXT2_FS_BLK_SIZE / 4;

	EXT2_FS_INO_SIZE = super_block->s_inode_size;
	EXT2_FS_FIRST_INO = super_block->s_first_ino;

	/* debug("init data @ %x\n", &ext2_fs_param); */
	/* debug("ext2 rev = %x\n", EXT2_FS_REV); */
	/* debug("block size = %x\n", EXT2_FS_BLK_SIZE); */
	/* debug("blocks per group = %x\n", EXT2_FS_BLK_PER_GRP); */
	/* debug("block numbers = %x\n", super_block->s_blocks_count); */
	/* debug("inode size = %x\n", EXT2_FS_INO_SIZE); */
	/* debug("inodes per group = %x\n", EXT2_FS_INO_PER_GRP); */
	/* debug("inodes number = %x\n", super_block->s_inodes_count); */
	/* debug("block group table is at sector %x\n", EXT2_FS_GPT_SECT_IDX); */
	/* debug("offset sectors = %x\n", EXT2_FS_SEC_OFF); */
}

#define BLK2SEC(blk_idx)						\
	((blk_idx) * EXT2_FS_SEC_PER_BLK + EXT2_FS_START_SECTOR)

/*
 * Read a block from disk to memory.
 * @param blk_idx  the block index
 * @param buf      the address of the output buffer
 * @return the amount of bytes actually read
 */
void read_block(uint32_t blk_idx, uint8_t *buf)
{
	BOOT_ASSERT(buf);

	uint64_t sec_idx = BLK2SEC(blk_idx);

	int i;
	uint8_t *p = buf;
	for (i = 0; i < EXT2_FS_SEC_PER_BLK; i++) {
		if (read_sector(EXT2_FS_DEV, sec_idx, p)) {
			panic("read_sector error: sect_idx = %x\n", sec_idx);
		}
		sec_idx++;
		p += SECTOR_SIZE;
	}
}

/*
 * Read a block group descriptor from disk to memory.
 * @param bg_idx  index of the block group that the block group descriptor
 *                decribes
 * @param bg_desc memory address of the block group descriptor
 */
void read_block_group_descriptor(uint32_t bg_idx,
				 ext2_block_group_descriptor_t *bg_desc)
{
	/* debug("read_block_group_descriptor(): block group idx=%x\n", bg_idx); */

	BOOT_ASSERT(bg_desc);

	uint32_t bg_desc_table_base =
		(EXT2_FS_BLK_SIZE > 1024) ? BLK2SEC(1) : BLK2SEC(2);
	uint32_t bg_desc_table_off =
		bg_idx * sizeof(ext2_block_group_descriptor_t);
	uint32_t bg_desc_addr =
		bg_desc_table_base + bg_desc_table_off / SECTOR_SIZE;
	uint32_t bg_desc_off = bg_desc_table_off % SECTOR_SIZE;

	uint8_t buf[SECTOR_SIZE];

	read_sector(EXT2_FS_DEV, bg_desc_addr, buf);

	memcpy(bg_desc, &buf[bg_desc_off],
	       sizeof(ext2_block_group_descriptor_t));
}

/*
 * Read an inode from disk to memory.
 * @param inode_idx        the inode index
 * @param inode            memory address of inode
 */
void read_inode(uint32_t inode_idx, ext2_inode_t *inode)
{
	/* debug("read_inode(inode_idx=%x)\n", inode_idx); */

	BOOT_ASSERT(inode);

	uint32_t inode_bg_idx = INODE_BG_IDX(inode_idx, EXT2_FS_INO_PER_GRP);
	uint32_t inode_local_idx = INODE_LOCAL_IDX(inode_idx,
						   EXT2_FS_INO_PER_GRP);

	ext2_block_group_descriptor_t bg_desc;
	read_block_group_descriptor(inode_bg_idx, &bg_desc);

	/* { */
	/*	debug("block group decriptor table\n"); */
	/*	info("block bitmap @ %x, inode map @ %x, inode table @ %x\n", */
	/*	     bg_desc.bg_block_bitmap, */
	/*	     bg_desc.bg_inode_bitmap, */
	/*	     bg_desc.bg_inode_table); */
	/* } */

	uint32_t inode_table = bg_desc.bg_inode_table;
	uint32_t inode_entry = inode_local_idx * EXT2_FS_INO_SIZE;
	uint32_t inode_entry_sec_idx =
		BLK2SEC(inode_table) + inode_entry / SECTOR_SIZE;
	uint32_t inode_entry_sec_off = inode_entry % SECTOR_SIZE;

	/* debug("inode @ %x:%x\n", inode_entry_sec_idx, inode_entry_sec_off); */

	BOOT_ASSERT(EXT2_FS_INO_SIZE <= SECTOR_SIZE);
	uint8_t sector[SECTOR_SIZE];
	read_sector(EXT2_FS_DEV, inode_entry_sec_idx, sector);
	memcpy(inode, &sector[inode_entry_sec_off], sizeof(ext2_inode_t));
}

/*
 * Search a file in a block of a directory.
 * @param blk  the direct block
 * @param name the file name
 * @param len  the length of the file name
 * @param dep  0 indicates blk is a direct block,
 *             1 indicates blk is a first indirect block,
 *             2 indicates blk is a doubly indirect block, and
 *             3 indicates blk is a triply indirect block
 * @return the inode number of the file if found, otherwise EXT2_BAD_INO
 */
static uint32_t search_in_block(uint32_t *blk,
				const char *name, const int len,
				const int dep)
{
	BOOT_ASSERT(blk);
	BOOT_ASSERT(name);
	BOOT_ASSERT(len > 0);
	BOOT_ASSERT(dep >= 0 && dep <= 3);

	if (dep == 0) {
		ext2_dir_t *dir = (ext2_dir_t *)blk;
		uint32_t total_len = 0;
		while (total_len < EXT2_FS_BLK_SIZE) {
			if (dir->name_len == len &&
			    memcmp(dir->name, name, len) == 0)
				return dir->inode;

			total_len += dir->rec_len;
			dir = (ext2_dir_t *) ((uint32_t)dir + dir->rec_len);
		}

		return EXT2_BAD_INO;
	} else {
		uint8_t block[EXT2_FS_BLK_SIZE];
		uint32_t ino;
		int i;

		for (i = 0; i < EXT2_FS_BLK_PER_BLK; i++) {
			if (blk[i] == 0)
				break;

			read_block(blk[i], block);

			if ((ino = search_in_block((uint32_t *)block,
						   name, len,
						   dep-1)) != EXT2_BAD_INO)
				return ino;
		}

		return EXT2_BAD_INO;
	}
}

/*
 * Search a file in a directory.
 * @param dir_ino the inode of the directory
 * @param name    the file name
 * @param len     the length of the file name
 * @return the inode number of the file if found, otherwise EXT2_BAD_INO
 */
uint32_t search_in_dir(ext2_inode_t *dir_ino, const char *name, const int len)
{
	BOOT_ASSERT(dir_ino);
	BOOT_ASSERT(dir_ino->i_mode & EXT2_S_IFDIR);
	BOOT_ASSERT(name);
	BOOT_ASSERT(len > 0);

	uint8_t blk[EXT2_FS_BLK_SIZE];
	uint32_t ino;

	/* the first 12 blocks are direct blocks */
	int i;
	for (i = 0; i < 12; i++) {
		/* debug(">> search in direct block %x\n", i); */
		if (dir_ino->i_block[i] == 0)
			return EXT2_BAD_INO;

		read_block(dir_ino->i_block[i], blk);

		ino = search_in_block((uint32_t *)blk, name, len, 0);
		if (ino != EXT2_BAD_INO)
			return ino;
	}

	/* the 13rd block is a first indirect block */
	/* debug(">> search in first indirect block\n"); */
	if (dir_ino->i_block[12] == 0)
		return EXT2_BAD_INO;
	read_block(dir_ino->i_block[12], blk);
	ino = search_in_block((uint32_t *)blk, name, len, 1);
	if (ino != EXT2_BAD_INO)
		return ino;

	/* the 14th block is a doubly-indirect block */
	/* debug(">> search in doubly indirect block\n"); */
	if (dir_ino->i_block[13] == 0)
		return EXT2_BAD_INO;
	read_block(dir_ino->i_block[13], blk);
	ino = search_in_block((uint32_t *)blk, name, len, 2);
	if (ino != EXT2_BAD_INO)
		return ino;

	/* the 15th block is a triply-indirect block */
	/* debug(">> search in triply indirect block\n"); */
	if (dir_ino->i_block[14] == 0)
		return EXT2_BAD_INO;
	read_block(dir_ino->i_block[14], blk);
	ino = search_in_block((uint32_t *)blk, name, len, 3);
	return ino;
}

uint32_t find_file(const char *fullname)
{
	BOOT_ASSERT(fullname != 0 && fullname[0] == '/');

	const char *path = &fullname[1];/* skip the starting slash */
	ssize_t path_len = strnlen(path, 255);
	char partname[256];		/* the file name in ext2 is limited to
					   255 characters */
	ssize_t part_len;

	ext2_inode_t inode;
	uint32_t inode_idx;

	/* load root directory */
	read_inode(EXT2_ROOT_INO, &inode);
	if ((inode_idx = search_in_dir(&inode, "boot", 4)) == EXT2_BAD_INO) {
		/* debug("Cannot find directory /boot/\n"); */
		return EXT2_BAD_INO;
	}

	do {
		char *next_slash = strchr(path, '/');

		if (next_slash != 0)
			part_len = next_slash - path;
		else
			part_len = path_len;

		memcpy(partname, path, path_len);

		if (next_slash == 0)	/* not a direcory */
			break;

		path += (part_len + 1);
		path_len -= (part_len + 1);

		uint32_t inode_idx = search_in_dir(&inode, partname, part_len);
		if (inode_idx == EXT2_BAD_INO) {
			/* debug("Cannot find in the directory.\n"); */
			return EXT2_BAD_INO;
		}

		read_inode(inode_idx, &inode);

		if (! (inode.i_mode & EXT2_S_IFDIR)) {
			/* debug("Not a directory.\n"); */
			return EXT2_BAD_INO;
		}
	} while (1);

	return search_in_dir(&inode, partname, part_len);
}

static void _ext2_fsread(ext2_inode_t *inode, uint8_t *buf,
			 uint32_t start, uint32_t size)
{
	/* debug("_ext2_fsred: buf = %x, start = %x, size = %x\n", buf, start, size); */

	BOOT_ASSERT(inode != 0 && buf != 0);

	uint32_t blk_idx = start / EXT2_FS_BLK_SIZE;
	uint32_t blk_off = start % EXT2_FS_BLK_SIZE;

	uint32_t _blk_idx;

	uint8_t blk_buf[EXT2_FS_BLK_SIZE];

	if (blk_idx < 12) {
		/* direct block */
		read_block(inode->i_block[blk_idx], blk_buf);
	} else if (blk_idx >= 12 && blk_idx < 12 + EXT2_FS_BLK_PER_BLK) {
		/* first indirect block */
		read_block(inode->i_block[12], blk_buf);
		read_block(((uint32_t *)blk_buf)[blk_idx - 12], blk_buf);
	} else if (blk_idx >= 12 + EXT2_FS_BLK_PER_BLK &&
		   blk_idx < 12 + EXT2_FS_BLK_PER_BLK +
		   EXT2_FS_BLK_PER_BLK * EXT2_FS_BLK_PER_BLK) {
		/* doubly indirect block */
		read_block(inode->i_block[13], blk_buf);

		uint32_t __blk_idx = blk_idx - 12 - EXT2_FS_BLK_PER_BLK;

		_blk_idx = __blk_idx / EXT2_FS_BLK_PER_BLK;
		read_block(((uint32_t *)blk_buf)[_blk_idx], blk_buf);

		_blk_idx = __blk_idx % EXT2_FS_BLK_PER_BLK;
		read_block(((uint32_t *)blk_buf)[_blk_idx], blk_buf);
	} else {
		/* triply indirect block */
		read_block(inode->i_block[14], blk_buf);

		uint32_t __blk_idx = blk_idx - 12 - EXT2_FS_BLK_PER_BLK -
			EXT2_FS_BLK_PER_BLK * EXT2_FS_BLK_PER_BLK;

		_blk_idx =
			__blk_idx / (EXT2_FS_BLK_PER_BLK * EXT2_FS_BLK_PER_BLK);
		read_block(((uint32_t *)blk_buf)[_blk_idx], blk_buf);


		_blk_idx =
			(__blk_idx / EXT2_FS_BLK_PER_BLK) % EXT2_FS_BLK_PER_BLK;
		read_block(((uint32_t *)blk_buf)[_blk_idx], blk_buf);

		_blk_idx = __blk_idx % EXT2_FS_BLK_PER_BLK;
		read_block(((uint32_t *)blk_buf)[_blk_idx], blk_buf);
	}

	int i;
	for (i = 0; i < size; i++)
		buf[i] = blk_buf[blk_off + i];
}

void ext2_fsread(ext2_inode_t *inode, uint8_t *buf,
		 uint32_t start, uint32_t size)
{
	/* debug("ext2_fsread: inode = %x, buf = %x, start = %x, size = %x\n", */
	/*       inode, buf, start, size); */

	if (size == 0)
		return;

	assert(inode != 0 && buf != 0);

	uint32_t fp = start;
	uint8_t *p = buf;
	uint32_t remain = size;
	uint32_t blk_read_count = 0;

	while (remain > 0) {
		blk_read_count++;

		uint32_t blk_off = fp % EXT2_FS_BLK_SIZE;
		uint32_t read_size = EXT2_FS_BLK_SIZE - blk_off;
		if (read_size > remain)
			read_size = remain;

		_ext2_fsread(inode, p, fp, read_size);

		fp += read_size;
		p += read_size;

		remain -= read_size;
	}
}
