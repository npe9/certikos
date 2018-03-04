#include <preinit/lib/debug.h>
#include <preinit/lib/pmap.h>
#include <preinit/lib/string.h>
#include <preinit/lib/types.h>

#include <lib/string.h>


#define ELF_MAGIC 0x464C457FU	/* "\x7FELF" in little endian */

// ELF header
typedef struct elfhdf {
	uint32_t e_magic;	// must equal ELF_MAGIC
	uint8_t e_elf[12];
	uint16_t e_type;
	uint16_t e_machine;
	uint32_t e_version;
	uint32_t e_entry;
	uint32_t e_phoff;
	uint32_t e_shoff;
	uint32_t e_flags;
	uint16_t e_ehsize;
	uint16_t e_phentsize;
	uint16_t e_phnum;
	uint16_t e_shentsize;
	uint16_t e_shnum;
	uint16_t e_shstrndx;
} elfhdr;

// ELF program header
typedef struct proghdr {
	uint32_t p_type;
	uint32_t p_offset;
	uint32_t p_va;
	uint32_t p_pa;
	uint32_t p_filesz;
	uint32_t p_memsz;
	uint32_t p_flags;
	uint32_t p_align;
} proghdr;

// ELF section header
typedef struct sechdr {
	uint32_t sh_name;
	uint32_t sh_type;
	uint32_t sh_flags;
	uint32_t sh_addr;
	uint32_t sh_offset;
	uint32_t sh_size;
	uint32_t sh_link;
	uint32_t sh_info;
	uint32_t sh_addralign;
	uint32_t sh_entsize;
} sechdr;

// Values for proghdr::p_type
#define ELF_PROG_LOAD		1

// Flag bits for proghdr::p_flags
#define ELF_PROG_FLAG_EXEC	1
#define ELF_PROG_FLAG_WRITE	2
#define ELF_PROG_FLAG_READ	4

// Values for sechdr::sh_type
#define ELF_SHT_NULL		0
#define ELF_SHT_PROGBITS	1
#define ELF_SHT_SYMTAB		2
#define ELF_SHT_STRTAB		3

// Values for sechdr::sh_name
#define ELF_SHN_UNDEF		0

#define PTE_P			0x001	/* Present */
#define PTE_W			0x002	/* Writeable */
#define PTE_U			0x004	/* User-accessible */

#define PAGESIZE		4096

#define NUM_PROC		64

extern void pt_resv(unsigned int pid, unsigned int vaddr, unsigned int perm);

void
__elf_load__(void *exe_ptr, int pmap_id)
{
	elfhdr *eh;
	proghdr *ph, *eph;
	sechdr *sh, *esh;
	char *strtab;
	uintptr_t bss_base, bss_size;
	uintptr_t exe = (uintptr_t) exe_ptr;


	eh = (elfhdr *) exe;

	KERN_ASSERT(eh->e_magic == ELF_MAGIC);
	KERN_ASSERT(eh->e_shstrndx != ELF_SHN_UNDEF);

	sh = (sechdr *) ((uintptr_t) eh + eh->e_shoff);
	esh = sh + eh->e_shnum;

	strtab = (char *) (exe + sh[eh->e_shstrndx].sh_offset);
	KERN_ASSERT(sh[eh->e_shstrndx].sh_type == ELF_SHT_STRTAB);

	bss_base = bss_size = 0;

	for (; sh < esh; sh++)
		if (strncmp(&strtab[sh->sh_name], ".bss", 4) == 0) {
			bss_base = sh->sh_addr;
			bss_size = sh->sh_size;
			break;
		}

	ph = (proghdr *) ((uintptr_t) eh + eh->e_phoff);
	eph = ph + eh->e_phnum;

	for (; ph < eph; ph++) {
		uintptr_t fa;
		uint32_t va, zva, eva, perm;

		if (ph->p_type != ELF_PROG_LOAD)
			continue;

		fa = (uintptr_t) eh + rounddown(ph->p_offset, PAGESIZE);
		va = rounddown(ph->p_va, PAGESIZE);
		zva = ph->p_va + ph->p_filesz;
		eva = roundup(ph->p_va + ph->p_memsz, PAGESIZE);

		perm = PTE_U | PTE_P;
		if (ph->p_flags & ELF_PROG_FLAG_WRITE)
			perm |= PTE_W;

		for(; va < eva; va += PAGESIZE, fa += PAGESIZE) {
			if (bss_base <= va &&
			    va + PAGESIZE <= bss_base + bss_size)
				continue;

			pt_resv(pmap_id, va, perm);

			if (va < rounddown(zva, PAGESIZE)) {
				/* copy a complete page */
				pt_copyout((void *) fa, pmap_id, va, PAGESIZE);
			} else if (va < zva && ph->p_filesz) {
				/* copy a partial page */
				pt_memset(pmap_id, va, 0, PAGESIZE);
				pt_copyout((void *) fa, pmap_id, va, zva-va);
			} else {
				/* zero a page */
				pt_memset(pmap_id, va, 0, PAGESIZE);
			}
		}
	}
}

uintptr_t
elf_entry(void *exe_ptr)
{
	uintptr_t exe = (uintptr_t) exe_ptr;
	elfhdr *eh = (elfhdr *) exe;
	KERN_ASSERT(eh->e_magic == ELF_MAGIC);
	return (uintptr_t) eh->e_entry;
}

extern uint8_t _binary___obj_user_idle_idle_start[];
extern uint8_t _binary___obj_user_pingpong_Alice_start[];
extern uint8_t _binary___obj_user_pingpong_Hacker_start[];
extern uint8_t _binary___obj_user_pingpong_Bob_start[];
extern uint8_t _binary___obj_user_vmm_vmm_start[];

const uint8_t * binaries[] = {
	_binary___obj_user_idle_idle_start,
	_binary___obj_user_vmm_vmm_start,
	_binary___obj_user_vmm_vmm_start,
	_binary___obj_user_pingpong_Alice_start,
	_binary___obj_user_pingpong_Hacker_start,
	_binary___obj_user_pingpong_Bob_start
};


#define TO_STRING(val) #val

const char * elf_names[] ={
	TO_STRING(_binary___obj_user_idle_idle_start),
	TO_STRING(_binary___obj_user_vmm_vmm_start),
	TO_STRING(_binary___obj_user_vmm_vmm_start),
	TO_STRING(_binary___obj_user_pingpong_Alice_start),
	TO_STRING(_binary___obj_user_pingpong_Hacker_start),
	TO_STRING(_binary___obj_user_pingpong_Bob_start)
};


void *ELF_LOC[NUM_PROC];
uintptr_t ELF_ENTRY_LOC[NUM_PROC] = {0};
uint32_t loaded[NUM_PROC] = {0};

void
__elf_load (void *exe_ptr, int pmap_id)
{
  KERN_DEBUG ("pmapid = %d\n", pmap_id);
	unsigned int i = 1;

	if (loaded[i] == 0 && pmap_id == i)
	{
		__elf_load__ (_binary___obj_user_idle_idle_start, 1);
		loaded[i] = 1;
		KERN_DEBUG("Idle process loaded.\n");
	}
	i+= 3;

	if (loaded[i] == 0 && pmap_id == i)
	{
		__elf_load__ (_binary___obj_user_pingpong_Alice_start, 4);
		loaded[i] = 1;
		KERN_DEBUG("Process Alice loaded.\n");
	}
	i++;

	if (loaded[i] == 0 && pmap_id == i)
	{
		__elf_load__ (_binary___obj_user_pingpong_Hacker_start, 5);
		loaded[i] = 1;
		KERN_DEBUG("Process Hacker loaded.\n");
	}
	i++;

	if (loaded[i] == 0 && pmap_id == i)
	{
		__elf_load__ (_binary___obj_user_pingpong_Bob_start, 6);
		loaded[i] = 1;
		KERN_DEBUG("Process Bob loaded.\n");
	}
}

void
elf_preload(void)
{
	unsigned int i = 0;

	ELF_LOC[i] = _binary___obj_user_idle_idle_start;
	ELF_ENTRY_LOC[i] = elf_entry(_binary___obj_user_idle_idle_start);
	i+= 3;
	
	ELF_LOC[i] = _binary___obj_user_pingpong_Alice_start;
	ELF_ENTRY_LOC[i] = elf_entry(_binary___obj_user_pingpong_Alice_start);
	i++;

	ELF_LOC[i] = _binary___obj_user_pingpong_Hacker_start;
	ELF_ENTRY_LOC[i] = elf_entry(_binary___obj_user_pingpong_Hacker_start);
	i++;

	ELF_LOC[i] = _binary___obj_user_pingpong_Bob_start;
	ELF_ENTRY_LOC[i] = elf_entry(_binary___obj_user_pingpong_Bob_start);
	i++;

	KERN_INFO("elf table:\n");
	unsigned int j;
	for (j = 0; j < i; j++)
	{
		KERN_INFO("%d: %-40s 0x%08x 0x%08x\n", j, elf_names[j], ELF_LOC[j], ELF_ENTRY_LOC[j]);
	}
}
