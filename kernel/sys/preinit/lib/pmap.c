#include <preinit/lib/pmap.h>
#include <preinit/lib/string.h>
#include <preinit/lib/types.h>

#include <lib/string.h>

#define PTE_P		0x001	/* Present */
#define PTE_W		0x002	/* Writeable */
#define PTE_U		0x004	/* User-accessible */

#define PAGESIZE	4096

#define VM_USERHI	0xf0000000
#define VM_USERLO	0x40000000

extern void pt_resv(unsigned int pid, unsigned int vaddr, unsigned int perm);
extern unsigned int pt_read(unsigned int pid, unsigned int vaddr);

size_t
pt_copyin(uint32_t pmap_id, uintptr_t uva, void *kva, size_t len)
{
	if (!(VM_USERLO <= uva && uva + len <= VM_USERHI))
		return 0;

	if ((uintptr_t) kva + len > VM_USERHI)
		return 0;

	size_t copied = 0;

	while (len) {
		uintptr_t uva_pa = pt_read(pmap_id, uva);

		if ((uva_pa & PTE_P) == 0) {
			pt_resv(pmap_id, uva, PTE_P | PTE_U | PTE_W);
			uva_pa = pt_read(pmap_id, uva);
		}

		uva_pa = (uva_pa & 0xfffff000) + (uva % PAGESIZE);

		size_t size = (len < PAGESIZE - uva_pa % PAGESIZE) ?
			len : PAGESIZE - uva_pa % PAGESIZE;

		memcpy(kva, (void *) uva_pa, size);

		len -= size;
		uva += size;
		kva += size;
		copied += size;
	}

	return copied;
}

size_t
pt_copyout(void *kva, uint32_t pmap_id, uintptr_t uva, size_t len)
{
	if (!(VM_USERLO <= uva && uva + len <= VM_USERHI))
		return 0;

	if ((uintptr_t) kva + len > VM_USERHI)
		return 0;

	size_t copied = 0;

	while (len) {
		uintptr_t uva_pa = pt_read(pmap_id, uva);

		if ((uva_pa & PTE_P) == 0) {
			pt_resv(pmap_id, uva, PTE_P | PTE_U | PTE_W);
			uva_pa = pt_read(pmap_id, uva);
		}

		uva_pa = (uva_pa & 0xfffff000) + (uva % PAGESIZE);

		size_t size = (len < PAGESIZE - uva_pa % PAGESIZE) ?
			len : PAGESIZE - uva_pa % PAGESIZE;

		memcpy((void *) uva_pa, kva, size);

		len -= size;
		uva += size;
		kva += size;
		copied += size;
	}

	return copied;
}

size_t
pt_memset(uint32_t pmap_id, uintptr_t va, char c, size_t len)
{
        size_t set = 0;

	while (len) {
		uintptr_t pa = pt_read(pmap_id, va);

		if ((pa & PTE_P) == 0) {
			pt_resv(pmap_id, va, PTE_P | PTE_U | PTE_W);
			pa = pt_read(pmap_id, va);
		}

		pa = (pa & 0xfffff000) + (va % PAGESIZE);

		size_t size = (len < PAGESIZE - pa % PAGESIZE) ?
			len : PAGESIZE - pa % PAGESIZE;

		memset((void *) pa, c, size);

		len -= size;
		va += size;
		set += size;
	}

	return set;
}

extern uint32_t get_curid(void);

uintptr_t
la2pa_reserve(uintptr_t va)
{
	uint32_t cur_pid = get_curid();
	uintptr_t pa = pt_read(cur_pid, va);

	if ((pa & PTE_P) == 0) {
		pt_resv(cur_pid, va, PTE_P | PTE_U | PTE_W);
		pa = pt_read(cur_pid, va);
	}

	pa = (pa & 0xfffff000) + (va % PAGESIZE);

	return pa;
}
