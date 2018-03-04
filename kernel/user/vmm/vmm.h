#ifndef _USER_VMM_H_
#define _USER_VMM_H_

#include <hvm.h>
#include <syscall.h>
#include <types.h>

#include "vmm_dev.h"

#define PAGESIZE		4096
#define MAX_GUEST_MEMSIZE	(4ULL * 1024 * 1024 * 1024)
#define MMAP_BITMAP_SIZE	(MAX_GUEST_MEMSIZE / (PAGESIZE * 32))

struct vmm_ops;

struct vm {
	int		vmid;		/* virtual machine ID */

	size_t		memsize;	/* guest physical memory size */
	uint64_t	cpufreq;	/* guest CPU frequency */
	uint8_t		*memory;
	uint8_t		*memory_dev;
	uint32_t	mmap_bitmap[MMAP_BITMAP_SIZE];
	uint64_t	tsc;

	struct vmm_ops	*ops;

	exit_reason_t	exit_reason;
	exit_info_t	exit_info;
	bool		exit_handled;

	struct vdev	vdev;
};

struct vmm_ops {
	int (*get_msr)(struct vm *vm, uint32_t msr, uint64_t *val);
	int (*set_msr)(struct vm *vm, uint32_t msr, uint64_t val);
	int (*get_cpuid)(struct vm *vm, uint32_t in_eax, uint32_t in_ecx,
			 uint32_t *eax, uint32_t *ebx,
			 uint32_t *ecx, uint32_t *edx);
};

/*
 * Initialize a virtual machine.
 *
 * @param vm      the virtual machine
 * @param cpufreq the guest CPU frequency in Hz
 * @param memsize the guest memory size in byte
 *
 * @return 0 if successful; otherwise, return a non-zero value.
 */
int vmm_init_vm(struct vm *vm, uint64_t cpufreq, size_t memsize);

/*
 * Run a virtual machine.
 *
 * @param vm the virtual machine
 *
 * @return 0 if the virtual machine teminates normally; otherwise, return a
 *         non-zero value.
 */
int vmm_run_vm(struct vm *vm);

/*
 * Copy (when write == 0) the data from the guest physical memory to the host
 * host linear address space.
 *
 * Copy (when write != 0) the data from the host linear address space to the
 * guest physical memory.
 *
 * @param vm    the virtual machine
 * @param gpa   the start guest physical address
 * @param la    the start host linear address
 * @param size  how many bytes will be copied
 * @param write non-zero: copy to the guest; 0: copy from the guest
 *
 * @return 0 if copy succeeds; otherwise, return a non-zero value
 */
int vmm_rw_guest_memory(struct vm *vm, uintptr_t gpa, uintptr_t hva,
			size_t size, int write);

#define vmm_read_guest_memory(vm, gpa, la, size)		\
	vmm_rw_guest_memory((vm), (gpa), (la), (size), 0)

#define vmm_write_guest_memory(vm, gpa, la, size)		\
	vmm_rw_guest_memory((vm), (gpa), (la), (size), 1)

/*
 * Translate a guest physical address to the host virtual address.
 */
uintptr_t vmm_translate_gp2hv(struct vm *vm, uintptr_t gpa);

#endif /* _USER_VMM_H_ */
