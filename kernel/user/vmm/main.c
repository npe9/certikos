#include <gcc.h>
#include <stdio.h>
#include <types.h>
#include <x86.h>

#include "vmm.h"
#include "vmm_dev.h"

#include "dev/i8042/kbd.h"
#include "dev/i8254/pit.h"
#include "dev/i8259/pic.h"
#include "dev/nvram/nvram.h"
#include "dev/serial/serial.h"
#include "dev/virtio/pci.h"
#include "dev/virtio/virtio_blk.h"

#define VM_MEMSIZE	(256UL * 1024 * 1024 * 4)
#define VM_CPUFREQ	(1ULL * 1000 * 1000)

static uint8_t vm_memory[VM_MEMSIZE] gcc_aligned(PAGESIZE);
static uint8_t vm_dev_memory[256UL * 1024 *1024] gcc_aligned(PAGESIZE);

struct vm vm;

int
main(int argc, char **argv)
{
	struct vnvram nvram;
	struct vkbd kbd;
	struct vpit pit;
	struct vpci_host pci_host;
	struct virtio_blk blk;
	struct vpic pic;
	struct vserial com1;


	vm.memory = vm_memory;
	vm.memory_dev = vm_dev_memory;

	printf("vmm vm_memory: 0x%08x\n", vm_memory);

	if (vmm_init_vm(&vm, VM_CPUFREQ, VM_MEMSIZE)) {
		printf("Cannot intialize VM.\n");
		return -1;
	}

	if (vnvram_init(&vm.vdev, &nvram, VM_MEMSIZE)) {
		printf("Cannot intialize virtual NVRAM.\n");
		return -2;
	}

	if (vkbd_init(&vm.vdev, &kbd)) {
		printf("Cannot initialize virtual keyborad controller.\n");
		return -2;
	}

	if (vpit_init(&vm.vdev, &pit, VM_CPUFREQ)) {
		printf("Cannot intialize virtual timer.\n");
		return -2;
	}

	if (virtio_blk_init(&vm.vdev, &pci_host, &blk)) {
		printf("Cannot initialize virtio block.\n");
		return -2;
	}

	if (vserial_init(&vm.vdev, &com1)) {
		printf("Cannot intiailize virtual COM1.\n");
		return -2;
	}

	if (vpic_init(&vm.vdev, &pic)) {
		printf("Cannot initialize virtual i8259.\n");
		return -2;
	}

	printf("Starting virtual machine ... \n");

	if (vmm_run_vm(&vm)) {
    printf("Failed to run the vm.\n");
		return -3;
  }

	return 0;
}
