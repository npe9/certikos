#ifndef _PREINIT_LIB_SYSCALL_H_
#define _PREINIT_LIB_SYSCALL_H_

#ifdef _KERN_

#include <preinit/lib/types.h>

#define NUM_PROC	64
#define UCTX_SIZE	17

#define PAGESIZE	4096

#define PFE_PR		0x1	/* Page fault caused by protection violation */

#define PTE_P		0x001	/* Present */
#define PTE_W		0x002	/* Writeable */
#define PTE_U		0x004	/* User-accessible */

#define PAGESIZE			4096

#define NUM_PROC			64
#define NUM_CHAN			64

#define VM_USERHI			0xf0000000
#define VM_USERLO			0x40000000

#define PTE_P				0x001	/* Present */
#define PTE_W				0x002	/* Writeable */
#define PTE_U				0x004	/* User-accessible */

#define VMEXIT_IOIO			0x07b
#define VMEXIT_NPF			0x400

#define VMCB_EVENTINJ_TYPE_INTR		0
#define VMCB_EVENTINJ_TYPE_EXCPT	3

#define ATA_SECTOR_SIZE			512

enum
{
	U_EDI,
	U_ESI,
	U_EBP,
	U_OLD_ESP,
	U_EBX,
	U_EDX,
	U_ECX,
	U_EAX,
	U_ES,
	U_DS,
	U_TRAPNO,
	U_ERRNO,
	U_EIP,
	U_CS,
	U_EFLAGS,
	U_ESP,
	U_SS
};

#define SYS_puts 0
#define SYS_ring0_spawn 1
#define SYS_spawn 2
#define SYS_yield 3
#define SYS_sleep 4
#define SYS_disk_op 5
#define SYS_disk_cap 6
#define SYS_is_chan_ready 7
#define SYS_send 8
#define SYS_recv 9
#define SYS_get_tsc_per_ms 10
#define SYS_hvm_run_vm 11
#define SYS_hvm_get_exitinfo 12
#define SYS_hvm_mmap 13
#define SYS_hvm_set_seg 14
#define SYS_hvm_set_reg 15
#define SYS_hvm_get_reg 16
#define SYS_hvm_get_next_eip 17
#define SYS_hvm_inject_event 18
#define SYS_hvm_check_int_shadow 19
#define SYS_hvm_check_pending_event 20
#define SYS_hvm_intercept_int_window 21
#define SYS_hvm_get_tsc_offset 22
#define SYS_hvm_set_tsc_offset 23
#define SYS_hvm_handle_rdmsr 24
#define SYS_hvm_handle_wrmsr 25
#define SYS_get_quota 26
#define MAX_SYSCALL_NR 27


enum __error_nr {
	E_SUCC,		/* no errors */
	E_MEM,		/* memory failure */
	E_IPC,
	E_INVAL_CALLNR,	/* invalid syscall number */
	E_INVAL_ADDR,	/* invalid address */
	E_INVAL_PID,	/* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID,     /* general invalid id */
	E_DISK_OP,	/* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR	/* XXX: always put it at the end of __error_nr */
};

#define DISK_READ	0
#define DISK_WRITE	1

typedef enum {
	GUEST_EAX, GUEST_EBX, GUEST_ECX, GUEST_EDX, GUEST_ESI, GUEST_EDI,
	GUEST_EBP, GUEST_ESP, GUEST_EIP, GUEST_EFLAGS,
	GUEST_CR0, GUEST_CR2, GUEST_CR3, GUEST_CR4,
	GUEST_MAX_REG
} guest_reg_t;

typedef enum {
	GUEST_CS, GUEST_DS, GUEST_ES, GUEST_FS, GUEST_GS, GUEST_SS,
	GUEST_LDTR, GUEST_TR, GUEST_GDTR, GUEST_IDTR,
	GUEST_MAX_SEG_DESC
} guest_seg_t;

unsigned int uctx_arg1(void);
unsigned int uctx_arg2(void);
unsigned int uctx_arg3(void);
unsigned int uctx_arg4(void);
unsigned int uctx_arg5(void);
unsigned int uctx_arg6(void);
void uctx_set_errno(unsigned int);
void uctx_set_retval1(unsigned int);
void uctx_set_retval2(unsigned int);
void uctx_set_retval3(unsigned int);
void uctx_set_retval4(unsigned int);
unsigned int get_curid(void);

void sys_puts(void);
void sys_spawn(void);
void sys_ring0_spawn(void);
void sys_yield(void);
void sys_disk_op(void);
void sys_disk_cap(void);
void sys_get_tsc_per_ms(void);
void sys_start_trace(void);
void sys_stop_trace(void);

void sys_hvm_run_vm(void);
void sys_hvm_get_exitinfo(void);
void sys_hvm_mmap(void);
void sys_hvm_set_reg(void);
void sys_hvm_get_reg(void);
void sys_hvm_set_seg(void);
void sys_hvm_get_next_eip(void);
void sys_hvm_inject_event(void);
void sys_hvm_check_pending_event(void);
void sys_hvm_check_int_shadow(void);
void sys_hvm_intercept_int_window(void);
void sys_hvm_get_tsc_offset(void);
void sys_hvm_set_tsc_offset(void);
void sys_is_chan_ready(void);
void sys_send(void);
void sys_recv(void);
void sys_ssend(void);
void sys_srecv(void);
void sys_sleep(void);

void sys_offer_shared_mem(void);
void sys_shared_mem_status(void);

void sys_hvm_handle_rdmsr(void);
void sys_hvm_handle_wrmsr(void);

#endif /* _KERN_ */

#endif /* !_PREINIT_LIB_STRING_H_ */
