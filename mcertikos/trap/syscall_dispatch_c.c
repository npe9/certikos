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

#define E_INVAL_CALLNR 3

extern void sys_proc_create(void);
extern void sys_get_tsc_offset(void);
extern void sys_set_tsc_offset(void);
extern void sys_get_exitinfo(void);
extern void sys_mmap(void);
extern void sys_set_reg(void);
extern void sys_get_reg(void);
extern void sys_set_seg(void);
extern void sys_get_next_eip(void);
extern void sys_inject_event(void);
extern void sys_check_pending_event(void);
extern void sys_check_int_shadow(void);
extern void sys_intercept_int_window(void);
extern void sys_handle_rdmsr(void);
extern void sys_handle_wrmsr(void);
extern void sys_receive_chan(void);
extern void uctx_set_errno(unsigned int);
extern unsigned int uctx_arg1(void);

void syscall_dispatch_c()
{
  unsigned int arg1;
  arg1 = uctx_arg1();
  if (arg1 == SYS_spawn)
    sys_proc_create();
  else if(arg1 == SYS_hvm_get_tsc_offset)
    sys_get_tsc_offset();
  else if(arg1 == SYS_hvm_set_tsc_offset)
    sys_set_tsc_offset();
  else if(arg1 == SYS_hvm_get_exitinfo)
    sys_get_exitinfo();
  else if(arg1 == SYS_hvm_mmap)
    sys_mmap();
  else if(arg1 == SYS_hvm_set_reg)
    sys_set_reg();
  else if(arg1 == SYS_hvm_get_reg)
    sys_get_reg();
  else if(arg1 == SYS_hvm_set_seg)
    sys_set_seg();
  else if(arg1 == SYS_hvm_get_next_eip)
    sys_get_next_eip();
  else if(arg1 == SYS_hvm_inject_event)
    sys_inject_event();
  else if(arg1 == SYS_hvm_check_pending_event)
    sys_check_pending_event();
  else if(arg1 == SYS_hvm_check_int_shadow)
    sys_check_int_shadow();
  else if(arg1 == SYS_hvm_intercept_int_window)
    sys_intercept_int_window();
  else if(arg1 == SYS_hvm_handle_rdmsr)
    sys_handle_rdmsr();
  else if(arg1 == SYS_hvm_handle_wrmsr)
    sys_handle_wrmsr();
  else if(arg1 == SYS_get_quota)
    sys_get_quota();
  else if(arg1 == SYS_recv)
    sys_receive_chan();
  else
    uctx_set_errno(E_INVAL_CALLNR);
}
