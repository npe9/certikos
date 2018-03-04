extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);

extern unsigned int get_curid(void);

extern unsigned int pt_read(unsigned int proc_index, unsigned int vaddr);
extern unsigned int pt_resv(unsigned int proc_index, unsigned int vaddr, unsigned int perm);
extern unsigned int vmx_set_mmap(unsigned int gpa, unsigned int hpa, unsigned int mem_type);

#define PAGESIZE			4096u
#define VM_USERHI			0xf0000000u
#define VM_USERLO			0x40000000u

#define PTE_P				0x001u	/* Present */
#define PTE_W				0x002u	/* Writeable */
#define PTE_U				0x004u	/* User-accessible */

enum __error_nr
{
	E_SUCC = 0, /* no errors */
	E_MEM, /* memory failure */
	E_IPC,
	E_INVAL_CALLNR, /* invalid syscall number */
	E_INVAL_ADDR, /* invalid address */
	E_INVAL_PID, /* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID, /* general invalid id */
	E_DISK_OP, /* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR /* XXX: always put it at the end of __error_nr */
};

void
sys_mmap ()
{
	unsigned int cur_pid;
	unsigned int gpa;
	unsigned int hva;
	unsigned int hpa;
	unsigned int mem_type;

	cur_pid = get_curid ();
	gpa = uctx_arg2 ();
	hva = uctx_arg3 ();
	mem_type = uctx_arg4 ();

	if (hva % PAGESIZE != 0 || gpa % PAGESIZE != 0
			|| !(VM_USERLO <= hva && hva <= VM_USERHI - PAGESIZE))
	{
		uctx_set_errno (E_INVAL_ADDR);
	}
  else
  {
    hpa = pt_read (cur_pid, hva);

    if ((hpa & PTE_P) == 0)
    {
      pt_resv (cur_pid, hva, PTE_P | PTE_U | PTE_W);
      hpa = pt_read (cur_pid, hva);
    }

    hpa = (hpa & 0xfffff000u) + (hva % PAGESIZE);

    vmx_set_mmap (gpa, hpa, mem_type);

    uctx_set_errno (E_SUCC);
  }
}
