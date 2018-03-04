(* *********************************************************************)
(*                                                                     *)
(*            The CertiKOS Certified Kit Operating System              *)
(*                                                                     *)
(*                   The FLINT Group, Yale University                  *)
(*                                                                     *)
(*  Copyright The FLINT Group, Yale University.  All rights reserved.  *)
(*  This file is distributed under the terms of the Yale University    *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)
(* *********************************************************************)
(*                                                                     *)
(*              Object Primitives                                      *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import FlatMemory.
Require Import AbstractDataType.
Require Import Integers.
Require Import Values.
Require Import Constant.
Require Import RealParams.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import CalRealSMSPool.
Require Import CalRealProcModule.
(*Require Import CalRealIntelModule.*)
Require Import liblayers.compat.CompatGenSem.

Require Import ObjArg.
Require Import ObjProc.
(*Require Import ObjVMX.
Require Import ObjVMCS.*)
Require Import ObjLMM.
Require Import ObjVMM.
Require Import ObjSyncIPC.
Require Import ObjThread.
Require Import ObjContainer.
Require Import ObjFlatMem.

Section OBJ_Trap.

(*
  (*
void
sys_is_chan_ready(void)
{
	syscall_set_retval1(is_chan_ready());
	syscall_set_errno(E_SUCC);
}
   *)

  Function trap_ischanready_spec (abd: RData) :=
      match is_chan_ready_spec abd with
        | Some r =>
          (* rewrite return value*)
          match uctx_set_retval1_spec r abd with
            | Some abd0 => uctx_set_errno_spec E_SUCC abd0
            | _ => None
          end
        | _ =>None
      end.
*)    

    (*
void
sys_send(void)
{
	unsigned int chid;
	unsigned int content;
	unsigned int val;

	chid = syscall_get_arg2();

	if (!(0 <= chid && chid < NUM_CHAN)) {
		syscall_set_errno(E_INVAL_CHID);
		return;
	}

	content = syscall_get_arg3();

	if (content == 0) {
		syscall_set_errno(E_INVAL_CHID);
		return;
	}

	val = send(chid, content);

	if (val == 1)
		syscall_set_errno(E_SUCC);
	else
		syscall_set_errno(E_IPC);
}
     *)

  (*Function trap_sendtochan_spec (abd: RData) :=
      match uctx_arg2_spec abd with
        | Some chid =>
          match uctx_arg3_spec abd with
            | Some content =>
              match sendto_chan_spec chid content abd with
                | Some (abd0, r)  =>
                  match uctx_set_retval1_spec r abd0 with
                    | Some abd1 =>
                      uctx_set_errno_spec E_SUCC abd1
                    | _ => None
                  end
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end.*)

  Function trap_sendtochan_pre_spec (abd: RData) : option (RData * Z) :=
    match uctx_arg2_spec abd with
      | Some chid =>
        match uctx_arg3_spec abd with
          | Some vaddr =>
            match uctx_arg4_spec abd with
              | Some scount =>
                syncsendto_chan_pre_spec chid vaddr scount abd
              | _ => None
            end
          | _ => None
        end
      | _ => None
    end.

  Function trap_sendtochan_post_spec (abd: RData) :=
    match syncsendto_chan_post_spec abd with
      | Some (abd0, r) =>
        match uctx_set_retval1_spec r abd0 with
          | Some abd1 =>
            uctx_set_errno_spec E_SUCC abd1
          | _ => None
        end
          
      | _ => None
    end.

    (*
void
sys_recv(void)
{
	unsigned int val;
	val = recv();
	syscall_set_retval1(val);
	syscall_set_errno(E_SUCC);
}*)

  Function trap_receivechan_spec (abd: RData) :=
    match uctx_arg2_spec abd with
      | Some fromid =>
        match uctx_arg3_spec abd with
          | Some vaddr =>
            match uctx_arg4_spec abd with
              | Some rcount =>
                match syncreceive_chan_spec fromid vaddr rcount abd with
                  | Some (abd0, r)  =>
                    match uctx_set_retval1_spec r abd0 with
                      | Some abd1 =>
                        uctx_set_errno_spec E_SUCC abd1
                      | _ => None
                    end
                  | _ => None
                end| _ => None
            end| _ => None
        end| _ => None
    end.

  Function trap_get_quota_spec (abd: RData) :=
    match get_curid_spec abd with
      | Some curid =>
        match container_get_quota_spec curid abd with
          | Some quota =>
            match container_get_usage_spec curid abd with
              | Some usage =>
                match uctx_set_retval1_spec (quota - usage) abd with
                  | Some abd0 =>
                    uctx_set_errno_spec E_SUCC abd0
                  | _ => None
                end
              | _ => None
            end
          | _ => None
        end
      | _ => None
    end.
(*
(*
void
sys_hvm_intercept_int_window(void)
{
	unsigned int enable;
	enable = syscall_get_arg2();
        vmx_set_intercept_intwin(enable);
	syscall_set_errno(E_SUCC);
}
*)
    Function trap_intercept_int_window_spec (abd: RData) :=
      match uctx_arg2_spec abd with
        | Some enable =>
          match vmx_set_intercept_intwin_spec enable abd with
            | Some abd0 => uctx_set_errno_spec E_SUCC abd0
            | _ => None
          end
        | _ => None
      end.

(*
void
sys_hvm_check_pending_event(void)
{
    unsigned int event = 0;
        event = vmx_check_pending_event();

	syscall_set_retval1(event);

	syscall_set_errno(E_SUCC);
}
*)

    Function trap_check_pending_event_spec (abd: RData) :=
      match vmx_check_pending_event_spec abd with
        | Some event => 
          match uctx_set_retval1_spec event abd with
            | Some abd0 => uctx_set_errno_spec E_SUCC abd0
            | _ => None
          end
        | _ => None
      end.


(*
void
sys_hvm_check_int_shadow(void)
{
    unsigned int shadow = 0;
        shadow = vmx_check_int_shadow();

	syscall_set_retval1(shadow);

	syscall_set_errno(E_SUCC);
}
*)
    Function trap_check_int_shadow_spec (abd: RData) :=
      match vmx_check_int_shadow_spec abd with
        | Some shadow => 
          match uctx_set_retval1_spec shadow abd with
            | Some abd0 => uctx_set_errno_spec E_SUCC abd0
            | _ => None
          end
        | _ => None
      end.


(*
    void
      sys_hvm_inject_event(void)
      {
	unsigned int ev_type;
	unsigned int vector;
	unsigned int errcode;
	unsigned int ev;

	ev_type = syscall_get_arg2();
	vector = syscall_get_arg3();
	errcode = syscall_get_arg4();
	ev = syscall_get_arg5();

        vmx_inject_event(ev_type, vector, errcode, ev);
        syscall_set_errno(E_SUCC);

        return;
*)

    Function trap_inject_event_spec (abd: RData) :=
      match uctx_arg2_spec abd, uctx_arg3_spec abd, uctx_arg4_spec abd, uctx_arg5_spec abd with
        | Some ev_type, Some vector, Some err, Some ev =>
          match vmx_inject_event_spec ev_type vector err ev abd with
          | Some abd0 => uctx_set_errno_spec E_SUCC abd0
          | _ => None
          end
        | _,_,_,_ => None
      end.

(*
void
sys_hvm_get_next_eip(void)
{
	unsigned int reason;
	unsigned int neip = 0;
        neip = vmx_get_next_eip();

    syscall_set_retval1(neip);

	syscall_set_errno(E_SUCC);
}

*)

    Function trap_get_next_eip_spec (abd: RData) :=
      match vmx_get_next_eip_spec abd with
      | Some neip =>
        if zle_le 0 neip Int.max_unsigned then
          match uctx_set_retval1_spec neip abd with
          | Some abd0 => uctx_set_errno_spec E_SUCC abd0
          | _ => None
          end
        else None
      | _ => None
      end.

(*
void
sys_hvm_set_reg(void)
{
	unsigned int reg;
	unsigned int val;

	reg = syscall_get_arg2();
	val = syscall_get_arg3();
        
        
	if (GUEST_EAX <= reg && reg < GUEST_MAX_REG) {
               vmx_set_reg(reg, val);
	       syscall_set_errno(E_SUCC);
	} else
          {
	    syscall_set_errno(E_INVAL_REG);
          }
	return;
}*)

    Function trap_set_reg_spec (abd: RData) :=
      match uctx_arg2_spec abd, uctx_arg3_spec abd with
        | Some r, Some v =>
          if zle_lt C_GUEST_EAX r C_GUEST_MAX_REG then
            match vmx_set_reg_spec r v abd with
              | Some abd0 => uctx_set_errno_spec E_SUCC abd0
              | _ => None
            end
          else 
            uctx_set_errno_spec E_INVAL_REG abd
        | _,_ => None
      end.

(*
    void
      sys_hvm_get_reg(void)
      {
	unsigned int reg;

	reg = syscall_get_arg2();

	if (GUEST_EAX <= reg && reg < GUEST_MAX_REG) {
               reg = vmx_get_reg(reg);
	       syscall_set_retval1(reg);
	       syscall_set_errno(E_SUCC);
	     } else
          {
	    syscall_set_errno(E_INVAL_REG);
          }
	return;

      }
*)

    Function trap_get_reg_spec (abd: RData) :=
      match uctx_arg2_spec abd with
        | Some r =>
          if zle_lt C_GUEST_EAX r C_GUEST_MAX_REG then
            match vmx_get_reg_spec r abd with
              | Some v =>
                match uctx_set_retval1_spec v abd with
                  | Some abd0 => uctx_set_errno_spec E_SUCC abd0
                  | _ => None
                end
              | _ => None
            end
          else 
            uctx_set_errno_spec E_INVAL_REG abd
        | _ => None
      end.

(*
    void
      sys_hvm_set_seg(void)
      {
	unsigned int seg;
	unsigned int sel;
	unsigned int base;
	unsigned int lim;
	unsigned int ar;

	seg = syscall_get_arg2();
	sel = syscall_get_arg3();
	base = syscall_get_arg4();
	lim = syscall_get_arg5();
	ar = syscall_get_arg6();

	if (GUEST_CS <= seg && seg < GUEST_MAX_SEG_DESC) {
               vmx_set_desc(seg, sel, base, lim, ar);
	       syscall_set_errno(E_SUCC);
	     } else
          {
	    syscall_set_errno(E_INVAL_SEG);
          }
	return;
      }
*)

    Function trap_set_seg_spec (abd: RData) :=
      match uctx_arg2_spec abd, uctx_arg3_spec abd, uctx_arg4_spec abd,
            uctx_arg5_spec abd, uctx_arg6_spec abd with
        | Some seg, Some sel, Some base, Some lim, Some ar =>
          if zle_lt C_GUEST_CS seg C_GUEST_MAX_SEG_DESC then
            match vmx_set_desc_spec seg sel base lim ar abd with
              | Some abd0 => uctx_set_errno_spec E_SUCC abd0
              | _ => None
            end
          else 
            uctx_set_errno_spec E_INVAL_SEG abd
        | _,_,_,_,_ => None
      end.

(*
void
sys_hvm_get_tsc_offset(void)
{
  uint64_t tsc_offset = 0;
  tsc_offset = vmx_get_tsc_offset();

  syscall_set_retval1(tsc_offset >> 32);
  syscall_set_retval2(tsc_offset & 0xffffffff);

  syscall_set_errno(E_SUCC);
}*)

    Function trap_get_tsc_offset_spec (abd: RData) :=
      match vmx_get_tsc_offset_spec abd with
        | Some (VZ64 ofs) => 
          let ofs1 := ofs / (2 ^ 32) in
          let ofs2 := ofs mod (2 ^ 32) in
          match uctx_set_retval1_spec ofs1 abd with
            | Some abd0 => 
              match uctx_set_retval2_spec ofs2 abd0 with
                | Some abd1 => 
                  uctx_set_errno_spec E_SUCC abd1
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end.

(*
void
sys_hvm_set_tsc_offset(void)
{
  unsigned int tsc_offset_high, tsc_offset_low;
  uint64_t tsc_offset;
  tsc_offset_high = syscall_get_arg2();
  tsc_offset_low = syscall_get_arg3();
  tsc_offset = (uint64_t)tsc_offset_high << 32 | tsc_offset_low;

    vmx_set_tsc_offset(tsc_offset);

  syscall_set_errno(E_SUCC);
}*)

    Function trap_set_tsc_offset_spec (abd: RData) :=
      match uctx_arg2_spec abd, uctx_arg3_spec abd with
        | Some ofs_high, Some ofs_low =>
          let ofs := ofs_high * (2 ^ 32) + ofs_low in
          match vmx_set_tsc_offset_spec (VZ64 ofs) abd with
            | Some abd0 => uctx_set_errno_spec E_SUCC abd0
            | _ => None
          end
        | _,_ => None
      end.

(*
void
sys_hvm_mmap(void)
{
	unsigned int cur_pid;
	unsigned int gpa;
	unsigned int hva;
	unsigned int hpa;
    unsigned int mem_type;

	cur_pid = get_curid();
	gpa = syscall_get_arg2();
	hva = syscall_get_arg3();
  mem_type = syscall_get_arg4();

	if (hva % PAGESIZE != 0 || gpa % PAGESIZE != 0 ||
	    !(VM_USERLO <= hva && hva + PAGESIZE <= VM_USERHI)) {
		syscall_set_errno(E_INVAL_ADDR);
		return;
	}

  hpa = pt_read(cur_pid, hva);

  if ((hpa & PTE_P) == 0) {
      pt_resv(cur_pid, hva, PTE_P | PTE_U | PTE_W);
      hpa = pt_read(cur_pid, hva);
  }

  hpa = (hpa & 0xfffff000) + (hva % PAGESIZE);

     vmx_set_mmap(gpa, hpa, mem_type);
     syscall_set_errno(E_SUCC);
}*)

    Function trap_mmap_spec (abd: RData) :=
      match uctx_arg2_spec abd, uctx_arg3_spec abd, uctx_arg4_spec abd with
        | Some gpa, Some hva, Some mem_type =>
          if andb (andb (Zdivide_dec PgSize hva HPS)
                        (Zdivide_dec PgSize gpa HPS))
                  (zle_le adr_low hva (adr_high - PgSize)) then
            match ptRead_spec (cid abd) hva abd with
              | Some hpa =>
                if zle_le 0 hpa Int.max_unsigned then
                  if zeq (Z.land hpa PT_PERM_P) 0 then
                    match ptResv_spec (cid abd) hva PT_PERM_PTU abd with
                      | Some (abd0, _) =>
                        match ptRead_spec (cid abd) hva abd0 with
                          | Some hpa' =>
                            if zle_le 0 hpa' Int.max_unsigned then
                              let hpa0 := (Z.land hpa' v0xfffff000) + (hva mod PgSize) in
                              match vmx_set_mmap_spec gpa hpa0 mem_type abd0 with
                                | Some (abd1, _) => uctx_set_errno_spec E_SUCC abd1
                                | _ => None
                              end
                            else None
                          | _ => None
                        end
                      | _ => None
                    end
          else
            let hpa0 := (Z.land hpa v0xfffff000) + (hva mod PgSize) in
            match vmx_set_mmap_spec gpa hpa0 mem_type abd with
              | Some (abd1, _) => uctx_set_errno_spec E_SUCC abd1
              | _ => None
            end
    else None
  | _ => None
    end
    else uctx_set_errno_spec E_INVAL_ADDR abd
  | _,_,_ => None
    end.

(*
void
sys_hvm_get_exitinfo(void)
{
	unsigned int reason = 0;
	unsigned int port = 0;
	unsigned int width = 0;
	unsigned int write = 0;
	unsigned int rep = 0;
	unsigned int str = 0;
	unsigned int fault_addr = 0;
	unsigned int flags;
	unsigned int reason_io = 0;
	unsigned int reason_fault = 0;
	flags = 0;

	reason = vmx_get_exit_reason();
        port = vmx_get_exit_io_port();
        width = vmx_get_exit_io_width();
        write = vmx_get_exit_io_write();
        rep = vmx_get_exit_io_rep();
        str = vmx_get_exit_io_str();
        fault_addr = vmx_get_exit_fault_addr();
        reason_io = EXIT_REASON_INOUT;
        reason_fault = EXIT_REASON_EPT_FAULT;

	syscall_set_retval1(reason);

	if (reason == reason_io) {
		syscall_set_retval2(port);
		syscall_set_retval3(width);
		if (write)
			flags |= (1 << 0);
		if (rep)
			flags |= (1 << 1);
		if (str)
			flags |= (1 << 2);
		syscall_set_retval4(flags);
	} else if (reason == reason_fault) {
		syscall_set_retval2(fault_addr);
	}

	syscall_set_errno(E_SUCC);
}

*)

    Function get_flags (write rep str: Z) :=
      let flags := 0 in
      let flags0 := if zeq write 0 then flags
                    else Z.lor flags 1 in
      let flags1 := if zeq rep 0 then flags0
                    else Z.lor flags0 2 in
      let flags2 := if zeq str 0 then flags1
                    else Z.lor flags1 4 in
      flags2.

    Function trap_get_exitinfo_spec (abd: RData) :=
      match vmx_get_exit_reason_spec abd, vmx_get_exit_io_port_spec abd,
            vmx_get_io_width_spec abd, vmx_get_io_write_spec abd,
            vmx_get_exit_io_rep_spec abd, vmx_get_exit_io_str_spec abd,
            vmx_get_exit_fault_addr_spec abd with
        | Some reason, Some port, Some width, Some write, Some rep, Some str, Some fault_addr =>
          match uctx_set_retval1_spec reason abd with
            | Some abd0 => 
              if zeq reason EXIT_REASON_INOUT then
                match uctx_set_retval2_spec port abd0 with
                  | Some abd1 => 
                    match uctx_set_retval3_spec width abd1 with
                      | Some abd2 => 
                        let flags := get_flags write rep str in
                        match uctx_set_retval4_spec flags abd2 with
                          | Some abd3 => uctx_set_errno_spec E_SUCC abd3
                          | _ => None
                        end
                      | _ => None
                    end
                  | _ => None
                end
              else if zeq reason EXIT_REASON_EPT_FAULT then
                     match uctx_set_retval2_spec fault_addr abd0 with
                       | Some abd1 => uctx_set_errno_spec E_SUCC abd1
                       | _ => None
                     end
                   else
                     uctx_set_errno_spec E_SUCC abd0
            | _ => None
          end
        | _,_,_,_,_,_,_ => None
      end.

(*
void
sys_hvm_handle_rdmsr(void)
{
    uint32_t msr, next_eip;
    uint64_t val;

    msr = vmx_get_reg(GUEST_EAX);

    /*
     * XXX: I/O permission check is not necessary when using HVM.
     */
    val = rdmsr (msr);
    vmx_set_reg(GUEST_EAX, val & 0xffffffff);
    vmx_set_reg(GUEST_EDX, (val >> 32) & 0xffffffff);

    next_eip = vmx_get_next_eip();
    vmx_set_reg(GUEST_EIP, next_eip);
    syscall_set_errno(E_SUCC);
}
*)

    Function trap_handle_rdmsr_spec (abd: RData) :=
      match vmx_get_reg_spec C_GUEST_EAX abd with
      | Some msr =>
        match rdmsr_spec msr abd with
        | Some (VZ64 val) =>
          let val_low := val mod (2 ^ 32) in
          let val_high := val / (2 ^ 32) in
          match vmx_set_reg_spec C_GUEST_EAX val_low abd with
          | Some abd0 => 
            match vmx_set_reg_spec C_GUEST_EDX val_high abd0 with
            | Some abd1 => 
              match vmx_get_next_eip_spec abd1 with
              | Some next_eip =>
                if zle_le 0 next_eip Int.max_unsigned then
                  match vmx_set_reg_spec C_GUEST_EIP next_eip abd1 with
                  | Some abd2 => uctx_set_errno_spec E_SUCC abd2
                  | _ => None
                  end
                else None
              | _ => None
              end
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end.

(*
    void
      sys_hvm_handle_wrmsr(void)
      {
	uint32_t msr, next_eip, eax, edx;
	uint64_t val;

	msr = vmx_get_reg(GUEST_ECX);
	eax = vmx_get_reg(GUEST_EAX);
	edx = vmx_get_reg(GUEST_EDX);
	val = ((uint64_t) edx << 32) | (uint64_t) eax;

	wrmsr(msr, val);
        next_eip = vmx_get_next_eip();
        vmx_set_reg(GUEST_EIP, next_eip);
        syscall_set_errno(E_SUCC);
      }
*)

    Function trap_handle_wrmsr_spec (abd: RData) :=
      match vmx_get_reg_spec C_GUEST_ECX abd, vmx_get_reg_spec C_GUEST_EAX abd,
            vmx_get_reg_spec C_GUEST_EDX abd with
      | Some msr, Some eax, Some edx =>
        let val := edx * 2 ^ 32 + eax in
        match wrmsr_spec msr (VZ64 val) abd with
        | Some _ =>
          match vmx_get_next_eip_spec abd with
          | Some next_eip =>
            if zle_le 0 next_eip Int.max_unsigned then
              match vmx_set_reg_spec C_GUEST_EIP next_eip abd with
              | Some abd0 => uctx_set_errno_spec E_SUCC abd0
              | _ => None
              end
            else None
          | _ => None
          end
        | _ => None
        end
      | _, _, _ => None
      end.
*)

    (*
- PTFaultResv: wrapper of pt_resv: content
  mksignature (Tint::nil) None
     *)
 
  Function ptfault_resv_spec (vadr: Z) (abd: RData) :=
    match ikern abd, ihost abd, pg abd with
      | true, true, true =>
        if zle_lt adr_low vadr adr_high then
          match ptResv_spec (cid abd) vadr PT_PERM_PTU abd with
            | Some (abd0, _)  =>
              Some abd0
            | _ => None
          end
        else Some abd
      | _, _, _ => None
    end.
  
  (*if zle_lt 1073741824 vadr 4026531840 then*)
    
    Require Import ObjShareMem.

    Function trap_offer_shared_mem_spec (abd: RData) :=
      match (uctx_arg2_spec abd, cid abd) with
        | (Some vadr, n) =>
          if zeq n 1 then
            match offer_shared_mem_spec 1 2 vadr abd with
              | Some (abd', res) =>
                match uctx_set_retval1_spec res abd' with
                  | Some abd'' => uctx_set_errno_spec E_SUCC abd''
                  | _ => None
                end
              | _ => None
            end
          else uctx_set_errno_spec E_SUCC abd
        | _ => None
      end.

    Function print_spec (adt: RData) :=
      match uctx_arg2_spec adt with
        | Some content =>
          uctx_set_errno_spec E_SUCC
                              (adt {devout: DeviceOutput_update (devout adt) (cid adt) (cid adt) (OUT content)})
        | _ => None
      end.

    Section Proc_Create.

      Require Import liblayers.compat.CompatLayers.
      Require Import GlobIdent.
      Require Import ASTExtra.
      Require Import liblayers.lib.Decision.

      Context `{Hstencil: Stencil}.
      Context `{Hmem: Mem.MemoryModel}.
      Context `{Hmwd: UseMemWithData mem}.

      (*
- TrapProcCreate: wrapper of proc_create
   mksignature (Tint :: nil) (Some Tint)
  Parameter:  there is a list of ELF files in memory; the parameter indicates which one we’re going to use
       *)

      Function ELF_ident (i: Z) : option ident :=
        match i with
          | 0 => Some proc_start_user
          | _ => None
        end.

      Function trap_proc_create_spec (s: stencil) (m: mem) (abd: RData) :=
        match uctx_arg3_spec abd with
          | Some arg3 =>
            if zle_le 0 arg3 (cquota (ZMap.get (cid abd) (AC abd)) - cusage (ZMap.get (cid abd) (AC abd))) then
              if zle_le 0 (cid abd * max_children + 1 + max_children) num_id then
                if zlt (Z_of_nat (length (cchildren (ZMap.get (cid abd) (AC abd))))) max_children then
                  match uctx_arg2_spec abd with
                    | Some arg1 =>
                      if zle_lt 0 arg1 num_id then
                        match ELF_ident arg1 with
                          | Some fun_id =>
                            match find_symbol s ELF_ENTRY_LOC, find_symbol s proc_start_user,
                                  find_symbol s ELF_LOC, find_symbol s STACK_LOC,
                                  find_symbol s fun_id with
                              | Some bentry, Some buserstart, Some belf, Some bstack, Some busercode  =>
                                match Mem.load Mint32 m bentry (arg1 * 4) with
                                  | Some (Vptr bb bn) =>
                                    if peq bb busercode then
                                      if Int.eq bn Int.zero then
                                        match proc_create_spec abd bstack buserstart busercode Int.zero arg3 with
                                          | Some (abd', n) =>
                                            match uctx_set_retval1_spec n abd' with
                                              | Some abd'' => uctx_set_errno_spec E_SUCC abd''
                                              | _ => None
                                            end
                                          | _ => None
                                        end
                                      else None
                                    else None
                                  | _ => None
                                end
                              | _,_,_,_,_ => None
                            end
                          | _ => None
                        end
                      else None
                    | _ => None
                  end
                else uctx_set_errno_spec E_MEM abd
              else uctx_set_errno_spec E_MEM abd
            else uctx_set_errno_spec E_MEM abd
          | _ => None
        end.

      Inductive Syscall_Num:=
      | NSYS_PUTS
      | NSYS_RING0_SPAWN
      | NSYS_SPAWN
      | NSYS_YIELD
      | NSYS_DISK_OP	
      | NSYS_DISK_CAP
      | NSYS_GET_QUOTA
      | NSYS_RECV
      | NSYS_SHARE
      | NSYS_PRINT
      | NSYS_NR.

      Notation SYS_share := 27.
      Notation SYS_print := 28.

     Definition Syscall_Z2Num (i: Z) :=
          if zeq i SYS_puts then NSYS_PUTS
          else if zeq i SYS_ring0_spawn then NSYS_RING0_SPAWN
          else if zeq i SYS_spawn then NSYS_SPAWN
          else if zeq i SYS_yield then NSYS_YIELD
          else if zeq i SYS_disk_op then NSYS_DISK_OP
          else if zeq i SYS_disk_cap then NSYS_DISK_CAP
          else if zeq i SYS_recv then NSYS_RECV
          else if zeq i SYS_get_quota then NSYS_GET_QUOTA
          else if zeq i SYS_share then NSYS_SHARE
          else if zeq i SYS_print then NSYS_PRINT
          else NSYS_NR.

      Function sys_dispatch_c_spec (s: stencil) (m: mem) (abd: RData) :=
        match uctx_arg1_spec abd with
          | Some arg1 =>
            if zle_le 0 arg1 Int.max_unsigned then
              match Syscall_Z2Num arg1 with
                (*| NSYS_PUTS
              | NSYS_RING0_SPAWN*)
                | NSYS_SPAWN => trap_proc_create_spec s m abd 
                (*| NSYS_YIELD
              | NSYS_DISK_OP	
              | NSYS_DISK_CAP*)
                | NSYS_GET_QUOTA => trap_get_quota_spec abd
                | NSYS_SHARE => trap_offer_shared_mem_spec abd
                | NSYS_PRINT => print_spec abd
                (*| NSYS_RECV => trap_receivechan_spec abd*)
                | _ => uctx_set_errno_spec (E_INVAL_CALLNR) abd
              end
            else None
          | _ => None
        end.

    End Proc_Create.

End OBJ_Trap.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import AuxLemma.
Require Import Observation.

Section OBJ_SIM.

  Context `{Hobs: Observation}.
  Context `{data : CompatData(Obs:=Obs) RData}.
  Context `{data0 : CompatData(Obs:=Obs) RData}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_prf := data) RData).
  Notation LDATAOps := (cdata (cdata_prf := data0) RData).

  Context `{rel_prf: CompatRel _ (Obs:=Obs) (memory_model_ops:= memory_model_ops) _
                               (stencil_ops:= stencil_ops) HDATAOps LDATAOps}.

  Lemma alloc_maintains_cid:
    forall habd habd' id b,
      alloc_spec id habd = Some (habd', b)
      -> cid habd = cid habd'.
  Proof.
    unfold alloc_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma ptInsertPTE0_maintains_cid:
    forall habd habd' nn vadr padr perm,
      ptInsertPTE0_spec nn vadr padr perm habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold ptInsertPTE0_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma ptAllocPDE0_maintains_cid:
    forall habd habd' nn vadr i,
      ptAllocPDE0_spec nn vadr habd = Some (habd', i)
      -> cid habd = cid habd'.
  Proof.
    unfold ptAllocPDE0_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma ptInsert0_maintains_cid:
    forall habd habd' nn vadr padr perm z,
      ptInsert0_spec nn vadr padr perm habd = Some (habd', z)
      -> cid habd = cid habd'.
  Proof.
    intros. functional inversion H; subst; auto.
    - eapply ptInsertPTE0_maintains_cid; eauto.
    - eapply ptAllocPDE0_maintains_cid; eauto.
    - erewrite ptAllocPDE0_maintains_cid; [| eassumption ].
      eapply ptInsertPTE0_maintains_cid; eauto.
  Qed.

  Lemma ptResv_maintains_cid:
    forall habd habd' i n v p,
      ptResv_spec n v p habd = Some (habd', i)
      -> cid habd = cid habd'.
  Proof.
    unfold ptResv_spec. intros.
    subdestruct; [ injection H as _ <-; reflexivity |].
    erewrite alloc_maintains_cid; [| exact Hdestruct ].
    eapply ptInsert0_maintains_cid; eauto.
  Qed.

  Lemma ptResv2_maintains_cid:
    forall habd habd' i n v p n' v' p',
      ptResv2_spec n v p n' v' p' habd = Some (habd', i)
      -> cid habd = cid habd'.
  Proof.
    intros. functional inversion H; subst; auto; clear H.
    - erewrite alloc_maintains_cid; [| eassumption ].
      eapply ptInsert0_maintains_cid; eauto.
    - erewrite alloc_maintains_cid; [| eassumption ].
      erewrite ptInsert0_maintains_cid; [|eassumption].
      eapply ptInsert0_maintains_cid; eauto.
  Qed.

  Lemma offer_shared_mem_maintains_cid:
    forall i1 i2 i3 d d' z,
      offer_shared_mem_spec i1 i2 i3 d = Some (d', z)
      -> cid d = cid d'.
  Proof.
    intros. functional inversion H; subst; auto; simpl; clear H.
    - eapply ptResv2_maintains_cid; eauto.
    - eapply ptResv2_maintains_cid; eauto.
  Qed.

  Lemma thread_wakeup_maintains_cid:
    forall habd habd' a,
      ObjThread.thread_wakeup_spec a habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold ObjThread.thread_wakeup_spec. intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma syncreceive_chan_maintains_cid:
    forall habd habd' a b c r,
      syncreceive_chan_spec a b c habd = Some (habd', r)
      -> cid habd = cid habd'.
  Proof.
    unfold syncreceive_chan_spec, flatmem_copy_spec. 
    intros. 
    subdestruct; inv H; trivial.
    eapply thread_wakeup_maintains_cid in Hdestruct17; eauto.
  Qed.

  Lemma syncsendto_chan_post_maintains_cid:
    forall habd habd' r,
      syncsendto_chan_post_spec habd = Some (habd', r)
      -> cid habd = cid habd'.
  Proof.
    unfold syncsendto_chan_post_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma proc_create_maintains_cid:
    forall habd habd' b b' buc ofs_uc q i,
      proc_create_spec habd b b' buc ofs_uc q = Some (habd', i)
      -> cid habd = cid habd'.
  Proof.
    unfold proc_create_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  (*Lemma vmx_set_intercept_intwin_maintains_cid:
    forall habd habd' enable,
      vmx_set_intercept_intwin_spec enable habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold vmx_set_intercept_intwin_spec.
    intros.
    subdestruct; injection H as <-; reflexivity.
  Qed.

  Lemma vmx_set_mmap_maintains_cid:
    forall habd habd' gpa hpa mem_type i,
      vmx_set_mmap_spec gpa hpa mem_type habd = Some (habd', i)
      -> cid habd = cid habd'.
  Proof.
    unfold vmx_set_mmap_spec.
    unfold ObjEPT.ept_add_mapping_spec, ObjEPT.ept_invalidate_mappings_spec.
    intros.
    subdestruct; injection H as _ <-; reflexivity.
  Qed.

  Lemma vmx_set_reg_maintains_cid:
    forall habd habd' reg v,
      vmx_set_reg_spec reg v habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold vmx_set_reg_spec.
    intros.
    subdestruct; injection H as <-; reflexivity.
  Qed.

  Lemma vmx_set_desc_maintains_cid:
    forall habd habd' seg sel base lim ar,
      vmx_set_desc_spec seg sel base lim ar habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold vmx_set_desc_spec.
    intros.
    subdestruct; injection H as <-; reflexivity.
  Qed.

  Lemma vmx_inject_event_maintains_cid:
    forall habd habd' type vector errcode ev,
      vmx_inject_event_spec type vector errcode ev habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    Local Opaque Z.land Z.lor.

    unfold vmx_inject_event_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma vmx_set_tsc_offset_maintains_cid:
    forall habd habd' ofs,
      vmx_set_tsc_offset_spec ofs habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold vmx_set_tsc_offset_spec.
    intros.
    subdestruct; injection H as <-; reflexivity.
  Qed.*)

  Lemma uctx_set_retval1_maintains_cid:
    forall habd habd' n,
      uctx_set_retval1_spec n habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold uctx_set_retval1_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma uctx_set_retval2_maintains_cid:
    forall habd habd' n,
      uctx_set_retval2_spec n habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold uctx_set_retval2_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma uctx_set_retval3_maintains_cid:
    forall habd habd' n,
      uctx_set_retval3_spec n habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold uctx_set_retval3_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma uctx_set_retval4_maintains_cid:
    forall habd habd' n,
      uctx_set_retval4_spec n habd = Some habd'
      -> cid habd = cid habd'.
  Proof.
    unfold uctx_set_retval4_spec; intros.
    subdestruct; inv H; reflexivity.
  Qed.

  Lemma uctx_arg1_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd z labd f,
      uctx_arg1_spec habd = Some z ->
      0 <= cid habd < num_proc ->
      relate_AbData s f habd labd ->
      uctx_arg1_spec labd = Some z.
  Proof. apply uctx_argn_exist; split; [ discriminate | reflexivity ]. Qed.

  Lemma uctx_arg2_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd z labd f,
      uctx_arg2_spec habd = Some z ->
      0 <= cid habd < num_proc ->
      relate_AbData s f habd labd ->
      uctx_arg2_spec labd = Some z.
  Proof. apply uctx_argn_exist; split; [ discriminate | reflexivity ]. Qed.

  Lemma uctx_arg3_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd z labd f,
      uctx_arg3_spec habd = Some z ->
      0 <= cid habd < num_proc ->
      relate_AbData s f habd labd ->
      uctx_arg3_spec labd = Some z.
  Proof. apply uctx_argn_exist; split; [ discriminate | reflexivity ]. Qed.

  Lemma uctx_arg4_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd z labd f,
      uctx_arg4_spec habd = Some z ->
      0 <= cid habd < num_proc ->
      relate_AbData s f habd labd ->
      uctx_arg4_spec labd = Some z.
  Proof. apply uctx_argn_exist; split; [ discriminate | reflexivity ]. Qed.

  Lemma uctx_arg5_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd z labd f,
      uctx_arg5_spec habd = Some z ->
      0 <= cid habd < num_proc ->
      relate_AbData s f habd labd ->
      uctx_arg5_spec labd = Some z.
  Proof. apply uctx_argn_exist; split; [ discriminate | reflexivity ]. Qed.

  Lemma uctx_arg6_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd z labd f,
      uctx_arg6_spec habd = Some z ->
      0 <= cid habd < num_proc ->
      relate_AbData s f habd labd ->
      uctx_arg6_spec labd = Some z.
  Proof. apply uctx_argn_exist; split; [ discriminate | reflexivity ]. Qed.

  Lemma uctx_set_retval1_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd habd' labd n f,
      uctx_set_retval1_spec n habd = Some habd'
      -> relate_AbData s f habd labd
      -> 0 <= cid habd < num_proc
      -> exists labd', uctx_set_retval1_spec n labd = Some labd'
                       /\ relate_AbData s f habd' labd'.
  Proof uctx_set_regk_exist U_EBX.

  Lemma uctx_set_retval2_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd habd' labd n f,
      uctx_set_retval2_spec n habd = Some habd'
      -> relate_AbData s f habd labd
      -> 0 <= cid habd < num_proc
      -> exists labd', uctx_set_retval2_spec n labd = Some labd'
                       /\ relate_AbData s f habd' labd'.
  Proof uctx_set_regk_exist U_ECX.

  Lemma uctx_set_retval3_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd habd' labd n f,
      uctx_set_retval3_spec n habd = Some habd'
      -> relate_AbData s f habd labd
      -> 0 <= cid habd < num_proc
      -> exists labd', uctx_set_retval3_spec n labd = Some labd'
                       /\ relate_AbData s f habd' labd'.
  Proof uctx_set_regk_exist U_EDX.

  Lemma uctx_set_retval4_exist {re1: relate_impl_iflags}
      {re2: relate_impl_cid} {re3: relate_impl_uctxt}:
    forall s habd habd' labd n f,
      uctx_set_retval4_spec n habd = Some habd'
      -> relate_AbData s f habd labd
      -> 0 <= cid habd < num_proc
      -> exists labd', uctx_set_retval4_spec n labd = Some labd'
                       /\ relate_AbData s f habd' labd'.
  Proof uctx_set_regk_exist U_ESI.

    (*Section TRAP_ISCHANREADY_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_syncchpool}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_uctxt}.

    Lemma trap_ischanready_exist:
      forall s habd habd' labd f,
        trap_ischanready_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_ischanready_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_ischanready_spec in *. intros.
      subdestruct.

      erewrite is_chan_ready_exist; eauto.
      exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eauto.
    Qed.

  End TRAP_ISCHANREADY_SIM.*)

  Section TRAP_SENDTOCHAN_PRE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_syncchpool}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_uctxt}.
    Context {re6: relate_impl_ptpool}.
    Context {re7: relate_impl_PT}.
    Context {re8: relate_impl_init}.
    Context {re9: relate_impl_abq}.
    Context {re10: relate_impl_abtcb}.

    Lemma trap_sendtochan_pre_exist:
      forall s habd habd' labd r f,
        trap_sendtochan_pre_spec habd = Some (habd', r)
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_sendtochan_pre_spec labd = Some (labd', r)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_sendtochan_pre_spec in *. intros.
      subdestruct.

      erewrite uctx_arg2_exist; eauto.
      erewrite uctx_arg3_exist; eauto.
      erewrite uctx_arg4_exist; eauto.
      exploit syncsendto_chan_pre_exist; eauto. 
    Qed.

  End TRAP_SENDTOCHAN_PRE_SIM.

  Section TRAP_SENDTOCHAN_POST_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_syncchpool}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_uctxt}.
    Context {re6: relate_impl_ptpool}.
    Context {re7: relate_impl_PT}.
    Context {re8: relate_impl_init}.
    Context {re9: relate_impl_abq}.
    Context {re10: relate_impl_abtcb}.

    Lemma trap_sendtochan_post_exist:
      forall s habd habd' labd f,
        trap_sendtochan_post_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_sendtochan_post_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_sendtochan_post_spec in *. intros.
      subdestruct.
      exploit syncsendto_chan_post_exist; eauto. 
      intros (labd' & HP & HR).
      rewrite HP.
      erewrite syncsendto_chan_post_maintains_cid in H1; eauto.
      exploit uctx_set_retval1_exist; eauto. intros (labd'' & HP' & HR').
      rewrite HP'.
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_SENDTOCHAN_POST_SIM.

  Section TRAP_RECEIVECHAN_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_syncchpool}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_uctxt}.
    Context {re6: relate_impl_abq}.
    Context {re7: relate_impl_abtcb}.
    Context {re8: relate_impl_pperm}.
    Context {re9: relate_impl_HP}.
    Context {re10: relate_impl_init}.
    Context {re11: relate_impl_ptpool}.
    Context {re12: relate_impl_PT}.
    Context {re13: relate_impl_nps}.

    Lemma trap_receivechan_exist:
      forall s habd habd' labd f,
        trap_receivechan_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_receivechan_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_receivechan_spec in *. intros.
      subdestruct.

      erewrite uctx_arg2_exist; eauto.
      erewrite uctx_arg3_exist; eauto.
      erewrite uctx_arg4_exist; eauto.
      exploit syncreceive_chan_exist; eauto. intros (labd' & HP & HR).
      rewrite HP.
      erewrite syncreceive_chan_maintains_cid in H1; eauto.
      exploit uctx_set_retval1_exist; eauto. intros (labd'' & HP' & HR').
      rewrite HP'.
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_RECEIVECHAN_SIM.

  Section TRAP_GET_QUOTA_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_AC}.
    Context {re4: relate_impl_uctxt}.

    Lemma trap_get_quota_exist:
      forall s habd habd' labd f,
        trap_get_quota_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_get_quota_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_get_quota_spec in *. intros.
      subdestruct.

      erewrite get_curid_exist; eauto.
      erewrite container_get_quota_exist; eauto.
      erewrite container_get_usage_exist; eauto.
      exploit uctx_set_retval1_exist; eauto. intros (labd'' & -> & HR').
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_GET_QUOTA_SIM.

  Section DEVOUT_SIM.

    Context {re1: relate_impl_devout}.
    Context {re2: relate_impl_cid}.
    Context {re4: relate_impl_iflags}.
    Context {re5: relate_impl_uctxt}.

    Lemma print_exist:
      forall s habd habd' labd f,
        print_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', print_spec labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold print_spec; intros.
      subdestruct.

      erewrite uctx_arg2_exist; eauto.
      exploit relate_impl_devout_eq; eauto. intros.
      exploit relate_impl_cid_eq; eauto. intros.
      revert H; subrewrite.
      eapply uctx_set_regk_exist; eauto.
      eapply relate_impl_devout_update. assumption.
    Qed.

    (*Context {mt2: match_impl_devout}.

    Lemma print_match:
      forall content s d  d' m f,
        print_spec content d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold print_spec; intros. subdestruct.
      inv H. eapply match_impl_devout_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) print_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) print_spec}.

    Lemma print_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem print_spec)
            (id ↦ gensem print_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit print_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply print_match; eauto.
    Qed.*)

  End DEVOUT_SIM.
 
  Section TRAP_OFFER_SHARED_MEM_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_HP}.
    Context {re9: relate_impl_smspool}.
    Context {re10: relate_impl_AC}.
    Context {re11: relate_impl_cid}.
    Context {re12: relate_impl_uctxt}.

    Lemma trap_offer_shared_mem_exist:
      forall s habd habd' labd f,
        trap_offer_shared_mem_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_offer_shared_mem_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_offer_shared_mem_spec in *. intros.
      exploit relate_impl_cid_eq; eauto. intros.
      subdestruct.
      - erewrite uctx_arg2_exist; eauto.
        rewrite <- H2. rewrite e. simpl.
        exploit offer_shared_mem_exists; eauto.
        intros (labd' & -> & Hr). 
        assert (Hrange: 0 <= cid r < num_proc) by
            (erewrite <- offer_shared_mem_maintains_cid; eauto).
        exploit uctx_set_retval1_exist; eauto. 
        intros (labd'' & -> & HR').
        eapply uctx_set_regk_exist; eauto.
        erewrite <- uctx_set_retval1_maintains_cid; eauto.
      - erewrite uctx_arg2_exist; eauto.
        rewrite <- H2. rewrite zeq_false; trivial. 
        eapply uctx_set_regk_exist; eauto.
    Qed.

  End TRAP_OFFER_SHARED_MEM_SIM.

  (*Section TRAP_INTERCEPT_INT_WINDOW_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.

    Lemma trap_intercept_int_window_exist:
      forall s habd habd' labd f,
        trap_intercept_int_window_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_intercept_int_window_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_intercept_int_window_spec in *. intros.
      subdestruct.

      erewrite uctx_arg2_exist; eauto.
      exploit vmx_set_intercept_intwin_exist; eauto. intros (? & -> & ?).
      erewrite vmx_set_intercept_intwin_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_INTERCEPT_INT_WINDOW_SIM.

  Section TRAP_CHECK_PENDING_EVENT_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.

    Lemma trap_check_pending_event_exist:
      forall s habd habd' labd f,
        trap_check_pending_event_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_check_pending_event_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_check_pending_event_spec in *. intros.
      subdestruct.

      erewrite vmx_check_pending_event_exists; eauto.
      exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_CHECK_PENDING_EVENT_SIM.

  Section TRAP_CHECK_INT_SHADOW_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.

    Lemma trap_check_int_shadow_exist:
      forall s habd habd' labd f,
        trap_check_int_shadow_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_check_int_shadow_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_check_int_shadow_spec in *. intros.
      subdestruct.

      erewrite vmx_check_int_shadow_exists; eauto.
      exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_CHECK_INT_SHADOW_SIM.

  Section TRAP_INJECT_EVENT_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.

    Lemma trap_inject_event_exist:
      forall s habd habd' labd f,
        trap_inject_event_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_inject_event_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_inject_event_spec in *. intros.
      destruct (uctx_arg2_spec habd) eqn:Hdestruct; contra_inv;
      destruct (uctx_arg3_spec habd) eqn:Hdestruct0; contra_inv;
      destruct (uctx_arg4_spec habd) eqn:Hdestruct1; contra_inv;
      destruct (uctx_arg5_spec habd) eqn:Hdestruct2; contra_inv.

      erewrite uctx_arg2_exist; eauto.
      erewrite uctx_arg3_exist; eauto.
      erewrite uctx_arg4_exist; eauto.
      erewrite uctx_arg5_exist; eauto.
      subdestruct.

      - exploit vmx_inject_event_exist; eauto. intros (? & -> & ?).
        erewrite vmx_inject_event_maintains_cid in H1; eauto.
        eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_INJECT_EVENT_SIM.

  Section TRAP_GET_NEXT_EIP_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmx}.
    Context {re5: relate_impl_vmcs}.

    Lemma trap_get_next_eip_exist:
      forall s habd habd' labd f,
        trap_get_next_eip_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_get_next_eip_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_get_next_eip_spec in *. intros.
      subdestruct.
      erewrite vmx_get_next_eip_exist; eauto.
      rewrite Hdestruct0.
      exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_GET_NEXT_EIP_SIM.

  Section TRAP_SET_REG_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmx}.
    Context {re5: relate_impl_vmcs}.

    Lemma trap_set_reg_exist:
      forall s habd habd' labd f,
        trap_set_reg_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_set_reg_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_set_reg_spec in *. intros.

      destruct (uctx_arg2_spec habd) eqn:Hdestruct; contra_inv;
      destruct (uctx_arg3_spec habd) eqn:Hdestruct0; contra_inv.

      erewrite uctx_arg2_exist; eauto.
      erewrite uctx_arg3_exist; eauto.
      subdestruct.

      - exploit vmx_set_reg_exist; eauto. intros (? & -> & ?).
        erewrite vmx_set_reg_maintains_cid in H1; eauto.
        eapply uctx_set_regk_exist; eassumption.

      - eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_SET_REG_SIM.

  Section TRAP_GET_REG_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmx}.
    Context {re5: relate_impl_vmcs}.

    Lemma trap_get_reg_exist:
      forall s habd habd' labd f,
        trap_get_reg_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_get_reg_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_get_reg_spec in *. intros.

      destruct (uctx_arg2_spec habd) eqn:Hdestruct; contra_inv.

      erewrite uctx_arg2_exist; eauto.
      subdestruct.

      - erewrite vmx_get_reg_exist; eauto.
        exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval1_maintains_cid in H1; eauto.
        eapply uctx_set_regk_exist; eassumption.

      - eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_GET_REG_SIM.

  Section TRAP_SET_SEG_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.

    Lemma trap_set_seg_exist:
      forall s habd habd' labd f,
        trap_set_seg_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_set_seg_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_set_seg_spec in *. intros.

      destruct (uctx_arg2_spec habd) eqn:Hdestruct; contra_inv;
      destruct (uctx_arg3_spec habd) eqn:Hdestruct0; contra_inv;
      destruct (uctx_arg4_spec habd) eqn:Hdestruct1; contra_inv;
      destruct (uctx_arg5_spec habd) eqn:Hdestruct2; contra_inv;
      destruct (uctx_arg6_spec habd) eqn:Hdestruct3; contra_inv.

      erewrite uctx_arg2_exist; eauto.
      erewrite uctx_arg3_exist; eauto.
      erewrite uctx_arg4_exist; eauto.
      erewrite uctx_arg5_exist; eauto.
      erewrite uctx_arg6_exist; eauto.
      subdestruct.

      - exploit vmx_set_desc_exist; eauto. intros (? & -> & ?).
        erewrite vmx_set_desc_maintains_cid in H1; eauto.
        eapply uctx_set_regk_exist; eassumption.

      - eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_SET_SEG_SIM.

  Section TRAP_GET_TSC_OFFSET_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.

    Lemma trap_get_tsc_offset_exist:
      forall s habd habd' labd f,
        trap_get_tsc_offset_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_get_tsc_offset_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.land Z.shiftr.

      unfold trap_get_tsc_offset_spec in *. intros.
      subdestruct.

      erewrite vmx_get_tsc_offset_exists; eauto. simpl.
      exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
      erewrite uctx_set_retval1_maintains_cid in H1; eauto.
      exploit uctx_set_retval2_exist; eauto. intros (? & -> & ?).
      erewrite uctx_set_retval2_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_GET_TSC_OFFSET_SIM.

  Section TRAP_SET_TSC_OFFSET_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.

    Lemma trap_set_tsc_offset_exist:
      forall s habd habd' labd f,
        trap_set_tsc_offset_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_set_tsc_offset_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.lor Z.shiftl.

      unfold trap_set_tsc_offset_spec in *. intros.
      subdestruct.

      erewrite uctx_arg2_exist; eauto.
      erewrite uctx_arg3_exist; eauto.
      exploit vmx_set_tsc_offset_exist; eauto. intros (? & -> & ?).
      erewrite vmx_set_tsc_offset_maintains_cid in H1; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_SET_TSC_OFFSET_SIM.

  Section TRAP_GET_EXITINFO_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmcs}.
    Context {re5: relate_impl_vmx}.

    Lemma trap_get_exitinfo_exist:
      forall s habd habd' labd f,
        trap_get_exitinfo_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_get_exitinfo_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_get_exitinfo_spec in *. intros.
      repeat (
        match goal with
        | HT:context [match ?con with | _ => _ end] |- _ =>
          let H := fresh "Hdestruct" in
          destruct con eqn:H; contra_inv;
          first [ erewrite vmx_get_exit_reason_exists
                | erewrite vmx_get_exit_io_port_exist
                | erewrite vmx_get_io_width_exist
                | erewrite vmx_get_io_write_exist
                | erewrite vmx_get_exit_io_rep_exist
                | erewrite vmx_get_exit_io_str_exist
                | erewrite vmx_get_exit_fault_addr_exists ];
          eauto; simpl in HT |- *
        end).
      subdestruct.

      - exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval1_maintains_cid in H1; eauto.
        exploit uctx_set_retval2_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval2_maintains_cid in H1; eauto.
        exploit uctx_set_retval3_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval3_maintains_cid in H1; eauto.
        exploit uctx_set_retval4_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval4_maintains_cid in H1; eauto.
        eapply uctx_set_regk_exist; eassumption.

      - exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval1_maintains_cid in H1; eauto.
        exploit uctx_set_retval2_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval2_maintains_cid in H1; eauto.
        eapply uctx_set_regk_exist; eassumption.

      - exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
        erewrite uctx_set_retval1_maintains_cid in H1; eauto.
        eapply uctx_set_regk_exist; eassumption.

    Qed.

  End TRAP_GET_EXITINFO_SIM.

  Section TRAP_HANDLE_RDMSR_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmx}.
    Context {re5: relate_impl_vmcs}.

    Lemma trap_handle_rdmsr_exist:
      forall s habd habd' labd f,
        trap_handle_rdmsr_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_handle_rdmsr_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.land Z.shiftr.

      unfold trap_handle_rdmsr_spec, rdmsr_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      revert H. subrewrite. subdestruct.

      erewrite vmx_get_reg_exist; eauto.
      erewrite vmx_set_reg_maintains_cid in H1; eauto.
      exploit vmx_set_reg_exist; try exact Hdestruct2; eauto. intros (? & -> & ?).
      erewrite vmx_set_reg_maintains_cid in H1; eauto.
      exploit vmx_set_reg_exist; try exact Hdestruct3; eauto. intros (? & -> & ?).
      erewrite vmx_get_next_eip_exist; eauto.
      erewrite vmx_set_reg_maintains_cid in H1; eauto.
      rewrite Hdestruct5.
      exploit vmx_set_reg_exist; try exact Hdestruct5; eauto. intros (? & -> & ?).

      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_HANDLE_RDMSR_SIM.

  Section TRAP_HANDLE_WRMSR_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_vmx}.
    Context {re5: relate_impl_vmcs}.

    Lemma trap_handle_wrmsr_exist:
      forall s habd habd' labd f,
        trap_handle_wrmsr_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_handle_wrmsr_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.lor Z.shiftl.

      unfold trap_handle_wrmsr_spec, wrmsr_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      revert H. subrewrite. subdestruct.

      erewrite vmx_get_reg_exist; eauto.
      erewrite vmx_get_reg_exist; eauto.
      erewrite vmx_get_reg_exist; eauto.
      erewrite vmx_get_next_eip_exist; eauto.
      erewrite vmx_set_reg_maintains_cid in H1; eauto.
      exploit vmx_set_reg_exist; eauto. intros (? & -> & ?).
      rewrite Hdestruct5.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_HANDLE_WRMSR_SIM.

  Section TRAP_MMAP_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_syncchpool}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_uctxt}.
    Context {re6: relate_impl_ptpool}.
    Context {re7: relate_impl_init}.
    Context {re8: relate_impl_LAT}.
    Context {re9: relate_impl_nps}.
    Context {re10: relate_impl_pperm}.
    Context {re11: relate_impl_HP}.
    Context {re12: relate_impl_ept}.
    Context {re13: relate_impl_AC}.

    Lemma trap_mmap_exist:
      forall s habd habd' labd f,
        trap_mmap_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_mmap_spec labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.land Z.modulo Z.add Z.sub.

      unfold trap_mmap_spec in *. intros.
      exploit relate_impl_cid_eq; eauto. intros.

      destruct (uctx_arg2_spec habd) eqn:Hdestruct; contra_inv;
      destruct (uctx_arg3_spec habd) eqn:Hdestruct0; contra_inv;
      destruct (uctx_arg4_spec habd) eqn:Hdestruct1; contra_inv.

      erewrite uctx_arg2_exist; eauto.
      erewrite uctx_arg3_exist; eauto.
      erewrite uctx_arg4_exist; eauto.
      revert H. subrewrite. clear Hdestruct Hdestruct0 Hdestruct1. subdestruct.

      - erewrite ptRead_exist; try exact Hdestruct0; eauto.
        exploit ptResv_exist; eauto. intros (? & -> & ?).
        erewrite ptResv_maintains_cid in H1; eauto.
        erewrite ptRead_exist; try exists Hdestruct4; eauto.
        exploit vmx_set_mmap_exist; eauto. intros (? & -> & ?).
        erewrite vmx_set_mmap_maintains_cid in H1; eauto.
        subrewrite'.

        eapply uctx_set_regk_exist; eassumption.

      - erewrite ptRead_exist; try exact Hdestruct0; eauto.
        exploit vmx_set_mmap_exist; try eauto. intros (? & -> & ?).
        erewrite vmx_set_mmap_maintains_cid in H1; eauto.
        subrewrite'.
        eapply uctx_set_regk_exist; eassumption.

      - eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_MMAP_SIM.*)

  Section PTFAULT_RESV_SPEC_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_HP}.
    Context {re9: relate_impl_cid}.
    Context {re10: relate_impl_uctxt}.
    Context {re11: relate_impl_AC}.

    Lemma ptfault_resv_exist:
      forall s habd habd' labd n f,
        ptfault_resv_spec n habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', ptfault_resv_spec n labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptfault_resv_spec; intros.
      exploit relate_impl_iflags_eq; eauto.  inversion 1.
      exploit relate_impl_cid_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      - exploit ptResv_exist; eauto. intros [ labd' [ -> rel' ] ].
        inv HQ; refine_split'; trivial.
      - inv HQ; refine_split'; trivial.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_ptpool}.
    Context {mt4: match_impl_HP}.
    Context {mt5: match_impl_uctxt}.
    Context {mt6: match_impl_AC}.

    Lemma ptfault_resv_match:
      forall s d d' m n f,
        ptfault_resv_spec n d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptfault_resv_spec; intros. subdestruct; inv H; trivial.
      eapply ptResv_match; eauto.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ptfault_resv_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptfault_resv_spec}.

    Lemma ptfault_resv_sim:
      forall id,
        (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                    0 <= cid d1 < num_proc) ->
        sim (crel RData RData) (id ↦ gensem ptfault_resv_spec)
            (id ↦ gensem ptfault_resv_spec).
    Proof.
      intros ? valid_cid. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ptfault_resv_exist; eauto; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ptfault_resv_match; eauto.
    Qed.

  End PTFAULT_RESV_SPEC_SIM.

  Section TRAP_PROC_CREATE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_kctxt}.
    Context {re4: relate_impl_abtcb}.
    Context {re5: relate_impl_abq}.
    Context {re6: relate_impl_uctxt}.
    Context {re7: relate_impl_cid}.
    Context {re8: relate_impl_AC}.

    Lemma trap_proc_create_exist:
      forall s hm lm habd habd' labd f,
        trap_proc_create_spec s hm habd = Some habd'
        -> relate_AbData s f habd labd
        -> Mem.inject f hm lm
        -> inject_incr (Mem.flat_inj (genv_next s)) f
        -> 0 <= cid habd < num_proc
        -> exists labd', trap_proc_create_spec s lm labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold trap_proc_create_spec, ELF_ident. intros.
      exploit relate_impl_AC_eq; eauto; intro HAC.
      exploit relate_impl_cid_eq; eauto; intro Hcid.
      rewrite <- HAC; rewrite <- Hcid.
      destruct (uctx_arg3_spec habd) eqn:Harg3; try discriminate H.
      erewrite uctx_arg3_exist; eauto.
(*
      destruct (zle_le 0 z
                       (cquota (ZMap.get (cid habd) (AC habd)) -
                        cusage (ZMap.get (cid habd) (AC habd)))) eqn:Hquota;*)
      subdestruct; try solve [eapply uctx_set_regk_exist; eassumption].

      assert (f b0 = Some (b0, 0)).
      { apply H2.
        unfold Mem.flat_inj.
        apply genv_symb_range in Hdestruct6.
        destruct (plt b0 (genv_next s)); [ reflexivity | contradiction ].
      }
      assert (f b3 = Some (b3, 0)).
      { apply H2.
        unfold Mem.flat_inj.
        rewrite <- e in Hdestruct7.
        apply genv_symb_range in Hdestruct7.
        destruct (plt b3 (genv_next s)); [ reflexivity | contradiction ].
      }

      erewrite uctx_arg2_exist; eauto.
      simpl; subrewrite'.

      (* Mem.inject f hm lm -> Mem.load ... hm ... = Some ...
                              -> Mem.load ... lm ... = Some ... *)
      exploit Mem.load_inject; eauto.
      simpl. intros (? & -> & ?).
      inv H6. rewrite H5 in H9; injection H9 as <- <-.
                                                   
      rewrite Hdestruct11, Int.add_zero, Hdestruct12.

      exploit proc_create_exist; eauto. intros (? & -> & ?).
      erewrite proc_create_maintains_cid in H3; eauto.
      exploit uctx_set_retval1_exist; eauto. intros (? & -> & ?).
      erewrite uctx_set_retval1_maintains_cid in H3; eauto.
      eapply uctx_set_regk_exist; eassumption.
    Qed.

  End TRAP_PROC_CREATE_SIM.

  Section SYS_DISPATCH_C_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_init}.
    Context {re6: relate_impl_PT}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_idpde}.
    Context {re9: relate_impl_smspool}.
    Context {re10: relate_impl_abtcb}.
    Context {re11: relate_impl_abq}.
    Context {re12: relate_impl_cid}.
    Context {re13: relate_impl_syncchpool}.
    Context {re14: relate_impl_vmxinfo}.
    Context {re15: relate_impl_pperm}.
    Context {re16: relate_impl_HP}.
    Context {re17: relate_impl_ept}.
    Context {re18: relate_impl_kctxt}.
    Context {re19: relate_impl_uctxt}.
    (*Context {re20: relate_impl_vmcs}.
    Context {re21: relate_impl_vmx}.*)
    Context {re22: relate_impl_AC}.
    Context {re23: relate_impl_devout}.

    Lemma sys_dispatch_c_exist:
      forall s hm lm habd habd' labd f,
        sys_dispatch_c_spec s hm habd = Some habd'
        -> relate_AbData s f habd labd
        -> Mem.inject f hm lm
        -> inject_incr (Mem.flat_inj (genv_next s)) f
        -> 0 <= cid habd < num_proc
        -> exists labd', sys_dispatch_c_spec s lm labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold sys_dispatch_c_spec. intros.
      destruct (uctx_arg1_spec habd) eqn:Hdestruct; try discriminate.
      erewrite uctx_arg1_exist; eauto.
      case_eq (zle_le 0 z Int.max_unsigned); intros; rewrite H4 in H; try discriminate H.
      destruct (Syscall_Z2Num z) eqn:Hdestruct0;
        try eapply uctx_set_regk_exist; eauto.

      eapply trap_proc_create_exist; eauto.
      (*eapply trap_get_tsc_offset_exist; eauto.
      eapply trap_set_tsc_offset_exist; eauto.
      eapply trap_get_exitinfo_exist; eauto.
      eapply trap_mmap_exist; eauto.
      eapply trap_set_reg_exist; eauto.
      eapply trap_get_reg_exist; eauto.
      eapply trap_set_seg_exist; eauto.
      eapply trap_get_next_eip_exist; eauto.
      eapply trap_inject_event_exist; eauto.
      eapply trap_check_pending_event_exist; eauto.
      eapply trap_check_int_shadow_exist; eauto.
      eapply trap_intercept_int_window_exist; eauto.
      eapply trap_handle_rdmsr_exist; eauto.
      eapply trap_handle_wrmsr_exist; eauto.*)
      eapply trap_get_quota_exist; eauto.
      (*eapply trap_ischanready_exist; eauto.
      eapply trap_sendtochan_exist; eauto.
      eapply trap_receivechan_exist; eauto.*)
      eapply trap_offer_shared_mem_exist; eauto.
      eapply print_exist; eauto.
    Qed.

  End SYS_DISPATCH_C_SIM.

End OBJ_SIM.
