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
Require Import CalRealIntelModule.
Require Import liblayers.compat.CompatGenSem.
Require Import ObjEPT.

Section OBJ_VMX.

  Context `{real_params: RealParams}.

  Function vmx_readz_spec (i: Z) (adt: RData): option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_lt 0 i VMX_Size' then
          match ZMap.get i (vmx adt) with
            | Vint v => Some (Int.unsigned v)
            | _ => None
          end
        else None
      | _ => None
    end.    

  Function vmx_writez_spec (i value: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_lt 0 i VMX_Size' then
          Some adt {vmx: ZMap.set i (Vint (Int.repr value)) (vmx adt)}
        else None
      | _ => None
    end.

  (*Function vmx_readz64_spec (i: Z) (adt: RData): option Z64 :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_lt 0 i VMX_Size' then
          match ZMap.get i (vmx adt), ZMap.get (i + 1) (vmx adt)  with
            | Vint v1, Vint v2 => 
              Some (VZ64 (Int.unsigned v1 + Z.shiftl (Int.unsigned v2) 32))
            | _, _ => None
          end
        else None
      | _ => None
    end.    

  Function vmx_writez64_spec (i : Z) (value: Z64) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_lt 0 i VMX_Size' then
          let d := ZMap.set i (Vint (Int.repr (Z642Z value))) (vmx adt) in
          let d1 := ZMap.set (i + 1) (Vint (Int.repr (Z.shiftr (Z642Z value) 32))) d in
          Some adt {vmx: d1}
        else None
      | _ => None
    end.
  
  (* Asm Prim *)
  Function vmx_read_spec (i: Z) (adt: RData): (option val) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_le 0 i VMX_Size' then
          Some (ZMap.get i (vmx adt))
        else None
      | _ => None
    end.    

  (* Asm Prim *)
  Function vmx_write_spec (i: Z) (value: val) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_le 0 i VMX_Size' then
          Some adt {vmx: ZMap.set i value (vmx adt)}
        else None
      | _ => None
    end.    *)

(*
unsigned int
vmx_get_reg(unsigned int reg)
{
    unsigned int val;

	switch (reg) {
	case GUEST_EAX:
		val = (uint32_t) vmx.g_rax;
		break;
	case GUEST_EBX:
		val = (uint32_t) vmx.g_rbx;
		break;
	case GUEST_ECX:
		val = (uint32_t) vmx.g_rcx;
		break;
	case GUEST_EDX:
		val = (uint32_t) vmx.g_rdx;
		break;
	case GUEST_ESI:
		val = (uint32_t) vmx.g_rsi;
		break;
	case GUEST_EDI:
		val = (uint32_t) vmx.g_rdi;
		break;
	case GUEST_EBP:
		val = (uint32_t) vmx.g_rbp;
		break;
	case GUEST_ESP:
		val = vmcs_read32(VMCS_GUEST_RSP);
		break;
	case GUEST_EIP:
		val = (uint32_t) vmx.g_rip;
		break;
	case GUEST_EFLAGS:
		val = vmcs_read32(VMCS_GUEST_RFLAGS);
		break;
	case GUEST_CR0:
		val = vmcs_read32(VMCS_GUEST_CR0);
		break;
	case GUEST_CR2:
		val = (uint32_t) vmx.g_cr2;
		break;
	case GUEST_CR3:
		val = vmcs_read32(VMCS_GUEST_CR3);
		break;
	case GUEST_CR4:
		val = vmcs_read32(VMCS_GUEST_CR4);
		break;
	default:
        break;
	}

	return val;
}
*)


  Inductive reg_type:=
    | TVMCS (z: Z)
    | TVMX (z: Z).

  Function Z2reg_type (reg: Z) :=
    match reg with
      | C_GUEST_EAX => Some (TVMX VMX_G_RAX')
      | C_GUEST_EBX => Some (TVMX VMX_G_RBX')
      | C_GUEST_ECX => Some (TVMX VMX_G_RCX')
      | C_GUEST_EDX => Some (TVMX VMX_G_RDX')
      | C_GUEST_ESI => Some (TVMX VMX_G_RSI')
      | C_GUEST_EDI => Some (TVMX VMX_G_RDI')
      | C_GUEST_CR2 => Some (TVMX VMX_G_CR2')
      | C_GUEST_EBP => Some (TVMX VMX_G_RBP')
      | C_GUEST_EIP => Some (TVMX VMX_G_RIP')
      (* get from vmcs *)
      | C_GUEST_ESP => Some (TVMCS C_VMCS_GUEST_RSP)
      | C_GUEST_EFLAGS => Some (TVMCS C_VMCS_GUEST_RFLAGS)
      | C_GUEST_CR0 => Some (TVMCS C_VMCS_GUEST_CR0)
      | C_GUEST_CR3 => Some (TVMCS C_VMCS_GUEST_CR3)
      | C_GUEST_CR4 => Some (TVMCS C_VMCS_GUEST_CR4)
      | _ => None
    end.

  Function vmx_get_reg_spec (reg: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
    | (true, true, true) =>
      match Z2reg_type reg with
        | Some (TVMX z) => 
          match ZMap.get z (vmx adt) with
            | Vint v => Some (Int.unsigned v)
            | _ => None
          end
        | Some (TVMCS z) =>
          match vmcs adt with
            | VMCSValid revid abrtid d =>
             match ZMap.get z d with
               | Vint v => Some (Int.unsigned v)
               | _ => None
             end
          end
        | _ => None
      end
    | _ => None
    end.


(*
void
vmx_set_reg(unsigned int reg, unsigned val)
{
	switch (reg) {
	case GUEST_EAX:
		vmx.g_rax = val;
		break;
	case GUEST_EBX:
		vmx.g_rbx = val;
		break;
	case GUEST_ECX:
		vmx.g_rcx = val;
		break;
	case GUEST_EDX:
		vmx.g_rdx = val;
		break;
	case GUEST_ESI:
		vmx.g_rsi = val;
		break;
	case GUEST_EDI:
		vmx.g_rdi = val;
		break;
	case GUEST_EBP:
		vmx.g_rbp = val;
		break;
	case GUEST_ESP:
		vmcs_write32(VMCS_GUEST_RSP, val);
		break;
	case GUEST_EIP:
		vmx.g_rip = val;
		break;
	case GUEST_EFLAGS:
		vmcs_write32(VMCS_GUEST_RFLAGS, val);
		break;
	case GUEST_CR0:
		vmcs_write32(VMCS_GUEST_CR0, val);
		break;
	case GUEST_CR2:
		vmx.g_cr2 = val;
		break;
	case GUEST_CR3:
		vmcs_write32(VMCS_GUEST_CR3, val);
		break;
	case GUEST_CR4:
		vmcs_write32(VMCS_GUEST_CR4, val);
		break;
	default:
        break;
	}
}
 *)
  
  Function vmx_set_reg_spec (reg v: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match Z2reg_type reg with
          | Some (TVMX z) => Some adt {vmx: ZMap.set z (Vint (Int.repr v)) (vmx adt)}
          | Some (TVMCS z) =>
            match vmcs adt with
              | VMCSValid revid abrtid d =>
                Some adt {vmcs: VMCSValid revid abrtid (ZMap.set z (Vint (Int.repr v)) d)}
            end
          | _ => None
        end
      | _ => None
    end.
  
(*
unsigned int
vmx_get_next_eip()
{
	return vmx.g_rip + vmcs_read32(VMCS_EXIT_ITRUCTION_LENGTH);
}
 *)

  Function vmx_get_next_eip_spec (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get VMX_G_RIP' (vmx adt) with
              | Vint v1 =>
                match ZMap.get C_VMCS_EXIT_INSTRUCTION_LENGTH d with
                  | Vint v2 => Some (Int.unsigned v1 + Int.unsigned v2)
                  | _ => None
                end
              | _ => None
            end
        end
      | _ => None
    end.

  
(*
#define EXIT_QUAL_IO_SIZE(q)	((q) & 7)
# define EXIT_QUAL_IO_ONE_BYTE	0
# define EXIT_QUAL_IO_TWO_BYTE	1
# define EXIT_QUAL_IO_FOUR_BYTE	3


unsigned int
vmx_get_exit_io_width(void)
{
    unsigned int width;

    if (EXIT_QUAL_IO_SIZE(vmx.exit_qualification) == EXIT_QUAL_IO_ONE_BYTE)
        width = SZ8;
    else if (EXIT_QUAL_IO_SIZE(vmx.exit_qualification) == EXIT_QUAL_IO_TWO_BYTE)
        width = SZ16;
    else
        width = SZ32;

    return width;
}
 *)

  Function vmx_get_io_width_spec (adt: RData): option Z :=
    match (ikern adt, pg adt, ihost adt) with
    | (true, true, true) =>
      match ZMap.get VMX_EXIT_QUALIFICATION' (vmx adt) with
        | Vint v =>
          let qsize := Z.land (Int.unsigned v) EXIT_QUAL_IO_SIZE in
          if zeq qsize EXIT_QUAL_IO_ONE_BYTE then Some SZ8
          else if zeq qsize EXIT_QUAL_IO_TWO_BYTE then Some SZ16
               else Some SZ32
        |_ => None
      end
    | _ => None
    end.

  
(*
#define EXIT_QUAL_IO_DIR(q)	(((q) >> 3) & 1)
# define EXIT_QUAL_IO_OUT	0
# define EXIT_QUAL_IO_IN	1

unsigned int
vmx_get_exit_io_write(void)
{
    unsigned int write;

    if (EXIT_QUAL_IO_DIR(vmx.exit_qualification) == EXIT_QUAL_IO_IN)
        write = 0;
    else
        write = 1;

    return write;
}
 *)
  
  Function vmx_get_io_write_spec (adt: RData): option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match ZMap.get VMX_EXIT_QUALIFICATION' (vmx adt) with
          | Vint v =>
            let qdir :=  (Z.land (Z.shiftr (Int.unsigned v) EXIT_QUAL_IO_DIR) 1) in
            if zeq qdir EXIT_QUAL_IO_IN then Some 0
            else Some 1
          |_ => None
        end
      | _ => None
    end.

(*
#define EXIT_QUAL_IO_REP(q)	(((q) >> 5) & 1)

unsigned int
vmx_get_exit_io_rep(void)
{
    return EXIT_QUAL_IO_REP(vmx.exit_qualification) ? 1 : 0;
}
 *)
  
  Function vmx_get_exit_io_rep_spec (adt: RData): option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match ZMap.get VMX_EXIT_QUALIFICATION' (vmx adt) with
          | Vint v =>
            let qrep := Z.land (Z.shiftr (Int.unsigned v) EXIT_QUAL_IO_REP) 1 in
            Some qrep
          |_ => None
        end
      | _ => None
    end.

  (*
#define EXIT_QUAL_IO_STR(q)	(((q) >> 4) & 1)

unsigned int
vmx_get_exit_io_str(void)
{
    return EXIT_QUAL_IO_STR(vmx.exit_qualification) ? 1 : 0;
}
   *)

  Function vmx_get_exit_io_str_spec (adt: RData): option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match ZMap.get VMX_EXIT_QUALIFICATION' (vmx adt) with
          | Vint v =>
            let qrep := Z.land (Z.shiftr (Int.unsigned v) EXIT_QUAL_IO_STR) 1 in
            Some qrep
          |_ => None
        end
      | _ => None
    end.

(*
unsigned int
vmx_get_exit_io_port(void)
{
    return EXIT_QUAL_IO_PORT(vmx.exit_qualification);
}

#define EXIT_QUAL_IO_PORT(q)	((uint16_t) (((q) >> 16) & 0xffff))
 *)                             
  
  Function vmx_get_exit_io_port_spec (adt: RData) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match ZMap.get VMX_EXIT_QUALIFICATION' (vmx adt) with
          | Vint v =>
            Some ((Int.unsigned v) / C_EXIT_QUAL_IO_PORT)
          | _ => None
        end
      | _ => None
    end.

(*
void
vmx_set_mmap(unsigned int gpa, unsigned int hpa, unsigned int mem_type)
{
	int rc = 0;

	rc = ept_add_mapping(gpa, hpa, mem_type);

	if (rc) {
		KERN_DEBUG("EPT_add mapping error : ept@0x%x, gpa:0x%x, "
			   "hpa:0x%llx\n", vmx.pml4ept, gpa, hpa);
                return rc;
	} else {
		return ept_invalidate_mappings((uint64_t)(uintptr_t) vmx.pml4ept);
	}
}

IMPORTANT: this function has to call ept_invalidate_mappings(),
But the semantics is empty!!!!!!!!!!!!!!!!!!!!!!
 *)
  Function vmx_set_mmap_spec (gpa : Z)  (hpa : Z) (mem_type: Z) (adt: RData) :=
    match ept_add_mapping_spec gpa hpa mem_type adt with
      | Some (adt', res) =>
        if zle_le 0 res Int.max_unsigned then
          if zle_lt 0 mem_type 4096 then
            if zeq res 0 then 
              match ept_invalidate_mappings_spec adt' with
                | Some z => Some (adt', z)
                | _ => None
              end
            else Some (adt', res)
          else None
        else None
      | _ => None
    end.


  (*
FIXME: ECX
vmx_enter:

             "pushl %%ebp;"
             "pushl %%edi;"

/*should be able to remove

             /* save the address of vmx on the stack */
             "pushl %%ecx;"         /* placeholder */
             "pushl %%ecx;"         /* address of vmx */
             "movl %1, %%edi;"
             "vmwrite %%esp, %%edi;"
             /* save entry TSC */
             "pushl %%ecx;"
             "rdtscp;"
             "popl %%ecx;"
             "movl %%eax, %c[enter_tsc_lo](%0);"
             "movl %%edx, %c[enter_tsc_hi](%0);"
*/


             /* load guest registers */
             "movl %c[g_cr2](%0), %%edi;"   /* guest %cr2 */
             "movl %%edi, %%cr2;"
             "movl %c[g_dr0](%0), %%edi;"   /* guest %dr0 */
             "movl %%edi, %%dr0;"
             "movl %c[g_dr1](%0), %%edi;"   /* guest %dr1 */
             "movl %%edi, %%dr1;"
             "movl %c[g_dr2](%0), %%edi;"   /* guest %dr2 */
             "movl %%edi, %%dr2;"
             "movl %c[g_dr3](%0), %%edi;"   /* guest %dr3 */
             "movl %%edi, %%dr3;"
             "movl %c[g_dr6](%0), %%edi;"   /* guest %dr6 */
             /* "movl %%edi, %%dr6;" */
             "movl %c[g_rax](%0), %%eax;"   /* guest %eax */
             "movl %c[g_rbx](%0), %%ebx;"   /* guest %ebx */
             "movl %c[g_rdx](%0), %%edx;"   /* guest %edx */
             "movl %c[g_rsi](%0), %%esi;"   /* guest %esi */
             "movl %c[g_rdi](%0), %%edi;"   /* guest %edi */
             "movl %c[g_rbp](%0), %%ebp;"   /* guest %ebp */

*)

  Definition vmx_enter_spec (rs: regset) (adt: RData) : option (RData * regset) :=
    match (ikern adt, ihost adt, pg adt, init adt) with
      | (true, true, true, true) =>
        let vvmx := vmx adt in
        let rs' := (Pregmap.init Vundef) 
                     # EAX <- (ZMap.get VMX_G_RAX' vvmx) # EBX <- (ZMap.get VMX_G_RBX' vvmx)
                     # EDX <- (ZMap.get VMX_G_RDX' vvmx) # ESI <- (ZMap.get VMX_G_RSI' vvmx)
                     # EDI <- (ZMap.get VMX_G_RDI' vvmx) # EBP <- (ZMap.get VMX_G_RBP' vvmx)
                     # RA <- (ZMap.get VMX_G_RIP' vvmx) in
        let vvmx1 := ZMap.set VMX_HOST_EBP' (rs EBP) vvmx in
        let vvmx2 := ZMap.set VMX_HOST_EDI' (rs EDI) vvmx1 in
        Some (adt {vmx: vvmx2}{ihost: false}, rs')
      | _ => None
    end.
  

(*
void vmx_enter_pre () {
    vmcs_write32(VMCS_GUEST_RIP, vmx.g_rip);
}
*)

  Function vmx_enter_pre_spec (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, init adt) with
      | (true, true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get VMX_G_RIP' (vmx adt) with
              | Vint v =>
                let d' := ZMap.set C_VMCS_GUEST_RIP (Vint v) d in
                Some (adt {vmcs: VMCSValid revid abrtid d'})
              | _ => None
            end
        end
      | _ => None
    end.

(* vm_run:
    vmptrld(vmx.vmcs);
    jump vmx_enter_pre;
    jump vmx_enter;
    jump hostout;
*)

  Definition vm_run_spec (rs: regset) (adt: RData) : option (RData * regset) :=
    match (ikern adt, pg adt, ihost adt, init adt) with
      | (true, true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get VMX_G_RIP' (vmx adt) with
              | Vint v =>
                let d' := ZMap.set C_VMCS_GUEST_RIP (Vint v) d in
                let vvmx := vmx adt in
                let rs' := (Pregmap.init Vundef) 
                             # EAX <- (ZMap.get VMX_G_RAX' vvmx) # EBX <- (ZMap.get VMX_G_RBX' vvmx)
                             # EDX <- (ZMap.get VMX_G_RDX' vvmx) # ESI <- (ZMap.get VMX_G_RSI' vvmx)
                             # EDI <- (ZMap.get VMX_G_RDI' vvmx) # EBP <- (ZMap.get VMX_G_RBP' vvmx)
                             # RA <- (ZMap.get VMX_G_RIP' vvmx) in
                let vvmx1 := ZMap.set VMX_HOST_EBP' (rs EBP) vvmx in
                let vvmx2 := ZMap.set VMX_HOST_EDI' (rs EDI) vvmx1 in
                Some (adt {vmx: vvmx2} {vmcs: VMCSValid revid abrtid d'} {ihost: false}, rs')
              | _ => None
            end
        end
      | _ => None
    end.

(*
FIXME: ecx

vmx_exit:

             "movl %%edi, %c[g_rdi](%0);"   /* guest %edi */
             "movl %%cr2, %%edi;"       /* guest %cr2 */
             "movl %%edi, %c[g_cr2](%0);"
             "movl %%dr0, %%edi;"       /* guest %dr0 */
             "movl %%edi, %c[g_dr0](%0);"
             "movl %%dr1, %%edi;"       /* guest %dr1 */
             "movl %%edi, %c[g_dr1](%0);"
             "movl %%dr2, %%edi;"       /* guest %dr2 */
             "movl %%edi, %c[g_dr1](%0);"
             "movl %%dr3, %%edi;"       /* guest %dr3 */
             "movl %%edi, %c[g_dr3](%0);"
             "movl %%dr6, %%edi;"       /* guest %dr6 */
             "movl %%edi, %c[g_dr6](%0);"
             "movl %%eax, %c[g_rax](%0);"   /* guest %eax */
             "movl %%ebx, %c[g_rbx](%0);"   /* guest %ebx */
             "popl %%edi;"          /* guest %ecx */
             "movl %%edi, %c[g_rcx](%0);"
             "movl %%edx, %c[g_rdx](%0);"   /* guest %edx */
             "movl %%esi, %c[g_rsi](%0);"   /* guest %esi */
             "movl %%ebp, %c[g_rbp](%0);"   /* guest %ebp */

/* should be removed

             /* save exit TSC */
             "pushl %%ecx;"
             "rdtscp;"
             "popl %%ecx;"
             "movl %%eax, %c[exit_tsc_lo](%0);"
             "movl %%edx, %c[exit_tsc_hi](%0);"
*/


             /* load host registers */
             "popl %%edi;"
             "popl %%ebp;"
*)

  Definition vmx_exit_spec (rs: regset) (adt: RData) : option (RData * regset) :=
    match (ikern adt, ihost adt, pg adt, init adt) with
      | (true, true, true, true) =>
        let vvmx := vmx adt in
        let vvmx1 := ZMap.set VMX_G_RDI' (rs EDI) vvmx in
        let vvmx2 := ZMap.set VMX_G_RAX' (rs EAX) vvmx1 in
        let vvmx3 := ZMap.set VMX_G_RBX' (rs EBX) vvmx2 in
        (*let vvmx4 := ZMap.set VMX_G_RCX' (rs ECX) vvmx3 in*)
        let vvmx5 := ZMap.set VMX_G_RDX' (rs EDX) vvmx3 in
        let vvmx6 := ZMap.set VMX_G_RSI' (rs ESI) vvmx5 in
        let vvmx7 := ZMap.set VMX_G_RBP' (rs EBP) vvmx6 in

        let rs' := (Pregmap.init Vundef)
                     # EDI <- (ZMap.get VMX_HOST_EDI' vvmx) # EBP <- (ZMap.get VMX_HOST_EBP' vvmx) in
        Some (adt {vmx: vvmx7}, rs')
      | _ => None
    end.

(*

void vmx_exit_post (){
   vmx.g_rip = vmcs_read32(VMCS_GUEST_RIP);
   vmx.exit_reason = vmcs_read32(VMCS_EXIT_REASON);
   vmx.exit_qualification = vmcs_read32(VMCS_EXIT_QUALIFICATION);
   vmx.launched = 1;
}
*)

  Function vmx_exit_post_spec (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            let vvmx := vmx adt in
            match ZMap.get C_VMCS_GUEST_RIP d, ZMap.get C_VMCS_EXIT_REASON d, 
                  ZMap.get C_VMCS_EXIT_QUALIFICATION d with
              | Vint v1, Vint v2, Vint v3 =>
                let vvmx1 := ZMap.set VMX_G_RIP' (Vint v1) vvmx in
                let vvmx2 := ZMap.set VMX_EXIT_REASON' (Vint v2) vvmx1 in
                let vvmx3 := ZMap.set VMX_EXIT_QUALIFICATION' (Vint v3) vvmx2 in
                let vvmx4 := ZMap.set VMX_LAUNCHED' Vone vvmx3 in
                Some (adt {vmx: vvmx4})
              | _,_,_ => None
            end
        end
      | _ => None
    end.

(*

vmx_return_from_guest:
   hostin;
   call vmx_exit;
   call vmx_exit_post_spec;
*)

  Definition vmx_return_from_guest_spec (rs: regset) (adt: RData) : option (RData * regset) :=
    match (ikern adt, pg adt, ihost adt, init adt) with
      | (true, true, false, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            let vvmx := vmx adt in
            let vvmx1 := ZMap.set VMX_G_RDI' (rs EDI) vvmx in
            let vvmx2 := ZMap.set VMX_G_RAX' (rs EAX) vvmx1 in
            let vvmx3 := ZMap.set VMX_G_RBX' (rs EBX) vvmx2 in
            (*let vvmx4 := ZMap.set VMX_G_RCX' (rs ECX) vvmx3 in*)
            let vvmx5 := ZMap.set VMX_G_RDX' (rs EDX) vvmx3 in
            let vvmx6 := ZMap.set VMX_G_RSI' (rs ESI) vvmx5 in
            let vvmx7 := ZMap.set VMX_G_RBP' (rs EBP) vvmx6 in
            match ZMap.get C_VMCS_GUEST_RIP d, ZMap.get C_VMCS_EXIT_REASON d, 
                  ZMap.get C_VMCS_EXIT_QUALIFICATION d with
              | Vint v1, Vint v2, Vint v3 =>
                let vvmx8 := ZMap.set VMX_G_RIP' (Vint v1) vvmx7 in
                let vvmx9 := ZMap.set VMX_EXIT_REASON' (Vint v2) vvmx8 in
                let vvmx10 := ZMap.set VMX_EXIT_QUALIFICATION' (Vint v3) vvmx9 in
                let vvmx11 := ZMap.set VMX_LAUNCHED' Vone vvmx10 in
                let rs' := (Pregmap.init Vundef)
                             # EDI <- (ZMap.get VMX_HOST_EDI' vvmx) # EBP <- (ZMap.get VMX_HOST_EBP' vvmx) in
                Some (adt {vmx: vvmx11} {ihost: true}, rs')
              | _,_,_ => None
            end
        end
      | _ => None
    end.

(*
FIXME: identifier

void
vmx_init(unsigned int mbi_addr)
{
    int rw;
    vmcs_set_defaults (mbi_addr);
    // What is this???? Why not using vmcs_write()?????
    vmx.vmcs->identifier = rdmsr(MSR_VMX_BASIC) & 0xffffffff;

    vmx.g_rip = 0xfff0;
    vmx.vpid = 1;
    vmx.g_cr2 = 0;
    vmx.g_dr0 = vmx.g_dr1 = vmx.g_dr2 = vmx.g_dr3 = 0;
    vmx.g_dr6 = 0xffff0ff0;

}
 *)

  Function vmx_init_spec (mbi_adr:Z)
           (pml4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b: block)
           (adt: RData) : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
             {smspool: real_smspool (smspool adt)}
             {abtcb: ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb (abtcb adt))}
             {abq: real_abq (abq adt)} {cid: 0} {syncchpool: real_syncchpool (syncchpool adt)}
             {ept: real_ept (ept adt)}
             {vmcs: real_vmcs (vmcs adt) real_vmxinfo
                              pml4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b}
             {vmx: real_vmx (vmx adt)}
      | _ => None
    end.

End OBJ_VMX.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import IntelPrimSemantics.
Require Import AuxLemma.

Section OBJ_SIM.

  Context `{data : CompatData RData}.
  Context `{data0 : CompatData RData}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_prf := data) RData).
  Notation LDATAOps := (cdata (cdata_prf := data0) RData).

  Context `{rel_prf: CompatRel _ (memory_model_ops:= memory_model_ops) _
                               (stencil_ops:= stencil_ops) HDATAOps LDATAOps}.

  Lemma val_inject_vint_eq:
    forall f n v v' i,
      val_inject f (ZMap.get n v) (ZMap.get n v')
      -> ZMap.get n v = Vint i
      -> ZMap.get n v' = Vint i.
  Proof.
    intros.
    rewrite H0 in H; inversion H; reflexivity.
  Qed.

  Section VMX_GET_REG_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.
    Context {re3: relate_impl_vmcs}.

    Lemma vmx_get_reg_exist:
      forall s habd labd reg v f,
        vmx_get_reg_spec reg habd = Some v
        -> relate_AbData s f habd labd
        -> vmx_get_reg_spec reg labd = Some v.
    Proof.
      unfold vmx_get_reg_spec in *. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H4. subrewrite.
      subdestruct; erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_reg_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_reg_spec)
            (id ↦ gensem vmx_get_reg_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      eapply vmx_get_reg_exist in H2; eauto.
      rewrite H2; reflexivity.
    Qed.

  End VMX_GET_REG_SIM.

  Section VMX_SET_REG_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.
    Context {re3: relate_impl_vmcs}.

    Lemma vmx_set_reg_exist:
      forall s habd habd' labd reg v f,
        vmx_set_reg_spec reg v habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', vmx_set_reg_spec reg v labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmx_set_reg_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H4. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.

      - apply relate_impl_vmcs_update; try assumption.
        apply VMCS_inj_set_int.
        rewrite H, H6; assumption.
      - apply relate_impl_vmx_update; try assumption.
        apply VMX_inj_set_int; auto.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmx}.
    Context {mt3: match_impl_vmcs}.

    Lemma vmx_set_reg_match:
      forall s d d' m reg v f,
        vmx_set_reg_spec reg v d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_set_reg_spec; intros. subdestruct; inv H; trivial;
        [ eapply match_impl_vmcs_update
        | eapply match_impl_vmx_update ];
        assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmx_set_reg_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmx_set_reg_spec}.

    Lemma vmx_set_reg_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_set_reg_spec)
            (id ↦ gensem vmx_set_reg_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmx_set_reg_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmx_set_reg_match; eauto.
    Qed.

  End VMX_SET_REG_SIM.

  Section VMX_GET_NEXT_EIP_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.
    Context {re3: relate_impl_vmcs}.

    Lemma vmx_get_next_eip_exist:
      forall s habd labd v f,
        vmx_get_next_eip_spec habd = Some v
        -> relate_AbData s f habd labd
        -> vmx_get_next_eip_spec labd = Some v.
    Proof.
      unfold vmx_get_next_eip_spec in *. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H4. subrewrite. subdestruct.
      erewrite 2 val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_next_eip_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_next_eip_spec)
            (id ↦ gensem vmx_get_next_eip_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      eapply vmx_get_next_eip_exist in H2; eauto.
      rewrite H2; reflexivity.
    Qed.

  End VMX_GET_NEXT_EIP_SIM.

  Section VMX_GET_IO_WIDTH_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.

    Lemma vmx_get_io_width_exist:
      forall s habd labd v f,
        vmx_get_io_width_spec habd = Some v
        -> relate_AbData s f habd labd
        -> vmx_get_io_width_spec labd = Some v.
    Proof.
      Local Opaque Z.land.

      unfold vmx_get_io_width_spec in *. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      revert H. subrewrite.

      (* Manually unfold to delimit subdestruct until the [ZMap.get], whose
         argument [vmx habd] couldn't be changed to [vmx labd] mismatching
         that in the goal. *)
      destruct (ikern labd) eqn:Hdestruct; contra_inv;
      destruct (pg labd) eqn:Hdestruct1; contra_inv;
      destruct (ihost labd) eqn:Hdestruct2; contra_inv;
      destruct (ZMap.get 28%Z (vmx habd)) eqn:Hdestruct3; contra_inv.
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_io_width_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_io_width_spec)
            (id ↦ gensem vmx_get_io_width_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      eapply vmx_get_io_width_exist in H2; eauto.
      rewrite H2; reflexivity.
    Qed.

  End VMX_GET_IO_WIDTH_SIM.

  Section VMX_GET_IO_WRITE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.

    Lemma vmx_get_io_write_exist:
      forall s habd labd v f,
        vmx_get_io_write_spec habd = Some v
        -> relate_AbData s f habd labd
        -> vmx_get_io_write_spec labd = Some v.
    Proof.
      Local Opaque Z.shiftr.

      unfold vmx_get_io_write_spec in *. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      revert H. subrewrite.

      (* Manually unfold to delimit subdestruct until the [ZMap.get], whose
         argument [vmx habd] couldn't be changed to [vmx labd] mismatching
         that in the goal. *)
      destruct (ikern labd) eqn:Hdestruct; contra_inv;
      destruct (pg labd) eqn:Hdestruct1; contra_inv;
      destruct (ihost labd) eqn:Hdestruct2; contra_inv;
      destruct (ZMap.get 28%Z (vmx habd)) eqn:Hdestruct3; contra_inv.
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_io_write_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_io_write_spec)
            (id ↦ gensem vmx_get_io_write_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      eapply vmx_get_io_write_exist in H2; eauto.
      rewrite H2; reflexivity.
    Qed.

  End VMX_GET_IO_WRITE_SIM.

  Section VMX_GET_EXIT_IO_REP_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.

    Lemma vmx_get_exit_io_rep_exist:
      forall s habd labd v f,
        vmx_get_exit_io_rep_spec habd = Some v
        -> relate_AbData s f habd labd
        -> vmx_get_exit_io_rep_spec labd = Some v.
    Proof.
      Local Opaque Z.land Z.shiftr.

      unfold vmx_get_exit_io_rep_spec in *. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      revert H. subrewrite. subdestruct.
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_exit_io_rep_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_exit_io_rep_spec)
            (id ↦ gensem vmx_get_exit_io_rep_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      eapply vmx_get_exit_io_rep_exist in H2; eauto.
      rewrite H2; reflexivity.
    Qed.

  End VMX_GET_EXIT_IO_REP_SIM.

  Section VMX_GET_EXIT_IO_STR_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.

    Lemma vmx_get_exit_io_str_exist:
      forall s habd labd v f,
        vmx_get_exit_io_str_spec habd = Some v
        -> relate_AbData s f habd labd
        -> vmx_get_exit_io_str_spec labd = Some v.
    Proof.
      Local Opaque Z.land Z.shiftr.

      unfold vmx_get_exit_io_str_spec in *. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      revert H. subrewrite. subdestruct.
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_exit_io_str_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_exit_io_str_spec)
            (id ↦ gensem vmx_get_exit_io_str_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      eapply vmx_get_exit_io_str_exist in H2; eauto.
      rewrite H2; reflexivity.
    Qed.

  End VMX_GET_EXIT_IO_STR_SIM.

  Section VMX_GET_EXIT_IO_PORT_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.

    Lemma vmx_get_exit_io_port_exist:
      forall s habd labd v f,
        vmx_get_exit_io_port_spec habd = Some v
        -> relate_AbData s f habd labd
        -> vmx_get_exit_io_port_spec labd = Some v.
    Proof.
      unfold vmx_get_exit_io_port_spec in *. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      revert H. subrewrite. subdestruct.
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_exit_io_port_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_exit_io_port_spec)
            (id ↦ gensem vmx_get_exit_io_port_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      eapply vmx_get_exit_io_port_exist in H2; eauto.
      rewrite H2; reflexivity.
    Qed.

  End VMX_GET_EXIT_IO_PORT_SIM.

  Section VMX_SET_MMAP_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ept}.

    Lemma vmx_set_mmap_exist:
      forall s habd habd' labd gpa hpa mem_type i f,
        vmx_set_mmap_spec gpa hpa mem_type habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', vmx_set_mmap_spec gpa hpa mem_type labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmx_set_mmap_spec; intros.
      destruct (ept_add_mapping_spec gpa hpa mem_type habd) as [ [] |] eqn:Hdestruct; contra_inv.
      exploit ept_add_mapping_exist; eauto; intros [labd' [HP HM]].
      revert H. subrewrite.
      subdestruct; inv HQ.
      erewrite ept_invalidate_mappings_exists; eauto.
      refine_split'; trivial.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_ept}.

    Lemma vmx_set_mmap_match:
      forall s d d' m gpa hpa mem_type i f,
        vmx_set_mmap_spec gpa hpa mem_type d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_set_mmap_spec; intros.
      subdestruct; inv H;
      eapply ept_add_mapping_match; eauto.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmx_set_mmap_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmx_set_mmap_spec}.

    Lemma vmx_set_mmap_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_set_mmap_spec)
            (id ↦ gensem vmx_set_mmap_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmx_set_mmap_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmx_set_mmap_match; eauto.
    Qed.

  End VMX_SET_MMAP_SIM.

  Section VM_RUN_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.
    Context {re3: relate_impl_vmcs}.
    Context {re4: relate_impl_init}.

    Lemma vm_run_exist:
      forall s n habd habd' labd rs0 rs1 r'0 f,
        vm_run_spec rs0 habd = Some (habd', rs1)
        -> relate_AbData s f habd labd
        -> (forall r, val_inject f (Pregmap.get r rs0) (Pregmap.get r r'0))
        -> (forall r, Val.has_type (r'0#r) AST.Tint)
        -> (forall r, val_inject (Mem.flat_inj n) (r'0 r) (r'0 r))
        -> VMX_inject_neutral (vmx labd) n
        -> exists labd' r'1, vm_run_spec r'0 labd = Some (labd', r'1)
                         /\ relate_AbData s f habd' labd'
                         /\ (forall r, val_inject f (Pregmap.get r rs1) (Pregmap.get r r'1))
                         /\ (forall r, Val.has_type (r'1#r) AST.Tint)
                         /\ (forall r, val_inject (Mem.flat_inj n) (r'1 r) (r'1 r)).
    Proof.
      unfold vm_run_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      exploit relate_impl_vmcs_eq; eauto. intros.
      exploit relate_impl_init_eq; eauto. intros.
      revert H. inversion H8. subrewrite.
      pose proof (H7 14%Z) as HINJ.
      subdestruct. inv HINJ.
      inv HQ. refine_split'; trivial.
      - apply relate_impl_ihost_update, relate_impl_vmcs_update.
        + apply relate_impl_vmx_update; try assumption.
          apply VMX_inj_set, H1.
          apply VMX_inj_set, H1; assumption.
        + apply VMCS_inj_set.
          rewrite H, H11; assumption.
          constructor.
      - intros.
        repeat apply AsmX.set_reg_inject; auto.
      - inv H4. intros.
        destruct r0 as [| [] | [] | | [] |]; try apply H10; try constructor.
      - inv H4.
        destruct r0 as [| [] | [] | | [] |];
        try apply H3; try apply H10;
        constructor.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmx}.
    Context {mt3: match_impl_vmcs}.

    Lemma vm_run_match:
      forall s d d' m rs0 rs1 f,
        vm_run_spec rs0 d = Some (d', rs1)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vm_run_spec; intros.
      subdestruct; inv H; trivial.
      apply match_impl_ihost_update.
      apply match_impl_vmcs_update.
      apply match_impl_vmx_update. assumption.
    Qed.

    Context {inv: VMXEnterInvariants (data_ops := data_ops) vm_run_spec}.
    Context {inv0: VMXEnterInvariants (data_ops:= data_ops0) vm_run_spec}.

    Lemma vm_run_sim :
      forall id,
        (forall n d, low_level_invariant n d -> VMX_inject_neutral (vmx d) n) ->
        sim (crel RData RData) (id ↦ primcall_vmx_enter_compatsem vm_run_spec id)
            (id ↦ primcall_vmx_enter_compatsem vm_run_spec id).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. intros.
      inv H1. inv H0. inv match_extcall_states.
      set (rs02 := (Pregmap.init Vundef) # EDI <- (rs2 EDI) # EBP <- (rs2 EBP)).
      assert (HR: forall reg,
                    val_inject f (Pregmap.get reg rs01) (Pregmap.get reg rs02)).
      {
        intros. subst rs01 rs02.
        val_inject_simpl.
      }        
      exploit vm_run_exist; eauto 2.

      intros r; destruct r as [| [] | [] | | [] |]; try constructor;
      try apply ASM_INV.

      intros r; destruct r as [| [] | [] | | [] |]; try constructor;
      try apply ASM_INV.

      intros (labd' & r'1 & HP & HM & Hrinj' & Hrwt' & Hrinj_flat').
      refine_split; eauto 1.
      econstructor; eauto 1.
      - eapply reg_symbol_inject; eassumption.
      - eapply reg_val_inject_defined; eauto 1.
      - intros.
        specialize (match_reg ESP); unfold Pregmap.get in match_reg.
        inv match_reg; try congruence.
        specialize (HESP_STACK _ _ (eq_sym H1)).
        replace b1 with b2 by congruence.
        split.
        * apply Ple_trans with b0;
          [ apply HESP_STACK | apply (match_inject_forward _ _ _ H3) ].
        * apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H3 match_inject).
      - econstructor; eauto. econstructor; eauto. 
        eapply vm_run_match; eassumption.
        subst rs0.
        val_inject_simpl.
    Qed.

  End VM_RUN_SIM.

  Section VMX_RETURN_FROM_GUEST_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.
    Context {re3: relate_impl_vmcs}.
    Context {re4: relate_impl_init}.

    Lemma vmx_return_from_guest_exist:
      forall s n habd habd' labd rs0 rs1 r'0 f,
        vmx_return_from_guest_spec rs0 habd = Some (habd', rs1)
        -> relate_AbData s f habd labd
        -> (forall r, val_inject f (Pregmap.get r rs0) (Pregmap.get r r'0))
        -> (forall r, Val.has_type (r'0#r) AST.Tint)
        -> (forall r, val_inject (Mem.flat_inj n) (r'0 r) (r'0 r))
        -> VMX_inject_neutral (vmx labd) n
        -> exists labd' r'1, vmx_return_from_guest_spec r'0 labd = Some (labd', r'1)
                         /\ relate_AbData s f habd' labd'
                         /\ (forall r, val_inject f (Pregmap.get r rs1) (Pregmap.get r r'1))
                         /\ (forall r, Val.has_type (r'1#r) AST.Tint)
                         /\ (forall r, val_inject (Mem.flat_inj n) (r'1 r) (r'1 r)).
    Proof.
      unfold vmx_return_from_guest_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmx_eq; eauto. inversion 1; subst.
      exploit relate_impl_vmcs_eq; eauto. intros.
      exploit relate_impl_init_eq; eauto. intros.
      revert H. inversion H8. subrewrite.
      pose proof (H12 26654%Z) as Hi1.
      pose proof (H12 17410%Z) as Hi2.
      pose proof (H12 25600%Z) as Hi3.
      subdestruct.
      inv HQ. inv Hi1. inv Hi2. inv Hi3.
      refine_split'; trivial.
      - apply relate_impl_ihost_update, relate_impl_vmx_update; try assumption.
        repeat (apply VMX_inj_set_int || apply VMX_inj_set);
         solve  [ assumption | apply H1 | apply H12 ].
      - intros.
        repeat apply AsmX.set_reg_inject; auto.
      - inv H4. intros.
        destruct r0 as [| [] | [] | | [] |]; try apply H10; try constructor.
      - inv H4.
        destruct r0 as [| [] | [] | | [] |]; try apply H3; try apply H10; constructor.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmx}.

    Lemma vmx_return_from_guest_match:
      forall s d d' m rs0 rs1 f,
        vmx_return_from_guest_spec rs0 d = Some (d', rs1)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_return_from_guest_spec; intros.
      subdestruct; inv H; trivial.
      apply match_impl_ihost_update.
      apply match_impl_vmx_update. assumption.
    Qed.

    Context {inv: VMXExitInvariants (data_ops := data_ops) vmx_return_from_guest_spec}.
    Context {inv0: VMXExitInvariants (data_ops:= data_ops0) vmx_return_from_guest_spec}.

    Lemma vmx_return_from_guest_sim :
      forall id,
        (forall n d, low_level_invariant n d -> VMX_inject_neutral (vmx d) n) ->
        sim (crel RData RData) (id ↦ primcall_vmx_return_compatsem vmx_return_from_guest_spec id)
            (id ↦ primcall_vmx_return_compatsem vmx_return_from_guest_spec id).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. intros.
      inv H1. inv H0. inv match_extcall_states.
      set (rs02 := (Pregmap.init Vundef)
                     #EAX <- (rs2 EAX) #EBX <- (rs2 EBX)
                     #EDX <- (rs2 EDX) #EDI <- (rs2 EDI)
                     #ESI <- (rs2 ESI) #EBP <- (rs2 EBP)).
      assert (HR: forall reg,
                    val_inject f (Pregmap.get reg rs01) (Pregmap.get reg rs02)).
      {
        intros. subst rs01 rs02.
        val_inject_simpl.
      }        

      exploit vmx_return_from_guest_exist; eauto 2.

      intros r; destruct r as [| [] | [] | | [] |]; try constructor;
      try apply ASM_INV.

      intros r; destruct r as [| [] | [] | | [] |]; try constructor;
      try apply ASM_INV.

      intros (labd' & r'1 & HP & HM & Hrinj' & Hrwt' & Hrinj_flat').
      refine_split; eauto 1.
      econstructor; eauto 1.
      - eapply reg_symbol_inject; eassumption.
      - eapply reg_val_inject_defined; eauto 1.
      - intros.
        specialize (match_reg ESP); unfold Pregmap.get in match_reg.
        inv match_reg; try congruence.
        specialize (HESP_STACK _ _ (eq_sym H1)).
        replace b1 with b2 by congruence.
        split.
        * apply Ple_trans with b0;
          [ apply HESP_STACK | apply (match_inject_forward _ _ _ H3) ].
        * apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H3 match_inject).
      - econstructor; eauto. econstructor; eauto. 
        eapply vmx_return_from_guest_match; eassumption.
        subst rs0.
        val_inject_simpl.
    Qed.

  End VMX_RETURN_FROM_GUEST_SIM.

  Section VMX_INIT_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_vmx}.
    Context {re3: relate_impl_vmcs}.
    Context {re4: relate_impl_ipt}.
    Context {re5: relate_impl_LAT}.
    Context {re6: relate_impl_nps}.
    Context {re7: relate_impl_init}.
    Context {re8: relate_impl_PT}.
    Context {re9: relate_impl_ptpool}.
    Context {re10: relate_impl_idpde}.
    Context {re11: relate_impl_smspool}.
    Context {re12: relate_impl_abtcb}.
    Context {re13: relate_impl_abq}.
    Context {re14: relate_impl_cid}.
    Context {re15: relate_impl_syncchpool}.
    Context {re16: relate_impl_vmxinfo}.
    Context {re17: relate_impl_ept}.
    Context {re18: relate_impl_AC}.

    Let block_inject_neutral f b :=
      forall ofs, val_inject f (Vptr b ofs) (Vptr b ofs).

    Lemma vmx_init_exist:
      forall s habd habd' labd mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b f,
        vmx_init_spec mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b habd = Some habd'
        -> relate_AbData s f habd labd
        -> block_inject_neutral f pm4ept_b
        -> block_inject_neutral f tss_b
        -> block_inject_neutral f gdt_b
        -> block_inject_neutral f idt_b
        -> block_inject_neutral f msr_bitmap_b
        -> block_inject_neutral f io_bitmap_b
        -> block_inject_neutral f host_rip_b
        -> exists labd', vmx_init_spec mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmx_init_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_idpde_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_smspool_eq; eauto.
      exploit relate_impl_ept_eq; eauto.
      exploit relate_impl_vmx_eq; eauto.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_vmx_update; [| repeat apply VMX_inj_set_int; auto ].
      apply relate_impl_vmcs_update.
      - apply relate_impl_ept_update.
        apply relate_impl_syncchpool_update.
        apply relate_impl_cid_update.
        apply relate_impl_abq_update.
        apply relate_impl_abtcb_update.
        apply relate_impl_smspool_update.
        apply relate_impl_idpde_update.
        apply relate_impl_ptpool_update.
        apply relate_impl_PT_update.
        apply relate_impl_init_update.
        apply relate_impl_AC_update.
        apply relate_impl_nps_update.
        apply relate_impl_LAT_update.
        apply relate_impl_pg_update.
        apply relate_impl_vmxinfo_update. assumption.
      - inversion H9.
        repeat (apply VMCS_inj_set_int || apply VMCS_inj_set);
          try rewrite H; auto.
        econstructor.
        assumption.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmx}.
    Context {mt3: match_impl_vmcs}.
    Context {mt4: match_impl_ipt}.
    Context {mt5: match_impl_LAT}.
    Context {mt6: match_impl_nps}.
    Context {mt7: match_impl_init}.
    Context {mt8: match_impl_PT}.
    Context {mt9: match_impl_ptpool}.
    Context {mt10: match_impl_idpde}.
    Context {mt11: match_impl_smspool}.
    Context {mt12: match_impl_abtcb}.
    Context {mt13: match_impl_abq}.
    Context {mt14: match_impl_cid}.
    Context {mt15: match_impl_syncchpool}.
    Context {mt16: match_impl_vmxinfo}.
    Context {mt17: match_impl_ept}.
    Context {mt18: match_impl_AC}.

    Lemma vmx_init_match:
      forall s d d' m mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b f,
        vmx_init_spec mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_init_spec; intros.
      subdestruct; inv H; trivial.
      apply match_impl_vmx_update.
      apply match_impl_vmcs_update.
      apply match_impl_ept_update.
      apply match_impl_syncchpool_update.
      apply match_impl_cid_update.
      apply match_impl_abq_update.
      apply match_impl_abtcb_update.
      apply match_impl_smspool_update.
      apply match_impl_idpde_update.
      apply match_impl_ptpool_update.
      apply match_impl_PT_update.
      apply match_impl_init_update.
      apply match_impl_AC_update.
      apply match_impl_nps_update.
      apply match_impl_LAT_update.
      apply match_impl_pg_update.
      apply match_impl_vmxinfo_update. assumption.
    Qed.

    Context {inv: VMCSSetDefaultsInvariants (data_ops := data_ops) vmx_init_spec}.
    Context {inv0: VMCSSetDefaultsInvariants (data_ops := data_ops0) vmx_init_spec}.

    Lemma inject_incr_block_inject_neutral s f i b :
        find_symbol s i = Some b
        -> inject_incr (Mem.flat_inj (genv_next s)) f
        -> block_inject_neutral f b.
    Proof.
      unfold block_inject_neutral; intros symbol_exists incr ?.
      apply val_inject_ptr with 0%Z.
      - apply incr.
        unfold Mem.flat_inj.
        destruct (plt b (genv_next s)); try reflexivity.
        contradict n.
        eapply genv_symb_range; eassumption.
      - symmetry; apply Int.add_zero.
    Qed.

    Lemma vmx_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ vmcs_set_defaults_compatsem vmx_init_spec)
            (id ↦ vmcs_set_defaults_compatsem vmx_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmx_init_exist; eauto 2 using inject_incr_block_inject_neutral.

      intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmx_init_match; eauto.
    Qed.

  End VMX_INIT_SIM.

End OBJ_SIM.
