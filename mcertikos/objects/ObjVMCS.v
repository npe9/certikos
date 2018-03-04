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
Require Import GlobIdent.
Require Import Z64Lemma.

Section OBJ_VMCS.

  Context `{real_params: RealParams}.

  Function vmcs_get_revid_spec (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid _ _ => 
            match revid with
              | Vint v => Some (Int.unsigned v)
              | _ => None
            end
        end
      | _ => None
    end.

  Function vmcs_set_revid_spec (revid: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => 
        match vmcs adt with
          | VMCSValid _ abrtid data =>
            Some adt {vmcs: VMCSValid (Vint (Int.repr revid)) abrtid data}
        end
      | _ => None
    end.

  Function vmcs_get_abrtid_spec (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => 
        match vmcs adt with
          | VMCSValid _ abrtid _ => 
            match abrtid with
              | Vint v => Some (Int.unsigned v)
              | _ => None
            end
        end
      | _ => None
    end.

  Function vmcs_set_abrtid_spec (abrtid: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => 
        match vmcs adt with
          | VMCSValid revid _ data =>
            Some adt {vmcs: VMCSValid revid (Vint (Int.repr abrtid)) data}
        end
      | _ => None
    end.

(*gcc_inline uint32_t
vmcs_read32(uint32_t encoding)
{
	return vmread(encoding);
}
*)
  Function vmcs_readz_spec (enc: Z) (adt: RData): option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid _ _ data =>
            match vmcs_ZtoEncoding enc with
              | Some _ => 
                match ZMap.get enc data with
                  | Vint v => Some (Int.unsigned v)
                  | _ => None
                end
              | _ => None
            end
        end
      | _ => None
    end.    

(*
gcc_inline void
vmcs_write32(uint32_t encoding, uint32_t val)
{
	vmwrite(encoding, val);
}
*)
  Function vmcs_writez_spec (enc value: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match vmcs_ZtoEncoding enc with
              | Some _ =>
                let d' := ZMap.set enc (Vint (Int.repr value)) d in
                Some adt {vmcs: VMCSValid revid abrtid d'}
              | _ => None
            end
        end
      | _ => None
    end.
  

(*
gcc_inline uint64_t
vmcs_read64(uint32_t encoding)
{
	return vmread(encoding) |
		((uint64_t) vmread(encoding+1) << 32);
}*)
  Function vmcs_readz64_spec (enc: Z) (adt: RData): option Z64 :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid _ _ data =>
            match vmcs_ZtoEncoding enc with
              | Some _ => 
                match ZMap.get enc data, ZMap.get (enc + 1) data with
                  | Vint v1, Vint v2 => 
                    Some (VZ64 (Z64ofwords (Int.unsigned v2) (Int.unsigned v1)))
                  | _, _  => None
                end
              | _ => None
            end
        end
      | _ => None
    end.    

(*
gcc_inline void
vmcs_write64(uint32_t encoding, uint64_t val)
{
	vmwrite(encoding, val);
	vmwrite(encoding+1, val >> 32);
}
*)

  Function vmcs_writez64_spec (enc : Z) (value: Z64) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match vmcs_ZtoEncoding enc with
              | Some _ =>
                Some adt {vmcs: VMCSValid revid abrtid (write64_aux enc value d)}
              | _ => None
            end
        end
      | _ => None
    end.
  
  (* Asm Prim *)  
  (*Function vmcs_read_spec (enc: Z) (adt: RData): (option val) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid _ _ data =>
            match vmcs_ZtoEncoding enc with
              | Some _ => Some (ZMap.get enc data)
              | _ => None
            end
        end
      | _ => None
    end.    

  (* Asm Prim *)  
  Function vmcs_write_spec (enc: Z) (value: val) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match vmcs_ZtoEncoding enc with
              | Some _ =>
                let d' := ZMap.set enc value d in
                Some adt {vmcs: VMCSValid revid abrtid d'}
              | _ => None
            end
        end
      | _ => None
    end.*)

  Function vmcs_Z2ident (v: Z) :=
    match v with
      | 0 => Some EPT_LOC
      | 1 => Some tss_LOC
      | 2 => Some gdt_LOC
      | 3 => Some idt_LOC
      | 4 => Some msr_bitmap_LOC
      | 5 => Some io_bitmap_LOC
      | 6 => Some vmx_return_from_guest
      | _ => None
    end.

  Function vmcs_write_ident_spec (enc: Z) (b: block) (ofs: int) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match vmcs_ZtoEncoding enc with
              | Some _ =>
                let d' := ZMap.set enc (Vptr b ofs) d in
                Some adt {vmcs: VMCSValid revid abrtid d'}
              | _ => None
            end
        end
      | _ => None
    end.

  (*
  void
    vmx_set_intercept_intwin(unsigned int enable)
    {
      unsigned int procbased_ctls = vmcs_read32(VMCS_PRI_PROC_BASED_CTLS);
      if (enable == 1)
	   procbased_ctls |= PROCBASED_INT_WINDOW_EXITING;
      else
	procbased_ctls &= ~PROCBASED_INT_WINDOW_EXITING;
      vmcs_write32(VMCS_PRI_PROC_BASED_CTLS, procbased_ctls);
    }
   *)
  Notation NOT_PROCBASED_INT_WINDOW_EXITING := 4294967291 % Z.
  Function vmx_set_intercept_intwin_spec (enable: Z) (adt: RData) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get C_VMCS_PRI_PROC_BASED_CTLS d with
              | Vint ctrls =>
                if zeq enable 1 then
                  let res := Z.lor (Int.unsigned ctrls) PROCBASED_INT_WINDOW_EXITING in
                  let d' := ZMap.set C_VMCS_PRI_PROC_BASED_CTLS (Vint (Int.repr res)) d in
                  Some adt {vmcs: VMCSValid revid abrtid d'}
                else
                  let res := Z.land (Int.unsigned ctrls) NOT_PROCBASED_INT_WINDOW_EXITING in
                  let d' := ZMap.set C_VMCS_PRI_PROC_BASED_CTLS (Vint (Int.repr res)) d in
                  Some adt {vmcs: VMCSValid revid abrtid d'}
              | _ => None
            end
        end
      | _ => None
    end.

  (*
static struct {
	uint32_t selector;
	uint32_t base;
	uint32_t limit;
	uint32_t access;
} seg_encode[10] = {
	[GUEST_CS] = { VMCS_GUEST_CS_SELECTOR, VMCS_GUEST_CS_BASE,
		       VMCS_GUEST_CS_LIMIT, VMCS_GUEST_CS_ACCESS_RIGHTS },
	[GUEST_SS] = { VMCS_GUEST_SS_SELECTOR, VMCS_GUEST_SS_BASE,
		       VMCS_GUEST_SS_LIMIT, VMCS_GUEST_SS_ACCESS_RIGHTS },
	[GUEST_DS] = { VMCS_GUEST_DS_SELECTOR, VMCS_GUEST_DS_BASE,
		       VMCS_GUEST_DS_LIMIT, VMCS_GUEST_DS_ACCESS_RIGHTS },
	[GUEST_ES] = { VMCS_GUEST_ES_SELECTOR, VMCS_GUEST_ES_BASE,
		       VMCS_GUEST_ES_LIMIT, VMCS_GUEST_ES_ACCESS_RIGHTS },
	[GUEST_FS] = { VMCS_GUEST_FS_SELECTOR, VMCS_GUEST_FS_BASE,
		       VMCS_GUEST_FS_LIMIT, VMCS_GUEST_FS_ACCESS_RIGHTS },
	[GUEST_GS] = { VMCS_GUEST_GS_SELECTOR, VMCS_GUEST_GS_BASE,
		       VMCS_GUEST_GS_LIMIT, VMCS_GUEST_GS_ACCESS_RIGHTS },
	[GUEST_LDTR] = { VMCS_GUEST_LDTR_SELECTOR, VMCS_GUEST_LDTR_BASE,
			 VMCS_GUEST_LDTR_LIMIT, VMCS_GUEST_LDTR_ACCESS_RIGHTS },
	[GUEST_TR] = { VMCS_GUEST_TR_SELECTOR, VMCS_GUEST_TR_BASE,
		       VMCS_GUEST_TR_LIMIT, VMCS_GUEST_TR_ACCESS_RIGHTS },
	[GUEST_GDTR] = { 0, VMCS_GUEST_GDTR_BASE, VMCS_GUEST_GDTR_LIMIT, 0 },
	[GUEST_IDTR] = { 0, VMCS_GUEST_IDTR_BASE, VMCS_GUEST_IDTR_LIMIT, 0 },
};

void
vmx_set_desc(unsigned int seg, unsigned int sel, unsigned int base, unsigned int lim, unsigned int ar)
{
	vmcs_write32(seg_encode[seg].base, base);
	vmcs_write32(seg_encode[seg].limit, lim);

	if (seg != GUEST_GDTR && seg != GUEST_IDTR) {
		vmcs_write32(seg_encode[seg].access, ar);
		vmcs_write32(seg_encode[seg].selector, sel);
	}
}
   *)

  Definition aux_zmap_2val_set (k1 v1 k2 v2: Z) (d: ZMap.t val): ZMap.t val :=
    ZMap.set k2 (Vint (Int.repr v2)) (ZMap.set k1 (Vint (Int.repr v1)) d).
  
  Definition aux_zmap_4val_set (k1 v1 k2 v2 k3 v3 k4 v4: Z) (d: ZMap.t val): ZMap.t val :=
    let d1 := aux_zmap_2val_set k1 v1 k2 v2 d in
    aux_zmap_2val_set k3 v3 k4 v4 d1.

  Inductive SegDescType :=
  | SegDesc4 (ebase elim ear esel: Z)
  | SegDesc2 (ebase elim: Z)
  | SegUndef.
  
  Function get_seg_desc_paramter (seg: Z) :=
    match seg with
    | C_GUEST_CS => SegDesc4
                      C_VMCS_GUEST_CS_BASE
                      C_VMCS_GUEST_CS_LIMIT
                      C_VMCS_GUEST_CS_ACCESS_RIGHTS
                      C_VMCS_GUEST_CS_SELECTOR
    | C_GUEST_SS => SegDesc4
                      C_VMCS_GUEST_SS_BASE
                      C_VMCS_GUEST_SS_LIMIT
                      C_VMCS_GUEST_SS_ACCESS_RIGHTS
                      C_VMCS_GUEST_SS_SELECTOR
    | C_GUEST_DS => SegDesc4
                      C_VMCS_GUEST_DS_BASE
                      C_VMCS_GUEST_DS_LIMIT
                      C_VMCS_GUEST_DS_ACCESS_RIGHTS
                      C_VMCS_GUEST_DS_SELECTOR
    | C_GUEST_ES => SegDesc4
                      C_VMCS_GUEST_ES_BASE
                      C_VMCS_GUEST_ES_LIMIT
                      C_VMCS_GUEST_ES_ACCESS_RIGHTS
                      C_VMCS_GUEST_ES_SELECTOR
    | C_GUEST_FS => SegDesc4
                      C_VMCS_GUEST_FS_BASE
                      C_VMCS_GUEST_FS_LIMIT
                      C_VMCS_GUEST_FS_ACCESS_RIGHTS
                      C_VMCS_GUEST_FS_SELECTOR
    | C_GUEST_GS => SegDesc4
                      C_VMCS_GUEST_GS_BASE
                      C_VMCS_GUEST_GS_LIMIT
                      C_VMCS_GUEST_GS_ACCESS_RIGHTS
                      C_VMCS_GUEST_GS_SELECTOR
    | C_GUEST_LDTR => SegDesc4
                        C_VMCS_GUEST_LDTR_BASE
                        C_VMCS_GUEST_LDTR_LIMIT
                        C_VMCS_GUEST_LDTR_ACCESS_RIGHTS
                        C_VMCS_GUEST_LDTR_SELECTOR
    | C_GUEST_TR => SegDesc4
                      C_VMCS_GUEST_TR_BASE
                      C_VMCS_GUEST_TR_LIMIT
                      C_VMCS_GUEST_TR_ACCESS_RIGHTS
                      C_VMCS_GUEST_TR_SELECTOR
    | C_GUEST_GDTR => SegDesc2
                        C_VMCS_GUEST_GDTR_BASE
                        C_VMCS_GUEST_GDTR_LIMIT
    | C_GUEST_IDTR => SegDesc2
                        C_VMCS_GUEST_IDTR_BASE
                        C_VMCS_GUEST_IDTR_LIMIT
    | _ => SegUndef
    end.
     
  Function vmx_set_desc_aux (seg sel base lim ar: Z) (d: ZMap.t val) :=
    match get_seg_desc_paramter seg with
    | SegDesc4 ebase elim ear esel => Some (aux_zmap_4val_set ebase base elim lim ear ar esel sel d)
    | SegDesc2 ebase elim => Some (aux_zmap_2val_set ebase base elim lim d)
    | _ => None
    end.
  
  Function vmx_set_desc_spec (seg sel base lim ar: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match vmx_set_desc_aux seg sel base lim ar d with
              | Some d' => Some adt {vmcs: VMCSValid revid abrtid d'}
              | None => None
            end
        end
      | _ => None
    end.
  
  (*
void
vmx_inject_event(unsigned int type,
		 unsigned int vector, unsigned int errcode, unsigned int ev)
{
	unsigned int intr_info = vmcs_read32(VMCS_ENTRY_INTR_INFO);
	if (intr_info & VMCS_INTERRUPTION_INFO_VALID) {
        KERN_DEBUG("intr_info & VMCS_INTERRUPTION_INFO_VALID is nonzero.\n");
        vmx_dump_info();
        KERN_DEBUG("end of vmx_inject_event error.\n\n\n\n\n\n\n");
		return;
    }

	intr_info = VMCS_INTERRUPTION_INFO_VALID |
		type | vector | ((ev == TRUE ? 1 : 0) << 11);
	vmcs_write32(VMCS_ENTRY_INTR_INFO, intr_info);
	if (ev == 1)
		vmcs_write32(VMCS_ENTRY_EXCEPTION_ERROR, errcode);
}
   *)

  Function vmx_inject_event_spec (type vector errcode ev : Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get C_VMCS_ENTRY_INTR_INFO d with
              | Vint intr_info =>
                let i := Int.unsigned intr_info in
                let is_invalid := Z.land i VMCS_INTERRUPTION_INFO_VALID in
                if zeq is_invalid 0 then
                  let i1 := Z.lor VMCS_INTERRUPTION_INFO_VALID type in
                  let i2 := Z.lor i1 vector in
                  if zeq ev 1 then
                    let i3 := Z.lor i2 VMCS_INTERRUPTION_INFO_EV in 
                    let d1 := ZMap.set C_VMCS_ENTRY_INTR_INFO  (Vint (Int.repr i3)) d in
                    let d2 := ZMap.set C_VMCS_ENTRY_EXCEPTION_ERROR (Vint (Int.repr errcode)) d1 in
                    Some adt {vmcs: VMCSValid revid abrtid d2}
                  else
                    let d1 := ZMap.set C_VMCS_ENTRY_INTR_INFO  (Vint (Int.repr i2)) d in
                    Some adt {vmcs: VMCSValid revid abrtid d1}
                else
                  Some adt
              | _ => None
            end
        end
      | _ => None
    end.
  

  (*
unsigned int
vmx_check_pending_event()
{
	return (vmcs_read32(VMCS_ENTRY_INTR_INFO) &
		VMCS_INTERRUPTION_INFO_VALID) ? 1 : 0;
}*)

  Function vmx_check_pending_event_spec (adt: RData) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get C_VMCS_ENTRY_INTR_INFO d with
              | Vint ctrls =>
                if zeq (Z.land (Int.unsigned ctrls) VMCS_INTERRUPTION_INFO_VALID) 0 then
                  Some 0
                else Some 1
              | _ => None
            end
        end
      | _ => None
    end.


  (*
unsigned int
vmx_check_int_shadow()
{
	return (vmcs_read32(VMCS_GUEST_INTERRUPTIBILITY) &
		(VMCS_INTERRUPTIBILITY_STI_BLOCKING |
		 VMCS_INTERRUPTIBILITY_MOVSS_BLOCKING)) ? 1 : 0;
}*)

  Function vmx_check_int_shadow_spec (adt: RData) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get C_VMCS_GUEST_INTERRUPTIBILITY d with
              | Vint ctrls =>
                if zeq (Z.land (Int.unsigned ctrls) VMCS_INTERRUPTIBILITY_STI_or_MOVSS_BLOCKING) 0 then
                  Some 0
                else Some 1
              | _ => None
            end
        end
      | _ => None
    end.

  (*
unsigned int
vmx_get_exit_reason()
{
    unsigned int exit_reason;

    exit_reason = vmcs_read32(VMCS_EXIT_REASON);

    return (exit_reason & EXIT_REASON_MASK);
}
   *)

  Function vmx_get_exit_reason_spec (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get C_VMCS_EXIT_REASON d with
              | Vint r => Some (Z.land (Int.unsigned r) EXIT_REASON_MASK)
              | _ => None
            end
        end
      | _ => None
    end.

  (*
void
vmx_set_tsc_offset(uint64_t tsc_offset)
{
   vmcs_write64(VMCS_TSC_OFFSET, tsc_offset);
}
   *)

  Function vmx_set_tsc_offset_spec (tsc_offset: Z64) (adt: RData) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            Some adt {vmcs: VMCSValid revid abrtid (write64_aux C_VMCS_TSC_OFFSET tsc_offset d)}
        end
      | _ => None
    end.

  (*
FIXMe: this is read64, but doesn't make sense

uint64_t
vmx_get_tsc_offset(void)
{
   return vmcs_read64(VMCS_TSC_OFFSET);
}
   *)

  Function vmx_get_tsc_offset_spec (adt: RData): option Z64 :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
          | VMCSValid revid abrtid d =>
            match ZMap.get C_VMCS_TSC_OFFSET d, ZMap.get (C_VMCS_TSC_OFFSET + 1) d with
              | Vint v1, Vint v2 => Some (VZ64 (Z64ofwords (Int.unsigned v2) (Int.unsigned v1)))
              | _ , _ => None
            end
        end
      | _ => None
    end.

  (*
FIXMe: this is read64, but doesn't make sense

unsigned int
vmx_get_exit_fault_addr(void)
{
    return (uintptr_t) vmcs_read64(VMCS_GUEST_PHYSICAL_ADDRESS);
}
   *)

  Function vmx_get_exit_fault_addr_spec (adt: RData): option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match vmcs adt with
        | VMCSValid revid abrtid d =>
          match ZMap.get C_VMCS_GUEST_PHYSICAL_ADDRESS d with
              | Vint v => Some (Int.unsigned v)
              | _ => None
          end
        end
      | _ => None
    end.

(*
static gcc_inline uint64_t
rdmsr(uint32_t msr)
{
	uint64_t rv;
	__asm __volatile("rdmsr" : "=A" (rv) : "c" (msr));
	return rv;
}
*)  
  Function rdmsr_spec (r: Z) (adt: RData) : option Z64 :=
    match (ikern adt, ihost adt) with
      | (true, true) => Some (VZ64 0)
      | _ => None
    end.

(*
static gcc_inline void
wrmsr(uint32_t msr, uint64_t newval)
{
        __asm __volatile("wrmsr" : : "A" (newval), "c" (msr));
}
*)
  Function wrmsr_spec (r: Z) (v: Z64) (adt: RData) := 
    match (ikern adt, ihost adt) with
      | (true, true) => Some 0
      | _ => None
    end.

(*
static gcc_inline uint32_t
rcr3(void)
{
    uint32_t val;
    __asm __volatile("movl %%cr3,%0" : "=r" (val));
    return val;
}*)

  Function rcr0_spec (adt: RData) := 
    match (ikern adt, ihost adt) with
      | (true, true) => Some 0
      | _ => None
    end.

  Function rcr3_spec (adt: RData) := 
    match (ikern adt, ihost adt) with
      | (true, true) => Some 0
      | _ => None
    end.

  Function rcr4_spec (adt: RData) := 
    match (ikern adt, ihost adt) with
      | (true, true) => Some 0
      | _ => None
    end.

(*static gcc_inline void
vmptrld(struct vmcs *vmcs)
{
	int error;
	uint64_t addr;

	addr = (uintptr_t) vmcs | 0ULL;

	__asm __volatile("vmptrld %0" : : "m" (*(uint64_t *) &addr)
			 : "cc", "memory");

	VMX_SET_ERROR_CODE(error);
	if (error)
		KERN_PANIC("vmptrld error %d", error);
}*)

  Function vmptrld_spec (adt: RData) := 
    match (ikern adt, ihost adt) with
      | (true, true) => Some adt
      | _ => None
    end.


  (*
// Host Rip: vmx_return_from_guest
void
vmcs_set_defaults( uint32_t pinbased_ctls,
          uint32_t procbased_ctls, uint32_t procbased_ctls2,
          uint32_t exit_ctls, uint32_t entry_ctls,
          uint16_t vpid, uint64_t cr0_ones_mask, uint64_t cr0_zeros_mask,
          uint64_t cr4_ones_mask, uint64_t cr4_zeros_mask)
{
    extern gatedesc_t idt[]; // make it global

    vmptrld(vmcs); //

    /*
     * Load the VMX controls
     */
    vmcs_write32(VMCS_PIN_BASED_CTLS, pinbased_ctls);
    vmcs_write32(VMCS_PRI_PROC_BASED_CTLS, procbased_ctls);
    vmcs_write32(VMCS_SEC_PROC_BASED_CTLS, procbased_ctls2);
    vmcs_write32(VMCS_EXIT_CTLS, exit_ctls);
    vmcs_write32(VMCS_ENTRY_CTLS, entry_ctls);

    /*
     * Load host state. (Intel Software Developer's Manual Vol 3, Sec 24.5)
     */
    /* host rip */
    vmcs_write32(VMCS_HOST_RIP, host_rip);

    /* host control registers */
    vmcs_write32(VMCS_HOST_CR0, rcr0());
    vmcs_write32(VMCS_HOST_CR3, rcr3());
    vmcs_write32(VMCS_HOST_CR4, rcr4());

    /* host segment selectors */
    vmcs_write16(VMCS_HOST_ES_SELECTOR, CPU_GDT_KDATA);
    vmcs_write16(VMCS_HOST_CS_SELECTOR, CPU_GDT_KCODE);
    vmcs_write16(VMCS_HOST_SS_SELECTOR, CPU_GDT_KDATA);
    vmcs_write16(VMCS_HOST_DS_SELECTOR, CPU_GDT_KDATA);
    vmcs_write16(VMCS_HOST_FS_SELECTOR, CPU_GDT_KDATA);
    vmcs_write16(VMCS_HOST_GS_SELECTOR, CPU_GDT_KDATA);
    vmcs_write16(VMCS_HOST_TR_SELECTOR, CPU_GDT_TSS);

    /* host segment base address */
    vmcs_write32(VMCS_HOST_FS_BASE, 0);
    vmcs_write32(VMCS_HOST_GS_BASE, 0);
    vmcs_write32(VMCS_HOST_TR_BASE, (uintptr_t) &tss);
    vmcs_write32(VMCS_HOST_GDTR_BASE, (uintptr_t) &gdt);
    vmcs_write32(VMCS_HOST_IDTR_BASE, (uintptr_t) idt);

    /* host control registers */
    vmcs_write32(VMCS_HOST_IA32_SYSENTER_CS, rdmsr(MSR_IA32_SYSENTER_CS));
    vmcs_write32(VMCS_HOST_IA32_SYSENTER_ESP, rdmsr(MSR_IA32_SYSENTER_ESP));
    vmcs_write32(VMCS_HOST_IA32_SYSENTER_EIP, rdmsr(MSR_IA32_SYSENTER_EIP));
    vmcs_write64(VMCS_HOST_IA32_PERF_GLOBAL_CTRL,
             rdmsr(MSR_IA32_PERF_GLOBAL_CTRL));
    vmcs_write64(VMCS_HOST_IA32_PAT, rdmsr(MSR_PAT));
    vmcs_write64(VMCS_HOST_IA32_EFER, rdmsr(MSR_EFER));

    /*
     * Load guest state. (Intel Software Developer's Manual Vol3, Sec 24.4,
     * Sec 9.1)
     */
    /* guest control registers */

    vmcs_write32(VMCS_GUEST_CR0, 0x60000010 | CR0_NE);
    vmcs_write32(VMCS_GUEST_CR3, 0);
    vmcs_write32(VMCS_GUEST_CR4, CR4_VMXE);

    /* guest debug registers */
    vmcs_write32(VMCS_GUEST_DR7, 0x00000400);

    /* guest MSRs */
    vmcs_write64(VMCS_GUEST_IA32_PAT, 0x7040600070406ULL);
    vmcs_write32(VMCS_GUEST_IA32_SYSENTER_CS, 0);
    vmcs_write32(VMCS_GUEST_IA32_SYSENTER_ESP, 0);
    vmcs_write32(VMCS_GUEST_IA32_SYSENTER_EIP, 0);
    vmcs_write64(VMCS_GUEST_IA32_DEBUGCTL, 0);

    /* EPTP */
    vmcs_write64(VMCS_EPTP, EPTP((uintptr_t) pml4ept));

    /* VPID */
    vmcs_write16(VMCS_VPID, vpid);

    /* exception bitmap */
    /* vmcs_write32(VMCS_EXCEPTION_BITMAP, (1 << T_MCHK)); */

#ifdef DEBUG_GUEST_SINGLE_STEP
    vmcs_write32(VMCS_EXCEPTION_BITMAP, (1 << T_DEBUG));
#endif

    /* MSR bitmap */
    vmcs_write64(VMCS_MSR_BITMAP, (uintptr_t) msr_bitmap);

    /* link pointer */
    vmcs_write64(VMCS_LINK_POINTER, 0xffffffffffffffffULL);

    /* CR0 mask & shadow */
    vmcs_write32(VMCS_CR0_MASK, cr0_ones_mask | cr0_zeros_mask);
    vmcs_write32(VMCS_CR0_SHADOW, cr0_ones_mask);

    /* CR4 mask & shadow */
    vmcs_write32(VMCS_CR4_MASK, cr4_ones_mask | cr4_zeros_mask);
    vmcs_write32(VMCS_CR4_SHADOW, cr4_ones_mask);

    /* I/O bitmap */
    vmcs_write64(VMCS_IO_BITMAP_A, (uintptr_t) io_bitmap_a);
    vmcs_write64(VMCS_IO_BITMAP_B, (uintptr_t) io_bitmap_b);

    /* others */
    vmcs_write32(VMCS_GUEST_ACTIVITY, 0);
    vmcs_write32(VMCS_GUEST_INTERRUPTIBILITY, 0);
    vmcs_write32(VMCS_GUEST_PENDING_DBG_EXCEPTIONS, 0);
    vmcs_write32(VMCS_ENTRY_INTR_INFO, 0);
}

#define	EPT_PWLEVELS	4		/* page walk levels */
#define PAT_WRITE_BACK      0x06
#define	EPTP(pml4)	((pml4) | (EPT_PWLEVELS - 1) << 3 | PAT_WRITE_BACK)
define T_MCHK		18	
   *)

  Function vmcs_set_defaults_spec (mbi_adr:Z)
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
      | _ => None
    end.

End OBJ_VMCS.

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

  Context {re1: relate_impl_iflags}.
  Context {re2: relate_impl_vmcs}.

  Lemma val_inject_vint_eq:
    forall f n v v' i,
      val_inject f (ZMap.get n v) (ZMap.get n v')
      -> ZMap.get n v = Vint i
      -> ZMap.get n v' = Vint i.
  Proof.
    intros.
    rewrite H0 in H; inversion H; reflexivity.
  Qed.

  Lemma rdmsr_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem rdmsr_spec)
          (id ↦ gensem rdmsr_spec).
  Proof.
    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    unfold rdmsr_spec in *.
    exploit relate_impl_iflags_eq; eauto. inversion 1.
    revert H2; subrewrite. subdestruct.

    inv HQ; trivial.
  Qed.

  Lemma wrmsr_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem wrmsr_spec)
          (id ↦ gensem wrmsr_spec).
  Proof.
    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    unfold wrmsr_spec in *.
    exploit relate_impl_iflags_eq; eauto. inversion 1.
    revert H2; subrewrite. subdestruct.

    inv HQ; trivial.
  Qed.

  Lemma vmcs_readz_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem vmcs_readz_spec)
          (id ↦ gensem vmcs_readz_spec).
  Proof.
    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    unfold vmcs_readz_spec in *.
    exploit relate_impl_iflags_eq; eauto. inversion 1.
    exploit relate_impl_vmcs_eq; eauto. intros.
    revert H2; inversion H0; subrewrite. subdestruct.

    erewrite val_inject_vint_eq; eauto.
    inv HQ; trivial.
  Qed.

  Section VMCS_WRITEZ_SIM.

    Lemma vmcs_writez_exist:
      forall s habd habd' labd enc value f,
        vmcs_writez_spec enc value habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', vmcs_writez_spec enc value labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmcs_writez_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H2. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_vmcs_update; try assumption.
      apply VMCS_inj_set_int. rewrite H, H4; auto.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmcs}.

    Lemma vmcs_writez_match:
      forall s d d' m enc value f,
        vmcs_writez_spec enc value d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmcs_writez_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_vmcs_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmcs_writez_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmcs_writez_spec}.

    Lemma vmcs_writez_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmcs_writez_spec)
            (id ↦ gensem vmcs_writez_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmcs_writez_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmcs_writez_match; eauto.
    Qed.

  End VMCS_WRITEZ_SIM.

  Lemma vmcs_readz64_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem vmcs_readz64_spec)
          (id ↦ gensem vmcs_readz64_spec).
  Proof.
    Local Opaque Z.shiftl.

    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    unfold vmcs_readz64_spec in *.
    exploit relate_impl_iflags_eq; eauto. inversion 1.
    exploit relate_impl_vmcs_eq; eauto. intros.
    revert H2. inversion H0. subrewrite. subdestruct.

    erewrite 2 val_inject_vint_eq; eauto.
    inv HQ; trivial.
  Qed.

  Section VMCS_WRITEZ64_SIM.

    Lemma vmcs_writez64_exist:
      forall s habd habd' labd enc value f,
        vmcs_writez64_spec enc value habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', vmcs_writez64_spec enc value labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmcs_writez64_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H2. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_vmcs_update; try assumption.
      repeat apply VMCS_inj_set_int.
      rewrite H, H4; auto.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmcs}.

    Lemma vmcs_writez64_match:
      forall s d d' m enc value f,
        vmcs_writez64_spec enc value d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmcs_writez64_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_vmcs_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmcs_writez64_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmcs_writez64_spec}.

    Lemma vmcs_writez64_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmcs_writez64_spec)
            (id ↦ gensem vmcs_writez64_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmcs_writez64_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmcs_writez64_match; eauto.
    Qed.

  End VMCS_WRITEZ64_SIM.

  Section VMX_SET_INTERCEPT_INTWIN_SIM.

    Lemma vmx_set_intercept_intwin_exist:
      forall s habd habd' labd enable f,
        vmx_set_intercept_intwin_spec enable habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', vmx_set_intercept_intwin_spec enable labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmx_set_intercept_intwin_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H2. subrewrite.

      (* Manually unfold to delimit subdestruct until the [ZMap.get], whose
         argument [v] couldn't be changed to [v'] mismatching that in
         the goal. *)
      destruct (ikern labd) eqn:Hdestruct; contra_inv;
      destruct (pg labd) eqn:Hdestruct1; contra_inv;
      destruct (ihost labd) eqn:Hdestruct2; contra_inv;
      destruct (ZMap.get C_VMCS_PRI_PROC_BASED_CTLS v) eqn:Hdestruct3; contra_inv.
      erewrite val_inject_vint_eq; eauto.
      subdestruct.

      - inv HQ; refine_split'. trivial.
        apply relate_impl_vmcs_update; try assumption.
        apply VMCS_inj_set_int.
        rewrite H, H4; auto.
      - inv HQ; refine_split'. trivial.
        apply relate_impl_vmcs_update; try assumption.
        apply VMCS_inj_set_int.
        rewrite H, H4; auto.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmcs}.

    Lemma vmx_set_intercept_intwin_match:
      forall s d d' m enable f,
        vmx_set_intercept_intwin_spec enable d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_set_intercept_intwin_spec; intros.
      subdestruct; inv H; trivial;
      eapply match_impl_vmcs_update; assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmx_set_intercept_intwin_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmx_set_intercept_intwin_spec}.

    Lemma vmx_set_intercept_intwin_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_set_intercept_intwin_spec)
            (id ↦ gensem vmx_set_intercept_intwin_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmx_set_intercept_intwin_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmx_set_intercept_intwin_match; eauto.
    Qed.

  End VMX_SET_INTERCEPT_INTWIN_SIM.

  Section VMX_SET_DESC_SIM.

    Lemma vmx_set_desc_exist:
      forall s habd habd' labd seg sel base lim ar f,
        vmx_set_desc_spec seg sel base lim ar habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', vmx_set_desc_spec seg sel base lim ar labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmx_set_desc_spec, vmx_set_desc_aux; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H2. subrewrite.
      subdestruct;
        inv HQ; refine_split';
        (trivial || apply relate_impl_vmcs_update;
         try assumption; repeat apply VMCS_inj_set_int;
         rewrite H, H4; auto ).
    Qed.
    
    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmcs}.

    Lemma vmx_set_desc_match:
      forall s d d' m seg sel base lim ar f,
        vmx_set_desc_spec seg sel base lim ar d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_set_desc_spec, vmx_set_desc_aux; intros.
      subdestruct; inv H; trivial;
      eapply match_impl_vmcs_update; assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmx_set_desc_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmx_set_desc_spec}.

    Lemma vmx_set_desc_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_set_desc_spec)
            (id ↦ gensem vmx_set_desc_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmx_set_desc_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmx_set_desc_match; eauto.
    Qed.

  End VMX_SET_DESC_SIM.

  Section VMX_INJECT_EVENT_SIM.

    Lemma vmx_inject_event_exist:
      forall s habd habd' labd type vector errcode ev f,
        vmx_inject_event_spec type vector errcode ev habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', vmx_inject_event_spec type vector errcode ev labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.land Z.lor.

      unfold vmx_inject_event_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H2. subrewrite.

      (* Manually unfold to delimit subdestruct until the [ZMap.get], whose
         argument [v] couldn't be changed to [v'] mismatching that in
         the goal. *)
      destruct (ikern labd) eqn:Hdestruct; contra_inv;
      destruct (pg labd) eqn:Hdestruct1; contra_inv;
      destruct (ihost labd) eqn:Hdestruct2; contra_inv;
      destruct (ZMap.get C_VMCS_ENTRY_INTR_INFO  v) eqn:Hdestruct3; contra_inv.
      erewrite val_inject_vint_eq; eauto.
      subdestruct; inv HQ; refine_split'; trivial.
      - apply relate_impl_vmcs_update; try assumption.
        repeat apply VMCS_inj_set_int.
        rewrite H, H4; auto.
      - apply relate_impl_vmcs_update; try assumption.
        repeat apply VMCS_inj_set_int.
        rewrite H, H4; auto.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmcs}.

    Lemma vmx_inject_event_match:
      forall s d d' m type vecter errcode ev f,
        vmx_inject_event_spec type vecter errcode ev d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_inject_event_spec; intros.
      subdestruct; inv H; trivial;
      eapply match_impl_vmcs_update; assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmx_inject_event_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmx_inject_event_spec}.

    Lemma vmx_inject_event_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_inject_event_spec)
            (id ↦ gensem vmx_inject_event_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmx_inject_event_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmx_inject_event_match; eauto.
    Qed.

  End VMX_INJECT_EVENT_SIM.

  Section VMX_SET_TSC_OFFSET_SIM.

    Lemma vmx_set_tsc_offset_exist:
      forall s habd habd' labd tsc_offset f,
        vmx_set_tsc_offset_spec tsc_offset habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', vmx_set_tsc_offset_spec tsc_offset labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmx_set_tsc_offset_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. inversion H2. subrewrite. subdestruct.

      inv HQ; refine_split'; trivial.
      apply relate_impl_vmcs_update; try assumption.
      repeat apply VMCS_inj_set_int.
      rewrite H, H4; auto.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmcs}.

    Lemma vmx_set_tsc_offset_match:
      forall s d d' m tsc_offset f,
        vmx_set_tsc_offset_spec tsc_offset d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmx_set_tsc_offset_spec; intros.
      subdestruct; inv H; trivial;
      eapply match_impl_vmcs_update; assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) vmx_set_tsc_offset_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmx_set_tsc_offset_spec}.

    Lemma vmx_set_tsc_offset_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_set_tsc_offset_spec)
            (id ↦ gensem vmx_set_tsc_offset_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmx_set_tsc_offset_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmx_set_tsc_offset_match; eauto.
    Qed.

  End VMX_SET_TSC_OFFSET_SIM.

  Section GET_TSC_SIM.

    Lemma vmx_get_tsc_offset_exists:
      forall habd labd z s f,
        vmx_get_tsc_offset_spec habd = Some z ->
        relate_AbData s f habd labd ->
        vmx_get_tsc_offset_spec labd = Some z.
    Proof.
      unfold vmx_get_tsc_offset_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv H2. 
      erewrite 2 val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_tsc_offset_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_tsc_offset_spec)
            (id ↦ gensem vmx_get_tsc_offset_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite vmx_get_tsc_offset_exists; eauto.
      reflexivity.
    Qed.

  End GET_TSC_SIM.

  Section GET_REASON_SIM.

    Lemma vmx_get_exit_reason_exists:
      forall habd labd z s f,
        vmx_get_exit_reason_spec habd = Some z ->
        relate_AbData s f habd labd ->
        vmx_get_exit_reason_spec labd = Some z.
    Proof.
      unfold vmx_get_exit_reason_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv H2. 
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_exit_reason_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_exit_reason_spec)
            (id ↦ gensem vmx_get_exit_reason_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite vmx_get_exit_reason_exists; eauto.
      reflexivity.
    Qed.

  End GET_REASON_SIM.

  Section GET_FAULT_SIM.

    Lemma vmx_get_exit_fault_addr_exists:
      forall habd labd z s f,
        vmx_get_exit_fault_addr_spec habd = Some z ->
        relate_AbData s f habd labd ->
        vmx_get_exit_fault_addr_spec labd = Some z.
    Proof.
      unfold vmx_get_exit_fault_addr_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv H2. 
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_get_exit_fault_addr_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_get_exit_fault_addr_spec)
            (id ↦ gensem vmx_get_exit_fault_addr_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite vmx_get_exit_fault_addr_exists; eauto.
      reflexivity.
    Qed.

  End GET_FAULT_SIM.

  Section CHECK_PEND_SIM.

    Lemma vmx_check_pending_event_exists:
      forall habd labd z s f,
        vmx_check_pending_event_spec habd = Some z ->
        relate_AbData s f habd labd ->
        vmx_check_pending_event_spec labd = Some z.
    Proof.
      unfold vmx_check_pending_event_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. subrewrite.
      destruct (ikern labd) eqn:Hdestruct; contra_inv.
      destruct (pg labd) eqn:Hdestruct1; contra_inv.
      destruct (ihost labd) eqn:Hdestruct2; contra_inv.
      destruct (vmcs habd). inv H2.
      destruct (ZMap.get C_VMCS_ENTRY_INTR_INFO data1) eqn:Hdestruct3; contra_inv.
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_check_pending_event_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_check_pending_event_spec)
            (id ↦ gensem vmx_check_pending_event_spec).
    Proof.
      Local Opaque Z.land.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite vmx_check_pending_event_exists; eauto.
      reflexivity.
    Qed.

  End CHECK_PEND_SIM.

  Section CHECK_INT_SIM.

    Lemma vmx_check_int_shadow_exists:
      forall habd labd z s f,
        vmx_check_int_shadow_spec habd = Some z ->
        relate_AbData s f habd labd ->
        vmx_check_int_shadow_spec labd = Some z.
    Proof.
      unfold vmx_check_int_shadow_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. subrewrite.
      destruct (ikern labd) eqn:Hdestruct; contra_inv.
      destruct (pg labd) eqn:Hdestruct1; contra_inv.
      destruct (ihost labd) eqn:Hdestruct2; contra_inv.
      destruct (vmcs habd). inv H2. 
      destruct (ZMap.get C_VMCS_GUEST_INTERRUPTIBILITY data1) eqn:Hdestruct3; contra_inv.
      erewrite val_inject_vint_eq; eauto.
    Qed.

    Lemma vmx_check_int_shadow_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmx_check_int_shadow_spec)
            (id ↦ gensem vmx_check_int_shadow_spec).
    Proof.
      Local Opaque Z.land.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite vmx_check_int_shadow_exists; eauto.
      reflexivity.
    Qed.

  End CHECK_INT_SIM.

  Section VMPTRLD_SIM.

    Lemma vmptrld_exists:
      forall habd habd' labd s f,
        vmptrld_spec habd = Some habd' ->
        relate_AbData s f habd labd ->
        exists labd', vmptrld_spec labd = Some labd' /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmptrld_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      revert H. subrewrite. subdestruct.

      inv HQ; refine_split'; trivial.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {inv: PreservesInvariants (HD:= data) vmptrld_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) vmptrld_spec}.
    
    Lemma vmptrld_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem vmptrld_spec)
            (id ↦ gensem vmptrld_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmptrld_exists; eauto.
      intro tmp; destruct tmp.
      destruct H.
      match_external_states_simpl.
      unfold vmptrld_spec in H1.
      subdestruct.
      inversion H1; subst.
      assumption.
    Qed.
    
  End VMPTRLD_SIM.

  Section VMCS_SET_DEFAULTS_SIM.

    Context `{real_params: RealParams}.

    Context {re3: relate_impl_ept}.
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
    Context {re17: relate_impl_AC}.

    Let block_inject_neutral f b :=
      forall ofs, val_inject f (Vptr b ofs) (Vptr b ofs).

    Lemma vmcs_set_defaults_exist:
      forall s habd habd' labd mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b f,
        vmcs_set_defaults_spec mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b habd = Some habd'
        -> relate_AbData s f habd labd
        -> block_inject_neutral f pm4ept_b
        -> block_inject_neutral f tss_b
        -> block_inject_neutral f gdt_b
        -> block_inject_neutral f idt_b
        -> block_inject_neutral f msr_bitmap_b
        -> block_inject_neutral f io_bitmap_b
        -> block_inject_neutral f host_rip_b
        -> exists labd', vmcs_set_defaults_spec mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold vmcs_set_defaults_spec; intros.
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
      exploit relate_impl_vmcs_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

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
        unfold real_vmcs.
        repeat (apply VMCS_inj_set_int || apply VMCS_inj_set);
          try rewrite H; auto.
        econstructor.
        assumption.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_vmcs}.
    Context {mt3: match_impl_ept}.
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
    Context {mt17: match_impl_AC}.

    Lemma vmcs_set_defaults_match:
      forall s d d' m mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b f,
        vmcs_set_defaults_spec mbi_adr pm4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold vmcs_set_defaults_spec; intros.
      subdestruct; inv H; trivial.
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

    Context {inv: VMCSSetDefaultsInvariants (data_ops := data_ops) vmcs_set_defaults_spec}.
    Context {inv0: VMCSSetDefaultsInvariants (data_ops := data_ops0) vmcs_set_defaults_spec}.

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

    Lemma vmcs_set_defaults_sim :
      forall id,
        sim (crel RData RData) (id ↦ vmcs_set_defaults_compatsem vmcs_set_defaults_spec)
            (id ↦ vmcs_set_defaults_compatsem vmcs_set_defaults_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit vmcs_set_defaults_exist; eauto 2 using inject_incr_block_inject_neutral.

      intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply vmcs_set_defaults_match; eauto.
    Qed.

  End VMCS_SET_DEFAULTS_SIM.

End OBJ_SIM.
