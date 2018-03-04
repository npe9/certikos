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
Require Export AuxStateDataType.
Require Import Constant.
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import XOmega.
Require Import CLemmas.
Require Import INVLemmaIntel.
Require Import Values.
Require Import liblayers.compat.CompatGenSem.

Section REAL_EPT.

  Function Calculate_EPDTE_at_j (i: Z) (j: Z) (ept: EPT) : EPT :=
    match ZMap.get 0 ept with
      | EPML4EValid epdpt => 
        match ZMap.get i epdpt with
          | EPDPTEValid epdt => 
            ZMap.set 0 (EPML4EValid (ZMap.set i (EPDPTEValid (ZMap.set j (EPDTEValid (ZMap.init EPTEUndef)) epdt)) epdpt)) ept
          | _ => ept
        end
      | _ => ept
    end.

  Fixpoint Calculate_EPDTE (i: Z) (j: nat) (ept: EPT) : EPT := 
    match j with
      | O => Calculate_EPDTE_at_j i 0 ept
      | S k => Calculate_EPDTE_at_j i (Z.of_nat (S k)) (Calculate_EPDTE i k ept)
    end.


  Function Calculate_EPDPTE_at_i (i: Z) (ept: EPT) : EPT :=
    match ZMap.get 0 ept with
      | EPML4EValid epdpt => 
        Calculate_EPDTE i 511 (ZMap.set 0 (EPML4EValid (ZMap.set i (EPDPTEValid (ZMap.init EPDTEUndef)) epdpt)) ept)
      | _ => ept
    end.
  Fixpoint Calculate_EPDPTE (i: nat) (ept: EPT) : EPT := 
    match i with
      | O => Calculate_EPDPTE_at_i 0 ept
      | S k => Calculate_EPDPTE_at_i (Z.of_nat (S k)) (Calculate_EPDPTE k ept)
    end.

  Definition real_ept (ept: EPT) := Calculate_EPDPTE 3 (ZMap.set 0 (EPML4EValid (ZMap.init EPDPTEUndef)) ept).

End REAL_EPT.

Section REAL_VMCS.

  Definition write64_aux (enc: Z) (value: Z64) (d: ZMap.t val) : ZMap.t val :=
    let d1 := ZMap.set enc (Vint (Int64.loword (Int64.repr (Z642Z value)))) d in
    ZMap.set (enc + 1) (Vint (Int64.hiword (Int64.repr (Z642Z value)))) d1.

  Definition write64_block_aux (enc: Z) (value: val) (d: ZMap.t val) : ZMap.t val :=
    let d1 := ZMap.set enc value d in
    ZMap.set (enc + 1) Vzero d1.

  Definition real_vmcs (vm: VMCS) (vmi: VMXInfo) (pml4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b host_rip_b: block):=
    match vm with
      | VMCSValid revid abrtid m =>

        let pinbased_ctls := ZMap.get (VMX_INFO_PINBASED_CTLS) vmi in
        let procbased_ctls := ZMap.get (VMX_INFO_PROCBASED_CTLS) vmi in
        let procbased_ctls2 := ZMap.get (VMX_INFO_PROCBASED_CTLS2) vmi in
        let exit_ctls := ZMap.get (VMX_INFO_EXIT_CTLS) vmi in
        let entry_ctls := ZMap.get (VMX_INFO_ENTRY_CTLS) vmi in
        let cr0_ones_mask := ZMap.get (VMX_INFO_CR0_ONES_MASK) vmi in
        let cr0_zeros_mask := ZMap.get (VMX_INFO_CR0_ZEROS_MASK) vmi in
        let cr4_ones_mask := ZMap.get (VMX_INFO_CR4_ONES_MASK) vmi in
        let cr4_zeros_mask := ZMap.get (VMX_INFO_CR4_ZEROS_MASK) vmi in

        let m1 := ZMap.set C_VMCS_PIN_BASED_CTLS (Vint (Int.repr pinbased_ctls)) m in
        let m2 := ZMap.set C_VMCS_PRI_PROC_BASED_CTLS (Vint (Int.repr procbased_ctls)) m1 in
        let m3 := ZMap.set C_VMCS_SEC_PROC_BASED_CTLS (Vint (Int.repr procbased_ctls2)) m2 in
        let m4 := ZMap.set C_VMCS_EXIT_CTLS (Vint (Int.repr exit_ctls)) m3 in
        let m5 := ZMap.set C_VMCS_ENTRY_CTLS (Vint (Int.repr entry_ctls)) m4 in

        let m6 := ZMap.set C_VMCS_HOST_RIP (Vptr host_rip_b Int.zero) m5 in

        (*rcr0_spec adt*)
        let m7 := ZMap.set C_VMCS_HOST_CR0 Vzero m6 in
        (*rcr3_spec adt*)
        let m8 := ZMap.set C_VMCS_HOST_CR3 Vzero m7 in
        (*rcr4_spec adt*)
        let m9 := ZMap.set C_VMCS_HOST_CR4 Vzero m8 in

        let m10 := ZMap.set C_VMCS_HOST_ES_SELECTOR (Vint (Int.repr CPU_GDT_KDATA)) m9 in
        let m11 := ZMap.set C_VMCS_HOST_CS_SELECTOR (Vint (Int.repr CPU_GDT_KCODE)) m10 in
        let m12 := ZMap.set C_VMCS_HOST_SS_SELECTOR (Vint (Int.repr CPU_GDT_KDATA)) m11 in
        let m13 := ZMap.set C_VMCS_HOST_DS_SELECTOR (Vint (Int.repr CPU_GDT_KDATA)) m12 in
        let m14 := ZMap.set C_VMCS_HOST_FS_SELECTOR (Vint (Int.repr CPU_GDT_KDATA)) m13 in
        let m15 := ZMap.set C_VMCS_HOST_GS_SELECTOR (Vint (Int.repr CPU_GDT_KDATA)) m14 in
        let m16 := ZMap.set C_VMCS_HOST_TR_SELECTOR (Vint (Int.repr CPU_GDT_TSS)) m15 in

        let m17 := ZMap.set C_VMCS_HOST_FS_BASE Vzero m16 in
        let m18 := ZMap.set C_VMCS_HOST_GS_BASE Vzero m17 in

        let m19 := ZMap.set C_VMCS_HOST_TR_BASE (Vptr tss_b Int.zero) m18 in
        let m20 := ZMap.set C_VMCS_HOST_GDTR_BASE (Vptr gdt_b Int.zero) m19 in
        let m21 := ZMap.set C_VMCS_HOST_IDTR_BASE (Vptr idt_b Int.zero) m20 in

        (* rdmsr_spec MSR_IA32_SYSENTER_CS adt *)
        let m22 := ZMap.set C_VMCS_HOST_IA32_SYSENTER_CS Vzero m21 in
        (*rdmsr_spec MSR_IA32_SYSENTER_ESP adt*)
        let m23 := ZMap.set C_VMCS_HOST_IA32_SYSENTER_ESP Vzero m22 in
        (*rdmsr_spec MSR_IA32_SYSENTER_EIP adt*)
        let m24 := ZMap.set C_VMCS_HOST_IA32_SYSENTER_EIP Vzero m23 in
        (*rdmsr_spec MSR_IA32_PERF_GLOBAL_CTRL adt*)
        let m25 := write64_aux C_VMCS_HOST_IA32_PERF_GLOBAL_CTRL (VZ64 0) m24 in
        (*rdmsr_spec MSR_PAT adt*)
        let m26 := write64_aux C_VMCS_HOST_IA32_PAT (VZ64 0) m25 in
        (*rdmsr_spec MSR_EFER adt*)
        let m27 := write64_aux C_VMCS_HOST_IA32_EFER (VZ64 0) m26 in

        let m28 := ZMap.set C_VMCS_GUEST_CR0 (Vint (Int.repr (Z.lor v0x60000010 CR0_NE))) m27 in
        let m29 := ZMap.set C_VMCS_GUEST_CR3 Vzero m28 in
        let m30 := ZMap.set C_VMCS_GUEST_CR4 (Vint (Int.repr CR4_VMXE)) m29 in
        let m31 := ZMap.set C_VMCS_GUEST_DR7 (Vint (Int.repr v0x00000400)) m30 in

        let m32 := write64_aux C_VMCS_GUEST_IA32_PAT (VZ64 v0x7040600070406) m31 in
        let m33 := ZMap.set C_VMCS_GUEST_IA32_SYSENTER_CS Vzero m32 in
        let m34 := ZMap.set C_VMCS_GUEST_IA32_SYSENTER_ESP Vzero m33 in
        let m35 := ZMap.set C_VMCS_GUEST_IA32_SYSENTER_EIP Vzero m34 in
        let m36 := write64_aux C_VMCS_GUEST_IA32_DEBUGCTL (VZ64 0) m35 in
        (*FIXME: it should be 64 bits*)
        let m37 := write64_block_aux C_VMCS_EPTP (Vptr pml4ept_b (Int.repr EPTP_pml4)) m36 in

        let m38 := ZMap.set C_VMCS_VPID Vone m37 in
(*        let m38' := ZMap.set C_VMCS_EXCEPTION_BITMAP (Vint (Int.repr T_MCHK_SHIFT)) m38 in *)
        let m39 := write64_block_aux C_VMCS_MSR_BITMAP (Vptr msr_bitmap_b Int.zero) m38 in
        let m40 := write64_aux C_VMCS_LINK_POINTER (VZ64 v0xffffffffffffffff) m39 in
        let m41 := ZMap.set C_VMCS_CR0_MASK (Vint (Int.repr (Z.lor cr0_ones_mask cr0_zeros_mask))) m40 in
        let m42 := ZMap.set C_VMCS_CR0_SHADOW (Vint (Int.repr cr0_ones_mask)) m41 in
        let m43 := ZMap.set C_VMCS_CR4_MASK (Vint (Int.repr (Z.lor cr4_ones_mask cr4_zeros_mask))) m42 in
        let m44 := ZMap.set C_VMCS_CR4_SHADOW (Vint (Int.repr cr4_ones_mask)) m43 in
        let m45 := write64_block_aux C_VMCS_IO_BITMAP_A (Vptr io_bitmap_b Int.zero) m44 in
        let m46 := write64_block_aux C_VMCS_IO_BITMAP_B (Vptr io_bitmap_b (Int.repr PgSize)) m45 in

        let m47 := ZMap.set C_VMCS_GUEST_ACTIVITY Vzero m46 in
        let m48 := ZMap.set C_VMCS_GUEST_INTERRUPTIBILITY Vzero m47 in
        let m49 := ZMap.set C_VMCS_GUEST_PENDING_DBG_EXCEPTIONS Vzero m48 in
        let m50 := ZMap.set C_VMCS_ENTRY_INTR_INFO Vzero m49 in

        let revid1 := Vzero in
        VMCSValid revid1 abrtid m50
    end.

  Lemma real_vmcs_inject_neutral:
    forall vm vmi n pml4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b
           host_rip_b,
      VMCS_inject_neutral vm n ->
      Mem.flat_inj n pml4ept_b = Some (pml4ept_b, 0) ->
      Mem.flat_inj n tss_b = Some (tss_b, 0) ->
      Mem.flat_inj n gdt_b = Some (gdt_b, 0) ->
      Mem.flat_inj n idt_b = Some (idt_b, 0) ->
      Mem.flat_inj n msr_bitmap_b = Some (msr_bitmap_b, 0) ->
      Mem.flat_inj n io_bitmap_b = Some (io_bitmap_b, 0) ->
      Mem.flat_inj n host_rip_b = Some (host_rip_b, 0) ->
      VMCS_inject_neutral
        (real_vmcs vm vmi pml4ept_b tss_b gdt_b idt_b msr_bitmap_b io_bitmap_b
                   host_rip_b) n.
  Proof.
    intros. unfold real_vmcs. 
    destruct vm.
    inversion H; subst.
    repeat (eapply VMCS_inject_neutral_gss_Vint_same 
                   || eapply VMCS_inject_neutral_gss_same); eauto 1;
    split; econstructor; eauto;
    generalize (H11 ofs); intro tmp; destruct tmp; eauto.
  Qed.

End REAL_VMCS.

Section REAL_VMX.

  Definition real_vmx (vm: VMX): VMX :=
    let vm1 := ZMap.set VMX_G_RIP' (Vint (Int.repr v0xfff0)) vm in
    let vm2 := ZMap.set VMX_VPID' Vone vm1 in
    let vm3 := ZMap.set VMX_G_CR2' Vzero vm2 in
    let vm4 := ZMap.set VMX_G_DR0' Vzero vm3 in
    let vm5 := ZMap.set VMX_G_DR1' Vzero vm4 in
    let vm6 := ZMap.set VMX_G_DR2' Vzero vm5 in
    let vm7 := ZMap.set VMX_G_DR3' Vzero vm6 in
    ZMap.set VMX_G_DR6' (Vint (Int.repr v0xffff0ff0)) vm7.

  Lemma real_vmx_inject_neutral:
    forall vm n,
      VMX_inject_neutral vm n ->
      VMX_inject_neutral
        (real_vmx vm) n.
  Proof.
    intros. unfold real_vmx. 
    repeat eapply VMX_inject_neutral_gss_Vint.
    assumption.
  Qed.

End REAL_VMX.
