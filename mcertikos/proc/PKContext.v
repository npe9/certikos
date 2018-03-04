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
(*              Layers of PM: PKContext                                *)
(*                                                                     *)
(*          Provide abstraction of Context                             *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*          Yu Guo <yu.guo@yale.edu>                                   *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the PKContext layer, 
which will introduce abstraction of kernel context*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import LoadStoreSem2.
Require Import XOmega.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealSMSPool.

Require Import INVLemmaMemory.
Require Import INVLemmaThread.

Require Import AbstractDataType.

Require Export MShare.
Require Export ObjThread.

(** * Abstract Data and Primitives at MPMap layer*)
(** The abstract data at MPMap layer is the same with MPTNew layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (** **Definition of the raw data at MPTBit layer*)
  (*Record RData :=
    mkRData {
        HP: flatmem; (**r we model the memory from 1G to 3G as heap*)
        ti: trapinfo; (**r abstract of CR2, stores the address where page fault happens*)
        pe: bool; (**r abstract of CR0, indicates whether the paging is enabled or not*)
        ikern: bool; (**r pure logic flag, shows whether it's in kernel mode or not*)
        ihost: bool; (**r logic flag, shows whether it's in the host mode or not*)         

        AT: ATable; (**r allocation table*)
        nps: Z; (**r number of the pages*)

        PT: Z; (**r the current page table index*)
        ptpool: PTPool; (**r page table pool*)
        ipt: bool; (**r pure logic flag, shows whether it's using the kernel's page table*)
        pb : PTBitMap; (**r [page table bit map], indicating which page table has been used*)

        kctxt: KContextPool (**r kernel context pool*)
      }.*)

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance kctxt_switch_inv: KCtxtSwitchInvariants kctxt_switch_spec.
    Proof.
      constructor; intros; functional inversion H. 
      - inv H1. constructor; trivial. 
        eapply kctxt_inject_neutral_gss_mem; eauto.
      - inv H0. subst. constructor; auto; simpl in *; intros; try congruence.
    Qed.

    Require Import compcert.cfrontend.Ctypes.

    Section kctxt_ra.

      Inductive extcall_kctxtra_sem  (s: stencil) (WB: block -> Prop):
        list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
      | extcall_kctxtra_sem_intro: 
          forall m adt adt' n b ofs,
            (exists fun_id, find_symbol s fun_id = Some b) ->
            kctxt_ra_spec adt (Int.unsigned n) b ofs = Some adt'
            -> extcall_kctxtra_sem s WB (Vint n::Vptr b ofs::nil) (m, adt) Vundef (m, adt').    

      Definition extcall_kctxtra_info: sextcall_info :=
        {|
          sextcall_step := extcall_kctxtra_sem;
          sextcall_csig := mkcsig (type_of_list_type (Tint32::Tpointer Tvoid noattr::nil)) Tvoid;
          sextcall_valid s := true
        |}.

      Global Instance extcall_kctxtra_invs:
        ExtcallInvariants extcall_kctxtra_info.
      Proof.
        constructor; intros; inv H;
        try (unfold kctxt_ra_spec in *; 
              inv H0; subdestruct; inv H8; constructor; simpl; eauto 2); try congruence.
        - (* low_level_invariant *) 
          eapply kctxt_inject_neutral_gss_ptr; eauto.
        - (* nextblock *)
          reflexivity.
        - (* inject neutral *)
          split; auto.
        - (* well typed *)
          simpl. trivial.
      Qed.

      Global Instance extcall_kctxtra_props:
        ExtcallProperties extcall_kctxtra_info.
      Proof.
        constructor; intros.
        - (* well typed *)
          inv H. simpl. trivial.
        - (* valid_block *)
          inv H. unfold Mem.valid_block in *.
          lift_unfold. trivial.
        - (* perm *)
          inv H. lift_unfold. trivial.
        - (* unchanges *)
          inv H. simpl. apply Mem.unchanged_on_refl.
        - (* extend *)
          inv H. inv_val_inject. lift_simpl.
          destruct H0 as [HT1 HT2].
          destruct m1' as [? ?]. simpl in *. subst.
          exists Vundef, (m0, adt'). 
          refine_split; eauto.
          + econstructor; eauto.
          + lift_unfold. split; trivial.
          + simpl. apply Mem.unchanged_on_refl.
        - (* inject *)
          inv H0. destruct H3 as [fun_id Hsymbol].
          pose proof Hsymbol as Hsymbol'. apply H in Hsymbol'. 
          inv_val_inject.
          lift_simpl. destruct H1 as [HT1 HT2].
          destruct m1' as [? ?]. simpl in *. subst.
          exists f, Vundef, (m0, adt'). 
          refine_split; eauto.
          + econstructor; eauto.
          + lift_unfold. split; trivial.
          + apply Mem.unchanged_on_refl.
          + simpl. apply Mem.unchanged_on_refl.
          + constructor; congruence.
        - (* deterministic*)
          inv H. inv H0. rewrite H2 in H10.
          inv H10. split; reflexivity.
        - (* WB *)
          inv H0. econstructor; eauto.
        - (* load *)
          inv H. lift_unfold. trivial.
      Qed.

      Definition kctxt_ra_compatsem : compatsem (cdata RData) :=
        compatsem_inl {|
            sextcall_primsem_step := extcall_kctxtra_info;
            sextcall_props := OK _;
            sextcall_invs := OK _
          |}.

    End kctxt_ra.

    Section kctxt_sp.

      Inductive extcall_kctxtsp_sem  (s: stencil) (WB: block -> Prop):
        list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
      | extcall_kctxtsp_sem_intro: 
          forall m adt adt' n b ofs,
            (exists fun_id, find_symbol s fun_id = Some b) ->
            (Int.unsigned ofs) = ((Int.unsigned n) + 1) * PgSize - 4 ->
            kctxt_sp_spec adt (Int.unsigned n) b ofs = Some adt' ->
            extcall_kctxtsp_sem s WB (Vint n::Vptr b ofs::nil) (m, adt) Vundef (m, adt').    

      Definition extcall_kctxtsp_info: sextcall_info :=
        {|
          sextcall_step := extcall_kctxtsp_sem;
          sextcall_csig := mkcsig (type_of_list_type (Tint32::Tpointer Tvoid noattr::nil)) Tvoid;
          sextcall_valid s := true
        |}.

      Global Instance extcall_kctxtsp_invs:
        ExtcallInvariants extcall_kctxtsp_info.
      Proof.
        constructor; intros; inv H;
        try (unfold kctxt_sp_spec in *;
              inv H0; subdestruct; inv H9; constructor; simpl; eauto 2); try congruence.
        - (* low_level_invariant *)
          eapply kctxt_inject_neutral_gss_ptr; eauto.
        - (* nextblock *)
          reflexivity.
        - (* well typed *)
          simpl. trivial.
      Qed.

      Global Instance extcall_kctxtsp_props:
        ExtcallProperties extcall_kctxtsp_info.
      Proof.
        constructor; intros.
        - (* well typed *)
          inv H. simpl. trivial.
        - (* valid_block *)
          inv H. unfold Mem.valid_block in *.
          lift_unfold. trivial.
        - (* perm *)
          inv H. lift_unfold. trivial.
        - (* unchanges *)
          inv H. simpl. apply Mem.unchanged_on_refl.
        - (* extend *)
          inv H. inv_val_inject. lift_simpl.
          destruct H0 as [HT1 HT2].
          destruct m1' as [? ?]. simpl in *. subst.
          exists Vundef, (m0, adt'). 
          refine_split; eauto.
          + econstructor; eauto.
          + lift_unfold. split; trivial.
          + simpl. apply Mem.unchanged_on_refl.
        - (* inject *)
          inv H0. destruct H3 as [fun_id Hsymbol].
          pose proof Hsymbol as Hsymbol'. apply H in Hsymbol'. 
          inv_val_inject.
          lift_simpl. destruct H1 as [HT1 HT2].
          destruct m1' as [? ?]. simpl in *. subst.
          exists f, Vundef, (m0, adt'). 
          refine_split; eauto.
          + econstructor; eauto.
          + lift_unfold. split; trivial.
          + apply Mem.unchanged_on_refl.
          + simpl. apply Mem.unchanged_on_refl.
          + constructor; congruence.
        - (* deterministic*)
          inv H. inv H0. rewrite H3 in H12.
          inv H12. split; reflexivity.
        - (* WB *)
          inv H0. econstructor; eauto.
        - (* load *)
          inv H. lift_unfold. trivial.
      Qed.

      Definition kctxt_sp_compatsem : compatsem (cdata RData) :=
        compatsem_inl {|
            sextcall_primsem_step := extcall_kctxtsp_info;
            sextcall_props := OK _;
            sextcall_invs := OK _
          |}.

    End kctxt_sp.

  End INV.

  (** * Layer Definition *)
  Definition pkcontext_fresh_c : compatlayer (cdata RData) :=
    set_RA ↦ kctxt_ra_compatsem
           ⊕ set_SP ↦ kctxt_sp_compatsem.

  Definition pkcontext_fresh_asm : compatlayer (cdata RData) :=
    kctxt_switch ↦ primcall_kctxt_switch_compatsem kctxt_switch_spec.

  Definition pkcontext_fresh : compatlayer (cdata RData) :=
    pkcontext_fresh_c
      ⊕ pkcontext_fresh_asm.

  Definition pkcontext_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          ⊕ pt_new ↦ gensem pt_new_spec
          (*⊕ pt_free ↦ gensem pt_free_spec*)
          ⊕ shared_mem_init ↦ gensem sharedmem_init_spec
          ⊕ shared_mem_status ↦ gensem ObjShareMem.shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem ObjShareMem.offer_shared_mem_spec
          ⊕ pt_in ↦ primcall_general_compatsem' ptin_spec (prim_ident:= pt_in)
          ⊕ pt_out ↦ primcall_general_compatsem' ptout_spec (prim_ident:= pt_out)
          ⊕ clear_cr2 ↦ gensem clearCR2_spec
          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_alloc ↦ gensem alloc_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ trap_out ↦ primcall_general_compatsem trapout_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  Definition pkcontext : compatlayer (cdata RData) := pkcontext_fresh ⊕ pkcontext_passthrough.

  (*Definition semantics := LAsm.Lsemantics pkcontext.*)
  
End WITHMEM.

Section WITHPARAM.

  (*Context `{real_params: RealParams}.*)

  Local Open Scope Z_scope.

  Section Impl.

    Function kctxt_new_spec (abd: RData) (b: block) (b':block) (ofs':int) id q : option (RData * Z) :=
      match pt_new_spec id q abd with
        | Some (abd0, i) =>
          if zeq i num_proc then Some (abd0, num_proc)
          else
          let ofs := Int.repr ((i + 1) * PgSize -4) in
          match kctxt_sp_spec abd0 i b ofs with
            | Some abd1 =>
              match kctxt_ra_spec abd1 i b' ofs' with
                | Some abd2 => Some (abd2, i)
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end.

  End Impl.

End WITHPARAM.
