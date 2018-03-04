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
(*           Layers of PM: Assembly Verification for Proc              *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Locations.
Require Import AuxStateDataType.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import FlatMemory.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import Constant.
Require Import AsmImplLemma.
Require Import AsmImplTactic.
Require Import GlobIdent.
Require Import CommonTactic.

Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compcertx.MakeProgram.
Require Import LAsmModuleSem.
Require Import LAsm.
Require Import liblayers.compat.CompatGenSem.
Require Import PrimSemantics.
Require Import Conventions.

Require Import TDispatch.
Require Import SysCallGenAsmSource.
Require Import AbstractDataType.

Section ASM_DATA.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.
  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

      Lemma proc_start_generate:
        forall abd1 abd' rs' m,
          proc_start_user_spec abd1 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. unfold proc_start_user_spec in *.
        subdestruct. subst v.
        inv H. eauto.
      Qed.

      Lemma set_errno_generate:
        forall abd0 abd1 m n,
          uctx_set_errno_spec n abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl. 
        repeat rewrite ZMap.gss.
        subst uctx' uctx.
        destruct (zeq i 7).
        subst.
        rewrite ZMap.gss.
        split; constructor.
        rewrite ZMap.gso; auto.
      Qed.

      Lemma set_retval1_generate:
        forall abd0 abd1 m shadow,
          uctx_set_retval1_spec shadow abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl. 
        repeat rewrite ZMap.gss.
        subst uctx' uctx.
        destruct (zeq i 4).
        subst.
        rewrite ZMap.gss.
        split; constructor.
        rewrite ZMap.gso; auto.
      Qed.

      Lemma set_retval2_generate:
        forall abd0 abd1 m shadow,
          uctx_set_retval2_spec shadow abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl. 
        repeat rewrite ZMap.gss.
        subst uctx' uctx.
        destruct (zeq i 6).
        subst.
        rewrite ZMap.gss.
        split; constructor.
        rewrite ZMap.gso; auto.
      Qed.

      Lemma set_retval3_generate:
        forall abd0 abd1 m shadow,
          uctx_set_retval3_spec shadow abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl. 
        repeat rewrite ZMap.gss.
        subst uctx' uctx.
        destruct (zeq i 5).
        subst.
        rewrite ZMap.gss.
        split; constructor.
        rewrite ZMap.gso; auto.
      Qed.

      Lemma set_retval4_generate:
        forall abd0 abd1 m shadow,
          uctx_set_retval4_spec shadow abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl. 
        repeat rewrite ZMap.gss.
        subst uctx' uctx.
        destruct (zeq i 1).
        subst.
        rewrite ZMap.gss.
        split; constructor.
        rewrite ZMap.gso; auto.
      Qed.

      Lemma proc_exit_generate:
        forall m abd abd1 uctx,
          proc_exit_user_spec abd uctx = Some abd1 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl. 
        repeat rewrite ZMap.gss. auto.
      Qed.

      (*Lemma vmx_set_mmap_generate:
        forall abd0 abd1 m v1 v2 v3 z,
          vmx_set_mmap_spec v1 v2 v3 abd0 = Some (abd1, z) ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl;
        functional inversion H4; simpl; eauto. 
      Qed.

      Lemma vmx_set_reg_generate:
        forall abd0 abd1 m v1 v2,
          vmx_set_reg_spec v1 v2 abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl; eauto.
      Qed.

      Lemma sys_get_generate:
        forall m shadow labd abd abd' abd0 abd1 rs' uctx n,
          proc_exit_user_spec labd uctx = Some abd ->
          uctx_set_retval1_spec shadow abd = Some abd0 ->
          uctx_set_errno_spec n abd0 = Some abd1 ->          
          proc_start_user_spec abd1 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply set_retval1_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.*)

      Lemma sys_yield_generate:
        forall m labd abd abd0 rs' uctx rs1,
          proc_exit_user_spec labd uctx = Some abd ->
          thread_yield_spec abd rs' = Some (abd0, rs1) ->
          high_level_invariant labd  ->
          low_level_invariant (Mem.nextblock m) labd  ->
          (forall v r, ZtoPreg v = Some r -> 
                       Val.has_type (rs1 r) Tint
                       /\  val_inject (Mem.flat_inj (Mem.nextblock m))
                                      (rs1 r) (rs1 r)).
      Proof.
        intros.
        functional inversion H; subst.
        Opaque remove.
        unfold thread_yield_spec in H0; simpl in H0.
        rewrite H5, H6 in H0; simpl in H0. subdestruct. inv H0. inv H1.
        assert(HIn: In (last l num_proc) l).
        {
          apply last_correct; auto.
        }
        assert (HOS: 0<= num_proc <= num_proc) by omega.
        unfold AbQCorrect in *.
        specialize (valid_TDQ H6 _ HOS).
        destruct valid_TDQ as [lt[HM HP]].
        rewrite Hdestruct in HM. inv HM.
        inv H2.
        eapply kctxt_INJECT.
        apply HP; trivial.
        eassumption.
      Qed.

      Lemma ptInsertPTE0_generate:
        forall abd0 abd1 m n vadr v1 v2,
          ptInsertPTE0_spec n vadr v1 v2 abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl; eauto. 
      Qed.

      Lemma ptAllocPDE0_generate:
        forall abd0 abd1 m n vadr z,
          ptAllocPDE0_spec n vadr abd0 = Some (abd1, z) ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl; subst; eauto.
      Qed.        

      Lemma ptInsert0_generate:
        forall abd0 abd1 m n vadr v1 v2 z,
          ptInsert0_spec n vadr v1 v2 abd0 = Some (abd1, z) ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; simpl.
        - eapply ptInsertPTE0_generate; eauto.
        - eapply ptAllocPDE0_generate; eauto.
        - eapply ptInsertPTE0_generate; eauto.
          eapply ptAllocPDE0_generate; eauto.
      Qed.

      Lemma pgf_handler_generate:
        forall m labd abd abd' abd0 rs' uctx vadr,
          proc_exit_user_spec labd uctx = Some abd ->
          ptfault_resv_spec vadr abd = Some abd0 ->
          proc_start_user_spec abd0 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          ikern abd = true
          /\ ihost abd = true
          /\ ikern abd0 = true
          /\ ihost abd0 = true
          /\ (forall i, 0<= i < UCTXT_SIZE ->
                        let v:= (ZMap.get i rs') in
                        Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        functional inversion H; subst; simpl in *.
        unfold ptfault_resv_spec in *; simpl in *.
        unfold ptResv_spec in *.
        unfold alloc_spec in *; simpl in *.
        assert (Habd0: ikern abd0 = true /\ ihost abd0 = true)
          by (clear H0; unfold proc_start_user_spec in *; subdestruct; auto).
        destruct Habd0; subdestruct; refine_split'; trivial; inv H0.
        - eapply proc_start_generate; eauto.
          simpl. rewrite ZMap.gss. intros.
          exploit proc_exit_generate; eauto.
        - eapply proc_start_generate; eauto.
          eapply ptInsert0_generate; eauto.
          simpl. rewrite ZMap.gss. intros.
          exploit proc_exit_generate; eauto.
        - eapply proc_start_generate; eauto.
          simpl. rewrite ZMap.gss. intros.
          exploit proc_exit_generate; eauto.
        - eapply proc_start_generate; eauto.
          simpl. rewrite ZMap.gss. intros.
          exploit proc_exit_generate; eauto.
      Qed.

      (*Lemma sys_run_vm_generate:
        forall m labd abd abd0 rs' uctx rs0,
          proc_exit_user_spec labd uctx = Some abd ->
          vm_run_spec rs0 abd = Some (abd0, rs') ->
          high_level_invariant labd  ->
          low_level_invariant (Mem.nextblock m) labd ->
          (forall r, Val.has_type (rs'#r) Tint 
                     /\ val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)).
      Proof.
        intros. functional inversion H; subst.
        unfold vm_run_spec in H0; simpl in H0.
        subdestruct. inv H0.
        inv H2. inv VMX_INJECT.
        
        destruct r as [| [] | [] | | [] |]; try (split; constructor); try eapply H0.
      Qed.*)

      Lemma sys_sendtochan_pre_generate:
        forall m labd abd abd0 abd1 rs' uctx chanid rs_yield,
          proc_exit_user_spec labd uctx = Some abd ->
          trap_sendtochan_pre_spec abd = Some (abd0, Int.unsigned chanid) ->
          thread_sleep_spec abd0 rs_yield (Int.unsigned chanid) = Some (abd1, rs') ->
          high_level_invariant labd  ->
          low_level_invariant (Mem.nextblock m) labd  ->
          (forall v r, ZtoPreg v = Some r ->
                       Val.has_type (rs'#r) Tint 
                       /\ val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)).
      Proof.
        intros. functional inversion H; subst.
        unfold thread_sleep_spec in H1.
        unfold proc_exit_user_spec in H.
        unfold trap_sendtochan_pre_spec in H0.
        subdestruct; inv H1. inv H. inv H0.
        assert(HIn: In (last l num_proc) l).
        {
          apply last_correct; auto.
        }
        assert (HOS: 0<= num_proc <= num_proc) by omega.
        unfold AbQCorrect_range, AbQCorrect in *.
        inv H2.
        specialize (valid_TDQ Hdestruct0 _ HOS).
        destruct valid_TDQ as [lt[HM HP]].
        functional inversion H1; simpl in *.
        - inv H; simpl in *; rewrite Hdestruct10 in HM. inv HM.
          eapply kctxt_INJECT; eauto.
        - inv H. inv H17. simpl in *. 
          rewrite Hdestruct10 in HM. inv HM.
          eapply kctxt_INJECT; eauto.
      Qed.

      Lemma trap_sendtochan_post_generate:
        forall abd0 abd m, 
          trap_sendtochan_post_spec abd = Some abd0 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd)
                                                   (uctxt abd))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H. 
        eapply set_errno_generate; eauto.
        eapply set_retval1_generate; eauto.
        functional inversion H3;
        subst; simpl; auto. 
      Qed.

      Lemma sys_sendtochan_post_generate:
        forall m abd abd' abd0 rs',
          trap_sendtochan_post_spec abd = Some abd0 ->
          proc_start_user_spec abd0 = Some (abd', rs') ->
          (*(forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->*)
          high_level_invariant abd ->
          low_level_invariant (Mem.nextblock m) abd ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply trap_sendtochan_post_generate; eauto.
        inv H1. unfold uctxt_inject_neutral in *. 
        intros; eapply uctxt_INJECT; eauto.
      Qed.

      Lemma ptResv_generate:
        forall abd0 abd1 m v1 v2 v3 z,
          ptResv_spec v1 v2 v3 abd0 = Some (abd1, z) ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; subst; simpl; eauto.
        eapply ptInsert0_generate; eauto.
        functional inversion H3; subst; eauto.
      Qed.

      Lemma trap_proc_create_generate:
        forall abd0 abd1 m s,
          trap_proc_create_spec s m abd0 = Some abd1 ->   
          (genv_next s <= Mem.nextblock m)%positive ->       
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        rename H into Hspec; unfold trap_proc_create_spec in Hspec.
        destruct (uctx_arg3_spec abd0); try discriminate Hspec.
        destruct (zle_le 0 z
                         (cquota (ZMap.get (cid abd0) (AC abd0)) -
                          cusage (ZMap.get (cid abd0) (AC abd0)))) eqn:Hquota.
        destruct (zle_le 0 (cid abd0 * max_children + 1 + max_children) num_id) eqn:Hchild.
        destruct (zlt (Z.of_nat (length (cchildren (ZMap.get (cid abd0) (AC abd0))))) 
                      max_children) eqn:Hnc; subdestruct; subst.
        - eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
          unfold proc_create_spec in *. subdestruct; subst.
          inv Hdestruct11; simpl in *.
          intros; zmap_solve; split; auto.
          econstructor.
          eapply stencil_find_symbol_inject'; eauto.
          eapply flat_inj_inject_incr. assumption.
          rewrite Int.add_zero. reflexivity.
        - eapply set_errno_generate; eauto.
        - eapply set_errno_generate; eauto.
        - eapply set_errno_generate; eauto.
      Qed.        

      Lemma ptResv2_generate:
        forall abd0 abd1 m v1 v2 v3 v4 v5 v6 z,
          ptResv2_spec v1 v2 v3 v4 v5 v6 abd0 = Some (abd1, z) ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; subst; simpl; eauto.
        - eapply ptInsert0_generate; eauto.
          functional inversion H4; subst; eauto.
        - eapply ptInsert0_generate; eauto.
          eapply ptInsert0_generate; eauto.
          functional inversion H3; subst; eauto.
      Qed.

      Lemma offer_shared_mem_generate:
        forall abd0 abd1 i1 i2 i3 m z,
          offer_shared_mem_spec i1 i2 i3 abd0 = Some (abd1, z) ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; subst; simpl; eauto; clear H.
        - eapply ptResv2_generate; eauto.
        - eapply ptResv2_generate; eauto.
      Qed.

      Lemma trap_offer_shared_mem_generate:
        forall abd0 abd1 m,
          trap_offer_shared_mem_spec abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; subst; simpl; eauto; clear H.
        - eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
          eapply offer_shared_mem_generate; eauto.
        - eapply set_errno_generate; eauto.
      Qed.

      Lemma print_generate:
        forall abd0 abd1 m,
          print_spec abd0 = Some abd1 ->          
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                   (uctxt abd1))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; subst; simpl; eauto; clear H.
        eapply set_errno_generate; eauto.
      Qed.

      Lemma sys_dispatch_c_generate:
        forall abd0 abd1 m s,
          sys_dispatch_c_spec s m abd0 = Some abd1 ->          
          forall (Hgenv: (genv_next s <= Mem.nextblock m)%positive),       
            (forall i, 0<= i < UCTXT_SIZE -> 
                       let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                     (uctxt abd0))) in
                       Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
            (forall i, 0<= i < UCTXT_SIZE -> 
                       let v:= (ZMap.get i (ZMap.get (cid abd1)
                                                     (uctxt abd1))) in
                       Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        unfold sys_dispatch_c_spec in *.
        subdestruct;
          try (eapply set_errno_generate; eauto; fail).
        - (* trap_proc_create *)
          eapply trap_proc_create_generate; eauto.
        (*- (* trap_get_tsc_offset *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval2_generate; eauto.
          eapply set_retval1_generate; eauto.
        - (* trap_set_tsc_offset *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          functional inversion H5; simpl; try subst; eauto.
        - (* trap_get_exitinfo  *)
          functional inversion H.
          + eapply set_errno_generate; eauto.
            eapply set_retval4_generate; eauto.
            eapply set_retval3_generate; eauto.
            eapply set_retval2_generate; eauto.
            eapply set_retval1_generate; eauto.
          + eapply set_errno_generate; eauto.
            eapply set_retval2_generate; eauto.
            eapply set_retval1_generate; eauto.
          + eapply set_errno_generate; eauto.
            eapply set_retval1_generate; eauto.
        - (* trap_mmap *)
          functional inversion H.
          + eapply set_errno_generate; eauto.
            eapply vmx_set_mmap_generate; eauto.
            eapply ptResv_generate; eauto.
          + eapply set_errno_generate; eauto.
            eapply vmx_set_mmap_generate; eauto.
          + eapply set_errno_generate; eauto.
        - (* trap_set_reg *)
          functional inversion H.
          + eapply set_errno_generate; eauto.
            eapply vmx_set_reg_generate; eauto.
          + eapply set_errno_generate; eauto.
        - (* trap_get_reg *)
          functional inversion H.
          + eapply set_errno_generate; eauto.
            eapply set_retval1_generate; eauto.
          + eapply set_errno_generate; eauto.
        - (* trap_set_seg *)
          functional inversion H.
          + eapply set_errno_generate; eauto.
            functional inversion H9; simpl; subst; eauto.
          + eapply set_errno_generate; eauto.
        - (* trap_get_next_eip *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
        - (* trap_inject_event *)
          functional inversion H.
          + eapply set_errno_generate; eauto.
            functional inversion H7; simpl; subst; eauto.
        - (* trap_check_pending_event *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
        - (* trap_check_int_shadow *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
        - (* trap_intercept_int_window *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          functional inversion H4; simpl; subst; eauto.
        - (* trap_handle_rdmsr *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply vmx_set_reg_generate; eauto.
          eapply vmx_set_reg_generate; eauto.
          eapply vmx_set_reg_generate; eauto.
        - (* trap_handle_wrmsr *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply vmx_set_reg_generate; eauto.*)
        - (* trap_get_quota *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
        (*- (* trap_ischanready *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
        - (* trap_sendtochan *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
          functional inversion H5; simpl; subst; eauto.
        - (* trap_receivechan *)
          functional inversion H.
          eapply set_errno_generate; eauto.
          eapply set_retval1_generate; eauto.
          functional inversion H6; simpl; subst; eauto.
          functional inversion H21; simpl; eauto;
          functional inversion H20; simpl; eauto.*)

        - (*offer_share*)
          eapply trap_offer_shared_mem_generate; eauto.
        - (* print *)
          eapply print_generate; eauto.
      Qed.

      Lemma sys_dispatch_generate:
        forall m labd abd abd' abd0 rs' uctx s,
          proc_exit_user_spec labd uctx = Some abd ->
          sys_dispatch_c_spec s m abd = Some abd0 ->
          proc_start_user_spec abd0 = Some (abd', rs') ->
          (genv_next s <= Mem.nextblock m)%positive ->       
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        eapply proc_start_generate; eauto.
        eapply sys_dispatch_c_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.

(*      Lemma sys_ready_generate:
        forall m labd abd abd' abd0 rs' uctx,
          proc_exit_user_spec labd uctx = Some abd ->
          trap_ischanready_spec abd = Some abd0 ->
          proc_start_user_spec abd0 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        unfold trap_ischanready_spec in *.
        caseEq (is_chan_ready_spec abd); intros; rewrite H4 in *; contra_inv.
        caseEq (uctx_set_retval1_spec abd z); intros; rewrite H5 in *; contra_inv.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply set_retval1_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.*)

(*        

      Lemma inject_event_generate:
        forall (abd0 abd1: LDATA) m type vector errcode ev,
          VVMCBOP.vmcb_inject_event abd0 type vector errcode ev = Some abd1 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd0))
                                                   (PPROC.uctxt (LADT abd0)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd1))
                                                   (PPROC.uctxt (LADT abd1)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        apply VVMCBOP.vmcb_inject_event_eq in H.
        subst v.
        functional inversion H; simpl; auto. 
      Qed.

      Lemma sys_inject_event_generate:
        forall m abd abd' abd0 abd1 (rs:regset) rs' uctx type vector errcode ev,
          PPROC.proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx = Some abd ->
          VVMCBOP.vmcb_inject_event abd type vector errcode ev = Some abd0 ->
          TTRAPARG.uctx_set_errno abd0 Int.zero = Some abd1 ->
          PPROC.proc_start_user abd1 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply inject_event_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.

      Lemma npt_insert_generate:
        forall (abd0 abd: LDATA) m gadr hadr,
          PPROC.nptInsert (HPS4:= HPS4) abd gadr hadr = Some abd0 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd))
                                                   (PPROC.uctxt (LADT abd)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd0))
                                                   (PPROC.uctxt (LADT abd0)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        apply PPROC.nptInsert_eq in H.
        subst v.
        functional inversion H; simpl; auto. 
      Qed.
*)

(*      Lemma la2pa_resv_generate:
        forall (abd0 abd: LDATA) m hadr padr,
          TTRAPARG.la2pa_resv (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:=Hhigh) abd hadr = Some (abd0, padr) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd))
                                                   (PPROC.uctxt (LADT abd)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd0))
                                                   (PPROC.uctxt (LADT abd0)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        functional inversion H; subst; simpl; auto. 
        subst v.
        apply PPROC.ptResv_eq in H7.
        functional inversion H7; subst; simpl; auto. 
        functional inversion H3; simpl; auto. 
        
        apply H0; trivial.
      Qed.*)

(*
      Lemma sys_npt_insert_generate:
        forall m abd abd' abd0 abd1 (rs:regset) rs' uctx gadr hadr padr abd2,
          PPROC.proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx = Some abd ->
          TTRAPARG.la2pa_resv (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:=Hhigh) abd hadr = Some (abd0, padr) ->
          PPROC.nptInsert (HPS4:= HPS4) abd0 gadr padr = Some abd1 ->
          TTRAPARG.uctx_set_errno abd1 Int.zero = Some abd2 ->
          PPROC.proc_start_user abd2 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply npt_insert_generate; eauto.
        eapply la2pa_resv_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.

      Lemma intwin_generate:
        forall (abd0 abd: LDATA) m enable,
          VSVM.svm_set_intercept_intwin abd enable = Some abd0 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd))
                                                   (PPROC.uctxt (LADT abd)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd0))
                                                   (PPROC.uctxt (LADT abd0)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        apply VSVM.svm_set_intercept_intwin_eq in H.
        subst v.
        functional inversion H; simpl; auto. 
      Qed.

      Lemma sys_set_intercept_intwin_generate:
        forall m abd abd' abd0 abd1 (rs:regset) rs' uctx enable,
          PPROC.proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx = Some abd ->
          VSVM.svm_set_intercept_intwin abd enable = Some abd0 ->
          TTRAPARG.uctx_set_errno abd0 Int.zero = Some abd1 ->
          PPROC.proc_start_user abd1 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply intwin_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.

      Lemma set_seg_generate:
        forall (abd0 abd: LDATA) m seg sel base lim ar,
          VVMCBOP.vmcb_set_seg abd seg sel base lim ar = Some abd0 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd))
                                                   (PPROC.uctxt (LADT abd)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd0))
                                                   (PPROC.uctxt (LADT abd0)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        apply VVMCBOP.vmcb_set_seg_eq in H.
        subst v.
        functional inversion H; simpl; auto. 
      Qed.

      Lemma sys_set_seg_generate:
        forall m abd abd' abd0 abd1 (rs:regset) rs' uctx seg sel base lim ar,
          PPROC.proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx = Some abd ->
          VVMCBOP.vmcb_set_seg abd seg sel base lim ar = Some abd0 ->
          TTRAPARG.uctx_set_errno abd0 Int.zero = Some abd1 ->
          PPROC.proc_start_user abd1 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply set_seg_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.

      Lemma sync_generate:
        forall (abd0 abd: LDATA) m,
          VSVM.svm_sync abd = Some abd0 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd))
                                                   (PPROC.uctxt (LADT abd)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (PPROC.cid (LADT abd0))
                                                   (PPROC.uctxt (LADT abd0)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        apply VSVM.svm_sync_eq in H.
        subst v.
        functional inversion H; simpl; auto. 
      Qed.

      Lemma sys_sync_generate:
        forall m abd abd' abd0 abd1 (rs:regset) rs' uctx,
          PPROC.proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx = Some abd ->
          VSVM.svm_sync abd = Some abd0 ->
          TTRAPARG.uctx_set_errno abd0 Int.zero = Some abd1 ->
          PPROC.proc_start_user abd1 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply sync_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.
*)

(*      Lemma send_generate:
        forall abd0 abd m chid content r, 
          sendto_chan_spec abd chid content = Some (abd0, r) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd)
                                                   (uctxt abd))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; subst; simpl; auto. 
      Qed.

      Lemma sys_send_generate:
        forall m labd abd abd' abd0 rs' uctx,
          proc_exit_user_spec labd uctx = Some abd ->
          trap_sendtochan_spec abd = Some abd0 ->
          proc_start_user_spec abd0 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        unfold trap_sendtochan_spec in *.
        destruct (uctx_arg1_spec abd); contra_inv.
        destruct (uctx_arg2_spec abd); contra_inv.
        caseEq (sendto_chan_spec abd z z0); intros; rewrite H4 in *; contra_inv.
        destruct p.
        caseEq (uctx_set_retval1_spec r z1); intros; rewrite H6 in *; contra_inv.
        eapply set_errno_generate; eauto.
        eapply set_retval1_generate; eauto.
        eapply send_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.

      Lemma recv_generate:
        forall abd0 abd m r, 
          receive_chan_spec abd = Some (abd0, r) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd)
                                                   (uctxt abd))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. subst v.
        functional inversion H; subst; simpl; auto. 
        unfold thread_wakeup_spec in *.
        subdestruct; inv H10; simpl; auto.
      Qed.

      Lemma sys_recv_generate:
        forall m labd abd abd' abd0 rs' uctx,
          proc_exit_user_spec labd uctx = Some abd ->
          trap_receivechan_spec abd = Some abd0 ->
          proc_start_user_spec abd0 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        unfold trap_receivechan_spec in *.
        caseEq (receive_chan_spec abd); intros; rewrite H4 in *; contra_inv.
        destruct p.
        caseEq (uctx_set_retval1_spec r z); intros; rewrite H6 in *; contra_inv.
        eapply set_errno_generate; eauto.
        eapply set_retval1_generate; eauto.
        eapply recv_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.
*)

(*
      Lemma set_reg_generate:
        forall (abd0 abd: LDATA) m v reg, 
          VSVM.svm_set_reg abd reg (Vint v) = Some abd0 ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid (LADT abd))
                                                   (uctxt (LADT abd)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid (LADT abd0))
                                                   (uctxt (LADT abd0)))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        apply VSVM.svm_set_reg_eq in H.
        subst v0.
        functional inversion H; simpl; auto. 
      Qed.

      Lemma sys_set_reg_generate:
        forall m abd abd' abd0 abd1 (rs:regset) rs' uctx reg v,
          proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx = Some abd ->
          VSVM.svm_set_reg abd reg (Vint v) = Some abd0 ->
          uctx_set_errno abd0 Int.zero = Some abd1 ->
          proc_start_user abd1 = Some (abd', rs') ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply set_reg_generate; eauto.
        eapply proc_exit_generate; eauto.
      Qed.
*)

(*      Lemma proc_create_generate:
        forall s m abd0 abd
               n bstack busercode buserstart belf fun_id,
          find_symbol s fun_id = Some busercode ->
          find_symbol s START_USER_FUN_LOC = Some buserstart ->
          find_symbol s ELF_LOC = Some belf ->
          find_symbol s STACK_LOC = Some bstack ->
          proc_create_spec abd bstack buserstart busercode Int.zero = Some (abd0, Int.unsigned n) ->
          (genv_next s <= Mem.nextblock m)%positive ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd)
                                                   (uctxt abd))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i (ZMap.get (cid abd0)
                                                   (uctxt abd0))) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros. unfold proc_create_spec in *. subst v.
        subdestruct. inv H3; simpl.
        destruct (zeq (cid abd) (Int.unsigned n)).
        - rewrite e in *; clear e.
          repeat rewrite ZMap.gss.
          inv_proc; try (split; constructor; fail).
          split. constructor.
          econstructor.
          eapply stencil_find_symbol_inject'; eauto.
          eapply flat_inj_inject_incr. assumption.
          rewrite Int.add_zero. reflexivity.
        - rewrite ZMap.gso; auto.
      Qed.

      Lemma sys_proc_create_generate:
        forall s m labd abd abd' abd0 abd1 rs' uctx abd2
               n bstack busercode buserstart belf fun_id,
          proc_exit_user_spec labd uctx = Some abd ->
          find_symbol s fun_id = Some busercode ->
          find_symbol s START_USER_FUN_LOC = Some buserstart ->
          find_symbol s ELF_LOC = Some belf ->
          find_symbol s STACK_LOC = Some bstack ->
          proc_create_spec abd bstack buserstart busercode Int.zero = Some (abd0, Int.unsigned n) ->
          uctx_set_retval1_spec abd0 (Int.unsigned n) = Some abd1 ->
          uctx_set_errno_spec abd1 0 = Some abd2 ->
          proc_start_user_spec abd2 = Some (abd', rs') ->
          (genv_next s <= Mem.nextblock m)%positive ->
          (forall i, 0<= i < UCTXT_SIZE -> 
                     let v:= (ZMap.get i uctx) in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          (forall i, 0<= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v Tint /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      Proof.
        intros.
        eapply proc_start_generate; eauto.
        eapply set_errno_generate; eauto.
        eapply set_retval1_generate; eauto.
        eapply proc_create_generate with (busercode:= busercode); eauto.
        eapply proc_exit_generate; eauto.
      Qed.
*)

(*
      Lemma sys_run_generate:
        forall m abd abd0 uctx vmcb xvm rs0 abd1,
          proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx = Some abd ->
          VVMCBOP.svm_run_vm abd1 rs0= Some (abd0, vmcb, xvm) ->
          TTRAP.low_level_invariant (Mem.nextblock m) (Mem.get_abstract_data m)  ->
          uctx_set_errno abd Int.zero = Some abd1 ->
          (forall ofs, is_VMCB_V_ofs ofs = true -> 
                       Val.has_type (ZMap.get ofs vmcb) Tint
                       /\ val_inject (Mem.flat_inj (Mem.nextblock m))
                                     (ZMap.get ofs vmcb) (ZMap.get ofs vmcb))
          /\ (forall ofs, 0<= ofs < XVMST_SIZE -> 
                          Val.has_type (ZMap.get ofs xvm) Tint
                          /\ val_inject (Mem.flat_inj (Mem.nextblock m)) 
                                        (ZMap.get ofs xvm) (ZMap.get ofs xvm))
          /\ ikern (LADT abd) = true
          /\ ihost (LADT abd) = true.
      Proof.
        intros.
        rename H2 into Herr.
        apply proc_exit_user_eq in H.
        functional inversion H; unfold adt in *.
        apply uctx_set_errno_eq in Herr.
        functional inversion Herr; unfold adt0 in *.
        apply VVMCBOP.svm_run_vm_eq in H0.
        functional inversion H0; unfold adt1 in *.
        rewrite <- H2 in H6; simpl in H6.
        rewrite <- H6 in H10; simpl in H10.
        inv H1.
        destruct H17 as [_[_[_[_[HVMCB HXVM]]]]].
        rewrite <- H6; simpl.
        eauto.
      Qed.
*)

      Lemma Hstart: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge proc_start_user = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external proc_start_user proc_start_user_sig)))
          /\ get_layer_primitive proc_start_user tdispatch = 
             OK (Some (primcall_start_user_compatsem proc_start_user_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive proc_start_user tdispatch = 
                       OK (Some (primcall_start_user_compatsem proc_start_user_spec)))
                 by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hexit: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge proc_exit_user = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external proc_exit_user proc_exit_user_sig)))
          /\ get_layer_primitive proc_exit_user tdispatch = 
             OK (Some (primcall_exit_user_compatsem proc_exit_user_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive proc_exit_user tdispatch = 
                       OK (Some (primcall_exit_user_compatsem proc_exit_user_spec)))
                 by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hyield: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge thread_yield = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external thread_yield thread_yield_sig)))
          /\ get_layer_primitive thread_yield tdispatch = 
             OK (Some (primcall_thread_schedule_compatsem 
                         thread_yield_spec (prim_ident:= thread_yield))).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive thread_yield tdispatch = 
                       OK (Some (primcall_thread_schedule_compatsem 
                                   thread_yield_spec (prim_ident:= thread_yield))))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hsleep: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge thread_sleep = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external thread_sleep thread_sleep_sig)))
          /\ get_layer_primitive thread_sleep tdispatch = 
             OK (Some (primcall_thread_transfer_compatsem thread_sleep_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive thread_sleep tdispatch = 
                       OK (Some (primcall_thread_transfer_compatsem thread_sleep_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      (*Lemma Hrun_vm: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge vmx_run_vm = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external vmx_run_vm null_signature)))
          /\ get_layer_primitive vmx_run_vm tdispatch = 
             OK (Some (primcall_vmx_enter_compatsem vm_run_spec vmx_run_vm)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive vmx_run_vm tdispatch = 
                       OK (Some (primcall_vmx_enter_compatsem vm_run_spec vmx_run_vm)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.*)

      Lemma Hget: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge trap_get = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external trap_get trap_get_sig)))
          /\ get_layer_primitive trap_get tdispatch = 
             OK (Some (primcall_trap_info_get_compatsem trap_info_get_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive trap_get tdispatch = 
                       OK (Some (primcall_trap_info_get_compatsem trap_info_get_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hpgfr: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge ptfault_resv = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external ptfault_resv ptfault_resv_sig)))
          /\ get_layer_primitive ptfault_resv tdispatch = 
             OK (Some (gensem ptfault_resv_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive ptfault_resv tdispatch = 
                       OK (Some (gensem ptfault_resv_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hdispatch_c: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge syscall_dispatch_C = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external syscall_dispatch_C syscall_c_dispatch_sig)))
          /\ get_layer_primitive syscall_dispatch_C tdispatch = 
             OK (Some (trap_proccreate_compatsem sys_dispatch_c_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive syscall_dispatch_C tdispatch = 
                       OK (Some (trap_proccreate_compatsem sys_dispatch_c_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hsys_dispatch_c:
        forall ge s b,
          make_globalenv s (syscall_dispatch ↦ sys_dispatch_function) tdispatch = ret ge ->
          find_symbol s syscall_dispatch = Some b ->
          stencil_matches s ge ->
          Genv.find_funct_ptr ge b = Some (Internal sys_dispatch_function).
      Proof.
        intros.
        assert (Hmodule: get_module_function syscall_dispatch (syscall_dispatch ↦ sys_dispatch_function)
                         = OK (Some sys_dispatch_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_dispatch_function = OK (AST.Internal sys_dispatch_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H; eauto.
        destruct H as [?[Hsymbol ?]].
        inv H1.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H0 in Hsymbol. inv Hsymbol.
        assumption.
      Qed.

      Lemma Hsendpre: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge trap_sendtochan_pre = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external trap_sendtochan_pre trap_sendtochan_pre_sig)))
          /\ get_layer_primitive trap_sendtochan_pre tdispatch = 
             OK (Some (gensem trap_sendtochan_pre_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive trap_sendtochan_pre tdispatch = 
                       OK (Some (gensem trap_sendtochan_pre_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hsendpost: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge trap_sendtochan_post = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external trap_sendtochan_post null_signature)))
          /\ get_layer_primitive trap_sendtochan_post tdispatch = 
             OK (Some (gensem trap_sendtochan_post_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive trap_sendtochan_post tdispatch = 
                       OK (Some (gensem trap_sendtochan_post_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      (*Lemma Hchan_ready: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge sys_is_chan_ready = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external sys_is_chan_ready sys_is_chan_ready_sig)))
          /\ get_layer_primitive sys_is_chan_ready tdispatch = 
             OK (Some (gensem trap_ischanready_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive sys_is_chan_ready tdispatch = 
                       OK (Some (gensem trap_ischanready_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hsend: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge sys_sendto_chan = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external sys_sendto_chan sys_sendto_chan_sig)))
          /\ get_layer_primitive sys_sendto_chan tdispatch = 
             OK (Some (gensem trap_sendtochan_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive sys_sendto_chan tdispatch = 
                       OK (Some (gensem trap_sendtochan_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hrecv: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge sys_receive_chan = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external sys_receive_chan sys_receive_chan_sig)))
          /\ get_layer_primitive sys_receive_chan tdispatch = 
             OK (Some (gensem trap_receivechan_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive sys_receive_chan tdispatch = 
                       OK (Some (gensem trap_receivechan_spec)))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.


      Lemma Hcreate: 
        forall MCode_Asm s ge,
          make_globalenv s MCode_Asm tdispatch = ret ge ->
          (exists b, Genv.find_symbol ge sys_proc_create = Some b
                     /\ Genv.find_funct_ptr ge b = 
                        Some (External (EF_external sys_proc_create sys_proc_create_sig)))
          /\ get_layer_primitive sys_proc_create tdispatch = 
             OK (Some trap_proccreate_compatsem).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive sys_proc_create tdispatch = 
                       OK (Some trap_proccreate_compatsem))
          by reflexivity.
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

    Lemma Hsys_ready:
      forall ge s b,
        make_globalenv s (sys_ready ↦ sys_ready_function) tdispatch = ret ge ->
        find_symbol s sys_ready = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_ready_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_ready (sys_ready ↦ sys_ready_function)
                       = OK (Some sys_ready_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_ready_function = OK (AST.Internal sys_ready_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    Lemma Hsys_send:
      forall ge s b,
        make_globalenv s (sys_send ↦ sys_send_function) tdispatch = ret ge ->
        find_symbol s sys_send = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_send_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_send (sys_send ↦ sys_send_function)
                       = OK (Some sys_send_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_send_function = OK (AST.Internal sys_send_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    Lemma Hsys_recv:
      forall ge s b,
        make_globalenv s (sys_recv ↦ sys_recv_function) tdispatch = ret ge ->
        find_symbol s sys_recv = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_recv_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_recv (sys_recv ↦ sys_recv_function)
                       = OK (Some sys_recv_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_recv_function = OK (AST.Internal sys_recv_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    Lemma Hsys_spawn:
      forall ge s b,
        make_globalenv s (sys_spawn ↦ sys_spawn_function) tdispatch = ret ge ->
        find_symbol s sys_spawn = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_spawn_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_spawn (sys_spawn ↦ sys_spawn_function)
                       = OK (Some sys_spawn_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_spawn_function = OK (AST.Internal sys_spawn_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.*)

    Lemma Hsys_yield:
      forall ge s b,
        make_globalenv s (sys_yield ↦ sys_yield_function) tdispatch = ret ge ->
        find_symbol s sys_yield = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_yield_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_yield (sys_yield ↦ sys_yield_function)
                       = OK (Some sys_yield_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_yield_function = OK (AST.Internal sys_yield_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    Lemma Hsys_sendtochan_pre:
      forall ge s b,
        make_globalenv s (sys_sendtochan_pre ↦ sys_sendtochan_pre_function) tdispatch = ret ge ->
        find_symbol s sys_sendtochan_pre = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_sendtochan_pre_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_sendtochan_pre (sys_sendtochan_pre ↦ sys_sendtochan_pre_function)
                       = OK (Some sys_sendtochan_pre_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_sendtochan_pre_function = 
                         OK (AST.Internal sys_sendtochan_pre_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    Lemma Hsys_sendtochan_post:
      forall ge s b,
        make_globalenv s (sys_sendtochan_post ↦ sys_sendtochan_post_function) tdispatch = ret ge ->
        find_symbol s sys_sendtochan_post = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_sendtochan_post_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_sendtochan_post (sys_sendtochan_post ↦ sys_sendtochan_post_function)
                       = OK (Some sys_sendtochan_post_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_sendtochan_post_function = 
                         OK (AST.Internal sys_sendtochan_post_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    (*Lemma Hsys_run_vm:
      forall ge s b,
        make_globalenv s (sys_run_vm ↦ sys_run_vm_function) tdispatch = ret ge ->
        find_symbol s sys_run_vm = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal sys_run_vm_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function sys_run_vm (sys_run_vm ↦ sys_run_vm_function)
                       = OK (Some sys_run_vm_function)) by
          reflexivity.
      assert (HInternal: make_internal sys_run_vm_function = OK (AST.Internal sys_run_vm_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.*)

    Lemma Hpgf_handler:
      forall ge s b,
        make_globalenv s (pgf_handler ↦ pgf_handler_function) tdispatch = ret ge ->
        find_symbol s pgf_handler = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal pgf_handler_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function pgf_handler (pgf_handler ↦ pgf_handler_function)
                       = OK (Some pgf_handler_function)) by
          reflexivity.
      assert (HInternal: make_internal pgf_handler_function = OK (AST.Internal pgf_handler_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

  End WITHMEM.

End ASM_DATA.
