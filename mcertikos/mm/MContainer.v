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
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the raw abstract data and the primitives for the MBoot layer, 
which is also the bottom layer of memory management*)
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
Require Import LoadStoreSem1.
Require Import ObservationImpl.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import INVLemmaMemory.
Require Import INVLemmaContainer.

Require Import AbstractDataType.

Require Export ObjCPU.
Require Export ObjPMM.
Require Export ObjFlatMem.
Require Export ObjContainer.

Section WITHMEM.

  Local Open Scope Z_scope.
  
  Context `{real_params: RealParams}.

  (** ** Invariants at this layer *)
  Record high_level_invariant (abd: RData) :=
    mkInvariant {
        valid_nps: init abd = true -> kern_low <= nps abd <= maxpage;
        valid_kern: ikern abd = false -> pg abd = true /\ init abd = true;
        valid_AT_kern: init abd = true -> AT_kern (AT abd) (nps abd);
        valid_AT_usr: init abd = true -> AT_usr (AT abd) (nps abd);
        valid_ihost: ihost abd = false -> pg abd = true /\ init abd = true /\ ikern abd = true;
        valid_pperm: consistent_ppage (AT abd) (pperm abd) (nps abd);
        init_pperm: init abd = false -> (pperm abd) = ZMap.init PGUndef;
        valid_container: Container_valid (AC abd);
        valid_preinit_container: 
          init abd = false ->
          forall x, 0 <= x < num_id -> cused (ZMap.get x (AC abd)) <> true;
        valid_quota_bounded: quota_bounded_AT (AC abd) (AT abd) (nps abd)
    }.

  (** ** Definition of the abstract state ops *)
  Global Instance mcontainer_data_ops : CompatDataOps RData :=
    {
      empty_data := init_adt;
      high_level_invariant := high_level_invariant;
      low_level_invariant := low_level_invariant;
      kernel_mode adt := ikern adt = true /\ ihost adt = true;
      observe := ObservationImpl.observe
    }.

  (** ** Proofs that the initial abstract_data should satisfy the invariants*)    
  Section Property_Abstract_Data.

    Lemma empty_data_high_level_invariant:
      high_level_invariant init_adt.
    Proof.
      constructor; auto; simpl; try discriminate 1.
      - apply consistent_ppage_init.
      - apply empty_container_valid.
      - intros; simpl; rewrite ZMap.gi; discriminate.
    Qed.

    (** ** Definition of the abstract state *)
    Global Instance mcontainer_data_prf : CompatData RData.
    Proof.
      constructor.
      - apply low_level_invariant_incr.
      - apply empty_data_low_level_invariant.
      - apply empty_data_high_level_invariant.
    Qed.

  End Property_Abstract_Data.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    (** MContainer primitives *)

    Global Instance container_init_inv: PreservesInvariants container_init_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant.
      - apply real_nps_range.
      - apply real_at_kern_valid.
      - apply real_at_usr_valid.
      - rewrite init_pperm0; try assumption.
        apply real_pperm_valid.
      - apply real_container_valid.
      - apply real_quota_bounded_AT.
    Qed.

    Global Instance container_split_inv: PreservesInvariants container_split_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      exploit split_container_valid; eauto.
      subst c; contradiction (valid_preinit_container0 H (Int.unsigned i)).
      inv valid_container0; auto.
      apply split_quota_bounded_AT in H2; auto.
    Qed.
(*
    Fact remove_in {A} : forall (l : list A) eq a1 a2, a1 <> a2 -> In a2 l -> In a2 (remove eq a1 l).
    Proof.
      induction l; simpl; intros; auto.
      destruct H0; subst.
      destruct (eq a1 a2); simpl; auto; contradiction.
      destruct (eq a1 a); simpl; auto.
    Qed.

    Fact remove_in_rev {A} : forall (l : list A) eq a1 a2, In a2 (remove eq a1 l) -> a1 <> a2 /\ In a2 l.
    Proof.
      induction l; simpl; intros; auto.
      destruct (eq a1 a); subst.
      apply IHl in H; destruct H; auto.
      simpl in H; destruct H; subst; auto.
      apply IHl in H; destruct H; auto.
    Qed.

    Fact remove_nodup {A} : forall (l : list A) eq a, NoDup l -> NoDup (remove eq a l).
    Proof.
      induction l; simpl; intros.
      constructor.
      inv H; destruct (eq a0 a); subst; auto.
      constructor; auto.
      intro H'; contradiction H2.
      apply remove_in_rev in H'; destruct H'; auto.
    Qed.


    Global Instance container_revoke_inv: PreservesInvariants (fun i d => container_revoke_spec d i).
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant;
        rename H3 into Hused, H1 into Hc_nil, _x into Hi_neq, i0 into i', H into Hused'.
      - (* cvalid_id *)
        destruct (zeq i' (cparent c)); subst.
        apply cvalid_id; apply cvalid_parent_used; auto.
        destruct (zeq i' (Int.unsigned i)); subst; auto.
        rewrite 2 ZMap.gso in Hused'; auto.
      - (* cvalid_root *)
        destruct (zeq i' (cparent c)); subst.
        rewrite ZMap.gss in Hused' |- *; simpl in Hused' |- *; subst p c; auto.
        rewrite ZMap.gso in Hused' |- *; auto.
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss in Hused'; inv Hused'.
        rewrite ZMap.gso in Hused' |- *; auto.
      - (* cvalid_usage *)
        destruct (zeq i' (cparent c)); subst.
        + rewrite ZMap.gss; simpl; split.
          specialize (cvalid_cqb _ (cvalid_parent_used _ Hused)).
          apply cqb_remove with (c := Int.unsigned i) in cvalid_cqb; auto.
          apply cqb_nonneg in cvalid_cqb; subst p c; omega.
          apply Z.le_trans with (m := cusage p).
          specialize (cvalid_usage _ Hused); subst c; omega.
          specialize (cvalid_usage _ (cvalid_parent_used _ Hused)); subst p c; omega.
        + rewrite ZMap.gso; auto.
          destruct (zeq i' (Int.unsigned i)); subst.
          rewrite ZMap.gss; simpl; omega.
          rewrite ZMap.gso; auto.
          rewrite 2 ZMap.gso in Hused'; auto.
      - (* cvalid_parent_used *)
        destruct (zeq i' (cparent c)) as [Heq|Hneq]; subst.
        + rewrite ZMap.gss in Hused' |- *; simpl in Hused' |- *.
          destruct (zeq (cparent p) (cparent c)) as [Heq1|Hneq1].
          rewrite Heq1; rewrite ZMap.gss; auto.
          rewrite ZMap.gso; auto.
          destruct (zeq (cparent p) (Int.unsigned i)) as [Heq2|Hneq2].
          destruct (zeq (cparent c) 0) as [Heq3|Hneq3].
          contradiction Hneq1; rewrite Heq3; subst p c; rewrite Heq3.
          rewrite Heq3 in Hused'; symmetry; apply (cvalid_root _ Hused'); auto.
          specialize (cvalid_parents_child _ (cvalid_parent_used _ Hused) Hneq3).
          subst p c; rewrite Heq2 in cvalid_parents_child; rewrite Hc_nil in cvalid_parents_child.
          inv cvalid_parents_child.
          rewrite ZMap.gso; subst p c; auto.
        + rewrite (ZMap.gso _ _ Hneq) in Hused' |- *; auto.
          destruct (zeq i' (Int.unsigned i)) as [Heq'|Hneq']; subst.
          rewrite ZMap.gss in Hused'; inv Hused'.
          rewrite (ZMap.gso _ _ Hneq') in Hused' |- *; auto.
          destruct (zeq (cparent (ZMap.get i' (AC d))) (cparent c)) as [Heq''|Hneq''].
          rewrite Heq''; rewrite ZMap.gss.
          simpl; subst p c; auto.
          rewrite 2 ZMap.gso; auto.
          destruct (zeq i' 0) as [Heq'''|Hneq''']; subst.
          replace (cparent (ZMap.get 0 (AC d))) with 0; auto.
          rewrite (cvalid_root _ Hused'); auto.
          specialize (cvalid_parents_child _ Hused' Hneq''').
          intro Heq_i; rewrite Heq_i in cvalid_parents_child.
          subst c; rewrite Hc_nil in cvalid_parents_child; inv cvalid_parents_child.
      - (* cvalid_children_used *)
        apply Forall_forall; intros i'' Hin.
        destruct (zeq i' (cparent c)) as [Heq|Hneq]; subst.
        + rewrite ZMap.gss in Hused', Hin; simpl in Hused', Hin.
          apply remove_in_rev in Hin; destruct Hin as [Hneq' Hin].
          destruct (zeq i'' (cparent c)); subst.
          rewrite ZMap.gss; simpl; auto.
          rewrite 2 ZMap.gso; auto.
          specialize (cvalid_children_used _ Hused').
          rewrite Forall_forall in cvalid_children_used; auto.
        + rewrite ZMap.gso in Hused', Hin; auto.
          destruct (zeq i' (Int.unsigned i)); subst.
          rewrite ZMap.gss in Hused'; inv Hused'.
          rewrite ZMap.gso in Hused', Hin; auto.
          destruct (zeq i'' (cparent c)); subst.
          rewrite ZMap.gss; simpl.
          specialize (cvalid_children_used _ Hused').
          rewrite Forall_forall in cvalid_children_used; subst p c; auto.
          rewrite ZMap.gso; auto.
          destruct (zeq i'' (Int.unsigned i)); subst.
          specialize (cvalid_childrens_parent _ Hused').
          rewrite Forall_forall in cvalid_childrens_parent.
          specialize (cvalid_childrens_parent _ Hin); contradiction Hneq; auto.
          rewrite ZMap.gso; auto.
          specialize (cvalid_children_used _ Hused').
          rewrite Forall_forall in cvalid_children_used; auto.
      - (* cvalid_parents_child *)
        rename H6 into Hi'_neq; destruct (zeq i' (cparent c)) as [Heq|Hneq]; subst.
        + rewrite ZMap.gss in Hused' |- *.
          destruct (zeq (cparent p') (cparent c)) as [Heq1|Hneq1].
          simpl in Hused', Heq1; subst p; symmetry in Heq1.
          apply (cvalid_root _ Hused') in Heq1; contradiction.
          rewrite ZMap.gso; auto; simpl in Hused' |- *.
          destruct (zeq (cparent p) (Int.unsigned i)) as [Heq2|Hneq2].
          specialize (cvalid_parents_child _ Hused' Hi'_neq).
          subst p c; rewrite Heq2 in cvalid_parents_child.
          rewrite Hc_nil in cvalid_parents_child; inv cvalid_parents_child.
          rewrite ZMap.gso; auto.
          specialize (cvalid_parents_child _ Hused' Hi'_neq); auto.
        + rewrite (ZMap.gso _ _ Hneq) in Hused' |- *; auto.
          destruct (zeq i' (Int.unsigned i)) as [Heq'|Hneq']; subst.
          rewrite ZMap.gss in Hused'; inv Hused'.
          rewrite (ZMap.gso _ _ Hneq') in Hused' |- *; auto.
          destruct (zeq (cparent (ZMap.get i' (AC d))) (cparent c)) as [Heq1|Hneq1].
          rewrite Heq1; rewrite ZMap.gss; simpl.
          apply remove_in; auto.
          specialize (cvalid_parents_child _ Hused' Hi'_neq).
          rewrite Heq1 in cvalid_parents_child; auto.
          rewrite ZMap.gso; auto.
          destruct (zeq (cparent (ZMap.get i' (AC d))) (Int.unsigned i)) as [Heq2|Hneq2].
          specialize (cvalid_parents_child _ Hused' Hi'_neq).
          rewrite Heq2 in cvalid_parents_child.
          subst c; rewrite Hc_nil in cvalid_parents_child; inv cvalid_parents_child.
          rewrite ZMap.gso; auto.
      - (* cvalid_childrens_parent *)
        apply Forall_forall; intros i'' Hin.
        destruct (zeq i' (cparent c)) as [Heq|Hneq]; subst.
        + rewrite ZMap.gss in Hused', Hin; simpl in Hused', Hin.
          apply remove_in_rev in Hin; destruct Hin as [Hneq' Hin].
          destruct (zeq i'' (cparent c)); subst.
          rewrite ZMap.gss; simpl.
          specialize (cvalid_childrens_parent _ Hused').
          rewrite Forall_forall in cvalid_childrens_parent; subst p c; auto.
          rewrite 2 ZMap.gso; auto.
          specialize (cvalid_childrens_parent _ Hused').
          rewrite Forall_forall in cvalid_childrens_parent; auto.
        + rewrite ZMap.gso in Hused', Hin; auto.
          destruct (zeq i' (Int.unsigned i)); subst.
          rewrite ZMap.gss in Hused'; inv Hused'.
          rewrite ZMap.gso in Hused', Hin; auto.
          destruct (zeq i'' (cparent c)); subst.
          rewrite ZMap.gss; simpl.
          specialize (cvalid_childrens_parent _ Hused').
          rewrite Forall_forall in cvalid_childrens_parent; subst p c; auto.
          rewrite ZMap.gso; auto.
          destruct (zeq i'' (Int.unsigned i)); subst.
          specialize (cvalid_childrens_parent _ Hused').
          rewrite Forall_forall in cvalid_childrens_parent.
          specialize (cvalid_childrens_parent _ Hin); contradiction Hneq; auto.
          rewrite ZMap.gso; auto.
          specialize (cvalid_childrens_parent _ Hused').
          rewrite Forall_forall in cvalid_childrens_parent; auto.
      - (* cvalid_cqb *)
        destruct (zeq i' (cparent c)) as [Heq|Hneq]; subst.
        + rewrite ZMap.gss in Hused' |- *; simpl in Hused' |- *.
          destruct (zeq (cparent c) (Int.unsigned i)) as [Heq1|Hneq1].
          subst c; symmetry in Heq1; rewrite (cvalid_root _ Hused) in Heq1; contradiction.
          apply cqb_weaken; simpl.
          apply cqb_weaken; simpl.
          apply cqb_remove.
          subst p; auto.
          apply (cvalid_parents_child _ Hused Hi_neq).
          specialize (cvalid_usage _ Hused); omega.
          rewrite ZMap.gso; auto.
          specialize (cvalid_usage _ Hused'); subst p; omega.
        + rewrite ZMap.gso in Hused' |- *; auto.
          destruct (zeq i' (Int.unsigned i)); subst.
          rewrite ZMap.gss in Hused'; inv Hused'.
          rewrite ZMap.gso in Hused' |- *; auto.
          destruct (zeq (cparent c) (Int.unsigned i)) as [Heq1|Hneq1].
          subst c; symmetry in Heq1; rewrite (cvalid_root _ Hused) in Heq1; contradiction.
          apply cqb_weaken; simpl.
          apply cqb_weaken; simpl.
          subst p; auto.
          specialize (cvalid_usage _ Hused); omega.
          rewrite ZMap.gso; auto.
          specialize (cvalid_usage _ (cvalid_parent_used _ Hused)); subst p c; omega.
      - (* cvalid_nodup *)
        destruct (zeq i' (cparent c)); subst.
        + rewrite ZMap.gss; simpl.
          apply remove_nodup.
          apply (cvalid_nodup _ (cvalid_parent_used _ Hused)).
        + rewrite ZMap.gso in Hused' |- *; auto.
          destruct (zeq i' (Int.unsigned i)); subst.
          rewrite ZMap.gss; constructor.
          rewrite ZMap.gso in Hused' |- *; auto.
    Qed.
*)

    Section CONTAINER_ALLOC.

      Lemma container_alloc_high_level_inv:
        forall d d' i n,
          container_alloc_spec i d = Some (d', n) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst c; try subst c0; subst; eauto. 
        inv H0. constructor; simpl; eauto; try congruence.
        - intros; eapply AT_kern_norm'; eauto.
        - intros; eapply AT_usr_norm; eauto.
        - eapply consistent_ppage_norm_alloc; eauto.
        - eapply alloc_container_valid'; eauto.
        - apply container_alloc_quota_bounded_AT in H; auto.
      Qed.
      
      Lemma container_alloc_low_level_inv:
        forall d d' n n' i,
          container_alloc_spec i d = Some (d', n) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst c; try subst c0; subst; eauto.
        inv H0. constructor; eauto.
      Qed.

      Lemma container_alloc_kernel_mode:
        forall d d' i n,
          container_alloc_spec i d = Some (d', n) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst c; try subst c0; subst; eauto.
      Qed.

      Global Instance container_alloc_inv: PreservesInvariants container_alloc_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply container_alloc_low_level_inv; eassumption.
        - eapply container_alloc_high_level_inv; eassumption.
        - eapply container_alloc_kernel_mode; eassumption.
      Qed.

    End CONTAINER_ALLOC.
(*      
    Global Instance container_free_inv: PreservesInvariants (fun i d => container_free_spec d i).  
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant;
        rename H1 into Hused, H into Hused', i0 into i'.
      - (* cvalid_id *)
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss in Hused'; auto.
        rewrite ZMap.gso in Hused'; auto.
      - (* cvalid_root *)
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss in Hused' |- *; simpl.
        subst c; auto.
        rewrite ZMap.gso in Hused' |- *; auto.
      - (* cvalid_usage *)
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss; simpl.
        rewrite Z.ltb_lt in H0.
        specialize (cvalid_usage _ Hused); subst c; omega.
        rewrite ZMap.gso in Hused' |- *; auto.
      - (* cvalid_parent_used *)
        destruct (zeq i' (Int.unsigned i)) as [Heq|Hneq]; subst.
        rewrite ZMap.gss in Hused' |- *; simpl.
        destruct (zeq (cparent c) (Int.unsigned i)) as [Heq'|Hneq'].
        rewrite Heq'; rewrite ZMap.gss; auto.
        subst c; rewrite ZMap.gso; auto.
        rewrite (ZMap.gso _ _ Hneq); auto; simpl.
        destruct (zeq (cparent (ZMap.get i' (AC d))) (Int.unsigned i)) as [Heq''|Hneq''].
        rewrite Heq''; rewrite ZMap.gss; simpl; auto.
        rewrite ZMap.gso in Hused' |- *; auto.
      - (* cvalid_children_used *)
        apply Forall_forall; intros i'' Hin.
        destruct (zeq i'' (Int.unsigned i)); subst.
        rewrite ZMap.gss; simpl; auto.
        rewrite ZMap.gso; auto.
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss in Hused', Hin; simpl in Hused', Hin.
        specialize (cvalid_children_used _ Hused').
        rewrite Forall_forall in cvalid_children_used; auto.
        rewrite ZMap.gso in Hused', Hin; auto.
        specialize (cvalid_children_used _ Hused').
        rewrite Forall_forall in cvalid_children_used; auto.
      - (* cvalid_parents_child *)
        rename H5 into Hi'_neq.
        destruct (zeq i' (Int.unsigned i)) as [Heq|Hneq]; subst.
        rewrite ZMap.gss; simpl.
        destruct (zeq (cparent c) (Int.unsigned i)) as [Heq'|Hneq'].
        rewrite Heq'; rewrite ZMap.gss; simpl.
        specialize (cvalid_parents_child _ Hused Hi'_neq).
        subst c; rewrite Heq' in cvalid_parents_child; auto.
        rewrite ZMap.gso; auto.
        specialize (cvalid_parents_child _ Hused Hi'_neq); auto.
        rewrite (ZMap.gso _ _ Hneq) in Hused' |- *; auto.
        destruct (zeq (cparent (ZMap.get i' (AC d))) (Int.unsigned i)) as [Heq''|Hneq''].
        specialize (cvalid_parents_child _ Hused' Hi'_neq).
        rewrite Heq'' in cvalid_parents_child; rewrite Heq''; rewrite ZMap.gss; simpl; auto.
        rewrite ZMap.gso; auto.
      - (* cvalid_childrens_parent *)
        apply Forall_forall; intros i'' Hin.
        destruct (zeq i'' (Int.unsigned i)); subst.
        rewrite ZMap.gss; simpl.
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss in Hused', Hin; simpl in Hused', Hin.
        specialize (cvalid_childrens_parent _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
        rewrite ZMap.gso in Hused', Hin; auto.
        specialize (cvalid_childrens_parent _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
        rewrite ZMap.gso; auto.
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss in Hused', Hin; simpl in Hused', Hin.
        specialize (cvalid_childrens_parent _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
        rewrite ZMap.gso in Hused', Hin; auto.
        specialize (cvalid_childrens_parent _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
      - (* cvalid_cqb *)
(* change spec of free to check that current usage is strictly greater than sum of child quotas *)
        apply cqb_weaken; simpl.
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss; simpl.
        apply cqb_bound with (n1 := cusage c); try omega.
        subst c; auto.
        rewrite ZMap.gso in Hused' |- *; auto.
        specialize (cvalid_usage _ Hused); subst c; omega.
      - (* cvalid_nodup *)
        destruct (zeq i' (Int.unsigned i)); subst.
        rewrite ZMap.gss; simpl; subst c; auto.
        rewrite ZMap.gso in Hused' |- *; auto.
    Qed.
 *)

    (** passthrough primitives *)

    Global Instance pfree'_inv: PreservesInvariants pfree'_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply AT_kern_norm; eauto. 
      - intros; eapply AT_usr_norm; eauto.
      - eapply consistent_ppage_norm_undef; eauto.
      - apply pfree_quota_bounded_AT; auto.
    Qed.

    Global Instance setPG_inv: PreservesInvariants setPG0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance clearCR2_inv: PreservesInvariants clearCR2_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance setCR3_inv: SetCR3Invariants setCR30_spec.
    Proof.
      constructor; intros.
      - functional inversion H; inv H0; constructor; trivial.
      - functional inversion H; inv H0; constructor; auto.
      - functional inversion H; simpl in *; assumption.
    Qed.

    Global Instance set_at_c_inv: PreservesInvariants set_at_c0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply AT_kern_norm; eauto. 
      - intros; eapply AT_usr_norm; eauto.
      - eapply consistent_ppage_norm; eauto.
      - unfold quota_bounded_AT in *; rewrite unused_pages_AT_set; cases; omega.
    Qed.

    Global Instance device_output_inv: PreservesInvariants device_output_spec.
    Proof. 
      preserves_invariants_simpl'' low_level_invariant high_level_invariant; eauto.
    Qed.

    Global Instance trapin_inv: PrimInvariants trapin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance trapout_inv: PrimInvariants trapout0_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance hostin_inv: PrimInvariants hostin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance hostout_inv: PrimInvariants hostout_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance fstore_inv: PreservesInvariants fstore0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; trivial;
      functional inversion H; subst; auto.
    Qed.

    Global Instance flatmem_copy_inv: PreservesInvariants flatmem_copy0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto.      
    Qed.

  End INV.

  Definition exec_loadex {F V} := exec_loadex1 (F := F) (V := V).

  Definition exec_storeex {F V} := exec_storeex1 (flatmem_store:= flatmem_store) (F := F) (V := V).

  Global Instance flatmem_store_inv: FlatmemStoreInvariant (flatmem_store:= flatmem_store).
  Proof.
    split; inversion 1; intros. 
    - functional inversion H0; constructor; auto.
    - functional inversion H1; constructor; auto.
  Qed.

  Global Instance trapinfo_set_inv: TrapinfoSetInvariant.
  Proof.
    split; inversion 1; intros; constructor; auto.
  Qed.

  (** * Layer Definition *)
  Definition mcontainer_fresh : compatlayer (cdata RData) :=
    container_init ↦ gensem container_init_spec
           ⊕ container_get_parent ↦ gensem container_get_parent_spec
           ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
           ⊕ container_get_quota ↦ gensem container_get_quota_spec
           ⊕ container_get_usage ↦ gensem container_get_usage_spec
           ⊕ container_can_consume ↦ gensem container_can_consume_spec
           ⊕ container_split ↦ gensem container_split_spec
(*           ⊕ container_revoke ↦ gensem container_revoke_spec*)
           ⊕ container_alloc ↦ gensem container_alloc_spec.
(*           ⊕ container_free ↦ gensem container_free_spec*)

  (** ** Layer Definition passthrough  *)
  Definition mcontainer_passthrough: compatlayer (cdata RData) :=
    fload ↦ gensem fload'_spec
          ⊕ fstore ↦ gensem fstore0_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy0_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ set_pg ↦ gensem setPG0_spec
          ⊕ pfree ↦ gensem pfree'_spec
          ⊕ clear_cr2 ↦ gensem clearCR2_spec
          ⊕ set_cr3 ↦ setCR3_compatsem setCR30_spec
          ⊕ at_get_c ↦ gensem get_at_c_spec
          ⊕ at_set_c ↦ gensem set_at_c0_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ trap_out ↦ primcall_general_compatsem trapout0_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  Definition mcontainer : compatlayer (cdata RData) := mcontainer_fresh ⊕ mcontainer_passthrough.

End WITHMEM.
