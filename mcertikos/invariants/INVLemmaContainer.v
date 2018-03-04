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
(*              Lemmas for invariants                                  *)
(*                                                                     *)
(*          Shu-Chun Weng <shu-chun.weng@yale.edu>                     *)
(*          David Costanzo <david.costanzo@yale.edu>                   *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)


Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import Constant.
Require Import RealParams.
Require Import CommonTactic.

Require Import AbstractDataType.
Require Import ObjContainer.
Require Import ObjProc.
Require Import ObjVMMFun.
Require Import ObjLMM.

Lemma parent_id_lt :
  forall i, i > 0 -> (i - 1) / max_children < i.
Proof.
  intros i Hi.
  apply Z.le_lt_trans with (m := i-1); try omega.
  apply Z.div_le_upper_bound; omega.
Qed.

Lemma child_id_gt :
  forall i k, i > 0 -> k >= 0 -> i < i * max_children + 1 + k.
Proof.
  intros; omega.
Qed.

Lemma parent_id_pos :
  forall i k, k < max_children -> i * max_children + 1 + k > 0 -> i >= 0.
Proof.
  intros; omega.
Qed.

Lemma parent_id_lt_child :
  forall i k, i >= 0 -> k >= 0 -> 
    (if zeq i 0 then 0 else (i - 1) / max_children) < i * max_children + 1 + k.
Proof.
  intros i k Hk.
  destruct (zeq i 0); subst; try omega.
  transitivity i.
  apply parent_id_lt; omega.
  apply child_id_gt; omega.
Qed.

Lemma z_lt_neq : 
  forall a b, a < b -> a <> b.
Proof.
  intros; omega.
Qed.

Ltac contr_eq_lt H :=
  match type of H with
  | ?a = ?b => apply (False_ind _); apply (z_lt_neq a b); auto
  end.

Section REAL_AC.

  Context `{real_params: RealParams}.

  Lemma real_container_valid : Container_valid real_AC.
  Proof.
    assert (Hrange:= real_quota_range).
    unfold real_AC; constructor; intros; zmap_solve; 
      try omega; try constructor; try solve [intuition].
    change Integers.Int.max_unsigned with 4294967295; try omega.
  Qed.

  Lemma real_quota_bounded_AT : 
    forall AT, quota_bounded_AT real_AC (real_AT AT) real_nps.
  Proof.
    intro; unfold quota_bounded_AT, real_AC.
    rewrite sum_quotas_inside; try omega; simpl; auto.
    rewrite real_quota_unused_pages_AT; try omega.
    rewrite real_quota_convert; omega.
  Qed.

  Lemma real_quota_bounded : 
    forall lat, quota_bounded real_AC (real_LAT lat) real_nps.
  Proof.
    intro; unfold quota_bounded, real_AC.
    rewrite sum_quotas_inside; try omega; simpl; auto.
    rewrite real_quota_unused_pages; try omega.
  Qed.

End REAL_AC.

Section CONTAINER_VALID_INV.

  Lemma empty_container_valid : Container_valid (ZMap.init Container_unused).
  Proof.
    constructor; simpl; intros; try rewrite ZMap.gi in *; simpl; auto; try discriminate.
  Qed.

  Lemma split_container_valid i n j adt adt' :
    Container_valid (AC adt) ->
    container_split_spec i n adt = Some (adt', j) ->
    Container_valid (AC adt').
  Proof.
    intros valid_container split_spec.
    assert (validC:= valid_container); destruct valid_container.
    functional inversion split_spec.

    unfold update_cusage, update_cchildren; constructor; simpl; intros; subst;
    rename i1 into i', _x0 into Hnc, _x1 into Hn, _x into Hi,
    H4 into Hused, H7 into Hused'; clear H1 H2 H3.
    - (* cvalid_id *)
      zmap_solve; subst; auto; omega.
    - (* cvalid_root *)
      zmap_solve.
      specialize (cvalid_id _ Hused).
      assert (Hcon1: i * max_children + 1 + Z.of_nat (length (cchildren c)) > i) by omega.
      assert (Hcon2: i * max_children + 1 + Z.of_nat (length (cchildren c)) > 0) by omega.
      split; intro Heq; rewrite Heq in *; omega.
    - (* cvalid_quota *)
      zmap_solve.
      specialize (cvalid_quota _ Hused); specialize (cvalid_usage _ Hused).
      subst c; omega.
    - (* cvalid_usage *)
      zmap_solve; try omega.
      subst c; specialize (cvalid_usage _ Hused); omega.
    - (* cvalid_parent_used *)
      zmap_solve.
    - (* cvalid_children_used *)
      apply Forall_forall; intros k Hin; zmap_solve; simpl in *.
      + specialize (cvalid_children_used _ Hused).
        destruct Hin; try congruence.
        rewrite Forall_forall in cvalid_children_used; auto.
      + specialize (cvalid_children_used _ Hused').    
        rewrite Forall_forall in cvalid_children_used; auto.
    - (* cvalid_parents_child *)
      rename H8 into Hi'; zmap_solve; simpl in *; specialize (cvalid_id _ Hused); rename e into Heq.
      + contr_eq_lt Heq; apply child_id_gt; omega.
      + contr_eq_lt Heq; rewrite cvalid_parent_id; auto.
        apply parent_id_lt_child; omega.
      + specialize (cvalid_parent_used _ Hused'); rewrite Heq in cvalid_parent_used.
        rewrite (cvalid_unused_child_id_range _ validC _ Hused) in cvalid_parent_used; try congruence.
        subst c; omega.
      + symmetry in Heq; assert (Hroot:= proj1 (cvalid_root _ Hused) Heq); congruence.
      + specialize (cvalid_parents_child _ Hused' Hi').
        rewrite Heq in cvalid_parents_child; auto.
      + congruence.
      + subst i'; auto.
    - (* cvalid_childrens_parent *)
      apply Forall_forall; intros k Hin; zmap_solve; simpl in *; try rename e into Heq; try solve [inv Hin].
      + specialize (cvalid_children_used _ Hused'); rewrite Forall_forall in cvalid_children_used.
        specialize (cvalid_children_used _ Hin).
        rewrite (cvalid_unused_child_id_range _ validC _ Hused) in cvalid_children_used; try congruence.
        subst c; omega.
      + destruct Hin as [Hin|Hin]; try congruence.
        specialize (cvalid_child_id_range _ Hused); rewrite Forall_forall in cvalid_child_id_range.
        apply cvalid_child_id_range in Hin.
        subst k; assert (Hcon:= child_id_gt i 0).
        specialize (cvalid_id _ Hused); omega.
      + specialize (cvalid_childrens_parent _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent; subst k; auto.
      + destruct Hin as [Hin|Hin]; try congruence.
        specialize (cvalid_childrens_parent _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent; subst i'; auto.
      + specialize (cvalid_childrens_parent _ Hused').
        rewrite Forall_forall in cvalid_childrens_parent; auto.
    - (* cvalid_cqb *)
      zmap_solve; simpl in *; try congruence.
      + constructor; omega.
      + constructor; zmap_solve; try omega.
        apply cqb_notin.
        specialize (cvalid_usage _ Hused); apply cqb_weaken.
        apply cqb_weaken.
        apply cvalid_cqb; auto.
        zmap_solve; simpl; omega.
        zmap_solve; omega.
        intro Hin; specialize (cvalid_children_used _ Hused).
        rewrite Forall_forall in cvalid_children_used; apply cvalid_children_used in Hin.
        rewrite (cvalid_unused_child_id_range _ validC _ Hused) in Hin; try congruence.
        subst c; omega.
      + apply cqb_notin.
        specialize (cvalid_usage _ Hused); apply cqb_weaken.
        apply cqb_weaken.
        apply cvalid_cqb; auto.
        zmap_solve; simpl; omega.
        zmap_solve; omega.
        intro Hin; specialize (cvalid_children_used _ Hused').
        rewrite Forall_forall in cvalid_children_used; apply cvalid_children_used in Hin.
        rewrite (cvalid_unused_child_id_range _ validC _ Hused) in Hin; try congruence.
        subst c; omega.
    - (* cvalid_nodup *)
      zmap_solve; constructor; simpl in *; subst.
      + intro Hin; specialize (cvalid_children_used _ Hused').
        rewrite Forall_forall in cvalid_children_used; apply cvalid_children_used in Hin.
        rewrite (cvalid_unused_child_id_range _ validC _ Hused) in Hin; try congruence.
        subst c; omega.
      + apply cvalid_nodup; auto.
    - (* cvalid_max_children *)
      zmap_solve; try omega.
      change (Z.of_nat (S (length (cchildren c))) <= 3).
      rewrite Nat2Z.inj_succ; omega.
    - (* cvalid_parent_id *)
      zmap_solve.
      destruct (zeq (i * 3 + 1 + Z.of_nat (length (cchildren c))) 0) as [Heq|Hneq].
      + specialize (cvalid_id _ Hused).
        assert (Hcon: i * max_children + 1 + Z.of_nat (length (cchildren c)) > 0) by omega.
        omega.
      + apply Zdiv.Zdiv_unique with (r:= Z.of_nat (length (cchildren c))); omega.
    - (* cvalid_child_id_range *)
      apply Forall_forall; intros k Hin; zmap_solve; simpl in *.
      + inv Hin.
      + change (Z.pos (Pos.of_succ_nat (length (cchildren c)))) with 
        (Z_of_nat (S (length (cchildren c)))).
        rewrite Nat2Z.inj_succ; destruct Hin as [Hin|Hin]; try omega.
        specialize (cvalid_child_id_range _ Hused).
        rewrite Forall_forall in cvalid_child_id_range.
        apply cvalid_child_id_range in Hin; subst c; omega.
      + specialize (cvalid_child_id_range _ Hused').
        rewrite Forall_forall in cvalid_child_id_range.
        apply cvalid_child_id_range in Hin; subst c; omega.
  Qed.

  Lemma alloc_container_valid':
    forall i (ac: ContainerPool),
      let c := ZMap.get i ac in
      let cur := mkContainer (cquota c) (cusage c + 1) (cparent c)
                             (cchildren c) (cused c) in
      Container_valid ac ->
      cusage c <? cquota c = true ->
      cused c = true ->
      Container_valid (ZMap.set i cur ac).
  Proof.
    intros. destruct H.
    econstructor; eauto 1; simpl; intros.
    - (* cvalid_id *)
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss in H; auto.
      rewrite ZMap.gso in H; auto.
    - (* cvalid_root *)
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss in H |- *; simpl.
      subst c; auto.
      rewrite ZMap.gso in H |- *; auto.
    - (* cvalid_quota *)
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss in *; simpl.
      apply cvalid_quota; auto.
      rewrite ZMap.gso in H |- *; auto.
    - (* cvalid_usage *)
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss in *; simpl.
      rewrite Z.ltb_lt in H0.
      specialize (cvalid_usage _ H); subst c; omega.
      rewrite ZMap.gso in H |- *; auto.
    - (* cvalid_parent_used *)
      destruct (zeq i0 i) as [Heq|Hneq]; subst.
      rewrite ZMap.gss in *; simpl.
      destruct (zeq (cparent c) i) as [Heq'|Hneq'].
      rewrite Heq'; rewrite ZMap.gss; auto.
      subst c; rewrite ZMap.gso; auto.
      rewrite (ZMap.gso _ _ Hneq); auto; simpl.
      destruct (zeq (cparent (ZMap.get i0 ac)) i) as [Heq''|Hneq''].
      rewrite Heq''; rewrite ZMap.gss in *; simpl; auto.
      rewrite ZMap.gso in *; auto.
    - (* cvalid_children_used *)
      apply Forall_forall; intros i'' Hin.
      destruct (zeq i'' i); subst.
      rewrite ZMap.gss; simpl; auto.
      rewrite ZMap.gso; auto.
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss in H, Hin; simpl in H, Hin.
      specialize (cvalid_children_used _ H).
      rewrite Forall_forall in cvalid_children_used; auto.
      rewrite ZMap.gso in H, Hin; auto.
      specialize (cvalid_children_used _ H).
      rewrite Forall_forall in cvalid_children_used; auto.
    - (* cvalid_parents_child *)
      rename H2 into Hi'_neq.
      destruct (zeq i0 i) as [Heq|Hneq]; subst.
      rewrite ZMap.gss; simpl.
      destruct (zeq (cparent c) i) as [Heq'|Hneq'].
      rewrite Heq'; rewrite ZMap.gss in *; simpl.
      specialize (cvalid_parents_child _ H1 Hi'_neq).
      subst c; rewrite Heq' in cvalid_parents_child; auto.
      rewrite ZMap.gso; auto.
      specialize (cvalid_parents_child _ H1 Hi'_neq); auto.
      rewrite (ZMap.gso _ _ Hneq) in H |- *; auto.
      destruct (zeq (cparent (ZMap.get i0 ac)) i) as [Heq''|Hneq''].
      specialize (cvalid_parents_child _ H Hi'_neq).
      rewrite Heq'' in cvalid_parents_child; rewrite Heq''; rewrite ZMap.gss; simpl; auto.
      rewrite ZMap.gso; auto.
    - (* cvalid_childrens_parent *)
      apply Forall_forall; intros i'' Hin.
      destruct (zeq i'' i); subst.
      rewrite ZMap.gss; simpl.
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss in H, Hin; simpl in H, Hin.
      specialize (cvalid_childrens_parent _ H).
      rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
      rewrite ZMap.gso in H, Hin; auto.
      specialize (cvalid_childrens_parent _ H).
      rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
      rewrite ZMap.gso; auto.
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss in H, Hin; simpl in H, Hin.
      specialize (cvalid_childrens_parent _ H).
      rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
      rewrite ZMap.gso in H, Hin; auto.
      specialize (cvalid_childrens_parent _ H).
      rewrite Forall_forall in cvalid_childrens_parent; subst c; auto.
    - (* cvalid_cqb *)
      apply cqb_weaken; simpl.
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss; simpl.
      apply cqb_bound with (n1 := cusage c); try omega.
      subst c; auto.
      rewrite ZMap.gso in H |- *; auto.
      specialize (cvalid_usage _ H1); subst c; omega.
    - (* cvalid_nodup *)
      destruct (zeq i0 i); subst.
      rewrite ZMap.gss; simpl; subst c; auto.
      rewrite ZMap.gso in H |- *; auto.
    - (* cvalid_max_children *)
      zmap_solve; eapply cvalid_max_children; eauto.
    - (* cvalid_parent_id *)
      zmap_solve; eapply cvalid_parent_id; eauto.
    - (* cvalid_child_id_range *)
      zmap_solve; eapply cvalid_child_id_range; eauto.
  Qed.

  Lemma alloc_container_valid i adt adt' z :
    Container_valid (AC adt) ->
    container_alloc_spec i adt = Some (adt',z) ->
    Container_valid (AC adt').
  Proof.
    intros. functional inversion H0; try congruence.
    eapply alloc_container_valid'; eauto.
  Qed.

End CONTAINER_VALID_INV.

Section QUOTA_BOUNDED_INV.

  Local Opaque nat_of_Z.

  Lemma split_quota_bounded_AT :
    forall d d' i n j,
      Container_valid (AC d) ->
      quota_bounded_AT (AC d) (AT d) (nps d) ->
      container_split_spec i n d = Some (d', j) ->
      quota_bounded_AT (AC d') (AT d') (nps d').
  Proof.
    intros d d' i n j Hvalid Hqb Hspec.
    functional inversion Hspec; subst; simpl in *.
    assert (Hi: 0 <= i < num_id) by (destruct Hvalid; auto).
    unfold quota_bounded_AT in *.
    rewrite sum_quotas_inside; simpl; auto; try solve [rewrite Z2Nat.id; omega].
    assert (j <> i) by omega; subst.
    unfold update_cusage, update_cchildren; zmap_simpl; simpl.
    subst c; rewrite cvalid_unused_next_child; auto.
    rewrite 2 sum_quotas_inside; simpl; auto; try solve [rewrite Z2Nat.id; omega].
    zmap_simpl; simpl; rewrites; simpl in *; omega.
  Qed.

  Lemma split_quota_bounded :
    forall d d' i n j,
      Container_valid (AC d) ->
      quota_bounded (AC d) (LAT d) (nps d) ->
      container_split_spec i n d = Some (d', j) ->
      quota_bounded (AC d') (LAT d') (nps d').
  Proof.
    intros d d' i n j Hvalid Hqb Hspec.
    functional inversion Hspec; subst; simpl in *.
    assert (Hi: 0 <= i < num_id) by (destruct Hvalid; auto).
    unfold quota_bounded in *.
    rewrite sum_quotas_inside; simpl; auto; try solve [rewrite Z2Nat.id; omega].
    assert (j <> i) by omega; subst.
    unfold update_cusage, update_cchildren; zmap_simpl; simpl.
    subst c; rewrite cvalid_unused_next_child; auto.
    rewrite 2 sum_quotas_inside; simpl; auto; try solve [rewrite Z2Nat.id; omega].
    zmap_simpl; simpl; rewrites; simpl in *; omega.
  Qed.

  Lemma container_alloc_quota_bounded_AT :
    forall d d' i p,
      Container_valid (AC d) ->
      quota_bounded_AT (AC d) (AT d) (nps d) ->
      container_alloc_spec i d = Some (d', p) ->
      quota_bounded_AT (AC d') (AT d') (nps d').
  Proof.
    intros d d' i p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl in *; try congruence.
    assert (Hi: 0 <= i < num_id) by (destruct Hvalid; auto).
    unfold quota_bounded_AT in *; simpl in *.
    rewrite sum_quotas_inside; auto; try solve [rewrite Z2Nat.id; omega].
    subst c; rewrites.
    rewrite unused_pages_AT_inside; auto; try solve [rewrite Z2Nat.id; omega].
    destruct _x as [? [[? Hp] ?]]; rewrite Hp.
    subst cur; simpl; omega.
  Qed.

  Lemma alloc_quota_bounded :
    forall d d' i p,
      Container_valid (AC d) ->
      quota_bounded (AC d) (LAT d) (nps d) ->
      alloc_spec i d = Some (d', p) ->
      quota_bounded (AC d') (LAT d') (nps d').
  Proof.
    intros d d' i p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl in *; try congruence.
    assert (Hi: 0 <= i < num_id) by (destruct Hvalid; auto).
    unfold quota_bounded in *; simpl in *.
    rewrite unused_pages_set.
    rewrite sum_quotas_inside; auto; try solve [rewrite Z2Nat.id; omega].
    subst c cur; simpl in *; rewrites; cases; try omega.
    destruct _x as [? [Hp ?]]; rewrite Hp; omega.
  Qed.

  Lemma ptAllocPDE_quota_bounded_AT :
    forall d d' i v p,
      Container_valid (AC d) ->
      quota_bounded_AT (AC d) (AT d) (nps d) ->
      ptAllocPDE_spec i v d = Some (d', p) ->
      quota_bounded_AT (AC d') (AT d') (nps d').
  Proof.
    intros d d' i v p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl in *; try congruence; subst.
    assert (Hi: 0 <= i < num_id) by (destruct Hvalid; auto).
    unfold quota_bounded_AT in *; simpl in *.
    rewrite unused_pages_AT_set.
    rewrite sum_quotas_inside; auto; try solve [rewrite Z2Nat.id; omega].
    subst c cur; simpl in *; rewrites; cases; try omega.
    destruct _x0 as [? [[? Hp] ?]]; rewrite Hp; omega.
  Qed.

  Lemma ptAllocPDE0_quota_bounded :
    forall d d' i v p,
      Container_valid (AC d) ->
      quota_bounded (AC d) (LAT d) (nps d) ->
      ptAllocPDE0_spec i v d = Some (d', p) ->
      quota_bounded (AC d') (LAT d') (nps d').
  Proof.
    intros d d' i v p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl in *; try congruence; subst.
    assert (Hi: 0 <= i < num_id) by (destruct Hvalid; auto).
    unfold quota_bounded in *; simpl in *.
    rewrite unused_pages_set.
    rewrite sum_quotas_inside; auto; try solve [rewrite Z2Nat.id; omega].
    subst c cur; simpl in *; rewrites; cases; try omega.
    destruct _x as [? [Hp ?]]; rewrite Hp; omega.
  Qed.

  Lemma ptInsertPTE_quota_bounded_AT :
    forall d d' i va pa pm,
      Container_valid (AC d) ->
      quota_bounded_AT (AC d) (AT d) (nps d) ->
      ptInsertPTE_spec i va pa pm d = Some d' ->
      quota_bounded_AT (AC d') (AT d') (nps d').
  Proof.
    intros d d' i va pa pm Hvalid Hqb Hspec.
    functional inversion Hspec; simpl.
    unfold quota_bounded_AT in *; rewrite unused_pages_AT_set; rewrites; cases; omega.
  Qed.

  Lemma ptInsertPTE0_quota_bounded :
    forall d d' i va pa pm,
      Container_valid (AC d) ->
      quota_bounded (AC d) (LAT d) (nps d) ->
      ptInsertPTE0_spec i va pa pm d = Some d' ->
      quota_bounded (AC d') (LAT d') (nps d').
  Proof.
    intros d d' i va pa pm Hvalid Hqb Hspec.
    functional inversion Hspec; simpl.
    clear H9; unfold quota_bounded in *; rewrite unused_pages_set; rewrites; cases; omega.
  Qed.

  Lemma ptInsert_quota_bounded_AT :
    forall d d' i va pa pm p,
      Container_valid (AC d) ->
      quota_bounded_AT (AC d) (AT d) (nps d) ->
      ptInsert_spec i va pa pm d = Some (d', p) ->
      quota_bounded_AT (AC d') (AT d') (nps d').
  Proof.
    intros d d' i va pa pm p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl in *; try congruence; subst.
    - eapply ptInsertPTE_quota_bounded_AT; eauto.
    - eapply ptAllocPDE_quota_bounded_AT; eauto.
    - assert (Hvalid': Container_valid (AC adt')) by
        (functional inversion H9; try congruence; eapply alloc_container_valid'; eauto).
      eapply ptInsertPTE_quota_bounded_AT; eauto.
      clear Hvalid'; eapply ptAllocPDE_quota_bounded_AT; eauto.
  Qed.

  Lemma ptInsert0_quota_bounded :
    forall d d' i va pa pm p,
      Container_valid (AC d) ->
      quota_bounded (AC d) (LAT d) (nps d) ->
      ptInsert0_spec i va pa pm d = Some (d', p) ->
      quota_bounded (AC d') (LAT d') (nps d').
  Proof.
    intros d d' i va pa pm p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl in *; try congruence; subst.
    - eapply ptInsertPTE0_quota_bounded; eauto.
    - eapply ptAllocPDE0_quota_bounded; eauto.
    - assert (Hvalid': Container_valid (AC adt')) by
        (functional inversion H8; try congruence; eapply alloc_container_valid'; eauto).
      eapply ptInsertPTE0_quota_bounded; eauto.
      clear Hvalid'; eapply ptAllocPDE0_quota_bounded; eauto.
  Qed.

  Lemma ptRmv_quota_bounded_AT :
    forall d d' i va p,
      Container_valid (AC d) ->
      quota_bounded_AT (AC d) (AT d) (nps d) ->
      ptRmv_spec i va d = Some (d', p) ->
      quota_bounded_AT (AC d') (AT d') (nps d').
  Proof.
    intros d d' i va p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl; try congruence; subst.
    unfold quota_bounded_AT in *; rewrite unused_pages_AT_set; rewrites; cases; omega.
  Qed.

  Lemma ptRmv0_quota_bounded :
    forall d d' i va p,
      Container_valid (AC d) ->
      quota_bounded (AC d) (LAT d) (nps d) ->
      ptRmv0_spec i va d = Some (d', p) ->
      quota_bounded (AC d') (LAT d') (nps d').
  Proof.
    intros d d' i va p Hvalid Hqb Hspec.
    functional inversion Hspec; simpl; try congruence; subst.
    unfold quota_bounded in *; rewrite unused_pages_set; rewrites; cases; omega.
  Qed.

  Lemma pfree_quota_bounded_AT :
    forall d i v,
      quota_bounded_AT (AC d) (AT d) (nps d) ->
      quota_bounded_AT (AC d) (ZMap.set i (ATValid false ATNorm v) (AT d)) (nps d).
  Proof.
    unfold quota_bounded_AT; intros d i v Hqb.
    rewrite unused_pages_AT_set.
    destruct (zle i 0); destruct (zlt (Z.of_nat (nat_of_Z (nps d - 1))) i);
      destruct (ZMap.get i (AT d)) as [[|] [| |]|]; omega.
  Qed.

  Lemma pfree_quota_bounded :
    forall d i v,
      quota_bounded (AC d) (LAT d) (nps d) ->
      quota_bounded (AC d) (ZMap.set i (LATValid false ATNorm v) (LAT d)) (nps d).
  Proof.
    unfold quota_bounded; intros d i v Hqb.
    rewrite unused_pages_set.
    destruct (zle i 0); destruct (zlt (Z.of_nat (nat_of_Z (nps d - 1))) i);
      destruct (ZMap.get i (LAT d)) as [[|] [| |]|]; omega.
  Qed.

  Lemma proc_create_quota_bounded :
    forall d d' b1 b2 b3 ofs i j,
      Container_valid (AC d) -> cused (ZMap.get (cid d) (AC d)) = true ->
      quota_bounded (AC d) (LAT d) (nps d) ->
      proc_create_spec d b1 b2 b3 ofs i = Some (d', j) ->
      quota_bounded (AC d') (LAT d') (nps d').
  Proof.
    unfold proc_create_spec; intros d d' b1 b2 b3 ofs i j Hvalid Hused Hqb Hspec.
    subdestruct; inv Hspec; simpl; unfold quota_bounded in *.
    assert (0 <= cid d < num_id) by (destruct Hvalid; auto).
    unfold update_cusage, update_cchildren; repeat rewrite sum_quotas_set; zmap_simpl; simpl.
    rewrites; cases; simpl in *; try omega.
    zmap_solve; try omega.
    rewrite cvalid_unused_next_child in Hdestruct11; auto; discriminate.
  Qed.

End QUOTA_BOUNDED_INV.

Lemma container_split_some :
  forall d id q,
    let c := ZMap.get id (AC d) in 
    let i := id * max_children + 1 + Z_of_nat (length (cchildren c)) in
    let child := mkContainer q 0 id nil true in
      ikern d = true -> ihost d = true -> cused (ZMap.get id (AC d)) = true ->
      0 <= i < num_id -> Z_of_nat (length (cchildren c)) < max_children ->
      0 <= q <= cquota c - cusage c ->
      container_split_spec id q d = 
        Some (d {AC: ZMap.set i child 
                       ((AC d) {usage id := cusage c + q}
                               {children id := (i :: cchildren c)})}, i).
Proof.
  unfold container_split_spec; intros.
  rewrite H, H0, H1.
  repeat (match goal with
          | [ |- context [if ?a then _ else _] ] => destruct a; try omega
          end); auto.
Qed.
