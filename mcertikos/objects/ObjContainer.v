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
Require Import RealParams.
Require Import Constant.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealPTPool.
Require Import CalRealPT.

Section PRIM_Container.

  Context `{real_params: RealParams}.

    Function container_init_spec (mbi: Z) (adt: RData) : option RData :=
      match (init adt, pg adt, ikern adt, ihost adt) with
        | (false, false, true, true) =>
          Some adt {vmxinfo: real_vmxinfo} {AT: real_AT (AT adt)} {nps: real_nps}
                   {init: true} {AC: real_AC}
        | _ => None
      end.

    Function container_init0_spec (mbi: Z) (adt: RData) : option RData :=
      match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
        | (false, false, true, true, true) =>
          Some adt {vmxinfo: real_vmxinfo} {AT: real_AT (AT adt)} {nps: real_nps}
                   {init: true} {AC: real_AC}
        | _ => None
      end.

    Function container_get_parent_spec (i: Z) (adt: RData): option Z :=
      let c := ZMap.get i (AC adt) in
      match (ikern adt, ihost adt, cused c) with
        | (true, true, true) => Some (cparent c) 
        | _ => None
      end.

    Function container_get_nchildren_spec (i: Z) (adt: RData) : option Z :=
      let c := ZMap.get i (AC adt) in
      match (ikern adt, ihost adt, cused c) with
        | (true, true, true) => Some (Z_of_nat (length (cchildren c)))
        | _ => None
      end.

    Function container_get_quota_spec (i: Z) (adt: RData) : option Z :=
      let c := ZMap.get i (AC adt) in
      match (ikern adt, ihost adt, cused c) with
        | (true, true, true) => Some (cquota c) 
        | _ => None
      end.

    Function container_get_usage_spec (i: Z) (adt: RData): option Z :=
      let c := ZMap.get i (AC adt) in
      match (ikern adt, ihost adt, cused c) with
        | (true, true, true) => Some (cusage c)
        | _ => None
      end.

    Function container_can_consume_spec (i: Z) (n: Z) (adt: RData) : option Z :=
      match (ikern adt, ihost adt, cused (ZMap.get i (AC adt))) with
        | (true, true, true) => 
          Some (if zle_le 0 n (cquota (ZMap.get i (AC adt)) - cusage (ZMap.get i (AC adt))) 
                then 1 else 0)
        | _ => None
      end.

    Function container_split_spec (id: Z) (q: Z) (adt: RData) : option (RData*Z) :=
      let c := ZMap.get id (AC adt) in 
      let i := id * max_children + 1 + Z_of_nat (length (cchildren c)) in
      match (ikern adt, ihost adt, cused c, zle_lt 0 i num_id,
             zlt (Z_of_nat (length (cchildren c))) max_children,
             zle_le 0 q (cquota c - cusage c)) with
      | (true, true, true, left _, left _, left _) =>
           let child := mkContainer q 0 id nil true in
             Some (adt {AC: ZMap.set i child ((AC adt) {usage id := cusage c + q}
                                                       {children id := (i :: cchildren c)})}, i)
      | _ => None
      end.
(*
    Function container_revoke_spec (adt: RData) (i: Z) : option RData :=
      if zeq i 0 then None else
      let c := ZMap.get i (AC adt) in 
      let p := ZMap.get (cparent c) (AC adt) in 
      match (ikern adt, ihost adt, cused c, cchildren c) with
      | (true, true, true, nil) => 
         let p' := mkContainer (cquota p) (cusage p - cquota c)
                     (cparent p) (remove zeq i (cchildren p)) (cused p) in
           Some (mkRData (HP adt) (MM adt) (MMSize adt)
                (ZMap.set (cparent c) p' (ZMap.set i Container_unused (AC adt)))
                (CR3 adt) (ti adt) (pg adt) (ikern adt) (ihost adt))
      | _ => None
      end.
*)
    Function container_alloc_spec (id: Z) (adt: RData)  : option (RData*Z) :=
      let c := ZMap.get id (AC adt) in
      match (ikern adt, ihost adt, init adt, cused c) with          
      | (true, true, true, true) =>
        if cusage c <? cquota c then
          let cur := mkContainer (cquota c) (cusage c + 1) (cparent c)
                                 (cchildren c) (cused c) in
          match first_free (AT adt) (nps adt) with
            | inleft (exist i _) => 
              Some (adt {AT: ZMap.set i (ATValid true ATNorm 0) (AT adt)}
                        {pperm: ZMap.set i PGAlloc (pperm adt)}
                        {AC: ZMap.set id cur (AC adt)}, i)
            | _ => None
          end
        else Some (adt, 0)
      | _ => None
    end.
(*
    Function container_free_spec (adt: RData) (i: Z) : option RData :=
      let c := ZMap.get i (AC adt) in 
      match (ikern adt, ihost adt, cused c, 0 <? cusage c) with 
      | (true, true, true, true) =>
        let cur := mkContainer (cquota c) (cusage c - 1) (cparent c)
                        (cchildren c) (cused c) in
        Some (mkRData (HP adt) (MM adt) (MMSize adt) (ZMap.set i cur (AC adt))
             (CR3 adt) (ti adt) (pg adt) (ikern adt) (ihost adt))
      | _ => None
      end.
*)

End PRIM_Container.

Section CVALID.

  Lemma cvalid_unused_child_id_range :
    forall C, Container_valid C ->
      forall i, cused (ZMap.get i C) = true -> 
        forall j, i * max_children + 1 + Z_of_nat (length (cchildren (ZMap.get i C))) <=
                  j < i * max_children + 1 + max_children -> cused (ZMap.get j C) = false.
  Proof.
    intros C Hvalid i Hi j Hrange; destruct Hvalid.
    destruct (cused (ZMap.get j C)) eqn:Hj; auto.
    destruct (zeq j 0) as [Heq|Hneq]; subst.
    specialize (cvalid_id _ Hi); omega.    
    specialize (cvalid_parents_child _ Hj Hneq).
    rewrite (cvalid_parent_id _ Hj) in cvalid_parents_child.
    destruct (zeq j 0); try congruence.
    replace ((j-1) / max_children) with i in cvalid_parents_child.
    specialize (cvalid_child_id_range _ Hi); rewrite Forall_forall in cvalid_child_id_range.
    specialize (cvalid_child_id_range _ cvalid_parents_child); omega.
    apply Zdiv.Zdiv_unique with (r:= j - (i * max_children + 1)); omega.
  Qed.

  Lemma cvalid_unused_next_child :
    forall C, Container_valid C ->
      forall i, cused (ZMap.get i C) = true ->
        Z_of_nat (length (cchildren (ZMap.get i C))) < max_children ->
        cused (ZMap.get (i * max_children + 1 + 
                         Z_of_nat (length (cchildren (ZMap.get i C)))) C) = false.
  Proof.
    intros; eapply cvalid_unused_child_id_range; eauto; omega.
  Qed.

  Lemma cvalid_child_id_pos :
    forall C, Container_valid C ->
      forall i, cused (ZMap.get i C) = true ->
        forall k, k >= 0 -> 0 < i * max_children + 1 + k.
  Proof.
    intros C Hvalid i Hi k Hk; destruct Hvalid.
    specialize (cvalid_id _ Hi); omega.
  Qed.

  Lemma cvalid_child_id_neq :
    forall C, Container_valid C ->
      forall i, cused (ZMap.get i C) = true ->
        i <> i * max_children + 1 + Z_of_nat (length (cchildren (ZMap.get i C))).
  Proof.
    intros C Hvalid i Hi; destruct Hvalid.
    assert (Hmath: forall i j, 0 <= i -> 0 <= j -> i <> i * max_children + 1 + j) by (intros; omega).
    apply Hmath.
    specialize (cvalid_id _ Hi); omega.
    apply Nat2Z.is_nonneg.
  Qed.

End CVALID.

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

  Context {re1: relate_impl_iflags}.
  Context {re2: relate_impl_init}.
  Context {re3: relate_impl_AC}.

  Section CONTAINER_INIT_SIM.

    Context `{real_params: RealParams}.

    Context {re4: relate_impl_AT}.
    Context {re5: relate_impl_nps}.
    Context {re6: relate_impl_vmxinfo}.

    Lemma container_init_exist:
      forall s habd habd' labd mbi f,
        container_init_spec mbi habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', container_init_spec mbi labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold container_init_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_AC_eq; eauto.
      exploit relate_impl_AT_eq; eauto.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_AC_update.
      apply relate_impl_init_update.
      apply relate_impl_nps_update. 
      apply relate_impl_AT_update.
      apply relate_impl_vmxinfo_update. assumption.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_init}.
    Context {mt3: match_impl_AC}.
    Context {mt4: match_impl_AT}.
    Context {mt5: match_impl_nps}.
    Context {mt6: match_impl_vmxinfo}.

    Lemma container_init_match:
      forall s d d' m mbi f,
        container_init_spec mbi d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold container_init_spec; intros. subdestruct. inv H.      
      apply match_impl_AC_update.
      apply match_impl_init_update.
      apply match_impl_nps_update. 
      apply match_impl_AT_update.
      apply match_impl_vmxinfo_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) container_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) container_init_spec}.

    Lemma container_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem container_init_spec)
            (id ↦ gensem container_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit container_init_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply container_init_match; eauto.
    Qed.

  End CONTAINER_INIT_SIM.

  Section CONTAINER_INIT0_SIM.

    Context `{real_params: RealParams}.

    Context {re4: relate_impl_AT}.
    Context {re5: relate_impl_nps}.
    Context {re6: relate_impl_vmxinfo}.
    Context {re7: relate_impl_ipt}.

    Lemma container_init0_exist:
      forall s habd habd' labd mbi f,
        container_init0_spec mbi habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', container_init0_spec mbi labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold container_init0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_AC_eq; eauto.
      exploit relate_impl_AT_eq; eauto.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_ipt_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_AC_update.
      apply relate_impl_init_update.
      apply relate_impl_nps_update. 
      apply relate_impl_AT_update.
      apply relate_impl_vmxinfo_update. assumption.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_init}.
    Context {mt3: match_impl_AC}.
    Context {mt4: match_impl_AT}.
    Context {mt5: match_impl_nps}.
    Context {mt6: match_impl_vmxinfo}.

    Lemma container_init0_match:
      forall s d d' m mbi f,
        container_init0_spec mbi d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold container_init0_spec; intros. subdestruct. inv H.      
      apply match_impl_AC_update.
      apply match_impl_init_update.
      apply match_impl_nps_update. 
      apply match_impl_AT_update.
      apply match_impl_vmxinfo_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) container_init0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) container_init0_spec}.

    Lemma container_init0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem container_init0_spec)
            (id ↦ gensem container_init0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit container_init0_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply container_init0_match; eauto.
    Qed.

  End CONTAINER_INIT0_SIM.

  Section CONTAINER_GET_PARENT_SIM.

    Lemma container_get_parent_exist:
      forall s habd labd i p f,
        container_get_parent_spec i habd = Some p
        -> relate_AbData s f habd labd
        -> container_get_parent_spec i labd = Some p.
    Proof.
      unfold container_get_parent_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_AC_eq; eauto. intros.
      revert H. subrewrite.
    Qed.

    Lemma container_get_parent_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem container_get_parent_spec)
                               (id ↦ gensem container_get_parent_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite container_get_parent_exist; eauto 1.
      reflexivity.
    Qed.

  End CONTAINER_GET_PARENT_SIM.

  Section CONTAINER_GET_NCHILDREN_SIM.

    Lemma container_get_nchildren_exist:
      forall s habd labd i p f,
        container_get_nchildren_spec i habd = Some p
        -> relate_AbData s f habd labd
        -> container_get_nchildren_spec i labd = Some p.
    Proof.
      unfold container_get_nchildren_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_AC_eq; eauto. intros.
      revert H. subrewrite.
    Qed.

    Lemma container_get_nchildren_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem container_get_nchildren_spec)
                               (id ↦ gensem container_get_nchildren_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite container_get_nchildren_exist; eauto 1.
      reflexivity.
    Qed.

  End CONTAINER_GET_NCHILDREN_SIM.

  Section CONTAINER_GET_QUOTA_SIM.

    Lemma container_get_quota_exist:
      forall s habd labd i p f,
        container_get_quota_spec i habd = Some p
        -> relate_AbData s f habd labd
        -> container_get_quota_spec i labd = Some p.
    Proof.
      unfold container_get_quota_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_AC_eq; eauto. intros.
      revert H. subrewrite.
    Qed.

    Lemma container_get_quota_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem container_get_quota_spec)
                               (id ↦ gensem container_get_quota_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite container_get_quota_exist; eauto 1.
      reflexivity.
    Qed.

  End CONTAINER_GET_QUOTA_SIM.

  Section CONTAINER_GET_USAGE_SIM.

    Lemma container_get_usage_exist:
      forall s habd labd i p f,
        container_get_usage_spec i habd = Some p
        -> relate_AbData s f habd labd
        -> container_get_usage_spec i labd = Some p.
    Proof.
      unfold container_get_usage_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_AC_eq; eauto. intros.
      revert H. subrewrite.
    Qed.

    Lemma container_get_usage_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem container_get_usage_spec)
                               (id ↦ gensem container_get_usage_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite container_get_usage_exist; eauto 1.
      reflexivity.
    Qed.

  End CONTAINER_GET_USAGE_SIM.

  Section CONTAINER_CAN_CONSUME_SIM.

    Lemma container_can_consume_exist:
      forall s habd labd i n b f,
        container_can_consume_spec i n habd = Some b
        -> relate_AbData s f habd labd
        -> container_can_consume_spec i n labd = Some b.
    Proof.
      unfold container_can_consume_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_AC_eq; eauto. intros.
      revert H. subrewrite.
    Qed.

    Lemma container_can_consume_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem container_can_consume_spec)
                               (id ↦ gensem container_can_consume_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite container_can_consume_exist; eauto 1.
      reflexivity.
    Qed.

  End CONTAINER_CAN_CONSUME_SIM.

  Section CONTAINER_SPLIT_SIM.

    Lemma container_split_exist:
      forall s habd habd' labd i n z f,
        container_split_spec i n habd = Some (habd', z)
        -> relate_AbData s f habd labd
        -> exists labd', container_split_spec i n labd = Some (labd', z)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold container_split_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_AC_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_AC_update. assumption.
    Qed.

    Context {mt2: match_impl_AC}.

    Lemma container_split_match:
      forall s d d' m i n z f,
        container_split_spec i n d = Some (d', z)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold container_split_spec; intros. subdestruct. inv H.
      eapply match_impl_AC_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) container_split_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) container_split_spec}.

    Lemma container_split_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem container_split_spec)
            (id ↦ gensem container_split_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit container_split_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply container_split_match; eauto.
    Qed.

  End CONTAINER_SPLIT_SIM.

  Section CONTAINER_ALLOC_SIM.

    Context {re4: relate_impl_AT}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_nps}.

    Lemma container_alloc_exist:
      forall s habd habd' labd i f z,
        container_alloc_spec i habd = Some (habd', z)
        -> relate_AbData s f habd labd
        -> exists labd', container_alloc_spec i labd = Some (labd', z)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold container_alloc_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_AT_eq; eauto.
      exploit relate_impl_pperm_eq; eauto.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_AC_eq; eauto. intros.
      revert H; subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      apply relate_impl_AC_update. 
      apply relate_impl_pperm_update.
      apply relate_impl_AT_update. assumption.
    Qed.

    Context {mt1: match_impl_AC}.
    Context {mt2: match_impl_pperm}.
    Context {mt3: match_impl_AT}.

    Lemma container_alloc_match:
      forall s d d' m i f z,
        container_alloc_spec i d = Some (d',z)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold container_alloc_spec; intros. 
      subdestruct; inv H; auto.
      apply match_impl_AC_update.
      apply match_impl_pperm_update.
      apply match_impl_AT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) container_alloc_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) container_alloc_spec}.

    Lemma container_alloc_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem container_alloc_spec)
            (id ↦ gensem container_alloc_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit container_alloc_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply container_alloc_match; eauto.
    Qed.

  End CONTAINER_ALLOC_SIM.

End OBJ_SIM.