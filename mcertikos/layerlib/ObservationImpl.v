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
Require Import Coqlib.
Require Import Maps.
Require Import List.
Require Import Decision.
Require Import Observation.

(* This file instantiates the Observation typeclass for mCertiKOS.
   It uses the output buffer present in the abstract data of all mCertiKOS
   layers as the observation, and defines the partial order and measure appropriately. *)

Section OBS_IMPL.

  Local Open Scope nat_scope.

  Section LIST.

    (* implementation of observation as a list of values (e.g., output buffer) *)

    Context {principal : Type}.
    Hypothesis principal_eq_dec : forall a1 a2 : principal, Decision (a1 = a2).

    Context {elt : Type}.
    Hypothesis elt_eq_dec : forall a1 a2 : elt, Decision (a1 = a2).

    Fixpoint list_leq (l1 l2 : list elt) :=
      match l1, l2 with
        | nil, _ => True
        | cons a1 l1, cons a2 l2 => if elt_eq_dec a1 a2 then list_leq l1 l2 else False
        | _, _ => False
      end.

    Lemma list_leq_app : forall l l', list_leq l (l ++ l').
    Proof.
      induction l; simpl; auto.
      destruct (elt_eq_dec a a); auto.
    Qed.

    Lemma list_leq_refl : forall l, list_leq l l.
    Proof.
      induction l; simpl; auto.
      destruct (elt_eq_dec a a); auto.
    Qed.

    Lemma list_leq_antisym : 
      forall l1 l2, list_leq l1 l2 -> list_leq l2 l1 -> l1 = l2.
    Proof.
      induction l1; destruct l2; simpl; try solve [intuition].
      destruct (elt_eq_dec a e), (elt_eq_dec e a); auto; try solve [intuition].
      clear e0; subst; intros; erewrite IHl1; eauto.
    Qed.

    Lemma list_leq_trans :
      forall l1 l2 l3, list_leq l1 l2 -> list_leq l2 l3 -> list_leq l1 l3.
    Proof.
      induction l1; destruct l2, l3; simpl; try solve [intuition].
      destruct (elt_eq_dec a e), (elt_eq_dec e e0), (elt_eq_dec a e0); subst; auto; try solve [intuition].
      eauto.
    Qed.

    Lemma list_leq_length :
      forall l1 l2, list_leq l1 l2 -> l1 <> l2 -> length l1 < length l2.
    Proof.
      induction l1; destruct l2; simpl; try solve [intuition].
      destruct (elt_eq_dec a e); subst; try solve [intuition].
      intros; cut (length l1 < length l2); [omega|].
      apply IHl1; auto.
      intro Hcon; subst; contradiction H0; reflexivity.
    Qed.

    Instance list_observation_ops : ObservationOps :=
      {
        principal := principal;
        obs := list elt;
        obs_leq := list_leq;
        obs_measure := @length elt
      }.

    Instance list_observation : Observation.
    Proof.
      constructor; simpl.
      - apply principal_eq_dec; assumption.
      - apply list_eq_dec; assumption.
      - apply list_leq_refl.
      - apply list_leq_antisym.
      - apply list_leq_trans.
      - unfold obs_lt; intros o1 o2 [Hleq Hneq].
        apply list_leq_length; auto.
    Qed.

    (* output buffers add output to the head of the list, so we need to reverse them *)

    Instance rev_list_observation_ops : ObservationOps :=
      {
        principal := principal;
        obs := list elt;
        obs_leq o1 o2 := list_leq (rev o1) (rev o2);
        obs_measure := @length elt
      }.

    Instance rev_list_observation : Observation.
    Proof.
      constructor; simpl.
      - apply principal_eq_dec; assumption.
      - apply list_eq_dec; assumption.
      - intros; apply list_leq_refl.
      - intros; rewrite <- (rev_involutive o1), <- (rev_involutive o2); f_equal.
        apply list_leq_antisym; auto.
      - intros; eapply list_leq_trans; eauto.
      - unfold obs_lt; intros o1 o2 [Hleq Hneq].
        rewrite <- (rev_length o1), <- (rev_length o2).
        apply list_leq_length; auto.
        intro Hcon; contradiction Hneq.
        rewrite <- (rev_involutive o1), <- (rev_involutive o2); f_equal; auto.
    Qed.

  End LIST.

  Section OBSLIST.

    (* implementation of observation as a list of observations
       (e.g., list of output buffers) *)

    Context `{Hobs : Observation}.

    Fixpoint obs_list_leq (l1 l2 : list obs) :=
      match l1, l2 with
        | nil, nil => True
        | a1::l1, a2::l2 => obs_leq a1 a2 /\ obs_list_leq l1 l2
        | _, _ => False
      end.

    Fixpoint obs_list_measure (l : list obs) :=
      match l with
        | nil => O
        | a::l => obs_measure a + obs_list_measure l
      end.

    Lemma obs_list_leq_refl : forall l, obs_list_leq l l.
    Proof.
      induction l; simpl; auto; split; auto.
      apply obs_leq_refl.
    Qed.

    Lemma obs_list_leq_antisym : 
      forall l1 l2, obs_list_leq l1 l2 -> obs_list_leq l2 l1 -> l1 = l2.
    Proof.
      induction l1; destruct l2; simpl; intros; auto; try contradiction.
      destruct H, H0; f_equal; auto.
      apply obs_leq_antisym; auto.
    Qed.

    Lemma obs_list_leq_trans :
      forall l1 l2 l3, obs_list_leq l1 l2 -> obs_list_leq l2 l3 -> obs_list_leq l1 l3.
    Proof.
      induction l1; destruct l2, l3; simpl; intros; auto; try contradiction.
      destruct H, H0; split; eauto.
      eapply obs_leq_trans; eauto.
    Qed.

    Lemma obs_list_leq_length :
      forall l1 l2, 
        obs_list_leq l1 l2 -> l1 <> l2 -> 
        obs_list_measure l1 < obs_list_measure l2.
    Proof.
      induction l1; destruct l2; simpl; intros; try contradiction.
      contradiction H0; auto.
      destruct H, (obs_eq_dec a o); subst.
      cut (obs_list_measure l1 < obs_list_measure l2); [omega|].
      apply IHl1; auto.
      intro Hcon; subst; contradiction H0; reflexivity.
      cut (obs_list_measure l1 <= obs_list_measure l2).
      cut (obs_measure a < obs_measure o); [omega|].
      apply obs_lt_measure; unfold obs_lt; auto.
      destruct (list_eq_dec obs_eq_dec l1 l2); subst; [omega|].
      apply lt_le_weak; auto.
    Qed.

    Instance obs_list_observation_ops : ObservationOps :=
      {
        principal := principal;
        obs := list obs;
        obs_leq := obs_list_leq;
        obs_measure := obs_list_measure
      }.

    Instance obs_list_observation : Observation.
    Proof.
      constructor; simpl.
      - apply principal_eq_dec.
      - apply list_eq_dec; apply obs_eq_dec.
      - apply obs_list_leq_refl.
      - apply obs_list_leq_antisym.
      - apply obs_list_leq_trans.
      - unfold obs_lt; intros o1 o2 [Hleq Hneq].
        apply obs_list_leq_length; auto.
    Qed.

  End OBSLIST.

  Section RDATA.

    (* implementation of observation on RData *)

    Require Import AbstractDataType.
    Require Import Constant.

    (* first define observation for lists of DeviceAction *)

    Lemma devact_eq_dec : forall a1 a2 : DeviceAction, Decision (a1 = a2).
    Proof.
      unfold Decision; decide equality; apply zeq.
    Qed.

    Global Instance devact_observation_ops : ObservationOps := 
      rev_list_observation_ops(principal:=Z) devact_eq_dec.
    Global Instance devact_observation : Observation := 
      rev_list_observation zeq devact_eq_dec.

    Definition observe (p : Z) (d : RData) : list DeviceAction := 
      ZMap.get p (devout d).

    (* Then define observation for DeviceOutput (list of lists of DeviceAction).
       We don't actually need to observe all output buffers simulataneously,
       but this definition might be useful at some point in the future. *)

    Instance devout_observation_ops : ObservationOps := 
      @obs_list_observation_ops devact_observation_ops.
    Instance devout_observation : Observation := 
      @obs_list_observation devact_observation_ops devact_observation.

    (* actually, DeviceOutput is a ZMap - thus we define the following function
       which takes a state of type RData and converts the DeviceOutput into a list *)

    (* NOTE: we can't define the ZMap directly as an observation because 
             decidable equality and antisymmetry don't hold for ZMaps *)

    Fixpoint zmap_to_list {elt : Type} (n : nat) (m : ZMap.t elt) :=
      ZMap.get (Z_of_nat n) m ::
      match n with
        | O => nil
        | S n => zmap_to_list n m
      end.

    Global Opaque zmap_to_list.

    Definition observe_all (d : RData) : list (list DeviceAction) := 
      zmap_to_list (nat_of_Z (num_id-1)) (devout d).

  End RDATA.

End OBS_IMPL.