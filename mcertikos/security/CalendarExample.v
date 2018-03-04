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
Require Import CommonTactic.
Require Import Equivalence.

Section WITHLABEL.

  Variable lbl : Type.
  Variable bot : lbl.
  Variable leq : lbl -> lbl -> Prop.
  Variable lub : lbl -> lbl -> lbl.
  
  Hypothesis leq_bot : forall l, leq bot l.
  Hypothesis leq_refl : forall l, leq l l.
  Hypothesis leq_antisym : forall l1 l2, leq l1 l2 -> leq l2 l1 -> l1 = l2.
  Hypothesis leq_trans : forall l1 l2 l3, leq l1 l2 -> leq l2 l3 -> leq l1 l3.
  Hypothesis leq_dec : forall l1 l2, {leq l1 l2} + {~ leq l1 l2}.

  Hypothesis lub_l : forall l1 l2, leq l1 (lub l1 l2).
  Hypothesis lub_r : forall l1 l2, leq l2 (lub l1 l2).
  Hypothesis lub_least : forall l l1 l2, leq l1 l -> leq l2 l -> leq (lub l1 l2) l.

  Section WITHOBS.

    Context {l : lbl}.
    Context {R : Type}.
    Variable obs : lbl.

    Definition cal (l : lbl) : Type := nat -> option nat.    

    Definition observe (c : cal l) (n : nat) :=
      match c n with
        | None => None
        | Some v => Some (if leq_dec l obs then v else O)
      end.

    Definition obs_eq_c (c1 c2 : cal l) :=
      forall n, observe c1 n = observe c2 n.

    Global Instance obs_eq_c_equiv : Equivalence obs_eq_c.
    Proof.
      constructor.
      - unfold obs_eq_c; auto.
      - unfold obs_eq_c; auto.
      - unfold obs_eq_c; congruence.
    Qed.

    Definition obs_eq_v (v1 v2 : prod R lbl) :=
      let (v1,l1) := v1 in let (v2,l2) := v2 in l1 = l2 /\ (leq l1 obs -> v1 = v2).

    Global Instance obs_eq_v_equiv : Equivalence obs_eq_v.
    Proof.
      constructor.
      - intros [? ?]; unfold obs_eq_v; auto.
      - intros [? ?] [? ?]; unfold obs_eq_v; intuition.
        symmetry; subst; auto.
      - intros [? ?] [? ?] [? ?]; unfold obs_eq_v; intuition; try congruence.
        transitivity r0; subst; auto.
    Qed.

  End WITHOBS.

  Variable N : nat.
    
    (* specifications of calendar object primitives *)

    Definition spec (D R : Type) := option (prod D (prod R lbl)).

    Function isFree {l} (c : cal l) (n : nat) : spec (cal l) bool :=
      match c n with 
        | None => Some (c, (true, bot))
        | Some _ => Some (c, (false, bot))
      end.

    Function getEvent {l} (c : cal l) (n : nat) : spec (cal l) (option nat) :=
      match c n with
        | None => Some (c, (None, bot))
        | Some v => Some (c, (Some v, l))
      end.

    (* noninterfering spec proofs *)

    Definition spec_secure {D A R} (f : D -> A -> spec D R) 
      (obs_eq_d : lbl -> D -> D -> Prop) (obs_eq_r : lbl -> prod R lbl -> prod R lbl -> Prop) :=
      forall (obs : lbl) (d1 d2 : D),
        obs_eq_d obs d1 d2 ->
        forall a : A,
          match f d1 a, f d2 a with
            | Some (d1', r1), Some (d2', r2) => obs_eq_d obs d1' d2' /\ obs_eq_r obs r1 r2
            | _, _ => True
          end.

    Ltac inv_observe H n := specialize (H n); unfold observe in H; subdestruct.

    Lemma isFree_secure {l} : spec_secure isFree (obs_eq_c(l:=l)) obs_eq_v.
    Proof.
      unfold spec_secure, obs_eq_c, obs_eq_v, isFree; intros; cases; auto; inv_observe H a.
    Qed.

    Lemma getEvent_secure {l} : spec_secure getEvent (obs_eq_c(l:=l)) obs_eq_v.
    Proof.
      unfold spec_secure, obs_eq_c, obs_eq_v, getEvent; intros; cases; auto; try solve [inv_observe H a].
      repeat (split; auto); inv_observe H a; congruence.
    Qed.


    (* coordination of two different calendars to find a common available slot *)

    Variables alice bob : lbl.

    Definition state := prod (cal alice) (cal bob).

    Definition obs_eq obs (s1 s2 : state) :=
      let (a1,b1) := s1 in let (a2,b2) := s2 in obs_eq_c obs a1 a2 /\ obs_eq_c obs b1 b2.

    Instance obs_eq_equiv : forall obs, Equivalence (obs_eq obs).
    Proof.
      constructor.
      - unfold obs_eq; intros [? ?]; split; reflexivity.
      - unfold obs_eq; intros [? ?] [? ?]; split; symmetry; intuition.
      - unfold obs_eq; intros [? ?] [? ?] [? ?]; split; etransitivity; intuition; eauto.
    Qed.

    Fixpoint findBothFree (ca : cal alice) (cb : cal bob) (n : nat) :=
      match ca n, cb n with
        | None, None => Some n
        | _, _ => match n with
                    | O => None
                    | S n => findBothFree ca cb n
                  end
      end.

    Definition upd_cal {l} (c : cal l) (n v : nat) := 
      fun n' => if eq_nat_dec n' n then Some v else c n.

    Lemma obs_eq_upd_cal {l} : 
      forall obs (c1 c2 : cal l) n v, 
        obs_eq_c obs c1 c2 -> obs_eq_c(l:=l) obs (upd_cal c1 n v) (upd_cal c2 n v).
    Proof.
      unfold obs_eq_c, upd_cal; intros; unfold observe; cases; auto; inv_observe H n; congruence.
    Qed.

    Function sched (s : state) (v : nat) : spec state (option nat) :=
      match findBothFree (fst s) (snd s) N with
        | None => Some (s, (None, bot))
        | Some n => Some ((upd_cal (fst s) n v, upd_cal (snd s) n v), (Some n, bot))
      end.

    Lemma findBothFree_secure : 
      forall n obs a1 a2 b1 b2,
        obs_eq_c obs a1 a2 -> obs_eq_c obs b1 b2 -> findBothFree a1 b1 n = findBothFree a2 b2 n.
    Proof.
      induction n; unfold obs_eq_c; simpl; intros; cases; eauto;
        try solve [inv_observe H O | inv_observe H0 O |
                   inv_observe H (S n) | inv_observe H0 (S n)].
    Qed.

    Lemma sched_secure : spec_secure sched obs_eq obs_eq_v.
    Proof.
      unfold spec_secure, obs_eq, obs_eq_v, sched; intros.
      destruct d1, d2, H.
      erewrite findBothFree_secure; simpl; eauto; cases; auto.
      repeat (split; auto); apply obs_eq_upd_cal; auto.
    Qed.

    Fixpoint findBothFree_bob (ca : cal alice) (cb : cal bob) (n : nat) :=
      match ca n, cb n with
        | None, Some v => Some v
        | _, _ => match n with
                    | O => None
                    | S n => findBothFree_bob ca cb n
                  end
      end.

    Function sched_bad (s : state) (_ : unit) : spec state (option nat) :=
      Some (s, (findBothFree_bob (fst s) (snd s) N, bot)).

    Lemma findBothFree_bob_secure : 
      forall n obs a1 a2 b1 b2, 
        obs_eq_c obs a1 a2 -> obs_eq_c obs b1 b2 -> findBothFree_bob a1 b1 n = findBothFree_bob a2 b2 n.
    Proof.
      induction n; unfold obs_eq_c; simpl; intros; cases; eauto;
        try solve [inv_observe H O | inv_observe H0 O; congruence |
                   inv_observe H (S n) | inv_observe H0 (S n); congruence].
      inv_observe H0 O; try congruence.
    Abort.

    Function sched_bob (s : state) (_ : unit) : spec state (option nat) :=
      Some (s, (findBothFree_bob (fst s) (snd s) N, bob)).

    Lemma findBothFree_bob_secure : 
      forall n obs a1 a2 b1 b2, 
        obs_eq_c obs a1 a2 -> obs_eq_c obs b1 b2 -> leq bob obs -> 
        findBothFree_bob a1 b1 n = findBothFree_bob a2 b2 n.
    Proof.
      induction n; unfold obs_eq_c; simpl; intros; cases; eauto;
        try solve [inv_observe H O | inv_observe H0 O; congruence |
                   inv_observe H (S n) | inv_observe H0 (S n); congruence].
    Qed.

    Lemma sched_bad_secure : spec_secure sched_bob obs_eq obs_eq_v.
    Proof.
      unfold spec_secure, obs_eq, obs_eq_v, sched_bob; intros; cases.
      repeat (split; auto); intros; simpl; eapply findBothFree_bob_secure; eauto; intuition.
    Qed.


    (* stronger policy: time slot is public only if it is free in BOTH calendars *)

    Definition observe_s (s : state) (n : nat) :=
      match fst s n, snd s n with
        | None, None => true
        | _, _ => false
      end.

    Definition obs_eq_s (s1 s2 : state) :=
      forall n, observe_s s1 n = observe_s s2 n.

    Global Instance obs_eq_s_equiv : Equivalence obs_eq_s.
    Proof.
      constructor.
      - unfold obs_eq_s; auto.
      - unfold obs_eq_s; auto.
      - unfold obs_eq_s; congruence.
    Qed.

    Ltac inv_observe_s H n := specialize (H n); unfold observe_s in H; subdestruct.

    Lemma findBothFree_s_secure : 
      forall n s1 s2, 
        obs_eq_s s1 s2 -> findBothFree (fst s1) (snd s1) n = findBothFree (fst s2) (snd s2) n.
    Proof.
      induction n; unfold obs_eq_s; simpl; intros; cases; auto;
        try solve [inv_observe_s H O | inv_observe_s H0 O |
                   inv_observe_s H (S n) | inv_observe_s H0 (S n)].
    Qed.

    Lemma obs_eq_s_upd_cal : 
      forall (s1 s2 : state) n v, 
        obs_eq_s s1 s2 -> obs_eq_s (upd_cal (fst s1) n v, upd_cal (snd s1) n v)
                                   (upd_cal (fst s2) n v, upd_cal (snd s2) n v).
    Proof.
      unfold obs_eq_s, upd_cal; intros; unfold observe_s; cases; auto; 
        simpl in *; subdestruct; inv_observe_s H n; congruence.
    Qed.

    Lemma sched_s_secure : spec_secure sched (fun _ => obs_eq_s) obs_eq_v.
    Proof.
      unfold spec_secure, obs_eq_v, sched; intros.
      erewrite findBothFree_s_secure; simpl; eauto; cases; auto.
      repeat (split; auto); apply obs_eq_s_upd_cal; auto.
    Qed.
      
  End WITHOBS.

End WITHLABEL.