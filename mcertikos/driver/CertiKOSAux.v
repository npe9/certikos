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
Require Import RealParams.
Require Import Maps.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import Coqlib.
Require Import ErrorMonad.
Require Import LinkSourceTemplate.
Require Export LinkTactic.  (* inv_monad' *)
Require Export LinkTemplate.
Require Export LAsmModuleSemEvent.
Require Import Behavior.
Require Export CompCertiKOSproofImpl.
Require Import CertiKOS.

(** * Tactics used for global linking *)

(** For some reason, applying the [Foo.make_program_exists] theorem
  efficiently is a little bit tricky. We use these tactics to
  massage everything as needed. *)

(** First, we unfold the [Foo_impl] modules which are of the form
  [link_impl Foo_module _], so that the corresponding theorem can
  unify without effort. *)

Ltac unfold_into_link_impl H :=
  lazymatch type of H with
    | ?Foo_impl = OK _ =>
      lazymatch eval red in Foo_impl with
        | link_impl ?module ?base_layer =>
          change Foo_impl with (link_impl module base_layer) in H
      end
  end.

Ltac unfold_all_into_link_impl :=
  repeat match goal with H: _ |- _ => unfold_into_link_impl H end.

(** With the assumption that our [Foo_impl] now match the generic
  [make_program_exists_type], we can locate the appropiate
  hypothesis to solve the corresponding subgoal, without computing
  the hell out of it. *)

Ltac impl_ok_assumption :=
  lazymatch goal with
    | |- ?impl = OK _ =>
      lazymatch goal with
        | H: impl = OK _ |- _ =>
          apply H
      end
  end ||
  eassumption.

(** We also do something similar for [make_program] hypotheses. *)

Ltac make_program_ok_assumption :=
  match goal with
    | |- make_program _ _ ?L = OK _ =>
      match goal with
        | H: make_program _ _ L = OK _ |- _ =>
          exact H
      end
  end.

(** Now, it's easy to destruct a [Foo.make_program_exists] theorem
  efficiently by using [impl_ok_assumption] for the first subgoal. *)

Ltac destruct_mpe hyp :=
  let p := fresh "p" in
  let Hp := fresh "H" p in
  edestruct hyp as [p Hp];
    [ impl_ok_assumption ..
    | make_program_ok_assumption
    | ].

(** Similarly, this tactic is used to apply 
    [Foo.cl_forward_simulation] and [Foo.cl_backward_simulation]. *)

Ltac last_simulation thm :=
  eapply thm;
   [ assumption
   | impl_ok_assumption..
   | make_program_ok_assumption
   | make_program_ok_assumption ].

Ltac compose_simulation thm :=
  eapply compose_simulation;
   [ last_simulation thm 
   | idtac ].

Ltac compose_forward_simulation thm :=
  eapply compose_forward_simulation;
  [ last_simulation thm
  | idtac ].

Ltac compose_backward_simulation thm :=
  eapply compose_backward_simulation;
  [ assumption
  | last_simulation thm
  | idtac ].


(** * Lemmas used to establish the final theorem *)

Lemma option_rel_eq_antisymmetry {A}{x y : option A} :
  option_le eq x y -> option_le eq y x -> x = y.
Proof.
  intros x_le_y y_le_x.
  inversion x_le_y; inversion y_le_x; congruence.
Qed.

Lemma prog_defs_le_antisymmetry {F V} p1 p2 :
    @CompcertStructures.prog_defs_le F V p1 p2 ->
    @CompcertStructures.prog_defs_le F V p2 p1 ->
    p1 = p2.
Proof.
  intros le12 le21.
  induction le12; try reflexivity.
  inversion le21.
  subst.
  f_equal.
  - inversion H.
    inversion H3.
    rewrite (surjective_pairing x), (surjective_pairing y).
    unfold RelationPairs.RelCompFun in H0.
    rewrite (option_rel_eq_antisymmetry H1 H4).
    congruence.
  - apply IHle12; assumption.
Qed.

Lemma make_program_equiv {D}(s: stencil)(M1 M2: module) L prog :
  M1 ≡ M2 ->
  make_program (D := D) s M1 L = OK prog ->
  make_program s M2 L = OK prog.
Proof.
  intros Mequiv mk1.
  assert (M1_le_M2 : M1 ≤ M2) by apply Mequiv.
  assert (M2_le_M1 : M2 ≤ M1) by apply Mequiv.
  assert (L_le_L : L ≤ L) by reflexivity.
  assert (res1_le_2 := make_program_monotonic s _ _ M1_le_M2 _ _ L_le_L).
  assert (res2_le_1 := make_program_monotonic s _ _ M2_le_M1 _ _ L_le_L).
  rewrite mk1 in res1_le_2, res2_le_1.
  clear mk1 M1_le_M2 M2_le_M1 L_le_L.

  inversion res2_le_1 as [ prog2 ? prog2_le mk2 |]; subst.
  inversion res1_le_2 as [ ? prog1 prog1_le xeq mk1 |]; [ subst | congruence ].
  simpl; rewrite <- mk1.
  rewrite <- mk1 in mk2; injection mk2 as ->.
  clear res1_le_2 res2_le_1 mk1 mk2.

  destruct prog1_le.
  f_equal; f_equal.
  inversion prog2_le.
  apply prog_defs_le_antisymmetry; assumption.
Qed.

Lemma CertiKOS_plus_context CTXT kernel:
  CertiKOS.certikos = OK kernel ->
  exists combined,
    CertiKOS.certikos_plus_ctxt CTXT = OK combined /\
    CTXT ⊕ kernel ≡ combined.
Proof.
  unfold CertiKOS.certikos.
  unfold CertiKOS.certikos_plus_ctxt.
  unfold CertiKOS.add_loc.
  intros Hkernel.
  inv_monad' Hkernel.
  repeat match goal with H: _ = ret _ |- _ => rewrite H end.
  clear.
  monad_norm.
  eexists.
  split.
  - reflexivity.
  - split; le_oplus.
Qed.

