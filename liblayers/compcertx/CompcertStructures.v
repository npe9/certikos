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
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.lib.Decision.
Require Export liblayers.logic.Structures.
Require Export liblayers.logic.OptionOrders.
Require Export liblayers.compcertx.ErrorMonad.
Require Import Coq.Classes.RelationPairs.


(** * Orders on definitions and programs *)

Definition prog_defs_le {F V}: relation (list (ident * option (globdef F V))) :=
  list_rel (eq * option_le eq).

Inductive program_le {F V}: relation (AST.program F V) :=
  | program_le_intro:
      Proper (prog_defs_le ++> - ==> program_le) (@AST.mkprogram F V).

Global Existing Instance program_le_intro.


(** * Order on global environments *)

(** A global environment [ge1] is smaller than [ge2] if in each table,
  every definition that appears in [ge1] also appears in [ge2]. *)

Record genv_le {F V} (ge1 ge2: Genv.t F V): Prop :=
  {
    genv_le_find_symbol:
      pointwise_relation AST.ident (option_le eq)
        (Genv.find_symbol ge1) (Genv.find_symbol ge2);

    genv_le_find_funct_ptr:
      pointwise_relation block (option_le eq)
        (Genv.find_funct_ptr ge1) (Genv.find_funct_ptr ge2);

    genv_le_find_var_info:
      pointwise_relation block (option_le eq)
        (Genv.find_var_info ge1) (Genv.find_var_info ge2);

    (** The following is necessary to prove monotonicity
        of [Genv.globalenv] *)
    genv_le_next:
      Genv.genv_next ge1 = Genv.genv_next ge2
  }.

Global Instance genv_le_op {F V}: Le (Genv.t F V) := { le := genv_le }.

Global Instance genv_le_preorder {F V}:
  PreOrder (@genv_le F V).
Proof.
  constructor.
  * (* reflexive *)
    constructor; try intro; reflexivity.
  * (* transitive *)
    constructor; inversion H; inversion H0; subst;
    unfold pointwise_relation in *;
      intros; etransitivity; eauto.
Qed.

Lemma genv_le_find_symbol_some {F V} (ge ge': Genv.t F V) i b:
  genv_le ge ge' ->
  Genv.find_symbol ge i = Some b ->
  Genv.find_symbol ge' i = Some b.
Proof.
  intros ? FIND.
  exploit @genv_le_find_symbol; eauto.
  instantiate (1 := i).
  rewrite FIND.
  inversion 1; subst; eauto.
Qed.

Lemma genv_le_find_var_info_some {F V} (ge ge': Genv.t F V) b v:
  genv_le ge ge' ->
  Genv.find_var_info ge b = Some v ->
  Genv.find_var_info ge' b = Some v.
Proof.
  intros LE VAR.
  generalize (genv_le_find_var_info _ _ LE b).
  inversion 1; congruence.
Qed.

Lemma genv_le_find_funct_ptr_some {F V} (ge ge': Genv.t F V) b f:
  genv_le ge ge' ->
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr ge' b = Some f.
Proof.
  intros LE FUN.
  generalize (genv_le_find_funct_ptr _ _ LE b).
  inversion 1; congruence.
Qed.

Section GENV_LE_MONO.

  Context {F V: Type}.

  Local Instance add_global_monotonic:
    Proper
      (genv_le ++> (eq * option_le eq) ++> genv_le)
      (@Genv.add_global F V).
  Proof.
    intros ge1 ge2 Hgele o1 o2 Hole.
    destruct o1; destruct o2.
    inv Hole.
    inv H.
    simpl in *; subst.
    constructor; unfold pointwise_relation.
    * unfold Genv.find_symbol; simpl.
      intro.
      repeat rewrite Maps.PTree.gsspec.
      destruct (peq a i0).
      + erewrite genv_le_next; eauto. reflexivity.
      + apply genv_le_find_symbol; auto.
    * unfold Genv.find_funct_ptr; simpl.
      destruct o; inv H0; simpl in *; subst.
      + erewrite genv_le_next; eauto.
        destruct y; try (apply genv_le_find_funct_ptr; eauto).
        intro.
        repeat rewrite Maps.PTree.gsspec.
        destruct (peq a (Genv.genv_next ge2)); try reflexivity.
        apply genv_le_find_funct_ptr; eauto.
      + destruct o0; try (apply genv_le_find_funct_ptr; eauto).
        destruct g; try (apply genv_le_find_funct_ptr; eauto).
        intro.
        rewrite Maps.PTree.gsspec.
        destruct (peq a (Genv.genv_next ge2));
          try (apply genv_le_find_funct_ptr; eauto).
        subst.
        erewrite <- genv_le_next; eauto.
        destruct (Maps.PTree.get (Genv.genv_next ge1) (Genv.genv_funs ge1)) eqn:?; try constructor.
        exfalso. exploit Genv.genv_funs_range; eauto. xomega.
    * unfold Genv.find_var_info; simpl.
      destruct o; inv H0; simpl in *; subst.
      + erewrite genv_le_next; eauto.
        destruct y; try (apply genv_le_find_var_info; eauto).
        intro.
        repeat rewrite Maps.PTree.gsspec.
        destruct (peq a (Genv.genv_next ge2)); try reflexivity.
        apply genv_le_find_var_info; eauto.
      + destruct o0; try (apply genv_le_find_var_info; eauto).
        destruct g; try (apply genv_le_find_var_info; eauto).
        intro.
        rewrite Maps.PTree.gsspec.
        destruct (peq a (Genv.genv_next ge2));
          try (apply genv_le_find_var_info; eauto).
        subst.
        erewrite <- genv_le_next; eauto.
        destruct (Maps.PTree.get (Genv.genv_next ge1) (Genv.genv_vars ge1)) eqn:?; try constructor.
        exfalso. exploit Genv.genv_vars_range; eauto. xomega.
    * simpl. erewrite genv_le_next; eauto.
  Qed.

  Local Instance add_globals_monotonic:
    Proper
      (genv_le ++> prog_defs_le ++> genv_le)
      (@Genv.add_globals F V).
  Proof.
    intros ge1 ge2 Hgele l1 l2 Hlle.
    revert ge1 ge2 Hgele.
    induction Hlle; simpl; auto.
    intros.
    eapply IHHlle; eauto.
    solve_monotonicity.
  Qed.

  Global Instance globalenv_monotonic:
    Proper (program_le ++> genv_le) (@Genv.globalenv F V).
  Proof.
    unfold Genv.globalenv. intro. intros.
    inv H.
    solve_monotonicity.
  Qed.

End GENV_LE_MONO.


(** * Clight signatures *)

Record csignature :=
  {
    csig_args: Ctypes.typelist;
    csig_res: Ctypes.type;
    csig_cc: calling_convention
  }.

(** ** Decision procedures *)

Global Instance calling_convention_eq_dec (cc1 cc2: calling_convention):
  Decision (cc1 = cc2) :=
    if decide (cc_vararg cc1 = cc_vararg cc2 /\
               cc_structret cc1 = cc_structret cc2) then left _ else right _.
Proof.
  abstract (destruct _H, cc1, cc2; f_equal; assumption).
  abstract (intro; subst; auto).
Defined.

Global Instance type_eq_dec: forall (ty1 ty2: Ctypes.type), Decision (ty1 = ty2) :=
  type_eq.

Global Instance typelist_eq_dec: forall (ts1 ts2: typelist), Decision (ts1 = ts2) :=
  typelist_eq.

Global Instance csig_eq_dec (sig1 sig2: csignature):
  Decision (sig1 = sig2).
Proof.
  destruct sig1 as [args1 res1 cc1].
  destruct sig2 as [args2 res2 cc2].
  destruct (decide (args1 = args2 /\ res1 = res2 /\ cc1 = cc2)).
  * left.
    abstract (f_equal; tauto).
  * right.
    abstract (injection 1; tauto).
Defined.

(** ** Helper functions *)

Definition mkcsig (args: Ctypes.typelist) (res: Ctypes.type): csignature :=
  {|
    csig_args := args;
    csig_res := res;
    csig_cc := cc_default
  |}.

Definition csig_union (sig1 sig2: csignature): res csignature :=
  _ <- eassert (MSG "signature mismatch" :: nil) (sig1 = sig2);
  ret sig1.

Definition csig_sig (csig: csignature): signature :=
  signature_of_type (csig_args csig) (csig_res csig) (csig_cc csig).
