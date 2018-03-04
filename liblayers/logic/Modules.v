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
Require Import liblayers.lib.Decision.
Require Export liblayers.logic.Structures.
Require Export liblayers.logic.PseudoJoin.
Require Export liblayers.logic.OptionOrders.
Require Import liblayers.compcertx.ErrorMonad.

(** * Modules *)

(** Modules are essentially maps from identifiers to definitions of
  global variable and function definitions. The file [PTreeModules]
  provides an implementation with [positive] identifiers. *)

Class ModuleOps ident F V module :=
  {
    module_le :> Le module;
    module_empty :> Emptyset module;
    module_oplus :> Oplus module;
    module_mapsto_fundef :> Mapsto ident F module;
    module_mapsto_vardef :> Mapsto ident V module;

    get_module_function (i: ident) (M: module): res (option F);
    get_module_variable (i: ident) (M: module): res (option V);

    module_decide_function (P: res (option F) -> Prop) :>
      (forall κ, Decision (P κ)) ->
      (forall L, Decision (forall i, P (get_module_function i L)));
    module_decide_function_name (P: ident -> Prop) :>
      (forall i, Decision (P i)) ->
      (forall M, Decision (forall i, get_module_function i M <> OK None -> P i));
    module_decide_variable (P: res (option V) -> Prop) :>
      (forall τ, Decision (P τ)) ->
      (forall L, Decision (forall i, P (get_module_variable i L)));
    module_decide_variable_name (P: ident -> Prop) :>
      (forall i, Decision (P i)) ->
      (forall M, Decision (forall i, get_module_variable i M <> OK None -> P i))
  }.

(** * Properties of modules *)

Class Modules ident F V module `{mops: ModuleOps ident F V module} :=
  {
    modules_pseudojoin :> PseudoJoin module ∅;

    get_module_function_empty i:
      get_module_function i ∅ = OK None;
    get_module_function_mapsto i (κ: F):
      get_module_function i (i ↦ κ) = OK (Some κ);
    get_module_function_mapsto_other_function i j (κ: F):
      i <> j -> get_module_function i (j ↦ κ) = OK None;
    get_module_function_mapsto_variable i j (τ: V):
      get_module_function i (j ↦ τ) = OK None;
    get_module_function_oplus i M1 M2:
      get_module_function i (M1 ⊕ M2) =
      get_module_function i M1 ⊕ get_module_function i M2;
    get_module_function_monotonic :>
      Proper (- ==> (≤) ++> res_le (option_le eq)) get_module_function;
    get_module_variable_empty i:
      get_module_variable i ∅ = OK None;
    get_module_variable_mapsto i (τ: V):
      get_module_variable i (i ↦ τ) = OK (Some τ);
    get_module_variable_mapsto_other_variable i j (τ: V):
      i <> j -> get_module_variable i (j ↦ τ) = OK None;
    get_module_variable_mapsto_function i j (κ: F):
      get_module_variable i (j ↦ κ) = OK None;
    get_module_variable_oplus i M1 M2:
      get_module_variable i (M1 ⊕ M2) =
      get_module_variable i M1 ⊕ get_module_variable i M2;
    get_module_variable_monotonic :>
      Proper (- ==> (≤) ++> res_le (option_le eq)) get_module_variable
  }.

Ltac get_module_normalize :=
  repeat rewrite
    ?get_module_function_empty,
    ?get_module_function_mapsto,
    ?get_module_function_mapsto_other_function,
    ?get_module_function_mapsto_variable,
    ?get_module_function_oplus,
    ?get_module_variable_empty,
    ?get_module_variable_mapsto,
    ?get_module_variable_mapsto_other_variable,
    ?get_module_variable_mapsto_function,
    ?get_module_variable_oplus by assumption.

Ltac get_module_normalize_in H :=
  repeat rewrite
    ?get_module_function_empty,
    ?get_module_function_mapsto,
    ?get_module_function_mapsto_other_function,
    ?get_module_function_mapsto_variable,
    ?get_module_function_oplus,
    ?get_module_variable_empty,
    ?get_module_variable_mapsto,
    ?get_module_variable_mapsto_other_variable,
    ?get_module_variable_mapsto_function,
    ?get_module_variable_oplus in H by assumption.

(** * Well-formed modules *)

Section MODULE_OK.
  Context `{Hmod: Modules}.
  Context `{Hident_dec: forall i j: ident, Decision (i = j)}.

  (** [ModuleOK] denotes the property that at every identifier, at most
    one of the variable or function is defined, and that the module
    contains no errors. *)

  Record ModuleOK_at M i :=
    {
      module_ok_function:
        isOK (get_module_function i M);
      module_ok_variable:
        isOK (get_module_variable i M);
      module_ok_disjoint:
        isOKNone (get_module_function i M) \/
        isOKNone (get_module_variable i M)
    }.

  Class ModuleOK (M: module): Prop :=
    module_ok_at: forall i, ModuleOK_at M i.

  (** ** [ModuleOK] is decidable *)

  (** Alternative definition of [ModuleOK] that can be decided
    automatically. *)
  Definition ModuleOK_alt (M: module) :=
    (forall i, isOK (get_module_function i M)) /\
    (forall i, isOK (get_module_variable i M)) /\
    (forall i, get_module_function i M <> OK None ->
               isOKNone (get_module_variable i M)) /\
    (forall i, get_module_variable i M <> OK None ->
               isOKNone (get_module_function i M)).

  Lemma ModuleOK_alt_iff (M: module):
    ModuleOK_alt M <-> ModuleOK M.
  Proof.
    split.
    * intros (HMf & HMv & HMd & HMd') i.
      split; eauto.
      destruct (decide (isOKNone (get_module_function i M))) as [HMi|HMi]; eauto.
    * intros HM.
      split; [|split]; [| |split]; intros i; destruct (HM i); tauto.
  Qed.

  Global Instance module_ok_dec (M: module):
    Decision (ModuleOK M) := _.
  Proof.
    eapply decide_rewrite.
    * apply ModuleOK_alt_iff.
    * unfold ModuleOK_alt.
      typeclasses eauto.
  Defined.

  (** ** Monotonicity *)

  Global Instance module_ok_at_antitonic:
    Proper ((≤) --> - ==> impl) ModuleOK_at.
  Proof.
    intros M1 M2 HM i [HMif HMiv HMifv].
    rewrite HM in *.
    split; assumption.
  Qed.

  Global Instance module_ok_antitonic:
    Proper ((≤) --> impl) ModuleOK.
  Proof.
    intros M1 M2 HM HM1 i.
    rewrite <- HM.
    eauto.
  Qed.

  (** ** Basic instances *)

  Global Instance empty_ok:
    ModuleOK ∅.
  Proof.
    intros i.
    split; get_module_normalize; repeat econstructor.
  Qed.

  Global Instance mapsto_function_ok (i: ident) (κ: F):
    ModuleOK (i ↦ κ).
  Proof.
    intros j.
    destruct (decide (j = i)); subst;
    split; get_module_normalize; eauto.
  Qed.

  Global Instance mapsto_variable_ok (i: ident) (τ: V):
    ModuleOK (i ↦ τ).
  Proof.
    intros j.
    destruct (decide (j = i)); subst;
    split; get_module_normalize; eauto.
  Qed.

  (** These instances should not be added to the hint database
    directly because that would cause a loop, however we can use them
    in conjunction with [Hint Immediate]. *)

  Local Instance module_oplus_ok_left M1 M2:
    ModuleOK (M1 ⊕ M2) ->
    ModuleOK M1.
  Proof.
    intros H.
    rewrite (left_upper_bound M1 M2).
    assumption.
  Qed.

  Local Instance module_oplus_ok_right M1 M2:
    ModuleOK (M1 ⊕ M2) ->
    ModuleOK M2.
  Proof.
    intros H.
    rewrite (right_upper_bound M1 M2).
    assumption.
  Qed.

  (** ** Other lemmas *)

  Lemma get_module_function_variable_disjoint M `{ModuleOK M} i:
    isOKNone (get_module_function i M) \/ isOKNone (get_module_variable i M).
  Proof.
    destruct (H i) as [_ _ Hdisj].
    assumption.
  Qed.

  Lemma module_oplus_function_ok_elim (M: module) (i: ident) (f: F):
    ModuleOK (M ⊕ i ↦ f) ->
    isOKNone (get_module_function i M) /\
    isOKNone (get_module_variable i M).
  Proof.
    intros HMif.
    destruct (HMif i) as [Hf _ Hd].
    get_module_normalize_in Hf.
    get_module_normalize_in Hd.
    rewrite <- right_upper_bound in Hd.
    destruct Hd as [Hd|Hd]; try discriminate.
    rewrite <- left_upper_bound in Hd.
    split; try assumption; clear Hd.
    destruct (get_module_function i M) as [[|]|]; eauto;
    simpl in Hf; monad_norm; apply isOK_Error in Hf;
    elim Hf.
  Qed.

  Lemma module_oplus_function_same (M: module) (i: ident) (κ: F):
    ModuleOK (M ⊕ i ↦ κ) ->
    get_module_function i (M ⊕ i ↦ κ) = OK (Some κ).
  Proof.
    intros MOK.
    destruct (MOK i) as [Hf _ Hdisj]; clear MOK.
    get_module_normalize_in Hf.
    get_module_normalize_in Hdisj.
    rewrite <- right_upper_bound in Hdisj.
    destruct Hdisj; try discriminate.
    destruct Hf as [x Hx].
    get_module_normalize.
    destruct (get_module_function i M) as [[|]|]; try discriminate.
    reflexivity.
  Qed.

  Lemma module_oplus_function_other (M: module) (i j: ident) (κ: F):
    i <> j ->
    get_module_function i (M ⊕ j ↦ κ) = get_module_function i M.
  Proof.
    intros Hij.
    get_module_normalize.
    destruct (get_module_function i M) as [[|]|]; reflexivity.
  Qed.

  Lemma module_oplus_variable (M: module) (i j: ident) (κ: F):
    get_module_variable i (M ⊕ j ↦ κ) = get_module_variable i M.
  Proof.
    get_module_normalize.
    destruct (get_module_variable i M) as [[|]|]; reflexivity.
  Qed.
End MODULE_OK.

Hint Immediate module_oplus_ok_left : typeclass_instances.
Hint Immediate module_oplus_ok_right : typeclass_instances.

Section AuxLemma.

  Lemma get_module_variable_left `{mo_ops: Modules}:
    forall i a b v,
      get_module_variable i a = OK (Some v) ->
      isOK (get_module_variable i (a ⊕ b)) ->
      get_module_variable i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_module_variable_oplus i a b).
    rewrite Hcom. rewrite H. 
    intros.
    destruct (get_module_variable i b); try destruct o; inv_monad H0.
    reflexivity.
  Qed.

  Lemma get_module_variable_right `{mo_ops: Modules}:
    forall i a b v,
      get_module_variable i b = OK (Some v) ->
      isOK (get_module_variable i (a ⊕ b)) ->
      get_module_variable i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_module_variable_oplus i a b).
    rewrite Hcom. rewrite H. 
    intros. 
    destruct (get_module_variable i a); try destruct o; inv_monad H0.
    reflexivity.
  Qed.

  Lemma get_module_variable_none `{mo_ops: Modules}:
    forall i a b,
      get_module_variable i b = OK None ->
      get_module_variable i a = OK None ->
      isOK (get_module_variable i (a ⊕ b)) ->
      get_module_variable i (a ⊕ b) = OK None.
  Proof.
    intros. destruct H1 as [? Hcom].
    specialize (get_module_variable_oplus i a b).
    rewrite Hcom. rewrite H. rewrite H0.
    intros. inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_module_variable_isOK `{mo_ops: Modules}:
    forall i a b,
      isOK (get_module_variable i (a ⊕ b)) ->
      isOK (get_module_variable i a)
      /\ isOK (get_module_variable i b).
  Proof.
    intros. destruct H as [? Hcom].
    specialize (get_module_variable_oplus i a b).
    rewrite Hcom.
    intros.
    destruct (get_module_variable i a);
      destruct (get_module_variable i b); inv_monad H.
    split; esplit; eauto.
  Qed.

  Lemma get_module_varible_OK_Some_left `{mo_ops: Modules}:
    forall v i a b v',
      get_module_variable i a = OK (Some v) ->
      get_module_variable i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_module_variable_oplus i a b).
    rewrite H. rewrite H0.
    intros.
    destruct (get_module_variable i b); try destruct o; inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_module_varible_OK_Some_right `{mo_ops: Modules}:
    forall v i a b v',
      get_module_variable i b = OK (Some v) ->
      get_module_variable i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_module_variable_oplus i a b).
    rewrite H. rewrite H0.
    intros.
    destruct (get_module_variable i a); try destruct o; inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_module_function_cancel `{mo_ops: Modules}:
    forall i a b,
      get_module_function i (a ⊕ b) = OK None ->
      get_module_function i b = OK None /\
      get_module_function i a = OK None.
  Proof.
    intros. 
    specialize (get_module_function_oplus i a b).
    rewrite H. 
    intros. 
    destruct (get_module_function i a); try destruct o;
    destruct (get_module_function i b); try destruct o;
    inv_monad H0.
    split; reflexivity.
  Qed.

  Lemma get_module_variable_cancel `{mo_ops: Modules}:
    forall i a b,
      get_module_variable i (a ⊕ b) = OK None ->
      get_module_variable i b = OK None /\
      get_module_variable i a = OK None.
  Proof.
    intros. 
    specialize (get_module_variable_oplus i a b).
    rewrite H. 
    intros. 
    destruct (get_module_variable i a); try destruct o;
    destruct (get_module_variable i b); try destruct o;
    inv_monad H0.
    split; reflexivity.
  Qed.

  Lemma get_module_function_none_oplus `{mo_ops: Modules}:
    forall i CTXT M,
      isOKNone (get_module_function i (CTXT ⊕ M)) ->    
      isOKNone (get_module_function i CTXT)
      /\ isOKNone (get_module_function i M).
  Proof.
    intros.
    specialize (get_module_function_oplus i CTXT M).
    unfold isOKNone in H. rewrite H.
    intros Hle.
    destruct (get_module_function i CTXT); try destruct o; destruct (get_module_function i M);
    try destruct o; inv_monad Hle.
    split; reflexivity.
  Qed.

  Lemma get_module_variable_none_oplus `{mo_ops: Modules}:
    forall i CTXT M,
      isOKNone (get_module_variable i (CTXT ⊕ M)) ->    
      isOKNone (get_module_variable i CTXT)
      /\ isOKNone (get_module_variable i M).
  Proof.
    intros.
    specialize (get_module_variable_oplus i CTXT M).
    unfold isOKNone in H. rewrite H.
    intros Hle.
    destruct (get_module_variable i CTXT); try destruct o; destruct (get_module_variable i M);
    try destruct o; inv_monad Hle.
    split; reflexivity.
  Qed.

  Lemma get_module_function_isOK `{mo_ops: Modules}:
    forall i a b,
      isOK (get_module_function i (a ⊕ b)) ->
      isOK (get_module_function i a)
      /\ isOK (get_module_function i b).
  Proof.
    intros. destruct H as [? Hcom].
    specialize (get_module_function_oplus i a b).
    rewrite Hcom.
    intros.
    destruct (get_module_function i a);
      destruct (get_module_function i b); inv_monad H.
    split; esplit; eauto.
  Qed.

End AuxLemma.
