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
Require Import liblayers.lib.Functor.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.logic.Structures.
Require Import liblayers.logic.LayerData.


(** * Discussion *)

(** From a pre-existing order on type [A], we can build two different
  orders on the type [option A] depending on whether we interpret
  the new element [None] as ⊥ or ⊤. For our purposes both are useful.

  Indeed consider modules for example. We say that [M1 ≤ M2] if all of
  the definitions in [M1] are present in [M2]. This means that when we
  inerpret [None] as the absence of a definition, we should think of
  it as a ⊥ element: any definition is bigger than no definition.

  But for a given symbol defined in [M1], in addition to providing the
  same definition, a larger module [M2] is also allowed to associate
  the special value [magic] with that symbol. This means that the
  symbol is "overdefined": [magic] is the result of linking two
  conflicting modules, for instance [i ↦ τ ⊕ i ↦ τ = i ↦ magic].
  Since we want [⊕] to be monotonic, and an upper bound of its
  arguments, it is natural to interpret [magic] as a top element.

  Of course, attempting to construct an actual program from a module
  containing [magic] will fail. But this failure fits right in as ⊤,
  since it results from a module that is in some sense too large.
  We like to use the option monad to express the program construction
  process, and if in this context we interpret [None] as a ⊤ element,
  then we do not need any special side-conditions when stating the
  monotonicity of program construction. *)


(** * Simple order *)

Section OPTION_LE_BOT.
  Inductive option_le {A B} (R: rel A B): rel (option A) (option B) :=
    | option_le_none:
        LowerBound (option_le R) None
    | option_le_some_def:
        (R ++> option_le R) (@Some _) (@Some _).

  Global Existing Instance option_le_none.

  Global Instance option_le_subrel A B:
    Proper (subrel ++> subrel) (@option_le A B).
  Proof.
    intros R1 R2 HR x y Hxy.
    destruct Hxy; constructor; eauto.
  Qed.

  Global Instance option_le_rel {A B} (R: rel A B):
    subrel (option_rel R) (option_le R).
  Proof.
    intros _ _ []; constructor; eauto.
  Qed.

  Global Instance option_le_some:
    Proper (∀ R, R ++> option_le R) (@Some).
  Proof.
    exact @option_le_some_def.
  Qed.

  Local Instance option_le_op `(Ale: Le): Le (option A) :=
    { le := option_le (≤) }.

  Global Instance option_le_monotonic {A B}:
    Proper (subrel ++> subrel) (@option_le A B).
  Proof.
    intros R1 R2 HR x y H.
    destruct H; constructor.
    apply HR.
    assumption.
  Qed.

  Global Instance option_le_bot_preorder {A} (R: relation A):
    PreOrder R -> PreOrder (option_le R).
  Proof.
    intros H.
    split.
    * intros [x|]; constructor; reflexivity.
    * intros _ _ z [x | x y Hxy] Hz; inversion Hz; subst; clear Hz.
      + constructor.
      + constructor.
      + constructor.
        etransitivity; eassumption.
  Qed.
End OPTION_LE_BOT.

(** The constructors of [option_le] have type classes as types, so we
  need to cast them before we use them as hints. *)
Hint Resolve (option_le_none : forall R y, option_le R _ _) : liblayers.
Hint Resolve (option_le_some : forall A B R x y _, option_le R _ _) : liblayers.

(** ** Option predicates *)

Global Instance isSome_le:
  Proper (∀ R, option_le R ++> impl) (@isSome).
Proof.
  intros A1 A2 RA x1 x2 Hx H.
  destruct Hx.
  * inversion H.
    discriminate.
  * exists y.
    reflexivity.
Qed.

Global Instance isNone_le:
  Proper (∀ R, option_le R --> impl) (@isNone).
Proof.
  intros A1 A2 RA x1 x2 Hx H.
  destruct Hx.
  * reflexivity.
  * inversion H.
Qed.

(** ** Monad operations *)

Instance option_bind_monotonic:
  Proper
    (∀ RA, ∀ RB, (RA ++> option_le RB) ++> option_le RA ++> option_le RB)
    (@bind option _ _).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg a1 a2 Ha.
  destruct Ha; autorewrite with monad; eauto with liblayers.
Qed.

Instance option_fmap_monotonic:
  Proper
    (∀ RA, ∀ RB, (RA ++> RB) ++> option_le RA ++> option_le RB)
    (@fmap option _).
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg a1 a2 Ha; simpl.
  destruct Ha; eauto with liblayers.
Qed.
