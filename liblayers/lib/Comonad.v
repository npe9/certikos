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
(** FIXME: rework to follow the same approach as [Monad]
  wrt its relation with [Functor]. *)

Require Export Coq.Program.Basics.
Require Import ExtensionalityAxioms.
Require Import Functor.
Require Import Lens.


(** * Interface of comonads *)

(** Comonads are defined in terms of [extract] and [extend]. *)

Class ComonadOps (W: Type -> Type) := {
  extract {A}: W A -> A;
  extend {A B}: (W A -> B) -> W A -> W B
}.

Class Comonad (W: Type -> Type) `{Wops: ComonadOps W}: Prop := {
  comonad_extract_extend {A B} (f: W A -> B) (w: W A):
    extract (extend f w) = f w;
  comonad_extend_extract {A} (w: W A):
    extend extract w = w;
  comonad_extend_extend {A B C} (f : W B -> C) (g: W A -> B) (w: W A):
    extend f (extend g w) = extend (fun w => f (extend g w)) w
}.

Hint Rewrite
    @comonad_extract_extend
    @comonad_extend_extract
    @comonad_extend_extend
  using typeclasses eauto : comonad.


(** * Comonads are functors *)

Section FUNCTOR.
  Context `{HW: Comonad}.

  Global Instance comonad_fmap: FunctorOps W := {
    fmap A B f :=
      extend (fun w => f (extract w))
  }.

  Global Instance comonad_functor: Functor W.
  Proof.
    split; intros; simpl; autorewrite with comonad.
    - reflexivity.
    - setoid_rewrite comonad_extract_extend.
      reflexivity.
  Qed.
End FUNCTOR.


(** * Definitions and theorems *)

Section THEORY.
  Context `{HW: Comonad}.

  Definition put {A B} (x: B): W A -> W B :=
    extend (const x).

  Theorem comonad_extend_eq {A B} (f g: W A -> B) (w: W A):
    extend f w = extend g w -> f w = g w.
  Proof.
    intros.
    apply (f_equal extract) in H.
    rewrite !comonad_extract_extend in H.
    assumption.
  Qed.

  Theorem comonad_put_eq {A B} (x y: B) (w: W A):
    put x w = put y w <-> x = y.
  Proof.
    split.
    - apply comonad_extend_eq.
    - intro; apply f_equal2; trivial.
  Qed.

  Theorem comonad_extract_put {A B} (x: A) (w: W B):
    extract (put x w) = x.
  Proof.
    unfold put.
    apply comonad_extract_extend.
  Qed.

  Theorem comonad_put_put {A B C} (x: A) (y: B) (w: W C):
    put x (put y w) = put x w.
  Proof.
    unfold put, const.
    rewrite comonad_extend_extend.
    reflexivity.
  Qed.
End THEORY.


(** * Comonad-based lens *)

(** Given a comonad [W], we can define lens operations, where we get
  a substructure of type [A] in a structure of type [W A]. However,
  [LensSetGet] does not follow from the comonad laws. *)

Section LENS.
  Context (W: Type -> Type) `{HW: Comonad W} (A: Type).

  Global Instance comonad_lensops: LensOps (V:=A) extract := {
    set := put
  }.

  Global Instance comonad_get_set: LensGetSet extract := {
    lens_get_set := comonad_extract_put
  }.

  Global Instance comonad_set_set: LensSetSet extract := {
    lens_set_set := comonad_put_put
  }.

  (** [LensSetGet] does not hold in general -- for instance in the store
    comonad, [put] overwrites all entries instead of just the focused one. *)
  Context `{Hps: !LensSetGet extract}.

  (** Provided the Put/Get law is proved separately, we get a lens. *)
  Global Instance comonad_lens: Lens extract := {}.

  (** In addition, we can provide this equivalent lemma, formulated in
    terms of extract and set. *)
  Lemma comonad_put_extract (w: W A):
    put (extract w) w = w.
  Proof.
    exact (lens_set_get w).
  Qed.
End LENS.

Hint Rewrite
    @comonad_put_eq
    @comonad_extract_put
    @comonad_put_put
    @comonad_put_extract
  using typeclasses eauto: comonad.


(** * Some instances *)

Section INSTANCES.
  Open Scope type_scope.

  (** ** [A * -] is a comonad. *)

  Global Instance prod_comonad_ops {A}: ComonadOps (prod A) := {
    extract := @snd A;
    extend X Y f x := (fst x, f x)
  }.

  Global Instance prod_comonad {A}: Comonad (prod A).
  Proof.
    split; simpl; try destruct w; now reflexivity.
  Qed.

  (** ** [- * A] is a comonad *)

  Global Instance prod_l_comonad_ops {A}: ComonadOps (fun X => X * A) := {
    extract X := @fst X A;
    extend X Y f x := (f x, snd x)
  }.

  Global Instance prod_l_comonad {A}: Comonad (fun X => X * A).
  Proof.
    split; intros; try destruct w; now reflexivity.
  Qed.
End INSTANCES.
