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
Require Import ExtensionalityAxioms.
Require Import Functor.
Require Import compcert.common.Errors.


(** * Interface of monads *)

(** As in Haskell, we define monads in terms of [ret] and [bind].
  However we want to be able to use the corresponding [Functor]
  instances both independently and in the context of monads.
  To permit this, instead of defining a generic [Functor] instance
  for all monads, we require a priori that monads be functors,
  then define the relationship between [fmap], [ret] and [bind]
  as the [monad_fmap] equation in the [Monad] class. This way,
  code need not depend on this module when they use, say, [option]
  as a simple [Functor] rather than a full-blown [Monad].
  In addition, [id] for instance is both a [Monad] and [Comonad],
  but we do not want to derive two separate instances of the
  corresponding [Functor].

  XXX: document tactics, and when to use unfold vs. simpl
  vs. autorewrite vs. inv_monad. *)

Class MonadOps (M: Type -> Type) `{Mfmap: FunctorOps M} := {
  ret {A}: A -> M A;
  bind {A B}: (A -> M B) -> M A -> M B
}.

(** Be careful not to gratuitously unfold [ret]s and [bind]s, which
  would break the [inv_monad] tactic. *)
Arguments ret : simpl never.
Arguments bind : simpl never.

Notation "x <- M ; N" := (bind (fun x => N) M)
  (at level 30, right associativity).

Class Monad (M: Type -> Type) `{Mops: MonadOps M}: Prop := {
  monad_functor :> Functor M;
  monad_fmap {A B} (f: A -> B):
    fmap f = bind (fun x => ret (f x));
  monad_ret_bind {A B} (f: A -> M B) (x: A):
    bind f (ret x) = f x;
  monad_bind_ret {A} (m: M A):
    bind ret m = m;
  monad_bind_bind {A B C} (f: B -> M C) (g: A -> M B) (m: M A):
    bind f (bind g m) = bind (fun x => bind f (g x)) m
}.

(** Some monads provide some of these inversion properties. *)

Class MonadInvRet M `{Mops: MonadOps M} :=
  monad_inv_ret:
    forall {A} (x y: A),
      ret x = ret y -> x = y.

Class MonadInvBind M `{Mops: MonadOps M} :=
  monad_inv_bind_extract:
    forall {A B} (f: A -> M B) (ma: M A) (b: B),
      bind f ma = ret b -> { a | ma = ret a }.

Class MonadInvBindWeak M `{Mops: MonadOps M} :=
  monad_inv_bind_weak:
    forall {A B} (f: A -> M B) (ma: M A) (b: B),
      bind f ma = ret b -> exists a, f a = ret b.


(** * Normalization *)

(** Using the theorem in [Monad], we can try to normalize monadic
  expressions to the form [x1 <- M1; x2 <- M2; ...; xn <- Mn]. *)
Hint Rewrite
    @monad_ret_bind
    @monad_bind_ret
    @monad_bind_bind
  using typeclasses eauto : monad.

(** Unfortunately, the [MonadOps] instance in [monad_fmap] cannot
  be obtained by unification when matching the left-hand side of
  the rewrite with the current goal. Since the [autorewrite] tactic
  does not do type class resolution, we cannot use [monad_fmap]
  as a rewrite rule. *)
Ltac rewrite_monad_fmap :=
  match goal with [ H: _ |- _ ] => rewrite monad_fmap in H end ||
  rewrite monad_fmap.
Ltac monad_norm :=
  repeat rewrite_monad_fmap; autorewrite with monad in *.


(** * Monad inversion *)

Section MONADINV.
  Context `{HM: Monad}.
  Context `{HMbind: !MonadInvBind M}.
  Context `{HMret: !MonadInvRet M}.

  Global Instance monad_inv_bind_inv_bind_weak:
    MonadInvBindWeak M.
  Proof.
    intros A B f ma b H.
    destruct (monad_inv_bind_extract f ma b H) as [a Ha].
    exists a.
    subst.
    monad_norm.
    assumption.
  Qed.

  Lemma monad_inv_bind {A B} (f: A -> M B) (ma: M A) (b: B):
    bind f ma = ret b ->
    { a | ma = ret a /\ f a = ret b }.
  Proof.
    intros H.
    destruct (monad_inv_bind_extract f ma b H) as [a Ha].
    exists a.
    split.
    * assumption.
    * subst.
      monad_norm.
      assumption.
  Qed.

  Lemma monad_inv_bind_iff {A B} (f: A -> M B) (ma: M A) (b: B):
    bind f ma = ret b <->
    exists a, ma = ret a /\ f a = ret b.
  Proof.
    split.
    * intros H.
      apply monad_inv_bind in H.
      destruct H.
      eauto.
    * intros [a [Hma Hfa]].
      subst.
      monad_norm.
      assumption.
  Qed.

  Lemma monad_inv_ret_iff {A} (x y: A):
    ret x = ret y <-> x = y.
  Proof.
    split.
    apply monad_inv_ret.
    apply f_equal.
  Qed.
End MONADINV.

Ltac inv_monad H :=
  repeat match type of H with
    | context C[Errors.OK ?x] =>
      change (OK x) with (ret (M:=res) x) in H
    | context C[@Errors.bind ?A ?B ?ra ?f] =>
      change (@Errors.bind A B ra f) with (bind (M:=res) (A:=A) (B:=B) f ra)
    | context C[Some ?x] =>
      change (Some x) with (ret x) in H
  end;
  match type of H with
    | ret ?x = ret ?y =>
      apply monad_inv_ret in H

    | ret ?mb = bind ?f ?ma =>
      symmetry in H;
      inv_monad H

    | bind ?f ?ma = ret ?mb =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct (monad_inv_bind f ma mb H) as [? [H1 H2]];
      clear H; rename H2 into H;
      try (inv_monad H1);
      inv_monad H

    | bind ?f ?ma = ret ?mb =>
      destruct (monad_inv_bind_weak f ma mb H) as [? ?]

    | _ => inversion H; clear H; subst
  end.


(** * Properties *)

Lemma monad_bind_fmap `{Monad} {A B C} (m: M A) (f: B -> C) (g: A -> M B):
  x <- m; fmap f (g x) = fmap f (x <- m; g x).
Proof.
  monad_norm.
  reflexivity.
Qed.


(** * Some instances *)

(** The unit monad is interesting because it is an example of a monad
  which accepts none of the inversion properties defined earlier. *)

Section CONST_UNIT.
  Global Instance const_unit_monad_ops: MonadOps (fun X => unit) := {
    bind A B f mx := tt;
    ret A x := tt
  }.

  Global Instance const_unit_monad: Monad (fun X => unit).
  Proof.
    split; unfold bind, ret; simpl.
    * typeclasses eauto.
    * intros _ _ _.
      apply functional_extensionality.
      intros [].
      reflexivity.
    * intros ? _ f x.
      destruct (f x).
      reflexivity.
    * intros _ [].
      reflexivity.
    * intros _ _ _ _ _ _.
      reflexivity.
  Qed.

  Lemma const_unit_no_inv_ret: ~ MonadInvRet (fun _ => unit).
  Proof.
    intros Hinv.
    assert (H: true <> false) by discriminate.
    apply H.
    apply (monad_inv_ret (M := fun _ => unit)).
    destruct (ret true), (ret false).
    reflexivity.
  Qed.

  Lemma const_unit_no_inv_weak_bind: ~ MonadInvBindWeak (fun _ => unit).
  Proof.
    intros Hinv.
    pose proof (Empty_set_rect (fun _ => unit) : Empty_set -> unit) as f.
    assert (H: bind f tt = ret tt) by reflexivity.
    apply monad_inv_bind_weak in H.
    destruct H as [x _].
    elim x.
  Qed.
End CONST_UNIT.
