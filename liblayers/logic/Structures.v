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
Require Export Coq.Lists.List.
Require Export Coq.Program.Basics.
Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Bool.Bool.
Require Export liblayers.lib.LogicalRelations.

(** Unfortunately, we cannot export this library because CompCert
  declares a conflicting notation for [@@]. *)
Require Import Coq.Classes.RelationPairs.


(** * Generic operations *)

(** The class definitions below are MathClasses-style overloaded
  operators. This is quite useful because common structures show up
  between modules and layers, and at different levels of their
  construction.

  We use Coq's excellent support for UTF-8, which helps with clarity
  and conciseness. Proof General users may want to use the TeX input
  method to type special characters: hit [C-\], and Emacs will ask you
  "Input method:". If you answer [tex], Emacs will automatically
  replace any LaTeX sequence you (say, [\le]) by the corresponding
  symbol (say, ≤).

  By convention, most of the time we use the LaTeX sequence of the
  operator as the name for the class and field, so the sequences for
  the operators below should be obvious. The only exception is
  [compose], which is denoted by [̧\circ]. *)

Class Id A := { id : A }.

Class Compose A B C := { compose : A -> B -> C }.
Notation "(;)" := compose.
Notation "f ∘ g" := (compose g f) (at level 40, left associativity).

Class Emptyset A := { emptyset : A }.
Notation "∅" := emptyset.

Class Bot A := { bot : A }.
Notation "⊥" := bot.

Class Top A := { top : A }.
Notation "⊤" := top.

Class Le A := { le : relation A }.
Notation "(≤)" := le.
Infix "≤" := le (at level 70, right associativity).

Class Equiv A := { equiv : relation A }.
Notation "(≡)" := equiv.
Infix "≡" := equiv (at level 70, right associativity).

Class Oplus A := { oplus : A -> A -> A }.
Notation "(⊕)" := oplus.
Infix "⊕" := oplus (at level 60, right associativity).

Class Mapsto A B C := { mapsto : A -> B -> C }.
Notation "(↦)" := mapsto.
Notation "( i ↦)" := (mapsto i).
Infix "↦" := mapsto (at level 55, right associativity).

Class Vdash A B C := { vdash : A -> B -> C -> Prop }.
Notation "Γ ⊢ M : τ" := (vdash Γ M τ)
  (at level 65, left associativity, M at level 99).

(** Generic operators for a type of specifications [T] *)

Definition sim_relation {layerdata} (simrel: layerdata -> layerdata -> Type) T :=
  forall D1 D2 (R: simrel D1 D2), rel (T D1) (T D2).

Class Sim {layerdata} simrel (T: layerdata -> Type) :=
  { simRR : sim_relation simrel T }.

Notation sim := (simRR _ _).

Class Semof {layerdata} (A: Type) (T U: layerdata -> Type) :=
  { semof: forall D, A -> T D -> U D }.

Notation "〚-〛" := (semof _).
Notation "〚 M 〛" := (semof _ M).

(** Sometimes we want [eauto] to unfold the generic operators so as to
  apply theorems about a specific implementation. *)
Hint Unfold le : liblayers.


(** * Generic properties *)

(** Now we can give generic definitions for some recurring properties,
  making use of the overloaded operators above. *)

Class Associative {A} (R: relation A) (op: A -> A -> A): Prop :=
  associativity x y z : R (op (op x y) z) (op x (op y z)).

Class Commutative {A} (R: relation A) (op: A -> A -> A): Prop :=
  commutativity x y : R (op x y) (op y x).

Class LeftIdentity {A} (R: relation A) (op: A -> A -> A) (u: A): Prop :=
  id_left y : R (op u y) y.

Class RightIdentity {A} (R: relation A) (op: A -> A -> A) (u: A): Prop :=
  id_right x : R (op x u) x.

Class LeftUpperBound {A} (R: relation A) (op: A -> A -> A): Prop :=
  left_upper_bound x y : R x (op x y).

Class RightUpperBound {A} (R: relation A) (op: A -> A -> A): Prop :=
  right_upper_bound x y : R y (op x y).

Class LowerBound {A B} (R: rel A B) (lb: A): Prop :=
  lower_bound : forall y, R lb y.

Class UpperBound {A B} (R: rel A B) (ub: B): Prop :=
  upper_bound : forall x, R x ub.


(** ** Hints for [eauto] and [autorewrite] *)

(** Most of the generic properties above cannot be used directly as
  hints because the head term is a variable. Hence we register a
  couple of versions specialized to often-used (families of)
  relations. *)

Hint Resolve (associativity (R := eq)) : liblayers.
Hint Resolve (commutativity (R := eq)) : liblayers.
Hint Resolve (id_left (R := eq)) : liblayers.
Hint Resolve (id_right (R := eq)) : liblayers.

Hint Resolve (associativity (R := (≡))) : liblayers.
Hint Resolve (commutativity (R := (≡))) : liblayers.
Hint Resolve (id_left (R := (≡))) : liblayers.
Hint Resolve (id_right (R := (≡))) : liblayers.

Hint Resolve (associativity (R := (≤))) : liblayers.
Hint Resolve (commutativity (R := (≤))) : liblayers.
Hint Resolve (id_left (R := (≤))) : liblayers.
Hint Resolve (id_right (R := (≤))) : liblayers.
Hint Resolve (left_upper_bound (R := (≤))) : liblayers.
Hint Resolve (right_upper_bound (R := (≤))) : liblayers.
Hint Resolve (lower_bound (R := (≤))) : liblayers.
Hint Resolve (upper_bound (R := (≤))) : liblayers.

(** For rewriting we have a similar problem, where once things are
  filled in by unification with the match found, the generated
  subgoals (namely the typeclass instances to resolve) cannot contain
  existential variables. Hence we apply the same specialization
  strategy. Unfortunately, here we have to spell it out as separate
  lemmas, because the registered rewrite theorems cannot contain holes
  (only regular premises to be solved by the tactic provided). *)

Lemma associativity_eq {A} `{Associative A eq}:
  forall x y z, op (op x y) z = op x (op y z).
Proof associativity.

Lemma id_left_eq {A} `{LeftIdentity A eq}:
  forall x, op u x = x.
Proof id_left.

Lemma id_right_eq {A} `{RightIdentity A eq}:
  forall x, op x u = x.
Proof id_right.

Lemma associativity_le `{Le} `{Associative _ (≤)}:
  forall x y z, op (op x y) z ≤ op x (op y z).
Proof associativity.

Lemma id_left_le `{Le} `{LeftIdentity _ (≤)}:
  forall x, op u x ≤ x.
Proof id_left.

Lemma id_right_le `{Le} `{RightIdentity _ (≤)}:
  forall x, op x u ≤ x.
Proof id_right.

Lemma associativity_equiv `{Equiv} `{Associative _ (≡)}:
  forall x y z, op (op x y) z ≡ op x (op y z).
Proof associativity.

Lemma id_left_equiv `{Equiv} `{LeftIdentity _ (≡)}:
  forall x, op u x ≡ x.
Proof id_left.

Lemma id_right_equiv `{Equiv} `{RightIdentity _ (≡)}:
  forall x, op x u ≡ x.
Proof id_right.

Hint Rewrite
    @associativity_eq
    @id_left_le
    @id_right_eq
    @associativity_le
    @id_left_le
    @id_right_le
    @associativity_equiv
    @id_left_equiv
    @id_right_equiv
  using typeclasses eauto : liblayers.


(** ** Some properties of properties *)

Global Instance assoc_subrel {A} (R S: relation A) (op: A -> A -> A):
  subrelation R S ->
  Unconvertible _ R S ->
  Associative R op ->
  Associative S op.
Proof.
  intros HRS _ Hassoc x y z.
  apply HRS.
  apply associativity.
Qed.

Global Instance comm_subrel {A} (R S: relation A) (op: A -> A -> A):
  subrelation R S ->
  Unconvertible _ R S ->
  Commutative R op ->
  Commutative S op.
Proof.
  intros HRS _ Hcomm x y.
  apply HRS.
  apply commutativity.
Qed.

Global Instance id_left_subrel {A} (R S: relation A) (op: A -> A -> A) (u: A):
  subrelation R S ->
  Unconvertible _ R S ->
  LeftIdentity R op u ->
  LeftIdentity S op u.
Proof.
  intros HRS _ Hid x.
  apply HRS.
  apply id_left.
Qed.

Global Instance id_right_subrel {A} (R S: relation A) (op: A -> A -> A) (u: A):
  subrelation R S ->
  Unconvertible _ R S ->
  RightIdentity R op u ->
  RightIdentity S op u.
Proof.
  intros HRS _ Hid x.
  apply HRS.
  apply id_right.
Qed.

Global Instance id_left_id_right {A} (R: relation A) op u:
  LeftIdentity R op u ->
  Commutative R op ->
  Transitive R ->
  RightIdentity R op u.
Proof.
  intros Hleft Hcomm Htrans.
  intros x.
  transitivity (op u x).
  * apply commutativity.
  * apply id_left.
Qed.

Global Instance left_upper_bound_right_upper_bound {A} (R: relation A) op:
  LeftUpperBound R op ->
  Commutative R op ->
  Transitive R ->
  RightUpperBound R op.
Proof.
  intros Hleft Hcomm Htrans.
  intros x y.
  rewrite <- (commutativity y x).
  apply left_upper_bound.
Qed.
  
Instance refl_subrel_eq {A} (R: relation A):
  Reflexive R -> subrelation eq R.
Proof.
  intros Hrefl x y Hxy.
  subst.
  reflexivity.
Qed.


(** * Logical relationish kind of things *)

Ltac rel_auto :=
  unfold flip, impl in *;
  unfold arrow_rel, forall_rel, arrow_pointwise_rel, forall_pointwise_rel in *;
  eauto with liblayers;
  eassumption || congruence.

Ltac solve_monotonicity :=
  solve_monotonic; try rel_auto.

(** ** Generic instances for relation properties *)

Global Instance respectful_eq_transitive {A B} (R: relation B):
  Transitive R ->
  Transitive (@eq A ==> R)%signature.
Proof.
  firstorder.
Qed.

Instance pointwise_preorder A {B} `(PreOrder B):
  @PreOrder (A -> B) (- ==> R).
Proof.
  split.
  * intros f i.
    reflexivity.
  * intros f g h Hfg Hgh i.
    transitivity (g i); eauto.
Qed.


(** * Basic instances *)

(** ** [Prop] *)

Instance impl_preorder:
  PreOrder impl.
Proof.
  firstorder.
Qed.

(** ** Booleans *)

(** Boolean are sufficiently simple that we can prove pretty much
  anything by just enumerating all possibilities. *)
Ltac booltac :=
  repeat (intros [|] || intro; simpl);
  try match goal with
    | H: true = false |- _ => inversion H
    | H: false = true |- _ => inversion H
  end;
  tauto.

Global Instance leb_op: Le bool := { le := leb }.

Global Instance leb_preorder:
  PreOrder leb.
Proof.
  split; booltac.
Qed.

Section BOOL.
  Local Hint Extern 10 => booltac : typeclass_instances.
  Global Instance leb_antisym: Antisymmetric bool eq leb := _.
  Global Instance leb_lower_bound: LowerBound leb false := _.
  Global Instance leb_upper_bound: UpperBound leb true := _.
  Global Instance orb_monotonic: Proper (leb ++> leb ++> leb) orb := _.
  Global Instance orb_id_left: LeftIdentity eq orb false := _.
  Global Instance orb_assoc: Associative eq orb := _.
  Global Instance orb_comm: Commutative eq orb := _.
  Global Instance orb_le_left: LeftUpperBound leb orb := _.
  Global Instance andb_monotonic: Proper (leb ++> leb ++> leb) andb := _.
  Global Instance andb_id_left: LeftIdentity eq andb true := _.
  Global Instance andb_assoc: Associative eq andb := _.
  Global Instance andb_comm: Commutative eq andb := _.
End BOOL.

Lemma bool_le_true b1 b2:
  leb b1 b2 ->
  b1 = true ->
  b2 = true.
Proof.
  revert b1 b2; booltac.
Qed.

Hint Resolve bool_le_true : liblayers.


(** ** The [Equivalence] derived from a [PreOrder] *)

(** XXX: those should be generic properties of [R ∩ flip R], since
  they also apply to say, [eqrel] = [subrel ∩ flip subrel]. *)

Global Instance le_equiv `(Le): Equiv A | 10 :=
  { equiv x y := x ≤ y /\ y ≤ x }.

Global Instance le_equiv_equivalence `{Ale: Le}:
  PreOrder (≤) -> Equivalence (≡).
Proof.
  split.
  - intros x.
    split; reflexivity.
  - intros x y [Hxy Hyx].
    split; assumption.
  - intros x y z [Hxy Hyx] [Hyz Hzy].
    split; etransitivity; eassumption.
Qed.

Global Instance le_equiv_antisymmetric `{Ale: Le}:
  forall (H: Equivalence (≡)), Antisymmetric A (≡) (≤).
Proof.
  intros x y Hxy Hyx.
  split; assumption.
Qed.

Global Instance le_equiv_subrel `{Ale: Le}:
  subrelation (≡) (≤).
Proof.
  intros x y Hxy.
  apply Hxy.
Qed.

Global Instance le_equiv_subrel_flip `{Ale: Le}:
  subrelation (≡) (flip (≤)).
Proof.
  intros x y Hxy.
  apply Hxy.
Qed.

Global Instance le_equiv_op_mor {A B C} `{Le A} `{Le B} `{Le C} (op: A->B->C):
  Proper ((≤) ++> (≤) ++> (≤)) op ->
  Proper ((≡) ==> (≡) ==> (≡)) op | 100.
Proof.
  intros Hop x1 x2 [Hx12 Hx21] y1 y2 [Hy12 Hy21].
  split; apply Hop; assumption.
Qed.

Local Instance le_antisym_equiv_eq `{Ale: Le}:
  Antisymmetric A eq (≤) ->
  subrelation (≡) eq.
Proof.
  intros Hantisym.
  intros x y [Hxy Hyx].
  apply antisymmetry; assumption.
Qed.

Local Instance le_equiv_assoc `{Le} op:
  PreOrder (≤) ->
  Proper ((≤) ++> (≤) ++> (≤)) op ->
  Commutative (≤) op ->
  Associative (≤) op ->
  Associative (≡) op.
Proof.
  split.
  * apply associativity.
  * rewrite (commutativity x (op y z)).
    rewrite (commutativity y z).
    rewrite <- (commutativity z (op x y)).
    rewrite <- (commutativity y x).
    apply associativity.
Qed.

Local Instance le_equiv_comm `{Le} op:
  Commutative (≤) op ->
  Commutative (≡) op.
Proof.
  intros Hcomm.
  split; apply commutativity.
Qed.


(** ** Trivial order *)

Local Instance trivial_le A: Le A | 100 := { le := eq }.

Global Instance trivial_le_preorder {A}:
  @PreOrder A (≤).
Proof.
  split; typeclasses eauto.
Qed.

Global Instance trivial_le_antisym {A}:
  Antisymmetric A eq (≤).
Proof.
  firstorder.
Qed.
