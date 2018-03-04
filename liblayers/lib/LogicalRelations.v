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
Require Import Coq.Program.Basics.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Local Open Scope type.
Global Open Scope signature.


(** * Prerequisites *)

(** Some instances that would normally cause loops can be used
  nontheless if we insist that some parameters cannot be existential
  variables. One way to do this is to use this guard class, similar in
  spirit to [Unconvertible]. *)

Class NotEvar {A} (x: A).

Hint Extern 1 (NotEvar ?x) =>
  not_evar x; constructor : typeclass_instances.

(** Sometimes we may want to introduce an auxiliary variable to help
  with unification. *)

Class Convertible {A} (x y: A) :=
  convertible: x = y.

Hint Extern 1 (Convertible ?x ?y) =>
  eapply eq_refl : typeclass_instances.


(** * Relations *)

(** The constructions in [Coq.Relations.Relation_Definitions] are only
  concerned with relations within a single type, so that [relation A]
  is defined as [A -> A -> Prop]. We will need more general
  relations, and so I define [rel A B] as [A -> B -> Prop]. *)

(** When we move to a version of Coq with universe polymorphism, we
  can make this a [Polymorphic Definition]. In the meantime, we need
  to use a notation so that universes levels are instantiated at every
  use site. *)

Notation rel := (fun A1 A2 => A1 -> A2 -> Prop).

(** ** Proper elements *)

(** I follow [Coq.Classes.Morphisms] and define morphisms as proper
  elements of a corresponding logical relation. They can be registered
  by declaring instances of the [Proper] typeclass.
  However, we will build up logical relations from our own set of
  relators, and use our own tactics to deduce new instances of
  [Proper] from the existing ones. To prevent the two systems from
  interfering with one another, I will use the following nearly
  identical, but distinct definition of [Proper]. *)

(** There is one ugly tweak that we need, compared with the original.
  Namely, we want the type parameter [A] to be unified in priority
  with the type of element [m], rather than that of the relation [R].
  That is because by necessity, the relator [forall_rel] defined below
  yields an eta-expanded type of the form [(fun x => T x) x].
  As a consequence, some instances declared using [forall_rel] become
  unusable because [A] takes this peculiar form. To work around this,
  we flip the order of arguments in our version of [Proper], so that
  [A] is unified against the type of [m], then use notations to fake
  the original order. *)

Class ProperDef {A} (m: A) (R: rel A A) := proper_prf : R m m.

Notation "'@' 'Proper' T R m" := (@ProperDef T m R)
  (at level 10, T at next level, R at next level, m at next level).

Notation Proper R m := (ProperDef m R).

(** ** Order on relations *)

(** This is our generalization of [subrelation]. Like the original it
  constitutes a preorder, and the union and intersection of relations
  are the corresponding join and meet. *)

Class subrel {A B} (R1 R2: rel A B) :=
  subrel_at x y: R1 x y -> R2 x y.

Global Instance subrel_preorder A B:
  @PreOrder (rel A B) subrel.
Proof.
  split; firstorder.
Qed.

Instance subrel_refl {A B} (R: rel A B):
  subrel R R.
Proof.
  firstorder.
Qed.

(** ** Union of relations *)

Definition rel_union {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y \/ R2 x y.

Infix "∪" := rel_union (at level 50) : signature_scope.

Lemma rel_union_introl {A B} (R1 R2: rel A B):
  subrel R1 (R1 ∪ R2).
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel _ (_ ∪ _)) =>
  eapply rel_union_introl : typeclass_instances.

Lemma rel_union_intror {A B} (R1 R2: rel A B):
  subrel R2 (R1 ∪ R2).
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel _ (_ ∪ _)) =>
  eapply rel_union_introl : typeclass_instances.

Lemma rel_union_lub {A B} (R1 R2 R: rel A B):
  subrel R1 R ->
  subrel R2 R ->
  subrel (R1 ∪ R2)%signature R.
Proof.
  firstorder.
Qed.

Hint Extern 2 (subrel (_ ∪ _) _) =>
  eapply rel_union_lub : typeclass_instances.


(** ** Intersection of relations *)

Definition rel_inter {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y /\ R2 x y.

Infix "∩" := rel_inter (at level 40) : signature_scope.

Lemma rel_inter_eliml {A B} (R1 R2: rel A B):
  subrel (R1 ∩ R2) R1.
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel (_ ∩ _) _) =>
  eapply rel_inter_eliml : typeclass_instances.

Lemma rel_inter_elimr {A B} (R1 R2: rel A B):
  subrel (R1 ∩ R2) R2.
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel (_ ∩ _) _) =>
  eapply rel_inter_elimr : typeclass_instances.

Lemma rel_inter_glb {A B} (R R1 R2: rel A B):
  subrel R R1 ->
  subrel R R2 ->
  subrel R (R1 ∩ R2).
Proof.
  firstorder.
Qed.

Hint Extern 2 (subrel _ (_ ∩ _)) =>
  eapply rel_inter_glb : typeclass_instances.

Lemma rel_inter_refl {A} (R1 R2: rel A A):
  Reflexive R1 ->
  Reflexive R2 ->
  Reflexive (R1 ∩ R2).
Proof.
  intros H1 H2.
  split; reflexivity.
Qed.

Hint Extern 2 (Reflexive (_ ∩ _)) =>
  eapply rel_inter_refl : typeclass_instances.

Lemma rel_inter_trans {A} (R1 R2: rel A A):
  Transitive R1 ->
  Transitive R2 ->
  Transitive (R1 ∩ R2).
Proof.
  intros H1 H2 x y z [Hxy1 Hxy2] [Hyz1 Hyz2].
  split; etransitivity; eassumption.
Qed.

Hint Extern 2 (Transitive (_ ∩ _)) =>
  eapply rel_inter_trans : typeclass_instances.

Lemma rel_inter_sym {A} (R1 R2: rel A A):
  Symmetric R1 ->
  Symmetric R2 ->
  Symmetric (R1 ∩ R2).
Proof.
  intros H1 H2 x y [Hxy1 Hxy2].
  split; symmetry; assumption.
Qed.

Hint Extern 2 (Symmetric (_ ∩ _)) =>
  eapply rel_inter_sym : typeclass_instances.

Global Instance rel_inter_flip_sym {A} (R: rel A A):
  Symmetric (R ∩ flip R).
Proof.
  intros x y [Hxy Hyx].
  split; assumption.
Qed.

(** ** The bottom and top relations *)

Definition rel_bot {A B}: rel A B :=
  fun x y => False.

Notation "⊥" := rel_bot : signature_scope.

Definition rel_top {A B}: rel A B :=
  fun x y => True.

Notation "⊤" := rel_top : signature_scope.

Hint Resolve (fun A B (x:A) (y:B) => I : rel_top x y).

(** ** Relation equivalence *)

Definition eqrel {A B}: rel (rel A B) (rel A B) :=
  (subrel ∩ flip subrel).

Global Instance eqrel_equivalence A B:
  Equivalence (@eqrel A B).
Proof.
  unfold eqrel.
  split; typeclasses eauto.
Qed.


(** * Relators for function types *)

(** With this infrastructure in place, we can define actual relators
  that cover the commonly used type constructors. There are two broad
  categories: those related to function types, and those derived from
  inductive types. First, we introduce the core relators necessary to
  develop the tactics that follow, namely those for function types.
  In a later section of this file, I provide a more comprehensive
  library which covers many of the basic inductive type constructors
  as well. *)

(** As a convention, we name relators and the associated monotonicity
  theorems by appending the suffix [_rel] to the name of original type
  and those of its constructors. Likewise, we use the suffix [_subrel]
  for monotonicity theorems that characterize the variance of
  corresponding relators with respect to [subrel]. *)

(** ** Non-dependent function types *)

(** First, I define relators for non-dependent functions. This
  generalizes [respectful]. *)

Definition arrow_rel {A1 A2 B1 B2}:
  rel A1 A2 -> rel B1 B2 -> rel (A1 -> B1) (A2 -> B2) :=
    fun RA RB f g => forall x y, RA x y -> RB (f x) (g y).

Notation "RA ==> RB" := (arrow_rel RA RB)
  (at level 55, right associativity) : signature_scope.

Notation "RA ++> RB" := (arrow_rel RA RB)
  (at level 55, right associativity) : signature_scope.

Notation "RA --> RB" := (arrow_rel (flip RA) RB)
  (at level 55, right associativity) : signature_scope.

Global Instance arrow_subrel {A1 A2 B1 B2}:
  Proper (subrel --> subrel ++> subrel) (@arrow_rel A1 A2 B1 B2).
Proof.
  firstorder.
Qed.

(** ** Pointwise extension of a relation *)

(** One useful special case is the pointwise extension of a relation
  on the domain to the function type. This is equivalent to [eq ==> R],
  however with the formulation below we don't have consider two equal
  elements of the domain. *)

Definition arrow_pointwise_rel A {B1 B2}:
  rel B1 B2 -> rel (A -> B1) (A -> B2) :=
    fun RB f g => forall a, RB (f a) (g a).

Notation "- ==> R" := (arrow_pointwise_rel _ R)
  (at level 55, right associativity) : signature_scope.

Global Instance arrow_pointwise_subrel {A B1 B2}:
  Proper (subrel ++> subrel) (@arrow_pointwise_rel A B1 B2).
Proof.
  firstorder.
Qed.

Global Instance arrow_pointwise_eq_subrel {A B1 B2} (RB1 RB2: rel B1 B2):
  subrel RB1 RB2 ->
  subrel (- ==> RB1) (@eq A ==> RB2).
Proof.
  intros HRB f g Hfg x y Hxy.
  subst.
  apply HRB.
  apply Hfg.
Qed.

(** ** Dependent products *)

(** Now we consider the dependent case. The definition of [forall_rel]
  is somewhat involved, but you can think of relating [f] and [g] in
  the context of a structure-preserving transformation from a quiver
  ([V], [E]) to the quiver ([Type], [rel]). Like a functor, it has two
  components: [FV] maps nodes to types, and [FE] maps edges to
  relations. Then, [forall_rel FE f g] states that given an edge
  [(e : E v1 v2)], the images [f v1] and [g v2] are related by the
  corresponding relation [FE v1 v2 e]. We will write [forall_rel FE f g]
  as [(∀ e : E v1 v2, FE[v1,v2,e]) f g]. Notice that this notation
  binds [v1] and [v2] as well as [e].

  If that makes no sense, you can think of specific source quivers. So
  for instance, oftentimes we will want to use ([Type], [rel]) as the
  source quiver too. This corresponds to parametric polymorphism. The
  type of [Some] is [∀ A : Type, A -> option A]; the corresponding
  logical relation is [∀ R : rel A1 A2, R ++> option_rel R]. Stating
  that [Proper (∀ R : rel A1 A2, R ++> option_rel R) Some] means that,
  given any relation [R] and elements [x1] and [x2], if [R] relates
  [x1] and [x2], then [option_rel R] will relate [Some x1] and [Some x2].

  Another example from [liblayers] is the quiver of our data-indexed
  simulation relations [simrel : layerdata -> layerdata -> Type].
  Here the structure-preserving transformations are our simulation
  relation diagrams, which have types such as
  [lsim : forall D1 D2, simrel D1 D2 -> rel (layer D1) (layer D2)] or
  [psim : forall {D1 D2}, simrel D1 D2 -> rel (primsem D1) (primsem D2)].
  Then, the monotonicity of a data-indexed function —
  say, [foo: forall D : layerdata, layer D -> primsem D] —
  can be expressed as
  [Proper (∀ R : simrel D1 D2, siml D1 D2 R ++> simp D1 D2 R) foo].

  This definition is the same as [respectful_hetero]. *)

Definition forall_rel {V1 V2} {E: V1->V2->Type} {FV1: V1->Type} {FV2: V2->Type}:
    (forall v1 v2, E v1 v2 -> rel (FV1 v1) (FV2 v2)) ->
    rel (forall v1, FV1 v1) (forall v2, FV2 v2) :=
  fun FE f g =>
    forall v1 v2 (e: E v1 v2), FE v1 v2 e (f v1) (g v2).

Notation "∀  α : E v1 v2 , R" := (forall_rel (E := E) (fun v1 v2 α => R))
  (at level 200, α ident, E at level 7, v1 ident, v2 ident, right associativity)
  : signature_scope.

Notation "∀  α : E , R" := (forall_rel (E := E) (fun _ _ α => R))
  (at level 200, α ident, E at level 7, right associativity)
  : signature_scope.

Notation "∀  α , R" := (forall_rel (fun _ _ α => R))
  (at level 200, α ident, right associativity)
  : signature_scope.

(** ** Dependent pointwise extension *)

(** Like we did for non-dependent functions, we can provide a simpler
  definition for the special case where [E] is [eq]. *)

Definition forall_pointwise_rel {V: Type} {FV1 FV2: V -> Type}:
    (forall v, rel (FV1 v) (FV2 v)) ->
    rel (forall v, FV1 v) (forall v, FV2 v) :=
  fun FE f g =>
    forall v, FE v (f v) (g v).

Notation "∀ - , FE" := (forall_pointwise_rel (fun _ => FE))
  (at level 200).

Notation "∀ - : 'rel' , FE" := (forall_pointwise_rel (fun _ => FE))
  (at level 200).

Notation "∀ - : 'rel' v , FE" := (forall_pointwise_rel (fun v => FE))
  (at level 200, a at level 0).


(** * Tactics *)

(** ** Resolution process *)

(** Now that we have a way to express and register the monotonicity
  properties of various operators, we want to use them to answer the
  queries generated by setoid rewriting and the [monotonicity] tactic.
  That is, given a relation [R] with existential holes and a term [m],
  use the registered theorems to prove [R m m], instantiating some of
  the existential holes in [R]. All things being equal, we will want
  those instantiations to yield the strongest theorem possible.

  I use the following procedure, implemented below.
    - First, choose an orientation. Since [R m m <-> (flip R) m m],
      we need to consider both of those goals. Furthermore, we need to
      normalize [flip R] so that [flip] is pushed inward and any
      occurence of [flip (flip Q)] is reduced to [Q].
    - Then, if [m] is an applied function, we may want to look for a
      more general [Proper] theorem. So for instance, assuming that
      [Q x x], we can use a theorem of the form [Proper (Q ++> R) f]
      to solve a goal of the form [R (f x) (f x)].
    - Once we've chosen an orientation and a degree of partial
      application, we can finally look for a corresponding [Proper]
      instance.

  We may want to add more phases in the future, for instance to
  generalize the goal using [subrel] instances.

  It is most convenient to embed this process into the typeclass
  resolution mechanism. In particular, nondeterministic choices come
  in handy. But we don't want these resolution steps to be applied
  arbitrarily. In order to enforce the sequential aspect, we use the
  proxy class [ProperQuery], which is parametrized by a list of
  processing phases remaining. *)

Inductive processing_phase :=
  | proper_orientation
  | proper_partial_app
  | proper_partial_arg
  | proper_subrel.

Class ProperQuery (φs: list processing_phase) {A} (R: rel A A) (m: A) :=
  proper_query_outcome: Proper R m.

(** The different [processing_phase]s will peel themselves off the
  list and generate subgoals to be handled by the next phase.
  Ultimately the list becomes empty, and we look for a regular
  instance of [Proper]. *)

Global Instance proper_query_finalize {A} (R: rel A A) (m: A):
  Proper R m ->
  ProperQuery nil R m.
Proof.
  tauto.
Qed.

(** ** Flipping [Proper] goals *)

(** Instances of this class can be used to indicate how [flip] is to
  be pushed to the inside of given relation operators. *)

Class FlipsTo {A B} (R: rel A B) (R': rel B A) :=
  flips_to: eqrel (flip R) R'.

(** Catch-all, default instance. *)

Instance atom_flipsto {A B} (R: rel A B):
  FlipsTo R (flip R) | 10.
Proof.
  firstorder.
Qed.

(** Flipping twice. This instance is also used when the first argument
  is an existential variable, so that the resulting relation is itself
  as general as possible. *)

Instance flip_flipsto {A B} (R: rel A B):
  FlipsTo (flip R) R.
Proof.
  firstorder.
Qed.

(** Symmetric relations flip to themselves. *)

Instance:
  forall {A} (R: rel A A) (HR: Symmetric R),
    FlipsTo R R.
Proof.
  firstorder.
Qed.

(** Instances for basic relators. *)

Instance arrow_flipsto {A1 A2 B1 B2} (RA: rel A1 A2) (RB: rel B1 B2) RA' RB':
  FlipsTo RA RA' ->
  FlipsTo RB RB' ->
  FlipsTo (RA ++> RB) (RA' ++> RB').
Proof.
  unfold FlipsTo, flip.
  firstorder.
Qed.

(** The [proper_orientation] phase causes both orientations to be tried. *)

Global Instance proper_orientation_direct φs {A} (R: rel A A) (m: A):
  ProperQuery φs R m ->
  ProperQuery (proper_orientation::φs) R m.
Proof.
  tauto.
Qed.

Lemma proper_orientation_flip φs {A} (R R': rel A A) (m: A):
  FlipsTo R R' ->
  ProperQuery φs R' m ->
  ProperQuery (proper_orientation::φs) R m.
Proof.
  firstorder.
Qed.

(** For [proper_orientation_flip] above, we only want to use the
  first instance of [FlipsTo] found. *)

Ltac proper_orientation_flip :=
  lazymatch goal with
    | |- @ProperQuery _ ?A ?R ?m =>
      let Rv := fresh in evar (Rv: rel A A);
      let R' := eval red in Rv in clear Rv;
      let H := fresh in
      assert (H: FlipsTo R R') by typeclasses eauto;
      eapply (@proper_orientation_flip _ A R R' m H);
      clear H
  end.

Hint Extern 2 (ProperQuery (proper_orientation::_) _ _) =>
  proper_orientation_flip : typeclass_instances.

(** ** Partial applications *)

(** In many contexts, we need to show [Proper Rg (op a₁ … aₖ … aₙ)],
  but what we acually have is a more general instance of
  [Proper R (op a₁ … aₖ)]. If [R] is built up from reflexive relations
  (or at least, relations for which the corresponding [aᵢ] is a proper
  element), then the former can be obtained from the latter.

  In [Coq.Classes.Morphisms], this is handled by [partial_application_tactic],
  which applies [Reflexive_partial_app_morphism] on a goal of the form
  [Proper R' (op x)] to obtain the new goal [Proper (R ==> R') op],
  with [R] an existential variable to be unified against the [Proper]
  instances of this form that are eventually found. However, we cannot
  naively extend this strategy to obtain goals of the form
  [Proper (forall_rel R) op]. We would need the many more existential
  variables [V : Type], [E : V -> V -> Type], [e : E x x],
  [FV : V -> Type], [R : forall v1 v2, E v1 v2 -> rel (FV v1) (FV v2)],
  and what's more we would have to perform the higher-order
  unification of [R'] — likely just some existential variable at this
  point — against [?R ?v ?v ?e]. #<em>#Maybe#</em># this could be achieved
  by going through another existential variable within the context of
  a lambda abstraction such that [R] ≐ [(fun v1 v2 e => ?)] (if that
  is even possible). However the resulting unification process would
  be rather messy and undebuggable.

  Instead, we start with whatever instances of [Proper (forall_rel R) op]
  we can find, then try to unify [R'] against the corresponding
  mostly-concrete [R x x ?e]. To this end, we use the following
  intermediate class. *)

Class ProperApplies A (B: A -> Type) R (a: A) R' (m: forall a, B a) :=
  proper_applies : Proper R m -> Proper R' (m a).

Ltac proper_applies :=
  let H := fresh in
  unfold ProperApplies, ProperDef;
  intro H;
  eapply H;
  eapply (@proper_query_outcome (proper_partial_arg::nil)).

Hint Extern 1 (ProperApplies _ _ _ _ _ _) =>
  proper_applies : typeclass_instances.

(** The processing phase [proper_partial_arg] is used for proving that
  a given argument can be applied. It is our version of
  [Morphisms.ProperProxy]. *)

Instance proper_partial_arg_eq φs {A} (m: A):
  ProperQuery (proper_partial_arg::φs) eq m.
Proof.
  firstorder.
Qed.

Instance proper_partial_arg_reflexive φs {A} (R: rel A A) (m: A):
  Reflexive R ->
  ProperQuery (proper_partial_arg::φs) R m.
Proof.
  firstorder.
Qed.

Instance proper_partial_arg_default φs {A} (R: rel A A) (m: A):
  NotEvar R ->
  ProperQuery φs R m ->
  ProperQuery (proper_partial_arg::φs) R m.
Proof.
  firstorder.
Qed.

(** The [proper_partial_app] processing phase consists in using
  [proper_applies] an arbitrary number of times. TODO: we may want to
  use the [Params] class to limit the resulting search space to only
  one possibility instead. *)

Global Instance proper_partial_app_bail φs {A} (R: rel A A) (m: A):
  ProperQuery φs R m ->
  ProperQuery (proper_partial_app::φs) R m.
Proof.
  tauto.
Qed.

Lemma proper_partial_app_arg φs {A} (B: A -> Type) R a R' m:
  @ProperQuery (proper_partial_app::φs) (forall a, B a) R m ->
  ProperApplies A B R a R' m ->
  @ProperQuery (proper_partial_app::φs) (B a) R' (m a).
Proof.
  firstorder.
Qed.

(** When using [proper_partial_app_arg], the unification of the goal
  against the subterm [(B a)] is problematic, because usually the type
  will be an arbitrary expression where [a] appears freely. Therefore,
  we first need to put the goal in the right form. The tactic
  [dependent_type_of] recovers the type of a term that can be applied,
  as a function of its first argument. *)

Ltac dependent_type_of f arg T :=
  let A := type of arg in
  let x := fresh "x" in evar (x : A);
  let fx := fresh "fx" in set (fx := f x);
  pattern x in fx;
  lazymatch type of fx with ?TT _ => set (T := TT) end;
  let y := eval red in x in unify y arg;
  subst x fx.

Ltac proper_partial_app_arg :=
  lazymatch goal with
    | |- ProperQuery (proper_partial_app::?φs) ?R (?op ?arg) =>
      let T := fresh "T" in dependent_type_of op arg T;
      eapply (proper_partial_app_arg φs T _ arg R op);
      subst T
  end.

Hint Extern 2 (ProperQuery (proper_partial_app::_) _ _) =>
  proper_partial_app_arg : typeclass_instances.

(** ** Using [subrel] *)

(** The processing step [proper_subrel] causes the search to be
  extended to subrelations. The order of the [ProperQuery] and
  [subrel] arguments is pretty critical: first, we go on and try to
  find /any/ instance of [Proper] for [m]; then, we check to see if
  the associated relation is a subrelation of the target one. *)

Global Instance do_proper_subrel {A} φs (R1 R2: rel A A) (m: A):
  ProperQuery φs R1 m ->
  subrel R1 R2 ->
  ProperQuery (proper_subrel::φs) R2 m.
Proof.
  firstorder.
Qed.

(** ** Compatibility with setoid rewriting *)

(** So far our system is isolated from the similar constructions in
  [Coq.Classes.Morphisms]. The [convert_proper] tactic permits a
  controlled interaction between them. It converts a [Morphisms.Proper]
  goal into a [Proper] one, replacing legacy relators such as
  [respectful] with their more general counterparts defined here.
  This allows the setoid rewriting mechanism to use the morphisms we
  define. *)

Notation rewrite_proper_query :=
  (proper_orientation :: proper_partial_app :: proper_subrel :: nil)
  (only parsing).

Ltac convert_proper :=
  repeat
    match goal with
      | |- appcontext C[respectful ?R1 ?R2] =>
        let T' := context C[R1 ==> R2] in change T'
      | |- appcontext C[forall_relation ?R] =>
        let T' := context C[∀ -, R] in change T'
      | |- Morphisms.Proper ?R ?m =>
        change (ProperQuery rewrite_proper_query R m)
    end.

(** We want [convert_proper] to be used for the initial [Proper] goal,
  but we're not really interested in having it applied to the subgoals
  generated by the original process in [Coq.Classes.Morphisms], since
  we have our own. The following tactic attempts to detect and reject
  cases where some work has already been done. *)

Ltac use_convert_proper :=
  match goal with
    | _ : normalization_done |- _ =>
      fail 1
    | H : apply_subrelation |- _ =>
      clear H;
      progress convert_proper
  end.

Hint Extern 1 (Morphisms.Proper _ _) =>
  use_convert_proper : typeclass_instances.

(** The monotonicity of transitive relations is sometimes needed to
  solve the goals generated by setoid rewriting. *)

Instance transitive_proper {A} (R: rel A A):
  Transitive R ->
  Proper (R --> R ++> impl) R.
Proof.
  firstorder.
Qed.

(** ** The [monotonicity] tactic *)

(** The purpose of the [monotonicity] tactic is to automatically
  select and apply a theorem of the form [Proper ?R ?m] in order to
  make progress when the goal is an applied relation. Compared with
  setoid rewriting, [monotonicity] is less powerful, but more direct
  and simple. This means it is easier to debug, and it can seamlessly
  handle dependent types and heterogenous relations.

  At the moment, [monotonicity] does not use any of the preprocessing
  phases. *)

Ltac monotonicity :=
  let rec apply_proper_prf m1 m2 :=
    match m1 with
      | m2 =>
        let A := type of m1 in
        let Rv := fresh "R" in evar (Rv: rel A A);
        let Re := eval red in Rv in clear Rv;
        let H := fresh in
        assert (H: ProperQuery nil Re m1) by typeclasses eauto;
        eapply H;
        clear H
      | ?f ?x1 =>
        match m2 with
          | ?g ?x2 => apply_proper_prf f g
        end
    end in
  lazymatch goal with
    | |- ?R ?m1 ?m2 =>
      apply_proper_prf m1 m2
  end.

(** Our version of [Morphisms.f_equiv]. *)

Ltac f_equiv :=
  repeat monotonicity.

(** Our version of [Morphisms.solve_proper]. Note that we are somewhat
  parcimonious with introductions because we don't want to cause undue
  unfoldings. For instance, if we define the relation [R1] from [R2]
  as [R1 x y := forall i, R2 (get i x) (get i y)], we may create a
  situation where applying the monotonicity theorem for [get] on a
  goal of the form [R2 (get i x) (get i y)] produces a subgoal of the
  form [R1 x y], but then an introduction would get us back to where
  we started. So we limit them to well-defined cases. *)

Ltac solve_monotonic_tac t :=
  repeat
    match goal with
      | |- Proper _ _ => red
      | |- flip _ _ _ => red
      | |- _ => progress t
      | |- _ _ _ => monotonicity
      | |- (_ --> _) _ _ => let H := fresh in intros ? ? H; red in H
      | |- (_ ++> _) _ _ => intros ? ? ?
      | |- (- ==> _) _ _ => intro
      | |- (∀ _, _) _ _ => intros ? ? ?
      | |- (∀ -, _) _ _ => intro
      | |- forall _, _ => intro
    end.

Tactic Notation "solve_monotonic" :=
  solve_monotonic_tac ltac:(eassumption || congruence || (now econstructor)).

Tactic Notation "solve_monotonic" tactic(t) :=
  solve_monotonic_tac ltac:(eassumption || congruence || (now econstructor)|| t).

(** ** Exploiting [foo_subrel] instances *)

(** Although we declared [Proper] instances for the relation
  constructors we defined, so far the usefulness of these instances
  has been limited. But now we can use them in conjunction with our
  [monotonicity] tactic to break up [subrel] goals along the structure
  of the relations being considered. *)

Hint Extern 5 (subrel _ _) =>
  monotonicity; unfold flip : typeclass_instances.

(** Furthermore, the following instance of [subrel] enables the use of
  [foo_subrel] instances for rewriting along within applied relations.
  So that for instance, a hypothesis [H: subrel R1 R2] can be used for
  rewriting in a goal of the form [(R1 * R1' ++> R) x y]. *)

Instance subrel_pointwise_subrel {A B}:
  subrel (@subrel A B) (eq ==> eq ==> impl).
Proof.
  intros R1 R2 HR x1 x2 Hx y1 y2 Hy H; subst.
  eauto.
Qed.


(** * More relators for basic types *)

(** ** Inductive types *)

(** For inductive types, there is a systematic way of converting their
  definition into that of the corresponding relator. Where the
  original inductive definition quantifies over types, the
  corresponding relator will quantify over pairs of types and
  relations between them. Then, the constructors of the relator will
  essentially be [Proper] instances for the original constructors.
  In other words, the resulting relation will be the smallest one such
  that the constructors are order-preserving. *)

(** *** Nullary type constructors *)

(** As a proof-of-concept, we start with the most elementary types
  [Empty_set] and [unit], which can be considered as nullary type
  constructors related to [sum] and [prod] below. *)

Inductive Empty_set_rel: rel Empty_set Empty_set := .

Inductive unit_rel: rel unit unit :=
  tt_rel: Proper unit_rel tt.

Global Existing Instance tt_rel.

(** *** Sum types *)

(** The definition of [sum_rel] could look something like this:
<<
  Inductive sum_rel:
    forall {A1 A2 B1 B2}, rel A1 A2 -> rel B1 B2 -> rel (A1+B1) (A2+B2):=
    | inl_rel: Proper (∀ RA : rel, ∀ RB : rel, RA ++> sum_rel RA RB) (@inl)
    | inr_rel: Proper (∀ RA : rel, ∀ RB : rel, RB ++> sum_rel RA RB) (@inr).
>>
  However, to minimize the need for [inversion]s we want to keep as
  many arguments as possible as parameters of the inductive type. *)

Inductive sum_rel {A1 A2} RA {B1 B2} RB: rel (A1 + B1) (A2 + B2) :=
  | inl_rel_def: (RA ++> sum_rel RA RB) (@inl A1 B1) (@inl A2 B2)
  | inr_rel_def: (RB ++> sum_rel RA RB) (@inr A1 B1) (@inr A2 B2).

Infix "+" := sum_rel : signature_scope.

(** Since it is not possible to retype the constructors after the
  fact, we use the [_def] suffix when defining them, then redeclare
  a corresponding, full-blown [Proper] instance. *)

Local Instance inl_rel:
  Proper (∀ RA, ∀ RB, RA ++> RA + RB) (@inl).
Proof.
  exact @inl_rel_def.
Qed.

Local Instance inr_rel:
  Proper (∀ RA, ∀ RB, RB ++> RA + RB) (@inr).
Proof.
  exact @inr_rel_def.
Qed.

Global Instance sum_subrel:
  Proper (∀ -, ∀ -, subrel ++> ∀ -, ∀ -, subrel ++> subrel) (@sum_rel).
Proof.
  intros A1 A2 RA1 RA2 HRA B1 B2 RB1 RB2 HRB.
  intros x1 x2 Hx.
  destruct Hx; constructor; eauto.
Qed.

Global Instance sum_rel_refl {A B} (R1: rel A A) (R2: rel B B):
  Reflexive R1 -> Reflexive R2 -> Reflexive (R1 + R2).
Proof.
  intros H1 H2 x.
  destruct x; constructor; reflexivity.
Qed.

Global Instance sum_rel_trans {A B} (R1: rel A A) (R2: rel B B):
  Transitive R1 -> Transitive R2 -> Transitive (R1 + R2).
Proof.
  intros H1 H2 x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; constructor; etransitivity; eassumption.
Qed.

Global Instance sum_rel_sym {A B} (R1: rel A A) (R2: rel B B):
  Symmetric R1 -> Symmetric R2 -> Symmetric (R1 + R2).
Proof.
  intros H1 H2 x y Hxy.
  destruct Hxy; constructor; symmetry; eassumption.
Qed.

Global Instance sum_rel_preorder {A B} (R1: rel A A) (R2: rel B B):
  PreOrder R1 -> PreOrder R2 -> PreOrder (R1 + R2).
Proof.
  split; typeclasses eauto.
Qed.

Hint Extern 0 (Proper _ (@inl)) => exact inl_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@inr)) => exact inr_rel : typeclass_instances.

(** *** Pairs *)

Inductive prod_rel {A1 A2} RA {B1 B2} RB: rel (A1 * B1) (A2 * B2):=
  | pair_rel_def: (RA ++> RB ++> prod_rel RA RB) (@pair A1 B1) (@pair A2 B2).

Infix "*" := prod_rel : signature_scope.

Local Instance pair_rel:
  Proper (∀ RA, ∀ RB, RA ++> RB ++> RA * RB) (@pair).
Proof.
  exact @pair_rel_def.
Qed.

Local Instance fst_rel:
  Proper (∀ RA, ∀ RB, RA * RB ==> RA) (@fst).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros _ _ [a1 a2 Ha b1 b2 Hb].
  assumption.
Qed.

Local Instance snd_rel:
  Proper (∀ RA, ∀ RB, RA * RB ==> RB) (@snd).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros _ _ [a1 a2 Ha b1 b2 Hb].
  assumption.
Qed.

Global Instance prod_rel_refl {A B} (R1: rel A A) (R2: rel B B):
  Reflexive R1 -> Reflexive R2 -> Reflexive (R1 * R2).
Proof.
  intros H1 H2 x.
  destruct x; constructor; reflexivity.
Qed.

Global Instance prod_rel_trans {A B} (R1: rel A A) (R2: rel B B):
  Transitive R1 -> Transitive R2 -> Transitive (R1 * R2).
Proof.
  intros H1 H2 x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; constructor; etransitivity; eassumption.
Qed.

Global Instance prod_rel_sym {A B} (R1: rel A A) (R2: rel B B):
  Symmetric R1 -> Symmetric R2 -> Symmetric (R1 * R2).
Proof.
  intros H1 H2 x y Hxy.
  destruct Hxy; constructor; symmetry; eassumption.
Qed.

Global Instance prod_rel_preorder {A B} (R1: rel A A) (R2: rel B B):
  PreOrder R1 -> PreOrder R2 -> PreOrder (R1 * R2).
Proof.
  split; typeclasses eauto.
Qed.

Hint Extern 0 (Proper _ (@pair)) => exact pair_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@fst)) => exact fst_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@snd)) => exact snd_rel : typeclass_instances.

(** *** Option types *)

Inductive option_rel {A1 A2} (RA: rel A1 A2): rel (option A1) (option A2) :=
  | Some_rel_def: (RA ++> option_rel RA) (@Some A1) (@Some A2)
  | None_rel_def: option_rel RA (@None A1) (@None A2).

Local Instance Some_rel:
  Proper (∀ R : rel A1 A2, R ++> option_rel R) (@Some).
Proof.
  exact @Some_rel_def.
Qed.

Local Instance None_rel:
  Proper (∀ R, option_rel R) (@None).
Proof.
  exact @None_rel_def.
Qed.

Global Instance option_subrel:
  Proper (∀ -, ∀ -, subrel ++> subrel) (@option_rel).
Proof.
  intros A1 A2 RA1 RA2 HRA.
  intros x1 x2 Hx.
  destruct Hx; constructor; eauto.
Qed.

Hint Extern 0 (Proper _ (@Some)) => exact Some_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@None)) => exact None_rel : typeclass_instances.

(** *** Lists *)

Inductive list_rel {A1 A2} (R: rel A1 A2): rel (list A1) (list A2) :=
  | nil_rel_def: (list_rel R) (@nil A1) (@nil A2)
  | cons_rel_def: (R ++> list_rel R ++> list_rel R) (@cons A1) (@cons A2).

Local Instance nil_rel:
  Proper (∀ R, list_rel R) (@nil).
Proof.
  exact @nil_rel_def.
Qed.

Local Instance cons_rel:
  Proper (∀ R, R ++> list_rel R ++> list_rel R) (@cons).
Proof.
  exact @cons_rel_def.
Qed.

Hint Extern 0 (Proper _ (@nil)) => exact nil_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@cons)) => exact cons_rel : typeclass_instances.

Global Instance app_rel:
  Proper (∀ R : rel, list_rel R ++> list_rel R ++> list_rel R) (@app).
Proof.
  intros A1 A2 R l1 l2 Hl.
  induction Hl as [ | x1 x2 Hx l1 l2 Hl IHl]; simpl.
  * firstorder.
  * solve_monotonic.
    apply IHl.
    assumption.
Qed.


(** * Tests *)

(** ** Partial applications *)

Goal forall A (a1 a2: A) B (b1 b2: B) (RA: rel A A), True.
Proof.
  intros.

  evar (T: Type); evar (R: rel T T); subst T;
  assert (H1: ProperQuery (proper_partial_app::nil) R (@pair A A a1)); subst R.
  typeclasses eauto.
  instantiate (1 := RA) in H1.

  evar (T: Type); evar (R: rel T T); subst T;
  assert (H2: ProperQuery (proper_partial_app::nil) R (@pair A)); subst R.
  typeclasses eauto.
  instantiate (1 := RA) in H2.

  evar (T: Type); evar (R: rel T T); subst T;
  assert (H3: ProperQuery (proper_partial_app::nil) R (@inl A B a2)); subst R.
  typeclasses eauto.
  instantiate (1 := eq) in H3.

  exact I.
Qed.

(** ** Setoid rewriting *)

Goal
  forall A (a b: A) `(HR: Equivalence A) (H: R a b),
    sum_rel R R (inl a) (inl b).
Proof.
  intros.
  rewrite H.
  rewrite <- H.
  reflexivity.
Qed.

(** This test checks that [transitive_proper] is used as expected. *)

Goal
  forall A (op: A -> A -> A) (R: rel A A) (x y z: A),
    Proper (R ++> R ++> R) op ->
    PreOrder R ->
    R (op y x) (op x y) ->
    R (op (op z y) x) (op z (op x y)).
Proof.
  intros A op R x y z Hop HR H.
  rewrite <- H.

  (** For your debugging convenience, here are the goals generated by
    the [rewrite] above. *)
  evar (RE: rel A A);
  assert (Morphisms.Proper (RE ==> flip impl) (R (op (op z y) x))
       /\ Morphisms.Proper (flip R ==> RE) (op z)); subst RE.
  {
    split.
    * convert_proper.
      proper_orientation_flip.
      proper_partial_app_arg.
      eapply proper_partial_app_bail.
      eapply transitive_proper.
      typeclasses eauto.
      proper_applies.
      typeclasses eauto.
    * convert_proper.
      typeclasses eauto.
  }
Abort.

(** ** Monotonicity tactics *)

Goal
  forall A (a b: A) (R: rel A A) (H: R a b),
    let f (x y: A * A) := (@pair (A+A) (A+A) (inr (fst x)) (inl (snd y))) in
    Proper (R * ⊤ ++> ⊤ * R ++> (⊥ + R) * (R + ⊥)) f.
Proof.
  intros; unfold f.
  solve_monotonic.
Qed.

Goal
  forall {A1 A2 B1 B2} (R1 R1': rel A1 A2) (R2 R2': rel B1 B2),
    subrel R1' R1 ->
    subrel R2 R2' ->
    subrel (R1 ++> R2) (R1' ++> R2').
Proof.
  solve_monotonic.
Qed.

(** ** Using [foo_subrel] instances *)

Goal
  forall A1 A2 B1 B2 C1 C2 (R1 R2: rel A1 A2) (R1': rel B1 B2) (R: rel C1 C2),
    subrel R1 R2 ->
    forall x y,
      (R2 ++> R) x y ->
      (R1 ++> R) x y.
Proof.
  intros A1 A2 B1 B2 C1 C2 R1 R2 R1' R HR12 x y H.
  rewrite HR12.
  assumption.
Qed.

(** FIXME: this should work as well. *)

Goal
  forall A1 A2 B1 B2 C1 C2 (R1 R2: rel A1 A2) (R1': rel B1 B2) (R: rel C1 C2),
    subrel R1 R2 ->
    forall x y,
      (R2 * R1' ++> R) x y ->
      (R1 * R1' ++> R) x y.
Proof.
  intros A1 A2 B1 B2 C1 C2 R1 R2 R1' R HR12 x y H.
  try rewrite HR12.
Abort.
