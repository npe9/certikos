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
Require Import liblayers.logic.Structures.


(** * Categories of abstract data and simulation relations *)


(** ** Reflexive graphs *)

(** A reflexive graph is given by a type of objects, types of arrows
  between any two vertices, and an identity edge at each vertex. *)

Class ReflexiveGraphOps (V: Type) (E: V -> V -> Type): Type :=
  {
    cat_id v :> Id (E v v)
  }.

Class ReflexiveGraph V E `{VEops: ReflexiveGraphOps V E}: Prop.


(** ** Categories *)
  
(** A category additionally provides a composition operator for arrows
  with matching endpoints, with unsurprising properties. *)

Class CategoryOps (V: Type) (E: V -> V -> Type): Type :=
  {
    cat_rg_ops :> ReflexiveGraphOps V E;
    cat_compose v1 v2 v3 :> Compose (E v1 v2) (E v2 v3) (E v1 v3)
  }.

Class Category V E `{VEops: CategoryOps V E}: Prop :=
  {
    cat_compose_id_left {v1 v2: V}:
      forall (e: E v1 v2),
        id ∘ e = e;
    cat_compose_id_right {v1 v2: V}:
      forall (e: E v1 v2),
        e ∘ id = e;
    cat_compose_assoc {v1 v2 v3 v4: V}:
      forall (e12: E v1 v2) (e23: E v2 v3) (e34: E v3 v4),
        e34 ∘ (e23 ∘ e12) = (e34 ∘ e23) ∘ e12
  }.

(** A category is a special case of a reflexive graph. *)
Global Instance cat_rg V E `{Category V E}: ReflexiveGraph V E.


(** * Associated concrete simulation relations *)

(** We map the objects and arrows onto types and relations in some
  kinds of structure-preserving ways. *)


(** ** Simulation relations indexed by reflexive graphs *)

(** For reflexive graphs, this means that the relations associated to
  [id] arrows are preorders, and some kind of identities for relation
  composition. *)

Class ReflexiveGraphSim V E T
  `{rg_ops: ReflexiveGraphOps V E}
  `{rg_sim: Sim V E T}: Prop :=
  {
    rg_sim_id (v: V) :>
      PreOrder (simRR v v id);
    rg_sim_compose (v1 v2: V) (e: E v1 v2) :>
      Proper (sim id --> sim id ++> impl) (sim e)
  }.

(** We also write [sim id] as [(≤)]. *)

Global Instance rg_sim_le_op {V E} T `{ReflexiveGraphOps V E} `{Sim V E T} v:
  Le (T v) :=
  {
    le := sim id
  }.

(* XXX: is it still necessary? *)
Global Instance rg_sim_equiv V E T `{ReflexiveGraphSim V E T}:
  forall (v1 v2: V) (e: E v1 v2),
    Proper ((≡) ==> (≡) ==> impl) (simRR v1 v2 e).
Proof.
  solve_monotonic; firstorder.
Qed.


(** ** Simulation relations indexed by categories *)

Class CategorySim V E T `{cat_ops: CategoryOps V E} `{cat_sim: Sim V E T} :=
  {
    cat_sim_refl v :> @Reflexive (T v) (sim id);
    cat_sim_trans {v1 v2 v3} {e12 e23} {t1: T v1} (t2: T v2) {t3: T v3}:
      sim e12 t1 t2 -> sim e23 t2 t3 -> sim (e23 ∘ e12) t1 t3
  }.

(* XXX: sort out, can generalize to [reflexivity]? *)
Hint Resolve (cat_sim_refl: forall v x, sim id x x) : liblayers.
Hint Immediate cat_sim_trans : liblayers.

Ltac sim_trans_apply σ2 :=
  lazymatch goal with
    | |- simRR (T := ?T) _ _ (?R23 ∘ ?R12) ?σ1 ?σ3 =>
      apply (cat_sim_trans (T := T) σ2)
  end.

Ltac sim_transitivity σ2 :=
  sim_trans_apply σ2 ||
  (setoid_rewrite <- cat_compose_id_right; sim_trans_apply σ2) ||
  (setoid_rewrite <- cat_compose_id_left; sim_trans_apply σ2).

(** Typeclass-friendly version of [cat_sim_trans] for [id]. *)

Global Instance cat_sim_trans_instance `(CategorySim):
  Category V E ->
  forall D, @Transitive (T D) (sim id).
Proof.
  intros HVE D x y z Hxy Hyz.
  sim_transitivity y;
  eassumption.
Qed.

(** Given a [CategorySim] we can derive the corresponding [QuiverSim]
  on the category's underlying quiver. *)

Global Instance catsim_quivsim_prf V E T `{CategorySim V E T} `{!Category V E}:
  ReflexiveGraphSim V E T.
Proof.
  split.
  * intros v; split.
    + apply cat_sim_refl.
    + intros x1 x2 x3 H12 H23.
      simpl.
      sim_transitivity x2; assumption.
  * intros v1 v2 e x1 x2 Hx y1 y2 Hy H1.
    sim_transitivity x1; try assumption.
    sim_transitivity y1; try assumption.
Qed.


(** * Free reflexive graph  *)

(** We can construct the free reflexive graph on a quiver by adjoining
  an identity arrow at every object. *)


(** ** Definition *)

Inductive freerg {V: Type} (E: V -> V -> Type) (v1: V): V -> Type :=
  | freerg_id: freerg E v1 v1
  | freerg_inj (v2: V) (e: E v1 v2): freerg E v1 v2.

Global Instance freerg_ops V E: ReflexiveGraphOps V (freerg E) :=
  {
    cat_id v := {| id := freerg_id E v |}
  }.

Global Instance freerg_prf V E: ReflexiveGraph V (freerg E).


(** ** Building simulation relations *)

Section FREERG_SIM.
  Context {V E T} (R: forall v, rel (T v) (T v)) (RR: @sim_relation V E T).

  Definition freerg_rel (v1 v2: V) (fe: freerg E v1 v2): rel (T v1) (T v2) :=
    match fe with
      | freerg_id => R v1
      | freerg_inj v2 e => RR v1 v2 e
    end.

  Local Instance freerg_sim_op: Sim (freerg E) T :=
    {
      simRR := freerg_rel
    }.

  Local Instance freerg_sim_prf:
    (forall v1 v2 (e: E v1 v2), Proper ((≤) --> (≤) ++> impl) (RR v1 v2 e)) ->
    (forall v, @PreOrder (T v) (R v)) ->
    ReflexiveGraphSim V (freerg E) T.
  Proof.
    intros Hle Hsim.
    split.
    * simpl.
      typeclasses eauto.
    * intros v1 v2 e.
      destruct e as [ | v2 e]; simpl.
      + typeclasses eauto.
      + typeclasses eauto.
  Qed.
End FREERG_SIM.
