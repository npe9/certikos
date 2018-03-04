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
Require Export compcert.lib.Maps.
Require Import compcert.common.Errors.
Require Import liblayers.lib.Decision.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.logic.Structures.
Require Import liblayers.logic.OptionOrders.
Require Import liblayers.logic.PseudoJoin.
Require Import liblayers.logic.LayerData.

(** * Generic operations on [PTree]s *)

Definition ptree_rel {A B} (R: rel (option A) (option B)): rel _ _ :=
  fun t1 t2 => forall i, R (t1!i) (t2!i).

Global Instance ptree_subrel A B:
  Proper (subrel ++> subrel) (@ptree_rel A B).
Proof.
  firstorder.
Qed.

Global Instance ptree_get_rel:
  Proper
    (∀ R : (fun A B => rel (option A) (option B)) A B, - ==> ptree_rel R ++> R)
    PTree.get.
Proof.
  intros A B R i t1 t2 H.
  apply H.
Qed.

(** Structures on [option A] can be extended to [PTree.t A] *)

Local Instance ptree_emptyset A : Emptyset (PTree.t A) :=
  { emptyset := PTree.empty A }.

Local Instance ptree_mapsto A : Mapsto positive A (PTree.t A) :=
  { mapsto i a := PTree.set i a (PTree.empty A) }.

Local Instance ptree_le_op {A} `(Ale: Le (option A)): Le (PTree.t A) :=
  { le := ptree_rel (≤) }.

Global Instance ptree_preorder A (R: relation (option A)):
  PreOrder R ->
  PreOrder (ptree_rel R).
Proof.
  intros HA.
  split.
  - intros t i.
    reflexivity.
  - intros t1 t2 t3 H12 H23 i.
    transitivity (t2 ! i); now trivial.
Qed.

Local Instance ptree_oplus A `{Aoplus: Oplus (option A)}: Oplus (PTree.t A) :=
  { oplus := PTree.combine (⊕) }.

Global Instance ptree_emptyset_lb A B (R: rel (option A) (option B)):
  LowerBound R None ->
  LowerBound (ptree_rel R) (PTree.empty A).
Proof.
  intros H t2 i.
  rewrite PTree.gempty.
  apply lower_bound.
Qed.

Lemma ptree_combine_rel:
  forall
    {A1 A2} (RA: rel (option A1) (option A2))
    {B1 B2} (RB: rel (option B1) (option B2))
    {C1 C2} (RC: rel (option C1) (option C2))
    (f: option A1 -> option B1 -> option C1)
    (g: option A2 -> option B2 -> option C2),
  f None None = None ->
  g None None = None ->
  (RA ++> RB ++> RC) f g ->
  (ptree_rel RA ++> ptree_rel RB ++> ptree_rel RC) (PTree.combine f) (PTree.combine g).
Proof.
  intros A1 A2 RA B1 B2 RB C1 C2 RC f g.
  intros Hf Hg Hfg x1 x2 Hx y1 y2 Hy i.
  rewrite !PTree.gcombine by assumption.
  apply Hfg; eauto.
Qed.

Lemma ptree_combine_id_left {A} R f:
  f None None = None ->
  LeftIdentity R f None ->
  LeftIdentity (ptree_rel R) (PTree.combine f) (PTree.empty A).
Proof.
  intros Hf H.
  intros y i.
  rewrite PTree.gcombine by assumption.
  rewrite PTree.gempty.
  apply id_left.
Qed.

Lemma ptree_combine_assoc {A} (R: relation (option A)) f:
  f None None = None ->
  Associative R f ->
  Associative (ptree_rel R) (PTree.combine f).
Proof.
  intros Hf H.
  intros x y z i.
  rewrite !PTree.gcombine by assumption.
  apply associativity.
Qed.

Lemma ptree_combine_comm {A} (R: relation (option A)) f:
  f None None = None ->
  Commutative R f ->
  Commutative (ptree_rel R) (PTree.combine f).
Proof.
  intros Hf H.
  intros x y i.
  rewrite !PTree.gcombine by assumption.
  apply commutativity.
Qed.

Lemma ptree_combine_left_upper_bound {A} (R: relation (option A)) f:
  f None None = None ->
  LeftUpperBound R f ->
  LeftUpperBound (ptree_rel R) (PTree.combine f).
Proof.
  intros Hf H.
  intros x y i.
  rewrite !PTree.gcombine by assumption.
  apply left_upper_bound.
Qed.

Global Instance ptree_pseudojoin A:
  forall `{Ale: Le (option A)} `{Aoplus: Oplus (option A)},
    None ⊕ None = None ->
    PseudoJoin (option A) None ->
    PseudoJoin (PTree.t A) ∅.
Proof with try (assumption || typeclasses eauto).
  intros Hnone Hop.
  split...
  * apply ptree_combine_rel...
    apply proper_prf.
  * apply ptree_combine_id_left...
  * apply ptree_combine_assoc...
  * apply ptree_combine_comm...
  * apply ptree_combine_left_upper_bound...
Qed.

(** Same thing, indexed by layer data *)

Section SIM.
  Context {V E T} `{Hsim: ReflexiveGraphSim V E (fun v => option (T v))}.

  Local Instance ptree_sim_op: Sim E (fun D => PTree.t (T D)) :=
    {
      simRR D1 D2 R := ptree_rel (sim R)
    }.

  Global Instance ptree_rg_sim:
    ReflexiveGraphSim V E (fun D => PTree.t (T D)).
  Proof.
    (** Those will be expressed in terms of [(fun u => option (T u)) v]
      instead of [option (T v)], so we need to get them explicitely in
      the context, and reduce. *)
    Set Printing All.
    pose proof (fun v => rg_sim_id v) as Hle_preorder.
    pose proof (fun v1 v2 e => rg_sim_compose v1 v2 e) as Hsim_le.
    simpl in *.
    Unset Printing All.

    split.
    * simpl.
      typeclasses eauto.
    * simpl.
      intros v1 v2 e x1 y1 H1 x2 y2 H2 Hx i.
      specialize (H1 i).
      specialize (H2 i).
      specialize (Hx i).
      rewrite H1, <- H2.
      assumption.
  Qed.

  (** Not-yet-updated category version: <<<
  Proof.
    split.
    * intros D t i.
      reflexivity.
    * intros D1 D2 D3 R12 R23 σ1 σ2 σ3 H12 H23 i.
      sim_transitivity (σ2 ! i); trivial.
  Qed.
  >>> *)

  Ltac eta_option :=
    repeat
      lazymatch goal with
        | |- context [option (?T ?v)] =>
          change (option (T v)) with ((fun u => option (T u)) v)
      end.

  Global Instance ptree_sim_pseudojoin:
    forall `{Aoplus: forall v, Oplus ((fun v => option (T v)) v)},
      (forall v, None ⊕ None = @None (T v)) ->
      SimPseudoJoin _ _ _ (Toplus := Aoplus) (fun v => @None (T v)) ->
      SimPseudoJoin _ _ _ (Toplus := fun v => ptree_oplus (T v)) (fun v => PTree.empty (T v)).
  Proof with eta_option; try (typeclasses eauto || simpl; eauto).
    intros.
    split; intros...
    * rewrite H1.
      apply ptree_emptyset_lb.
      eta_option.
      eapply @oplus_sim_lower_bound.
      + eassumption.
      + typeclasses eauto.
    * intros v1 v2 R.
      apply ptree_combine_rel...
      eta_option.
      apply oplus_sim_monotonic.
    * rewrite H1.
      apply ptree_combine_id_left...
    * apply ptree_combine_assoc...
      eta_option.
      apply oplus_sim_assoc_le.
    * apply ptree_combine_comm...
      eta_option.
      apply oplus_sim_comm_le.
    * apply ptree_combine_left_upper_bound...
  Qed.
End SIM.

(** * Decidable properties of [PTree]s *)

(** ** Some property holds for all bindings *)

Definition ptree_forall {A} (P: positive -> A -> Prop) (t: PTree.t A) :=
  forall i a, t!i = Some a -> P i a.

Program Instance ptree_forall_decision {A} (P: positive -> A -> Prop):
  (forall i a, Decision (P i a)) ->
  (forall t, Decision (ptree_forall P t)) :=
  fun HP t =>
    match (decide (Forall (fun b => P (fst b) (snd b)) (PTree.elements t))) with
      | left HPt => left _
      | right HPt => right _
    end.

Next Obligation.
  clear Heq_anonymous.
  intros i a Hia.
  apply PTree.elements_correct in Hia.
  rewrite Forall_forall in HPt.
  specialize (HPt (i, a)); simpl in *.
  tauto.
Qed.

Next Obligation.
  clear Heq_anonymous.
  intros H.
  apply HPt; clear HPt.
  rewrite Forall_forall.
  intros [i a] Hia; simpl.
  apply H.
  apply PTree.elements_complete.
  assumption.
Qed.

(** ** Two [PTree]s have disjoint domains *)

Definition ptree_disjoint {A B} (ta: PTree.t A) (tb: PTree.t B) :=
  ptree_forall (fun i _ => tb ! i = None) ta.

Lemma ptree_disjoint_sym {A B} (ta: PTree.t A) (tb: PTree.t B):
  ptree_disjoint ta tb ->
  ptree_disjoint tb ta.
Proof.
  unfold ptree_disjoint, ptree_forall. intros.
  destruct (ta ! i) eqn:?; try reflexivity.
  exploit H; eauto. congruence.
Qed.


(** * Applying a partial function to all data of a tree. *)

(** If it fails on one element, then it fails on the whole tree.  If
    it succeeds on all elements, then it succeeds on the whole tree.
*)

Module PTree.
Export Maps.PTree.

    Fixpoint xmap_error {A B : Type} (f : positive -> A -> res B) (m : t A) (i : positive)
             {struct m} : res (t B) :=
      match m with
      | Leaf => OK Leaf
      | Node l o r =>
        match xmap_error f l (append i (xO xH)) with
            | Error msg => Error msg
            | OK l' =>
              match xmap_error f r (append i (xI xH)) with
                | Error msg => Error msg
                | OK r' =>
                  match o with
                    | None => OK (Node l' None r')
                    | Some a =>
                      match f i a with
                        | Error msg => Error msg
                        | OK b => OK (Node l' (Some b) r')
                      end
                  end
              end
        end
      end.

  Definition map_error {A B : Type} (f : positive -> A -> res B) m := xmap_error f m xH.

    Lemma xgmap_error_ok:
      forall (A B: Type) (f: positive -> A -> res B) (i j : positive) (m: t A),
        forall (m': t B),
          xmap_error f m j = OK m' ->
          match get i m with
            | None => get i m' = None
            | Some a => exists b, f (append j i) a = OK b /\ get i m' = Some b
          end. 
    Proof.
      induction i; intros until m'; destruct m; simpl; auto.
      + inversion 1; subst; reflexivity.
      + destruct (xmap_error f m1 (append j 2)) eqn:?; try discriminate.
        destruct (xmap_error f m2 (append j 3)) eqn:?; try discriminate.
        destruct o.
        - destruct (f j a) eqn:?; try discriminate.
          inversion 1; subst.
          rewrite (append_assoc_1 j i). eapply IHi; eauto.
        - inversion 1; subst.
          rewrite (append_assoc_1 j i). eapply IHi; eauto.
      + inversion 1; subst; reflexivity.
      + destruct (xmap_error f m1 (append j 2)) eqn:?; try discriminate.
        destruct (xmap_error f m2 (append j 3)) eqn:?; try discriminate.
        destruct o.
        - destruct (f j a) eqn:?; try discriminate.
          inversion 1; subst.
          rewrite (append_assoc_0 j i). eapply IHi; eauto.
        - inversion 1; subst.
          rewrite (append_assoc_0 j i). eapply IHi; eauto.
      + inversion 1; subst; reflexivity.
      + destruct (xmap_error f m1 (append j 2)) eqn:?; try discriminate.
        destruct (xmap_error f m2 (append j 3)) eqn:?; try discriminate.
        destruct o.
        - destruct (f j a) eqn:?; try discriminate.
          inversion 1; subst.
          rewrite (append_neutral_r j). eauto.
        - inversion 1; subst.
          reflexivity.
    Qed.

    Theorem gmap_error_ok:
      forall (A B: Type) (f: positive -> A -> res B) (i: positive) (m: t A),
        forall (m': t B),
          map_error f m = OK m' ->
          match get i m with
            | None => get i m' = None
            | Some a => exists b, f i a = OK b /\ get i m' = Some b
          end. 
    Proof.
      unfold map_error.
      intros.
      replace (f i) with (f (append xH i)).
      apply xgmap_error_ok; auto.
      rewrite append_neutral_l; auto.
    Qed.

    Lemma xgmap_error_error:
      forall (A B: Type) (f: positive -> A -> res B) (m: t A) (j : positive),
        forall msg,
          xmap_error f m j = Error msg ->
          exists k, exists a, exists msg',
            get k m = Some a /\
            f (append j k) a = Error msg'.
    Proof.
      induction m; simpl; try discriminate.
      intros.
      destruct (xmap_error f m1 (append j 2)) eqn:?.
      destruct (xmap_error f m2 (append j 3)) eqn:?.
      destruct o; try discriminate.
      destruct (f j a) eqn:?; try discriminate.
      + exists xH; simpl. rewrite append_neutral_r. eauto.
      + exploit IHm2; eauto.
        destruct 1 as [? [? [? [? ?]]]].
        exists (xI x); simpl. rewrite append_assoc_1. eauto.
      + exploit IHm1; eauto.
        destruct 1 as [? [? [? [? ?]]]].
        exists (xO x); simpl. rewrite append_assoc_0. eauto.
    Qed.

    Theorem gmap_error_error:
      forall (A B: Type) (f: positive -> A -> res B) (i: positive) (m: t A),
        forall msg,
          map_error f m = Error msg ->
          exists k, exists a, exists msg',
          get k m = Some a /\
          f k a = Error msg'.
    Proof.
      unfold map_error.
      intros.
      exploit xgmap_error_error; eauto.
    Qed.

    Lemma xmap_compose_ok:
      forall (A B C: Type) (fab: positive -> A -> res B) (fbc: positive -> B -> res C) (fac: positive -> A -> res C) (ma: t A) (j: positive),
        forall (mb: t B) (mc: t C),
          xmap_error fab ma j = OK mb ->
          xmap_error fbc mb j = OK mc ->
          (forall i a, get i ma = Some a ->
                       forall b, fab (append j i) a = OK b ->
                                 forall c,
                                 fbc (append j i) b = OK c ->
                                 fac (append j i) a = OK c) ->
          xmap_error fac ma j = OK mc.
    Proof.
      induction ma; simpl; intros.
      * inv H. inv H0. reflexivity.
      * destruct (xmap_error fab ma1 (append j 2)) eqn:?; try discriminate.
        destruct (xmap_error fab ma2 (append j 3)) eqn:?; try discriminate.        
        destruct o.
        + destruct (fab j a) eqn:?; try discriminate.
          inv H.
          simpl in H0.
          destruct (xmap_error fbc t0 (append j 2)) eqn:?; try discriminate.
          destruct (xmap_error fbc t1 (append j 3)) eqn:?; try discriminate.
          destruct (fbc j b) eqn:?; try discriminate.
          inv H0.
          generalize (H1 xH _ (refl_equal _) b).
          rewrite append_neutral_r.
          intro.
          erewrite H; eauto.
          erewrite IHma1.
          erewrite IHma2.
          reflexivity.
          eassumption.
          assumption.
          intros until 1. intro.
          rewrite <- append_assoc_1.
          eauto.
          eassumption.
          assumption.
          intros until 1. intro.
          rewrite <- append_assoc_0.
          eauto.
        + inv H.
          simpl in H0.
          destruct (xmap_error fbc t0 (append j 2)) eqn:?; try discriminate.
          destruct (xmap_error fbc t1 (append j 3)) eqn:?; try discriminate.
          inv H0.
          erewrite IHma1.
          erewrite IHma2.
          reflexivity.
          eassumption.
          assumption.
          intros until 1. intro.
          rewrite <- append_assoc_1.
          eauto.
          eassumption.
          assumption.
          intros until 1. intro.
          rewrite <- append_assoc_0.
          eauto.
    Qed.

    Lemma map_compose_ok:
      forall (A B C: Type) (fab: positive -> A -> res B) (fbc: positive -> B -> res C) (fac: positive -> A -> res C) (ma: t A),
        forall (mb: t B) (mc: t C),
          map_error fab ma = OK mb ->
          map_error fbc mb = OK mc ->
          (forall i a, get i ma = Some a ->
                       forall b, fab i a = OK b ->
                                 forall c,
                                 fbc i b = OK c ->
                                 fac i a = OK c) ->
          map_error fac ma = OK mc.
    Proof.
      intros.
      eapply xmap_compose_ok; eauto.
    Qed.

    Fixpoint xmap_option {A B : Type} (f : positive -> A -> option B) (m : t A) (i : positive)
             {struct m} : (t B) :=
      match m with
      | Leaf => Leaf
      | Node l o r =>
        Node
          (xmap_option f l (append i (xO xH)))
          match o with
            | Some a => f i a
            | None => None
          end
          (xmap_option f r (append i (xI xH)))
      end.

  Definition map_option {A B : Type} (f : positive -> A -> option B) m := xmap_option f m xH.

    Lemma xgmap_option_some:
      forall (A B: Type) (f: positive -> A -> option B) (i j : positive) (m: t A),
        forall a,
          get i m = Some a ->
          get i (xmap_option f m j) = f (append j i) a. 
    Proof.
      induction i; destruct m; simpl; intros; try discriminate.
      + rewrite (append_assoc_1 j i); eauto.
      + rewrite (append_assoc_0 j i); eauto.
      + subst. rewrite append_neutral_r. reflexivity.
    Qed.

    Theorem gmap_option_some:
      forall (A B: Type) (f: positive -> A -> option B) (i: positive) (m: t A),
        forall a,
          get i m = Some a ->
          get i (map_option f m) = f i a.
    Proof.
      unfold map_option.
      intros.
      replace (f i) with (f (append xH i)).
      apply xgmap_option_some; auto.
      rewrite append_neutral_l; auto.
    Qed.

    Lemma xgmap_option_none:
      forall (A B: Type) (f: positive -> A -> option B) (i: positive) (m: t A) (j : positive),
        get i m = None ->
        get i (xmap_option f m j) = None.
    Proof.
      induction i; destruct m; simpl; intros; try reflexivity; eauto.
      subst. reflexivity.
    Qed.

    Theorem gmap_option_none:
      forall (A B: Type) (f: positive -> A -> option B) (i: positive) (m: t A),
        get i m = None ->
        get i (map_option f m) = None.
    Proof.
      unfold map_option.
      intros.
      exploit xgmap_option_none; eauto.
    Qed.

    Lemma gmap_option {A B} (f: positive -> A -> option B) (i: positive) m:
      (PTree.map_option f m) ! i =
      x <- m ! i; f i x.
    Proof.
      case_eq (m ! i).
      * apply PTree.gmap_option_some.
      * apply PTree.gmap_option_none.
    Qed.

 (** A PTree is never completely full... *)

 Theorem get_none_ex {A} (m: _ A):
   exists i, get i m = None.
 Proof.
   induction m; simpl.
   * exists xH. reflexivity.
   * destruct IHm1 as (x & ?).
     exists (xO x); simpl.
     assumption.
 Qed.   

End PTree.

Theorem ptree_forall_decision_strong {A}
        (P: positive -> A -> Prop)
        (Q: Prop):
  (forall i a, Decision (P i a)) ->
  Decision Q ->
  (forall t, Decision (forall i,
                         match t ! i with
                           | Some a => P i a
                           | None => Q
                         end)).
Proof.
  intros DP DQ t.
  apply (decide_discr (fun i => t ! i = None) (fun i => t ! i <> None)).
  + intro. apply OptionMonad.isNone_dec.
  + revert DQ.
    apply decide_rewrite.
    split.
    - intros until i. intro Li.
      rewrite Li.
      assumption.
    - intro J.
      destruct (PTree.get_none_ex t) as (? & Hx).
      generalize (J _ Hx).
      rewrite Hx.
      tauto.
  + generalize (ptree_forall_decision _ DP t).
    apply decide_rewrite.
    unfold ptree_forall.
    split.
    - intros J i Hi.
      destruct (t ! i) eqn:Ti; try congruence.
      auto.
    - intros J i a Ha.
      generalize (J i).
      rewrite Ha.
      intro K.
      apply K; congruence.
Defined.

(** ** Monotonicity wrt. [ptree_rel] *)

Global Instance ptree_map_monotonic:
  Proper
    (∀ RA, ∀ RB,
      (- ==> RA ++> RB) ++>
      ptree_rel (option_le RA) ++>
      ptree_rel (option_le RB))
    PTree.map.
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg t1 t2 Ht i.
  rewrite !PTree.gmap.
  solve_monotonic.
  apply Hfg.
  assumption.
Qed.

Global Instance ptree_map_option_monotonic {A B} (RA: relation A) (RB: relation B):
  Proper ((- ==> RA ++> option_le RB) ++> (ptree_rel (option_le RA) ++> ptree_rel (option_le RB)))
    PTree.map_option.
Proof.
  intros f g Hfg t1 t2 Ht i.
  specialize (Ht i).
  inversion Ht as [x2 Hx1 Hx2 | x1 x2 Hx Hx1 Hx2].
  * rewrite PTree.gmap_option_none by congruence.
    constructor.
  * symmetry in Hx1, Hx2.
    erewrite !PTree.gmap_option_some by eassumption.
    apply Hfg.
    assumption.
Qed.

(** FIXME: those could actually be strengthened to use [option_rel] if
  we had the appropriate subrelation infrastructure. *)

Instance ptree_set_le:
  Proper (∀ R, - ==> R ++> ptree_rel (option_le R) ++> ptree_rel (option_le R)) (@PTree.set).
Proof.
  intros A1 A2 RA i x1 x2 Hx t1 t2 Ht j.
  destruct (decide (j = i)) as [Hij | Hij]; subst.
  * rewrite !PTree.gss.
    solve_monotonic.
  * rewrite !PTree.gso by assumption.
    solve_monotonic.
Qed.

Instance ptree_empty_le:
  Proper (∀ R, ptree_rel (option_le R)) (@PTree.empty).
Proof.
  intros A1 A2 RA i.
  rewrite !PTree.gempty.
  constructor.
Qed.
