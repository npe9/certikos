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
Require Import liblayers.lib.Decision.
Require Export liblayers.logic.LayerData.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Primitives.
Require Export liblayers.compcertx.ErrorMonad.

Section WITH_LAYER_DATA.
Context {layerdata simrel} `{HVE: ReflexiveGraph layerdata simrel}.


(** * Layers *)

(** The semantic counterpart of modules are layers, which are indexed
  by abstract data and simulation relations. As for modules, there is
  a generic implementation using [positive] identifiers in the file
  [PTreeLayers]. *)

Class LayerOps ident primsem V (layer: layerdata -> Type)
    `{primsem_ops: PrimitiveOps layerdata primsem} :=
  {
    layer_empty :> forall D, Emptyset (layer D);
    layer_oplus :> forall D, Oplus (layer D);
    layer_mapsto_primitive :> forall D, Mapsto ident (primsem D) (layer D);
    layer_mapsto_globalvar :> forall D, Mapsto ident V (layer D);

    get_layer_primitive {D} (i: ident): layer D -> res (option (primsem D));
    get_layer_globalvar {D} (i: ident): layer D -> res (option V);
    layers_disjoint {D1} {D2} : layer D1 -> layer D2 -> Prop;

    layer_decide_primitive D (P: res (option (primsem D)) -> Prop) :>
      (forall σ, Decision (P σ)) ->
      (forall L, Decision (forall i, P (get_layer_primitive i L)));
    layer_decide_primitive_name D (P: ident -> Prop) :>
      (forall i, Decision (P i)) ->
      (forall L, Decision (forall i, get_layer_primitive (D:=D) i L <> OK None -> P i));
    layer_decide_globalvar D (P: res (option V) -> Prop) :>
      (forall τ, Decision (P τ)) ->
      (forall L, Decision (forall i, P (get_layer_globalvar (D:=D) i L)));
    layer_decide_globalvar_name D (P: ident -> Prop) :>
      (forall i, Decision (P i)) ->
      (forall L, Decision (forall i, get_layer_globalvar (D:=D) i L <> OK None -> P i));
    layers_disjoint_dec {D1 D2} (L1: layer D1) (L2: layer D2) :>
      Decision (layers_disjoint L1 L2)
  }.


(** Properties of layers *)

Class Layers ident primsem V layer
    `{lops: LayerOps ident primsem V layer}
    `{psim_op: Sim layerdata simrel primsem}
    `{lsim_op: Sim layerdata simrel layer} :=
  {
    layer_pseudojoin :>
      SimPseudoJoin layerdata simrel layer (fun D => ∅);
    layer_sim_intro D1 D2 (R: simrel D1 D2) i σ1 σ2 :
      sim R σ1 σ2 ->
      sim R (i ↦ σ1) (i ↦ σ2);
    (*
    layer_oplus_idempotent {D} (L: layer D):
      L ⊕ L ≤ L;
    *)

    get_layer_primitive_empty {D} i:
      get_layer_primitive (D:=D) i ∅ = OK None;
    get_layer_primitive_mapsto {D} i σ:
      get_layer_primitive (D:=D) i (i ↦ σ) = OK (Some σ);
    get_layer_primitive_mapsto_other_primitive {D} i j (σ: primsem D):
      i <> j -> get_layer_primitive (D:=D) i (j ↦ σ) = OK None;
    get_layer_primitive_mapsto_globalvar {D} i j (τ: V):
      get_layer_primitive (D:=D) i (j ↦ τ) = OK None;
    get_layer_primitive_oplus {D} i (L1 L2: layer D):
      get_layer_primitive i (L1 ⊕ L2) =
      get_layer_primitive i L1 ⊕ get_layer_primitive i L2;
    get_layer_primitive_sim_monotonic :>
      Proper
        (∀ R, - ==> sim R ++> res_le (option_le (sim R)))
        (@get_layer_primitive _ _ _ _ _ _);

    get_layer_globalvar_empty {D} i:
      get_layer_globalvar (D:=D) i ∅ = OK None;
    get_layer_globalvar_mapsto {D} i τ:
      get_layer_globalvar (D:=D) i (i ↦ τ) = OK (Some τ);
    get_layer_globalvar_mapsto_other_globalvar {D} i j (τ: V):
      i <> j -> get_layer_globalvar (D:=D) i (j ↦ τ) = OK None;
    get_layer_globalvar_mapsto_primitive {D} i j (σ: primsem D):
      get_layer_globalvar (D:=D) i (j ↦ σ) = OK None;
    get_layer_globalvar_oplus {D} i (L1 L2: layer D):
      get_layer_globalvar (D:=D) i (L1 ⊕ L2) =
      get_layer_globalvar i L1 ⊕ get_layer_globalvar i L2;
    get_layer_globalvar_sim_monotonic :>
      Proper
        (∀ R, - ==> sim R ++> res_le (option_le eq))
        (@get_layer_globalvar _ _ _ _ _ _);

    layers_disjoint_empty {D1 D2} L:
      layers_disjoint (D1:=D1) (D2:=D2) ∅ L;
    layer_sim_cancel_disjoint {D D'} (R: simrel D D') L L1 L2:
      layers_disjoint L L2 ->
      sim R L (L1 ⊕ L2) ->
      sim R L L1
  }.

  (** Specialized version of [layer_sim_intro]. *)
  Lemma layer_le_intro `{Layers} {D} i (σ1 σ2: primsem D):
    σ1 ≤ σ2 ->
    i ↦ σ1 ≤ i ↦ σ2.
  Proof.
    apply layer_sim_intro.
  Qed.

(** NOW WRONG -- though can be enforced through layer_ok
  <<<
    get_layer_primitive_globalvar_disjoint {D} (L: layer D) (i: ident):
      isOK (get_layer_primitive i L) ->
      isOK (get_layer_globalvar i L) ->
      isOKNone (get_layer_primitive i L) \/ isOKNone (get_layer_globalvar i L)
  >>> *)
End WITH_LAYER_DATA.

(** Rewrite hints for [get_layer_primitive] and [get_layer_globalvar] *)

Ltac get_layer_normalize :=
  repeat rewrite
    ?get_layer_primitive_empty,
    ?get_layer_primitive_mapsto,
    ?get_layer_primitive_mapsto_other_primitive,
    ?get_layer_primitive_mapsto_globalvar,
    ?get_layer_primitive_oplus,
    ?get_layer_globalvar_empty,
    ?get_layer_globalvar_mapsto,
    ?get_layer_globalvar_mapsto_other_globalvar,
    ?get_layer_globalvar_mapsto_primitive,
    ?get_layer_globalvar_oplus by assumption.

Ltac get_layer_normalize_in H :=
  repeat rewrite
    ?get_layer_primitive_empty,
    ?get_layer_primitive_mapsto,
    ?get_layer_primitive_mapsto_other_primitive,
    ?get_layer_primitive_mapsto_globalvar,
    ?get_layer_primitive_oplus,
    ?get_layer_globalvar_empty,
    ?get_layer_globalvar_mapsto,
    ?get_layer_globalvar_mapsto_other_globalvar,
    ?get_layer_globalvar_mapsto_primitive,
    ?get_layer_globalvar_oplus in H by assumption.


(** * Well-formed layers *)

Section LAYER_OK.
  Context `{Hlayer: Layers}.
  Context `{ident_dec: forall i j: ident, Decision (i = j)}.

  Record LayerOK_at {D} (L: layer D) (i: ident): Prop :=
    {
      layer_ok_primitive:
        isOK (get_layer_primitive i L);
      layer_ok_globalvar:
        isOK (get_layer_globalvar i L);
      layer_ok_disjoint:
        isOKNone (get_layer_primitive i L) \/
        isOKNone (get_layer_globalvar i L)
    }.

  Global Instance layer_ok_at_dec {D} (L: layer D) (i: ident):
    Decision (LayerOK_at L i) :=
    match (decide (isOK (get_layer_primitive i L) /\
                   isOK (get_layer_globalvar i L) /\
                   (isOKNone (get_layer_primitive i L) \/
                    isOKNone (get_layer_globalvar i L))))
    with
      | left Hyes => left _
      | right Hno => right _
    end.
  Proof.
    abstract (destruct Hyes as (H1 & H2 & H3); split; assumption).
    abstract (intros [H1 H2 H3]; eauto).
  Defined.

  Class LayerOK {D} (L: layer D): Prop :=
    layer_ok_at: forall i, LayerOK_at L i.

  (** This alternate definition is used for providing a decision procedure. *)
  Definition LayerOK_alt {D} (L: layer D) :=
    (forall i, get_layer_primitive i L <> OK None ->
               (fun i => isOK (get_layer_primitive i L) /\
                         isOKNone (get_layer_globalvar i L)) i) /\
    (forall i, get_layer_globalvar i L <> OK None ->
               (fun i => isOK (get_layer_globalvar i L) /\
                         isOKNone (get_layer_primitive i L)) i).

  (** Let's prove it is equivalent *)
  Lemma LayerOK_alt_equiv {D} (L: layer D):
    LayerOK_alt L <-> LayerOK L.
  Proof.
    unfold LayerOK_alt.
    split.
    * intros [H1 H2] i.
      specialize (H1 i).
      specialize (H2 i).
      split.
      + destruct (get_layer_primitive i L) as [[|]|]; eauto.
        destruct H1; try discriminate.
        assumption.
      + destruct (get_layer_globalvar i L) as [[|]|]; eauto.
        destruct H2; try discriminate.
        assumption.
      + destruct (get_layer_primitive i L) as [[|]|]; eauto.
        - destruct H1; try discriminate; eauto.
        - destruct H1; try discriminate; eauto.
    * intros H.
      split; intros i Hi; destruct (H i) as [Hp Hv Hd];
      split; destruct Hd; eauto; congruence.
  Qed.

  Global Instance LayerOK_dec {D} (L: layer D): Decision (LayerOK L) :=
    match decide (LayerOK_alt L) with
      | left Hyes => left _
      | right Hno => right _
    end.
  Proof.
    * abstract (apply LayerOK_alt_equiv; assumption).
    * abstract (rewrite <- LayerOK_alt_equiv; assumption).
  Defined.

  (** ** Monotonicity *)

  Global Instance layer_ok_at_le:
    Proper (∀ -, (≤) --> - ==> impl) (@LayerOK_at).
  Proof.
    intros D L2 L1 HL i [Hp Hg Hd].
    rewrite HL in *.
    split; assumption.
  Qed.

  Lemma layer_ok_at_sim {D1 D2} (R: simrel D1 D2) L1 L2 i:
    sim R L1 L2 ->
    LayerOK_at L2 i ->
    LayerOK_at L1 i.
  Proof.
    intros HL [H2p H2v H2d].
    split.
    * eapply (isOK_le _ _ (option_le (sim R))); try eassumption.
      solve_monotonic.
    * eapply (isOK_le _ _ (option_le eq)); try eassumption.
      solve_monotonic.
    * destruct H2d; [left|right].
      + eapply (isOKNone_le _ _ (sim R)); try eassumption.
        solve_monotonic.
      + eapply (isOKNone_le _ _ eq); try eassumption.
        solve_monotonic.
  Qed.

  (** XXX: need as an instance of [LayerOK] also? *)
  Global Instance layer_ok_antitonic:
    Proper (∀ -, (≤) --> impl) (@LayerOK).
  Proof.
    intros D L2 L1 HL H i.
    specialize (H i).
    eapply layer_ok_at_le; eassumption.
  Qed.

  Global Instance layer_ok_sim_antitonic {D1 D2} (R: simrel D1 D2) L1 L2:
    sim R L1 L2 ->
    LayerOK L2 ->
    LayerOK L1.
  Proof.
    intros HL HL2 i.
    specialize (HL2 i).
    eapply layer_ok_at_sim; eassumption.
  Qed.

  (** ** Basic instances *)

  Global Instance empty_ok `{Layers} D:
    LayerOK (D := D) ∅.
  Proof.
    intros i.
    split; get_layer_normalize; eauto.
  Qed.

  Global Instance mapsto_function_ok {D} i (σ: primsem D):
    LayerOK (i ↦ σ).
  Proof.
    intros j.
    destruct (decide (j = i)); subst;
    split; get_layer_normalize; eauto.
  Qed.

  Global Instance mapsto_variable_ok {D} i (τ: V):
    LayerOK (D:=D) (i ↦ τ).
  Proof.
    intros j.
    destruct (decide (j = i)); subst;
    split; get_layer_normalize; eauto.
  Qed.

  Lemma layer_oplus_primitive_ok {D} (L: layer D) (i: ident) (σ: primsem D):
    isOKNone (get_layer_primitive i L) ->
    isOKNone (get_layer_globalvar i L) ->
    LayerOK L ->
    LayerOK (L ⊕ i ↦ σ).
  Proof.
    intros HLip HLiv HL j.
    specialize (HL j); destruct HL as [HLp HLv HLd].
    destruct (decide (j = i)); subst.
    * split; get_layer_normalize;
      rewrite ?HLip, ?HLiv, ?id_left;
      eauto.
    * split; get_layer_normalize;
      rewrite ?id_right;
      eauto.
  Qed.
End LAYER_OK.

(** * Other properties *)

(** Express the monotonicity of [i ↦ σ] in terms of [≤]. *)

Global Instance layer_mapsto_mon `{Layers} D:
  @Proper (ident -> primsem D -> layer D) (- ==> (≤) ++> (≤)) (↦).
Proof.
  intros i σ1 σ2 Hσ.
  apply layer_le_intro.
  assumption.
Qed.

Global Instance layer_lower_bound `{Layers} D:
  LowerBound (A := layer D) (≤) ∅.
Proof.
  typeclasses eauto.
Qed.

Lemma layer_oplus_primitive_same `{Layers} {D} L i (σ: primsem D):
  isOKNone (get_layer_primitive i L) ->
  get_layer_primitive i (L ⊕ i ↦ σ) = OK (Some σ).
Proof.
  intros HLi.
  get_layer_normalize.
  rewrite HLi.
  rewrite id_left.
  reflexivity.
Qed.

Lemma layer_oplus_primitive_other `{Layers} {D} L i (σ: primsem D) j:
  j <> i ->
  get_layer_primitive j (L ⊕ i ↦ σ) = get_layer_primitive j L.
Proof.
  intros Hij.
  get_layer_normalize.
  rewrite id_right.
  reflexivity.
Qed.

Lemma layer_oplus_globalvar `{Layers} {D} L i (σ: primsem D) j:
  get_layer_globalvar j (L ⊕ i ↦ σ) = get_layer_globalvar j L.
Proof.
  get_layer_normalize.
  rewrite id_right.
  reflexivity.
Qed.

Section AuxLemma.

  Lemma get_layer_primitive_isOK `{LOps: Layers} {D}:
    forall i (a b: _ D),
      isOK (get_layer_primitive i (a ⊕ b)) ->
      isOK (get_layer_primitive i a)
      /\ isOK (get_layer_primitive i b).
  Proof.
    intros. destruct H as [? Hcom].
    specialize (get_layer_primitive_oplus i a b).
    rewrite Hcom.
    intros.
    destruct (get_layer_primitive i a);
      destruct (get_layer_primitive i b); inv_monad H.
    split; esplit; eauto.
  Qed.

  Lemma get_layer_primitive_OK_Some_left `{LOps: Layers} {D}:
    forall i (a b: _ D) v v',
      get_layer_primitive i a = OK (Some v) ->
      get_layer_primitive i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_layer_primitive_oplus i a b).
    rewrite H. rewrite H0.
    intros.
    destruct (get_layer_primitive i b); try destruct o; inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_layer_primitive_OK_Some_right `{LOps: Layers} {D}:
    forall i (a b: _ D) v v',
      get_layer_primitive i b = OK (Some v) ->
      get_layer_primitive i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_layer_primitive_oplus i a b).
    rewrite H. rewrite H0.
    intros.
    destruct (get_layer_primitive i a); try destruct o; inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_layer_primitive_left `{LOps: Layers} {D}:
    forall i (a b: _ D) v,
      get_layer_primitive i a = OK (Some v) ->
      isOK (get_layer_primitive i (a ⊕ b)) ->
      get_layer_primitive i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_layer_primitive_oplus i a b).
    rewrite Hcom. rewrite H. 
    intros. 
    destruct (get_layer_primitive i b); try destruct o; inv_monad H0.
    reflexivity.
  Qed.

  Lemma get_layer_primitive_right `{LOps: Layers} {D}:
    forall i (a b: _ D) v,
      get_layer_primitive i b = OK (Some v) ->
      isOK (get_layer_primitive i (a ⊕ b)) ->
      get_layer_primitive i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_layer_primitive_oplus i a b).
    rewrite Hcom. rewrite H. 
    intros. 
    destruct (get_layer_primitive i a); try destruct o; inv_monad H0.
    reflexivity.
  Qed.

  Lemma get_layer_primitive_none `{LOps: Layers} {D}:
    forall i (a b: _ D),
      get_layer_primitive i b = OK None ->
      get_layer_primitive i a = OK None ->
      isOK (get_layer_primitive i (a ⊕ b)) ->
      get_layer_primitive i (a ⊕ b) = OK None.
  Proof.
    intros. destruct H1 as [? Hcom].
    specialize (get_layer_primitive_oplus i a b).
    rewrite Hcom. rewrite H. rewrite H0.
    intros. inv_monad H1. 
    reflexivity.
  Qed.
 
  Lemma get_layer_globalvar_isOK `{LOps: Layers} {D}:
    forall i (a b: _ D),
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      isOK (get_layer_globalvar i a)
      /\ isOK (get_layer_globalvar i b).
  Proof.
    intros. destruct H as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom.
    intros.
    destruct (get_layer_globalvar i a);
      destruct (get_layer_globalvar i b); inv_monad H.
    split; esplit; eauto.
  Qed.

  Lemma get_layer_globalvar_OK_Some_left `{LOps: Layers} {D}:
    forall i (a b: _ D) v v',
      get_layer_globalvar i a = OK (Some v) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_layer_globalvar_oplus i a b).
    rewrite H. rewrite H0.
    intros.
    destruct (get_layer_globalvar i b); try destruct o; inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_layer_globalvar_OK_Some_right `{LOps: Layers} {D}:
    forall i (a b: _ D) v v',
      get_layer_globalvar i b = OK (Some v) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v') ->
      v' = v.
  Proof.
    intros. 
    specialize (get_layer_globalvar_oplus i a b).
    rewrite H. rewrite H0.
    intros.
    destruct (get_layer_globalvar i a); try destruct o; inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_layer_globalvar_left `{LOps: Layers} {D}:
    forall i (a b: _ D) v,
      get_layer_globalvar i a = OK (Some v) ->
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom. rewrite H. 
    intros. 
    destruct (get_layer_globalvar i b); try destruct o; inv_monad H0.
    reflexivity.
  Qed.

  Lemma get_layer_globalvar_right `{LOps: Layers} {D}:
    forall i (a b: _ D) v,
      get_layer_globalvar i b = OK (Some v) ->
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      get_layer_globalvar i (a ⊕ b) = OK (Some v).
  Proof.
    intros. destruct H0 as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom. rewrite H. 
    intros. 
    destruct (get_layer_globalvar i a); try destruct o; inv_monad H0.
    reflexivity.
  Qed.

  Lemma get_layer_globalvar_none `{LOps: Layers} {D}:
    forall i (a b:_ D),
      get_layer_globalvar i b = OK None ->
      get_layer_globalvar i a = OK None ->
      isOK (get_layer_globalvar i (a ⊕ b)) ->
      get_layer_globalvar i (a ⊕ b) = OK None.
  Proof.
    intros. destruct H1 as [? Hcom].
    specialize (get_layer_globalvar_oplus i a b).
    rewrite Hcom. rewrite H. rewrite H0.
    intros. inv_monad H1. 
    reflexivity.
  Qed.

  Lemma get_layer_primitive_cancel `{LOps: Layers} {D}:
    forall i (a b: _ D),
      get_layer_primitive i (a ⊕ b) = OK None ->
      get_layer_primitive i b = OK None /\
      get_layer_primitive i a = OK None.
  Proof.
    intros. 
    specialize (get_layer_primitive_oplus i a b).
    rewrite H. 
    intros. 
    destruct (get_layer_primitive i a); try destruct o;
    destruct (get_layer_primitive i b); try destruct o;
    inv_monad H0.
    split; reflexivity.
  Qed.

  Lemma get_layer_globalvar_cancel `{LOps: Layers} {D}:
    forall i (a b: _ D),
      get_layer_globalvar i (a ⊕ b) = OK None ->
      get_layer_globalvar i b = OK None /\
      get_layer_globalvar i a = OK None.
  Proof.
    intros. 
    specialize (get_layer_globalvar_oplus i a b).
    rewrite H. 
    intros. 
    destruct (get_layer_globalvar i a); try destruct o;
    destruct (get_layer_globalvar i b); try destruct o;
    inv_monad H0.
    split; reflexivity.
  Qed.

  Lemma get_layer_primitive_OK_eq `{LOps: Layers} {D}
       `{Heq: forall i j: ident, Decision (i = j)}:
    forall i j σ1 σ2,
      get_layer_primitive (D:=D) j (i ↦ σ2) = OK (Some σ1) ->
      σ2 = σ1.      
  Proof.
    intros.  
    destruct (Heq j i); subst.
    - subst. rewrite get_layer_primitive_mapsto in H.
      inversion H. reflexivity.
    - rewrite get_layer_primitive_mapsto_other_primitive in H.
      discriminate. assumption.
  Qed.

End AuxLemma.
