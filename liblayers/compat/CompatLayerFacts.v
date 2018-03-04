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
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcertx.ia32.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.compcertx.ErrorMonad.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Export liblayers.compcertx.Stencil.
Require Export liblayers.compcertx.MemWithData.
Require Export liblayers.compat.CompatData.
Require Export liblayers.compat.CompatPrimSem.
Require Export liblayers.compat.CompatLayerDef.
Require Import liblayers.compcertx.Observation.

Section WITH_MEMORY_MODEL.
  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.

  (** * Extra interface *)

  Section POINTWISE.

  Local Existing Instance ptree_layer_sim_op.
  Local Existing Instance ptree_layer_ops.
  Local Existing Instance ptree_layer_prf.

  (** FIXME: those are theorems about [ptree_layer] *)
  Lemma cl_layer_pointwise D1 D2 (R: freerg compatrel D1 D2) L1 L2:
    sim R (cl_base_layer L1) (cl_base_layer L2) <->
    (forall (i: ident),
       res_le (option_le (compatsim R))
         (get_layer_primitive i L1)
         (get_layer_primitive i L2)) /\
     (forall (i: ident),
        res_le (option_le eq)
         (get_layer_globalvar i L1)
         (get_layer_globalvar i L2)).
  Proof.
    simpl.
    generalize (cl_base_layer L1) (cl_base_layer L2); clear L1 L2.
    intros L1 L2.
    split.
    * intros H.
      simpl.
      split; solve_monotonic.
      simpl.
      eassumption.
    * intros [Hfun Hvar].
      destruct L1 as [L1p L1v], L2 as [L2p L2v].
      Local Transparent ptree_layer_ops.
      constructor; intro i;
      specialize (Hfun i);
      specialize (Hvar i);
      simpl in *;
      unfold ptree_layer_primitive, ptree_layer_globalvar in *; simpl in *.
      Local Opaque ptree_layer_ops.
      + destruct (Maps.PTree.get i L1p) as [[|]|];
        destruct (Maps.PTree.get i L2p) as [[|]|];
        simpl in *;
        inversion Hfun as [x1 x2 Hx | ]; try inversion Hx; subst;
        solve_monotonic.
      + destruct (Maps.PTree.get i L1v) as [[|]|];
        destruct (Maps.PTree.get i L2v) as [[|]|];
        simpl in *;
        inversion Hvar as [x1 x2 Hx | ]; try inversion Hx; subst;
        solve_monotonic.
  Qed.

  (** FIXME: those are theorems about [ptree_layer] *)
  Lemma cl_le_layer_pointwise D (L1 L2: compatlayer D):
    sim id (cl_base_layer L1) (cl_base_layer L2) <->
    (forall (i: ident),
       res_le (option_le (compatsem_le D))
         (get_layer_primitive i L1)
         (get_layer_primitive i L2)) /\
     (forall (i: ident),
        res_le (option_le eq)
         (get_layer_globalvar i L1)
         (get_layer_globalvar i L2)).
  Proof.
    apply cl_layer_pointwise.
  Qed.

  (** FIXME: those are theorems about [ptree_layer] *)
  Lemma cl_sim_layer_pointwise D1 D2 (R: compatrel D1 D2) L1 L2:
    sim (freerg_inj _ _ _ R) (cl_base_layer L1) (cl_base_layer L2) <->
    (forall (i: ident),
       res_le (option_le (compatsim (freerg_inj _ _ _ R)))
         (get_layer_primitive i L1)
         (get_layer_primitive i L2)) /\
     (forall (i: ident),
        res_le (option_le eq)
         (get_layer_globalvar i L1)
         (get_layer_globalvar i L2)).
  Proof.
    apply cl_layer_pointwise.
  Qed.

  End POINTWISE.

  (** * Properties of LayerOK *)

  Lemma get_layer_primitive_mapsto_le_ok
        {D}
        (L: compatlayer D)
        {HOK: LayerOK L}
        i (σ: compatsem D)
        (Hle: (i ↦ σ) ≤ L):
    exists σ',
      get_layer_primitive i L = OK (Some σ') /\
      compatsem_le _ σ σ'.
  Proof.
    generalize (get_layer_primitive_sim_monotonic _ _ _ i _ _ Hle).
    rewrite get_layer_primitive_mapsto.
    inversion 1; subst.
    * inversion H2; subst.
      eauto.
    * exfalso. destruct (HOK i) as [[σ' Hσ'] _ _].
      simpl in *.
      congruence.
  Qed.

  Lemma get_layer_globalvar_mapsto_le_ok
        {D}
        (L: compatlayer D)
        {HOK: LayerOK L}
        i (τ: globvar (Ctypes.type))
        (Hle: (i ↦ τ) ≤ L):
    get_layer_globalvar i L = OK (Some τ).
  Proof.
    generalize (get_layer_globalvar_sim_monotonic _ _ _ i _ _ Hle).
    rewrite get_layer_globalvar_mapsto.
    inversion 1; subst.
    * inversion H2; subst.
      symmetry; assumption.
    * exfalso. destruct (HOK i) as [_ [τ' Hτ'] _].
      simpl in *.
      congruence.
  Qed.


  (** * Primitive names *)

  (** In our layers, we need to make sure that the names associated
    with specifications match the identifier which they appear under.
    To this end we define this checkable property. *)

  Class LayerNamesMatch D (L: compatlayer D) :=
    {
      layer_names_match_ok :>
        LayerOK L;
      layer_names_match i j σ:
        get_layer_primitive i L = OK (Some (compatsem_inr σ)) ->
        sprimcall_name D σ = Some j ->
        i = j
    }.

  Global Instance layer_names_match_sim:
    Proper (∀ R, cl_sim _ _ R --> impl) LayerNamesMatch.
  Proof.
    intros D2 D1 R L2 L1 HL [HOK2 Hnames2].
    unfold flip in *.
    split.
    * eapply layer_ok_sim_antitonic;
      try eassumption.
    * intros i j σ Hi Hj.
      destruct (HOK2 i) as [[σ2 Hσ2] _ _].
      specialize (Hnames2 i j).
      pose proof (get_layer_primitive_sim_monotonic D1 D2 R i L1 L2 HL).
      destruct R; simpl in *.
      + destruct H as [_ _ [ | _ _ [|]] | ]; try discriminate.
        inversion Hi; subst; clear Hi.
        specialize (Hnames2 y eq_refl).
        destruct H as [_ Hσy _].
        destruct Hσy; try discriminate.
        apply Hnames2.
        congruence.
      + destruct H as [_ _ [ | _ _ [| |]] | ]; try discriminate.
        inversion Hi; subst; clear Hi.
        specialize (Hnames2 sem2 eq_refl).
        destruct H as [_ _ _ Hσy _].
        destruct Hσy; try discriminate.
        apply Hnames2.
        congruence.
  Qed.

  (** The decision procedure is easier to write for this alternative
    definition. *)
  Definition LayerNamesMatch_alt D L :=
    LayerOK L /\
    forall i,
      get_layer_primitive i L <> OK None ->
      ((fun i =>
          forall j σ,
            get_layer_primitive i L = OK (Some (compatsem_inr σ)) ->
            sprimcall_name D σ = Some j ->
            i = j)
       i).

  Instance layer_names_match_alt_dec D L:
    Decision (LayerNamesMatch_alt D L).
  Proof.
    apply and_dec; [typeclasses eauto | ].
    apply layer_decide_primitive_name.
    intros i.
    destruct (get_layer_primitive i L) as [[[|σ]|]|];
      [ left | | left .. ];
      try abstract discriminate.
    unfold compatsem_inr.
    destruct (sprimcall_name D σ) as [j|] eqn:Hj.
    * destruct (decide (i = j)) as [Hij | Hij].
      + left. abstract congruence.
      + right. abstract eauto.
    * left. abstract congruence.
  Defined.

  Lemma layer_names_match_alt_equiv D L:
    LayerNamesMatch_alt D L <->
    LayerNamesMatch D L.
  Proof.
    split.
    * intros [HOK Hnames].
      split; eauto.
      intros i j σ Hi Hj.
      eapply Hnames; eauto.
      congruence.
    * intros [HOK Hnames].
      split; eauto.
  Qed.

  Global Instance layers_names_match_dec D L:
    Decision (LayerNamesMatch D L).
  Proof.
    apply (decide_rewrite _ _ (layer_names_match_alt_equiv D L)).
    typeclasses eauto.
  Defined.

  (** Quick test. *)

  Goal
    forall D, LayerNamesMatch D ∅.
  Proof.
    intro.
    decision.
  Qed.


  (** * Matching initial states *)

  Require Import MakeProgram.

  Record cl_init_sim_mem D1 D2 (R: compatrel D1 D2) (s: stencil) (m2: mem) :=
    {
      cl_init_sim_relate:
        relate_AbData s (Mem.flat_inj (genv_next s)) empty_data empty_data;
      cl_init_sim_match:
        match_AbData s empty_data m2 (Mem.flat_inj (genv_next s))
    }.

  Section WITH_PROGRAM.

    Context `{Fm: Type}.
    Context `{Fp: Type}.
    Context `{Vp: Type}.
    Context `{Hmodule: Modules AST.ident Fm (globvar Ctypes.type)}.
    Context `{mkp_fmt_ops: !ProgramFormatOps Fm Ctypes.type Fp Vp}.
    Context `{mkp_fmt: !ProgramFormat Fm Ctypes.type Fp Vp}.
    Context `{mkp_ops: !MakeProgramOps Fm Ctypes.type Fp Vp}.
    Context `{Hmkp: !MakeProgram Fm Ctypes.type Fp Vp}.

    Require Import InitMem.

    Record cl_init_sim_def D1 D2 R (L1: compatlayer D1) (M: module) (L2: compatlayer D2) :=
      {
        cl_init_sim_init_mem:
          forall (s: stencil) (CTXT: module) (m2: mem),
            (p <- make_program s (CTXT ⊕ M) L2; ret (Genv.init_mem p) = OK (Some m2)) ->
            cl_init_sim_mem D1 D2 R s m2;

        cl_init_sim_glbl:
          forall i,
            List.In i new_glbl ->
            isOKNone (get_layer_globalvar i L1);

        cl_init_sim_glbl_prim:
          forall i,
            List.In i new_glbl ->
            isOKNone (get_layer_primitive i L1);

        cl_init_sim_glbl_module:
          forall i,
            List.In i new_glbl ->
            exists vi, get_module_variable i M = OK (Some vi);

        cl_init_sim_M:
          forall {F V} (ge: Genv.t F V) i vi,
          get_module_variable i M = OK (Some vi) ->
          Genv.init_data_list_valid ge 0 (gvar_init vi) = true;

        cl_init_sim_low:
          forall i,
            isOKNone (get_layer_globalvar i L2)

      }.

    Definition cl_init_sim D1 D2 (R: freerg compatrel D1 D2):
      compatlayer D1 -> module -> compatlayer D2 -> Prop :=
      match R with
        | freerg_id => fun _ _ _ => False
        | freerg_inj D2 R => cl_init_sim_def D1 D2 R
      end.

    Lemma cl_init_sim_intro D1 D2 R (L1: compatlayer D1) (M: module) (L2: compatlayer D2):
      (forall (s: stencil) (CTXT: module) (m2: mem),
         (p <- make_program s (CTXT ⊕ M) L2; ret (Genv.init_mem p)) = OK (Some m2) ->
         cl_init_sim_mem D1 D2 R s m2) ->
      (forall i,
         List.In i new_glbl ->
         isOKNone (get_layer_globalvar i L1)) ->
      (forall i,
         List.In i new_glbl ->
         isOKNone (get_layer_primitive i L1)) ->
      (forall i,
         List.In i new_glbl ->
         exists vi, get_module_variable i M = OK (Some vi)) ->
      (forall {F V} (ge: Genv.t F V)  i vi,
         get_module_variable i M = OK (Some vi) ->
         Genv.init_data_list_valid ge 0 (gvar_init vi) = true) ->
      (forall i,
         isOKNone (get_layer_globalvar i L2)) ->
      cl_init_sim D1 D2 (freerg_inj _ _ _ R) L1 M L2.
    Proof.
      intros H1 H2.
      split.
      * intros.
        eauto.
      * intros i Hi.
        eauto.
      * intros. eauto.
      * intros. eauto.
      * intros. eauto.
      * intros. eauto.
    Qed.

  End  WITH_PROGRAM.

(** Validity of stencils for primitives *)

Definition compatsem_valid {D} (p: compatsem D) (s: stencil) : bool :=
  match p with
    | inl pe => sextcall_valid pe s
    | inr pp => sprimcall_valid pp s
  end.

Definition get_layer_prim_valid `{D: compatdata} (L: compatlayer D) (s: stencil):=
  forall (i: ident) (p: compatsem D), 
    get_layer_primitive (V:= globvar Ctypes.type) i L = OK (Some p) 
    -> compatsem_valid p s = true.

Global Instance prim_valid_dec: forall (D: compatdata) (L: compatlayer D) (s: stencil),
                                 Decision.Decision (get_layer_prim_valid L s).
Proof.
  intros.
  unfold get_layer_prim_valid.
  change (forall i p,
            get_layer_primitive i L = OK (Some p) -> compatsem_valid p s = true)
  with (forall i, (fun l => forall p, l = OK (Some p) -> compatsem_valid p s = true) (get_layer_primitive i L)).
  apply layer_decide_primitive.
  intros.
  destruct σ as [[|]|].
  - destruct (compatsem_valid c s) eqn:?; intros.
    + left. intros. inversion H; subst. assumption.
    + right. red; intros. specialize (H _ refl_equal).
      congruence.
  - left. intros. discriminate.
  - left. intros. discriminate.
Defined.

End WITH_MEMORY_MODEL.

(*
Hint Extern 10 (LayerNamesMatch _ _) => decision : typeclass_instances.
*)
