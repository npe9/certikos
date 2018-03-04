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
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Export liblayers.lib.OptionMonad.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.Semantics.
Require Import liblayers.compcertx.CompcertStructures.
Require Export liblayers.compcertx.ErrorMonad.
Require Export liblayers.compcertx.Stencil.
Require liblayers.compcertx.InitMem.

(** ** Prerequisites *)
 
(** The class below specifies the prerequisites for our implementation
  of [MakeProgram]. Basically, we need to know how to convert the
  definition in modules and layers into Compcert program definitions.

  Note that the types of function and variable definitions in the
  produced program are not always related to the types of definitions
  in our modules and layers. For instance, in order to be able to use
  our layers to construct C as well as assembly programs, their global
  variable definitions need to store C-style typing information. When
  building assembly programs they will be converted into low-level
  types. Hence, we need to distinguish between to output program types
  [Fp] and [Vp], and the types used in the module and layer [Fm] and [Vm]. *)

Class ProgramFormatOps {layerdata} (Fm Vm Fp Vp: Type)
    `{module_ops: ModuleOps AST.ident Fm (AST.globvar Vm)}
    `{layer_ops: LayerOps layerdata AST.ident (V := AST.globvar Vm)} :=
  {
    make_internal: Fm -> res Fp;
    make_external {D}: AST.ident -> primsem D -> res Fp;
    make_varinfo: Vm -> Vp
  }.

Class ProgramFormat {layerdata simrel} Fm Vm Fp Vp
  `{pf_ops: ProgramFormatOps layerdata Fm Vm Fp Vp}
  `{rg_ops: !ReflexiveGraphOps layerdata simrel}
  `{psim_ops: Sim layerdata simrel primsem}
  `{lsim_ops: Sim layerdata simrel layer} :=
  {
    make_external_monotonic {D} :>
      Proper (eq ==> (≤) ++> res_le eq) (make_external (D:=D))
  }.

(** From there, the code in [StencilImpl] can build instances of the
  following classes. *)

Class MakeProgramOps {layerdata} Fm Vm Fp Vp
    `{progfmt: ProgramFormatOps layerdata Fm Vm Fp Vp}
    `{stencil_ops: StencilOps} :=
  {
    make_program {D}: stencil -> module -> layer D -> res (AST.program Fp Vp)
  }.

Definition globvar_map {Vm Vp} (f: Vm -> Vp) gt :=
  {|
    AST.gvar_info := f (AST.gvar_info gt);
    AST.gvar_init := AST.gvar_init gt;
    AST.gvar_readonly := AST.gvar_readonly gt;
    AST.gvar_volatile := AST.gvar_volatile gt
  |}.

Definition make_globalenv `{mkp_ops: MakeProgramOps} {D} γ (M: module) (L: layer D) :=
  p <- make_program γ M L;
  ret (Genv.globalenv p).

Class MakeProgram {layerdata simrel} Fm Vm Fp Vp
    `{mkp_ops: MakeProgramOps layerdata Fm Vm Fp Vp}
    `{rg_ops: !ReflexiveGraphOps layerdata simrel}
    `{psim_ops: !Sim simrel primsem}
    `{lsim_ops: !Sim simrel layer} :=
  {
      make_globalenv_stencil_matches {D} (γ: stencil) (M: module) (L: layer D) ge:
        make_globalenv γ M L = ret ge ->
        stencil_matches γ ge;

      make_globalenv_external {D} (γ: stencil) (i: AST.ident) (σ: primsem D) ge:
        make_globalenv γ ∅ (i ↦ σ) = ret ge ->
        exists σdef b,
          make_external i σ = OK σdef /\
          Genv.find_symbol ge i = Some b /\
          Genv.find_funct_ptr ge b = Some σdef;

      make_globalenv_internal {D} (γ: stencil) (i: AST.ident) (f: Fm) ge:
        make_globalenv (D:=D) γ (i ↦ f) ∅ = ret ge ->
        exists fdef b,
          make_internal f = OK fdef /\
          Genv.find_symbol ge i = Some b /\
          Genv.find_funct_ptr ge b = Some fdef;

      make_globalenv_module_globvar {D} (γ: stencil) (i: AST.ident) (τ: AST.globvar Vm) ge:
        make_globalenv (D:=D) γ (i ↦ τ) ∅ = ret ge ->
        exists b,
          Genv.find_symbol ge i = Some b /\
          Genv.find_var_info ge b = Some (globvar_map make_varinfo τ);

      make_globalenv_layer_globvar {D: layerdata} (γ: stencil) (i: AST.ident) (τ: AST.globvar Vm) ge:
        make_globalenv (D:=D) γ ∅ (i ↦ τ) = ret ge ->
        exists b,
          Genv.find_symbol ge i = Some b /\
          Genv.find_var_info ge b = Some (globvar_map make_varinfo τ);

      make_program_monotonic {D} :>
        Proper (- ==> (≤) ++> (≤) ++> res_le program_le) (make_program (D:=D))
      ;

      make_program_sim_monotonic :>
        Proper
          (∀ R, - ==> sim R ++> res_le eq)
          (fun D => make_external (D := D)) ->
        Proper
          (∀ R, - ==> (≤) ++> sim R ++> res_le program_le)
          (fun D => make_program (D:=D))
      ;

      make_program_get_module_function_prop {D} s M L i f:
        isOK (make_program (D := D) s M L) ->
        get_module_function i M = OK (Some f) ->
        isOK (make_internal f) /\
        isOKNone (get_layer_primitive i L) /\
        isOKNone (get_layer_globalvar i L)
      ;

      make_program_get_module_variable_prop {D} s M L i v:
        isOK (make_program (D := D) s M L) ->
        get_module_variable i M = OK (Some v) ->
        gvar_volatile v = false /\
        isOKNone (get_layer_primitive i L) /\
        isOKNone (get_layer_globalvar i L)
      ;

      make_program_get_layer_primitive_prop {D} s M L i f:
        isOK (make_program (D := D) s M L) ->
        get_layer_primitive i L = OK (Some f) ->
        isOK (make_external i f) /\
        isOKNone (get_module_function i M) /\
        isOKNone (get_module_variable i M)
      ;

      make_program_get_layer_globalvar_prop {D} s M L i v:
        isOK (make_program (D := D) s M L) ->
        get_layer_globalvar i L = OK (Some v) ->
        gvar_volatile v = false /\
        isOKNone (get_module_function i M) /\
        isOKNone (get_module_variable i M)
      ;

      make_program_gfun {D} s M L p i f :
        make_program (D := D) s M L = OK p ->
        In (i, Some (Gfun f)) (prog_defs p) ->
        (exists fi,
           get_module_function i M = OK (Some fi) /\
           make_internal fi = OK f) \/
        (exists fe,
           get_layer_primitive i L = OK (Some fe) /\
           make_external i fe = OK f)
      ;

      make_globalenv_find_funct_ptr {D} s M L ge b f :
        make_globalenv (D := D) s M L = OK ge ->
        Genv.find_funct_ptr ge b = Some f ->
        exists i,
          Genv.find_symbol ge i = Some b /\
          (
            (exists fi,
               get_module_function i M = OK (Some fi) /\
               make_internal fi = OK f) \/
            (exists fe,
               get_layer_primitive i L = OK (Some fe) /\
               make_external i fe = OK f)
          )
      ;

      make_program_gvar {D} s M L p i v :
        make_program (D := D) s M L = OK p ->
        In (i, Some (Gvar v)) (prog_defs p) ->
        exists vi,
          globvar_map make_varinfo vi = v /\
          (
            get_module_variable i M = OK (Some vi) \/
            get_layer_globalvar i L = OK (Some vi)
          )
      ;

      make_globalenv_find_var_info {D} s M L ge b v :
        make_globalenv (D := D) s M L = OK ge ->
        Genv.find_var_info ge b = Some v ->
        exists i,
          Genv.find_symbol ge i = Some b /\
          (
            exists vi,
              globvar_map make_varinfo vi = v /\
              (
                get_module_variable i M = OK (Some vi)
                \/
                get_layer_globalvar i L = OK (Some vi)
              )
          )
      ;

      make_program_get_module_function {D} s M L p i fi f:
        make_program (D := D) s M L = OK p ->
        get_module_function i M = OK (Some fi) ->
        make_internal fi = OK f ->
        In (i, Some (Gfun f)) (prog_defs p)
      ;

      make_globalenv_get_module_function {D} s M L ge i fi f:
        make_globalenv (D := D) s M L = OK ge ->
        get_module_function i M = OK (Some fi) ->
        make_internal fi = OK f ->
        exists b,
          Genv.find_symbol ge i = Some b /\
          Genv.find_funct_ptr ge b = Some f
      ;

      make_program_get_module_variable {D} s M L p i v:
        make_program (D := D) s M L = OK p ->
        get_module_variable i M = OK (Some v) ->
        In (i, Some (Gvar (globvar_map make_varinfo v))) (prog_defs p)
      ;

      make_globalenv_get_module_variable {D} s M L ge i v:
        make_globalenv (D := D) s M L = OK ge ->
        get_module_variable i M = OK (Some v) ->
        exists b,
          Genv.find_symbol ge i = Some b /\
          Genv.find_var_info ge b = Some (globvar_map make_varinfo v)
      ;

      make_program_get_layer_primitive {D} s M L p i fe f:
        make_program (D := D) s M L = OK p ->
        get_layer_primitive i L = OK (Some fe) ->
        make_external i fe = OK f ->
        In (i, Some (Gfun f)) (prog_defs p)
      ;

      make_globalenv_get_layer_primitive {D} s M L ge i fe f:
        make_globalenv (D := D) s M L = OK ge ->
        get_layer_primitive i L = OK (Some fe) ->
        make_external i fe = OK f ->
        exists b,
          Genv.find_symbol ge i = Some b /\
          Genv.find_funct_ptr ge b = Some f
      ;

      make_program_get_layer_globalvar {D} s M L p i v:
        make_program (D := D) s M L = OK p ->
        get_layer_globalvar i L = OK (Some v) ->
        In (i, Some (Gvar (globvar_map make_varinfo v))) (prog_defs p)
      ;

      make_globalenv_get_layer_globalvar {D} s M L ge i v:
        make_globalenv (D := D) s M L = OK ge ->
        get_layer_globalvar i L = OK (Some v) ->
        exists b,
          Genv.find_symbol ge i = Some b /\
          Genv.find_var_info ge b = Some (globvar_map make_varinfo v)
      ;

      make_program_layer_ok {D} s M L:
        isOK (make_program (D := D) s M L) ->
        LayerOK L
      ;

      make_program_module_ok {D} s M L:
        isOK (make_program (D := D) s M L) ->
        ModuleOK M
      ;

      make_program_module_layer_disjoint {D} s M L:
        isOK (make_program (D:=D) s M L) ->
        module_layer_disjoint M L
      ;

      make_program_exists {D} (L: _ D) M s:
        LayerOK L ->
        ModuleOK M ->
        (forall i fe, get_layer_primitive i L = OK (Some fe) ->
                      isOK (make_external i fe) /\
                      isOKNone (get_module_function i M) /\
                      isOKNone (get_module_variable i M)) ->
        (forall i fi, get_module_function i M = OK (Some fi) ->
                      isOK (make_internal fi) /\
                      isOKNone (get_layer_primitive i L) /\
                      isOKNone (get_layer_globalvar i L)) ->
        (forall i v, get_layer_globalvar i L = OK (Some v) ->
                     gvar_volatile v = false /\
                     isOKNone (get_module_function i M) /\
                     isOKNone (get_module_variable i M)) ->
        (forall i v, get_module_variable i M = OK (Some v) ->
                     gvar_volatile v = false /\
                     isOKNone (get_layer_primitive i L) /\
                     isOKNone (get_layer_globalvar i L)) ->
        (forall i p,
           get_layer_primitive i L = OK (Some p) ->
           isSome (find_symbol s i)) ->
        (forall i v,
           get_layer_globalvar i L = OK (Some v) ->
           isSome (find_symbol s i)) ->
        (forall i f,
           get_module_function i M = OK (Some f) ->
           isSome (find_symbol s i)) ->
        (forall i v,
           get_module_variable i M = OK (Some v) ->
           isSome (find_symbol s i)) ->
        isOK (make_program s M L)

      ;

      make_program_init_mem_le
        {D1 D2} (L1: layer D1) (L2: layer D2)
        (M1 M2: module) s (p1 p2: _)
        (function_domains:
           forall i,
             (~ isOKNone (get_layer_primitive i L1) \/ ~ isOKNone (get_module_function i M1)) ->
             (~ isOKNone (get_layer_primitive i L2) \/ ~ isOKNone (get_module_function i M2)))
        (variable_domains:
           forall i v,
             (get_layer_globalvar i L1 = OK (Some v) \/ get_module_variable i M1 = OK (Some v)) ->
             (get_layer_globalvar i L2 = OK (Some v) \/ get_module_variable i M2 = OK (Some v)))
        (prog1: make_program s M1 L1 = OK p1)
        (prog2: make_program s M2 L2 = OK p2)
      :
        InitMem.prog_defs_le (prog_defs p1) (prog_defs p2);

      make_program_prog_main
        {D} (L: layer D)
        (M: module) s (p: _)
        (prog: make_program s M L = OK p)
      :
        (prog_main p) = xH;

      make_program_var_transfer {D} (L: _ D) M s v τ
          (OKLayer: LayerOK (L ⊕ v ↦ τ)) p:
          make_program s (M ⊕ v ↦ τ) L = ret p ->
          make_program s M (L  ⊕ v ↦ τ) = ret p

  }.

Global Instance make_globalenv_monotonic `{MakeProgram} {D}:
  Proper (- ==> (≤) ++> (≤) ++> res_le (≤)) (make_globalenv (D:=D)).
Proof.
  unfold make_globalenv.
  solve_monotonicity.
Qed.


(** * The [inv_make_globalenv] tactic *)

(** The tactic defined in the following decomposes a hypothesis of the
  form [make_globalenv s M L = ret ge] into statements abour the
  blocks, variables and functions mapped by the global environment [ge].
  First, assuming [M] and [L] are of the form [i_1 ↦ d_1 ⊕ ⋯ ⊕ i_n ↦ d_n],
  the hypothesis is split recursively along [⊕] until hypotheses of
  the forms [make_globalenv s (i ↦ d) ∅ = ret ge'] or
  [make_globalenv s ∅ (i ↦ d) = ret ge'] are obtained, with [ge' ≤ ge].
  Then, the monotonicity of [make_globalenv] is exploited to convert
  those into, for example, [find_symbol ge i = Some b] and
  [find_var_info ge b = Some d].

  This is useful when doing proofs about actual code, since the
  Compcert semantics are expressed in terms of global environments
  rather than in terms of stencils. *)

Section PROPERTIES.
  Context `{Hmp: MakeProgram}.
  Context `{Hdata: !ReflexiveGraph layerdata simrel}.
  Context `{Hlayer: !Layers AST.ident primsem (AST.globvar Vm) layer}.
  Context `{Hmodule: !Modules AST.ident Fm (AST.globvar Vm) module}.

  Lemma make_program_make_globalenv {D} s (M: module) (L: layer D) p:
    make_program s M L = ret p ->
    make_globalenv s M L = ret (Genv.globalenv p).
  Proof.
    intros H.
    unfold make_globalenv.
    rewrite H.
    reflexivity.
  Qed.

  Lemma make_globalenv_split_module_left {D} s M1 M2 (L: _ D) ge:
    make_globalenv s (M1 ⊕ M2) L = ret ge ->
    exists ge1,
      make_globalenv s M1 L = ret ge1 /\
      ge1 ≤ ge.
  Proof.
    intros Hge.
    assert (HL: L ≤ L) by reflexivity.
    assert (HM1: M1 ≤ M1 ⊕ M2) by apply left_upper_bound.
    pose proof (make_globalenv_monotonic s _ _ HM1 _ _ HL) as Hge1.
    rewrite Hge in Hge1.
    inversion Hge1 as [ge1 xge Hge_ge1 Hge1' Hxge | ].
    exists ge1; intuition congruence.
  Qed.

  Lemma make_globalenv_split_module_right {D} s M1 M2 (L: _ D) ge:
    make_globalenv s (M1 ⊕ M2) L = ret ge ->
    exists ge2,
      make_globalenv s M2 L = ret ge2 /\
      ge2 ≤ ge.
  Proof.
    intros Hge.
    assert (HL: L ≤ L) by reflexivity.
    assert (HM2: M2 ≤ M1 ⊕ M2) by apply right_upper_bound.
    pose proof (make_globalenv_monotonic s _ _ HM2 _ _ HL) as Hge2.
    rewrite Hge in Hge2.
    inversion Hge2 as [ge2 xge Hge_ge2 Hge2' Hxge | ].
    exists ge2; intuition congruence.
  Qed.

  Lemma make_globalenv_split_module {D} s M1 M2 (L: _ D) ge:
    make_globalenv s (M1 ⊕ M2) L = ret ge ->
    exists ge1 ge2,
      (make_globalenv s M1 L = ret ge1 /\ ge1 ≤ ge) /\
      (make_globalenv s M2 L = ret ge2 /\ ge2 ≤ ge).
  Proof.
    intros Hge.
    generalize Hge.
    intro Hge'.
    apply make_globalenv_split_module_left in Hge.
    apply make_globalenv_split_module_right in Hge'.
    destruct Hge as [? [? ?]].
    destruct Hge' as [? [? ?]].
    eauto 10.
  Qed.


  Lemma make_globalenv_split_layer_left {D} s M (L1 L2: _ D) ge:
    make_globalenv s M (L1 ⊕ L2) = ret ge ->
    exists ge1,
      make_globalenv s M L1 = ret ge1 /\
      ge1 ≤ ge.
  Proof.
    intros Hge.
    assert (HM: M ≤ M) by reflexivity.
    assert (HL1: L1 ≤ L1 ⊕ L2) by apply left_upper_bound.
    pose proof (make_globalenv_monotonic s _ _ HM _ _ HL1) as Hge1.
    rewrite Hge in Hge1.
    inversion Hge1 as [ge1 xge Hge_ge1 Hge1' Hxge | ].
    exists ge1; intuition congruence.
  Qed.

  Lemma make_globalenv_split_layer_right {D} s M (L1 L2: _ D) ge:
    make_globalenv s M (L1 ⊕ L2) = ret ge ->
    exists ge2,
      make_globalenv s M L2 = ret ge2 /\
      ge2 ≤ ge.
  Proof.
    intros Hge.
    assert (HM: M ≤ M) by reflexivity.
    assert (HL2: L2 ≤ L1 ⊕ L2) by apply right_upper_bound.
    pose proof (make_globalenv_monotonic s _ _ HM _ _ HL2) as Hge2.
    rewrite Hge in Hge2.
    inversion Hge2 as [ge2 xge Hge_ge2 Hge2' Hxge | ].
    exists ge2; intuition congruence.
  Qed.

  Lemma make_globalenv_split_layer {D} s M (L1 L2: _ D) ge:
    make_globalenv s M (L1 ⊕ L2) = ret ge ->
    exists ge1 ge2,
      (make_globalenv s M L1 = ret ge1 /\ ge1 ≤ ge) /\
      (make_globalenv s M L2 = ret ge2 /\ ge2 ≤ ge).
  Proof.
    intros Hge.
    generalize Hge.
    intro Hge'.
    apply make_globalenv_split_layer_left in Hge.
    apply make_globalenv_split_layer_right in Hge'.
    destruct Hge as [? [? ?]].
    destruct Hge' as [? [? ?]].
    eauto 10.
  Qed.

  Lemma make_globalenv_split_module_layer {D} s M L ge:
    make_globalenv s M L = ret ge ->
    exists geM geL,
      (make_globalenv (D:=D) s M ∅ = ret geM /\ geM ≤ ge) /\
      (make_globalenv (D:=D) s ∅ L = ret geL /\ geL ≤ ge).
  Proof.
    intros Hge.
    assert (HM: res_le (≤) (make_globalenv (D:=D) s M ∅) (ret ge)).
      rewrite <- Hge; clear Hge.
      apply make_globalenv_monotonic.
      reflexivity.
      apply lower_bound.
    assert (HL: res_le (≤) (make_globalenv (D:=D) s ∅ L) (ret ge)).
      rewrite <- Hge; clear Hge.
      apply make_globalenv_monotonic.
      apply lower_bound.
      reflexivity.
    inversion HM; subst.
    inversion HL; subst.
    exists x, x0.
    eauto.
  Qed.
End PROPERTIES.

Ltac inv_make_globalenv_leaftac Hge Hgele :=
  match type of Hge with
    (** Module function *)
    | make_globalenv (D:=?D) ?s (?i ↦ ?f) ∅ = ret ?ge =>
      let κdef := fresh "κdef" in
      let b := fresh "b" in
      let Hκdef := fresh "H" κdef in
      let Hbfs := fresh "H" b "fs" in
      let Hbfp := fresh "H" b "fp" in
      let H := fresh "H" in
      pose proof (make_globalenv_internal (D:=D) s i f ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as (κdef & b & Hκdef & Hbfs & Hbfp);
      try (injection Hκdef; clear Hκdef; intro; subst κdef);
      apply (genv_le_find_symbol_some _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_funct_ptr_some _ _ _ _ Hgele) in Hbfp;
      clear ge Hgele

    (** Module variable *)
    | make_globalenv (D:=?D) ?s (?i ↦ ?τ) ∅ = ret ?ge =>
      let b := fresh "b" in
      let Hbfs := fresh "H" b "fs" in
      let Hbvi := fresh "H" b "vi" in
      let H := fresh "H" in
      pose proof (make_globalenv_module_globvar (D:=D) s i τ ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as [b [Hbfs Hbvi]];
      apply (genv_le_find_symbol_some _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_var_info_some _ _ _ _ Hgele) in Hbvi;
      clear ge Hgele

    (** Layer primitive *)
    | make_globalenv (D:=?D) ?s ∅ (?i ↦ ?σ) = ret ?ge =>
      let σdef := fresh "σdef" in
      let b := fresh "b" in
      let Hσdef := fresh "H" σdef in
      let Hbfs := fresh "H" b "fs" in
      let Hbfp := fresh "H" b "fp" in
      let H := fresh "H" in
      pose proof (make_globalenv_external (D:=D) s i σ ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as (σdef & b & Hσdef & Hbfs & Hbfp);
      try (injection Hσdef; clear Hσdef; intro; subst σdef);
      apply (genv_le_find_symbol_some _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_funct_ptr_some _ _ _ _ Hgele) in Hbfp;
      clear ge Hgele

    (** Layer variable *)
    | make_globalenv (D:=?D) ?s ∅ (?i ↦ ?τ) = ret ?ge =>
      let b := fresh "b" in
      let Hbfs := fresh "H" b "fs" in
      let Hbvi := fresh "H" b "vi" in
      let H := fresh "H" in
      pose proof (make_globalenv_layer_globvar (D:=D) s i τ ge) as H;
      apply H in Hge;
      clear H;
      destruct Hge as [b [Hbfs Hbvi]];
      apply (genv_le_find_symbol_some _ _ _ _ Hgele) in Hbfs;
      apply (genv_le_find_var_info_some _ _ _ _ Hgele) in Hbvi;
      clear ge Hgele

    | _ => idtac
  end.

Ltac inv_make_globalenv_split_layer leaftac HLge Hgele :=
  match type of HLge with
    | make_globalenv ?s ?M (?L1 ⊕ ?L2) = ret ?ge =>
      let ge1 := fresh "ge0" in
      let ge2 := fresh "ge0" in
      let HLge1 := fresh "HL" ge1 in
      let HLge2 := fresh "HL" ge2 in
      let Hge1le := fresh "HL" ge1 "le" in
      let Hge2le := fresh "HL" ge2 "le" in
      destruct (make_globalenv_split_layer s M L1 L2 ge HLge)
        as [ge1 [ge2 [[HLge1 Hge1le] [HLge2 Hge2le]]]];
      clear HLge;
      try rewrite Hgele in Hge1le;
      try rewrite Hgele in Hge2le;
      clear ge Hgele;
      inv_make_globalenv_split_layer leaftac HLge1 Hge1le;
      inv_make_globalenv_split_layer leaftac HLge2 Hge2le

    | _ =>
      leaftac HLge Hgele
  end.

Ltac inv_make_globalenv_split_module leaftac HMge Hgele :=
  match type of HMge with
    | make_globalenv ?s (?M1 ⊕ ?M2) ?L = ret ?ge =>
      let ge1 := fresh "ge0" in
      let ge2 := fresh "ge0" in
      let HMge1 := fresh "HM" ge1 in
      let HMge2 := fresh "HM" ge2 in
      let Hge1le := fresh "HM" ge1 "le" in
      let Hge2le := fresh "HM" ge2 "le" in
      destruct (make_globalenv_split_module s M1 M2 L ge HMge)
        as [ge1 [ge2 [[HMge1 Hge1le] [HMge2 Hge2le]]]];
      clear HMge;
      try rewrite Hgele in Hge1le;
      try rewrite Hgele in Hge2le;
      clear ge Hgele;
      inv_make_globalenv_split_module leaftac HMge1 Hge1le;
      inv_make_globalenv_split_module leaftac HMge2 Hge2le

    | _ =>
      leaftac HMge Hgele
  end.

Ltac inversion_make_globalenv H :=
  match type of H with
    | make_globalenv ?s ?M ?L = ret ?ge =>
      let geM := fresh "geM" in
      let geL := fresh "geL" in
      let HgeM := fresh "H" geM in
      let HgeL := fresh "H" geL in
      let HgeMle := fresh "H" geM "le" in
      let HgeLle := fresh "H" geL "le" in
      destruct (make_globalenv_split_module_layer s M L ge H)
        as [geM [geL [[HgeM HgeMle] [HgeL HgeLle]]]];
      inv_make_globalenv_split_module inv_make_globalenv_leaftac HgeM HgeMle;
      inv_make_globalenv_split_layer inv_make_globalenv_leaftac HgeL HgeLle
  end.

Ltac inv_make_globalenv H :=
  inversion_make_globalenv H;
  clear H.
