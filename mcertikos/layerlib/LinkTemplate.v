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
Require Export LinkSourceTemplate.
Require Export MakeProgram.
Require Import Behavior.

Global Opaque Structures.semof.
Global Opaque Structures.oplus.
Global Opaque Structures.emptyset.
Global Opaque LAsmModuleSem.lasm_semantics_ops.
Global Opaque LAsm.module_ops.
Global Opaque compatlayer_ops.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  (** Because backward_simulation is in [Type], we need to stay in [Type] as well. *)

  Definition link_impl_inverted_add_cfunction (P: LAsm.module -> Type) f M :=
    { Mf : LAsm.module &
      prod (CompCertiKOS.transf_module (lcf_id f ↦ lcf_fun f) = ret Mf)
           (P (Mf ⊕ M)) }.

  Fixpoint link_impl_inverted_add_gvars {D} vs (M: LAsm.module) L P0 :=
    prod
      (LayerOK (〚M〛 (link_impl_add_gvar_specs (LDATA:=D) vs L ⊕ L64) ⊕
                (link_impl_add_gvar_specs (LDATA:=D) vs L ⊕ L64)))
      (match vs with
         | nil => P0
         | v::vs =>
           link_impl_inverted_add_gvars vs (M ⊕ lgv_id v ↦ lgv_type v) L P0
       end).

  Definition link_impl_inverted_base {D} lm (ll: compatlayer D) M Mc :=
    link_impl_inverted_add_gvars
      (lm_gvar lm) 
      (Mc ⊕ link_impl_asm lm)
      ll
      (prod
         (LayerOK (〚M〛 (ll ⊕ L64) ⊕ ll ⊕ L64))
         (M = link_impl_add_gvar_defs (lm_gvar lm) (Mc ⊕ link_impl_asm lm) ⊕ ∅)).

  Definition link_impl_inverted {D} (lm: link_module) (ll: compatlayer D) M :=
    fold_left
      (link_impl_inverted_add_cfunction)
      (lm_cfun lm)
      (link_impl_inverted_base lm ll M)
      ∅.

  Lemma link_impl_imply_add_cfunction (P: LAsm.module -> Type) f M M':
    link_add_cfunction f (ret M) = ret M' ->
    P M' ->
    link_impl_inverted_add_cfunction P f M.
  Proof.
    intros HfM HM'.
    unfold link_add_cfunction in HfM.
    inv_monad HfM.
    eexists.
    split.
    - eassumption.
    - subst.
      assumption.
  Qed.

  Lemma link_impl_imply_fold_add_cfunction P fs M M':
    fold_right link_add_cfunction (ret M) fs = ret M' ->
    P M' ->
    fold_left link_impl_inverted_add_cfunction fs P M.
  Proof.
    revert P M M'.
    induction fs as [ | f fs IHfs].
    - simpl.
      inversion 1.
      tauto.
    - simpl.
      intros P M M' HfM HM'.
      specialize (IHfs (link_impl_inverted_add_cfunction P f) M).
      destruct (fold_right link_add_cfunction (ret M) fs); try now inversion HfM.
      eapply IHfs.
      reflexivity.
      eapply link_impl_imply_add_cfunction; eauto.
  Qed.

  Lemma link_impl_imply_add_gvars {D} vs M L P0 M':
    link_impl_add_gvars (LDATA:=D) vs M L = ret M' ->
    P0 ->
    link_impl_inverted_add_gvars vs M L P0.
  Proof.
    revert M M' L.
    induction vs; intros M M' L.
    - simpl.
      intros H; inv_monad H.
      tauto.
    - simpl.
      intros H; inv_monad H.
      eauto.
  Qed.

  Lemma link_impl_imply_gvar {D} (lm: link_module) (ll: compatlayer D) M M':
    link_impl_gvar lm ll M = ret M' ->
    M' = link_impl_add_gvar_defs (lm_gvar lm) M.
  Proof.
    unfold link_impl_gvar.
    generalize (lm_gvar lm); clear lm.
    intros vs.
    revert M M'.
    induction vs as [ | v vs IHvs]; intros M M'.
    - simpl.
      intros H.
      inv_monad H.
      congruence.
    - simpl.
      intros H.
      inv_monad H.
      eauto.
  Qed.

  Lemma link_impl_imply {D} (lm: link_module) (ll: compatlayer D) M:
    link_impl lm ll = OK M ->
    link_impl_inverted lm ll M.
  Proof.
    unfold link_impl, link_impl_c.
    intros H.
    inv_monad H; subst.
    unfold link_impl_inverted.
    eapply link_impl_imply_fold_add_cfunction; eauto.
    unfold link_impl_inverted_base.
    eapply link_impl_imply_add_gvars; eauto.
    split; eauto.
    f_equal.
    eapply link_impl_imply_gvar; eauto.
  Qed.

  (** * Types of typical linking theorems *)

  (** A linking file typically proves 3 lemmas: [init_correct],
    [cl_backward_simulation], and [make_program_exists], as well as an
    auxiliary lemma [link_correct_aux] use for proving the last two.
    It is convenient to compute the type of those theorems
    systematically from the linking module and the two adjascent layer
    interfaces. Additionally, the tactics further down can help with
    the proofs themselves. *)

  (* CompCertiKOSOps requires the output buffer instance of observation,
     so it's included here. Maybe make this more abstract at some point? *)
  Require Import ObservationImpl.

  Context {DL DH: Type} `{CompatData(Obs:=devact_observation_ops) DL} 
                        `{CompatData(Obs:=devact_observation_ops) DH}.
  Context `{!CompatRelOps (cdata DH) (cdata DL)} `{!CompatRel (cdata DH) (cdata DL)}.

  Definition init_correct_type lm LL LH :=
    forall M: LAsm.module,
      link_impl lm LL = OK M ->
      ModuleOK M ->
      cl_init_sim (cdata DH) (cdata DL) (crel DH DL) (LH ⊕ L64) M (LL ⊕ L64).

  Definition link_correct_aux_type lm LL LH :=
    forall M: LAsm.module,
      link_impl (LDATA := cdata DL) lm LL = OK M ->
      LL ⊕ L64 ⊢ (crel DH DL, M) : LH ⊕ L64.

  (* Interestingly, if the type annotations for LL and LH are omitted here, Coq infers
     incorrect types of the form (compatlayer (cdata (cdata D))). Maybe a bug? *)
  Definition cl_simulation_type lm (LL : compatlayer (cdata DL)) (LH : compatlayer (cdata DH)) :=
    fun `{!LAsm.AccessorsDefined (LL ⊕ L64)}
        `{!LAsm.AccessorsDefined (LH ⊕ L64)} =>
    forall p (s: stencil) (CTXT M: LAsm.module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      link_impl lm LL = OK M ->
      make_program (D := cdata DH) s CTXT (LH ⊕ L64) = OK ph ->
      make_program (D := cdata DL) s (CTXT ⊕ M) (LL ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (LH ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (LL ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).

  Definition cl_forward_simulation_type lm LL LH :=
    fun `{!LAsm.AccessorsDefined (LL ⊕ L64)}
        `{!LAsm.AccessorsDefined (LH ⊕ L64)} =>
    forall (s: stencil) (CTXT M: LAsm.module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      link_impl lm LL = OK M ->
      make_program (D := cdata DH) s CTXT (LH ⊕ L64) = OK ph ->
      make_program (D := cdata DL) s (CTXT ⊕ M) (LL ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (LH ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (LL ⊕ L64)) pl).

  Definition cl_backward_simulation_type lm LL LH :=
    fun `{!LAsm.AccessorsDefined (LL ⊕ L64)}
        `{!LAsm.AccessorsDefined (LH ⊕ L64)} =>
    forall (s: stencil) (CTXT M: LAsm.module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      link_impl lm LL = OK M ->
      make_program (D := cdata DH) s CTXT (LH ⊕ L64) = OK ph ->
      make_program (D := cdata DL) s (CTXT ⊕ M) (LL ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (LH ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (LL ⊕ L64)) pl).

  Definition make_program_exist_type lm LL LH :=
    forall (s: stencil) (CTXT M: LAsm.module) pl,
      link_impl lm LL = OK M ->
      make_program (D := cdata DL) s (CTXT ⊕ M) (LL ⊕ L64) = OK pl ->
      exists ph, make_program (D := cdata DH) s CTXT (LH ⊕ L64) = OK ph.

End WITHCOMPCERTIKOS.

Ltac destruct_impl_inverted H :=
  lazymatch type of H with
    | link_impl_inverted_add_cfunction _ _ _ =>
      let M := fresh "M" in
      let HM := fresh "H" M in
      let H' := fresh in
      destruct H as (M & HM & H');
      simpl in HM;
      destruct_impl_inverted H'
    | prod (LayerOK _) _ =>
      let Hok := fresh "Hok" in
      let H' := fresh in
      destruct H as [Hok H'];
      destruct_impl_inverted H'
    | _ =>
      idtac
  end.

Ltac inv_link_impl HM :=
  apply link_impl_imply in HM;
  unfold link_impl_inverted in HM;
  unfold link_impl_inverted_base in HM;
  unfold link_impl_asm in HM;
  simpl in HM;
  destruct_impl_inverted HM.

(** Commonly used in FooGenLink.v: *)
Require Export Coqlib.
Require Export FlatMemory.
Require Export Decision.
Require Export LAsm.
Require Export LAsmModuleSem.
Require Export LAsmModuleSemMakeProgram.
Require Export LayerCalculusLemma.
Require Export LinkTactic.
Require Export Soundness.
Require Export CompatExternalCalls.

(** * Proof templates for linking theorems *)

(** ** Proof template for [link_correct] *)

Ltac link_correct_aux_fresh :=
  lazymatch goal with
    | |- ?LL ⊢ _ : ?LH =>
      LinkTactic.transfer_variables;
      unfold_layer LH;
      match goal with
        | |- _ ⊢ (_, _ ⊕ ∅) : _ =>
          apply LayerLogicImpl.vdash_oplus_empty (* no assembly code *)
        | |- _ =>
          hcomp_tac (* split C from assembly code *)
      end;
      layer_link_split_tac
  end.

Ltac link_correct_aux_passthrough :=
  eapply layer_link_new_glbl_both;
  apply oplus_sim_monotonic; [ | apply L64_auto_sim].

Ltac link_correct_aux :=
  let M := fresh "M" in
  let HM := fresh "H" M in
  intros M HM;
  inv_link_impl HM; subst;
  eapply conseq_le_assoc_comm;
  hcomp_tac;
    [link_correct_aux_fresh |
     link_correct_aux_passthrough].

Ltac cl_simulation init_correct lc :=
  let H := fresh in
  intros ? ? ? ? ? ? ? H;
  intros;
  eapply soundness_simulation;
  try eassumption;
  try decision;
  [ eapply lc; now eauto |
    eapply init_correct; [ | eapply make_program_oplus_right]; eassumption |
    inv_link_impl H; assumption ].

Ltac cl_forward_simulation init_correct lc :=
  let H := fresh in
  intros ? ? ? ? ? ? H;
  intros;
  eapply soundness_forward;
  try eassumption;
  try decision;
  [ eapply lc; now eauto |
    eapply init_correct; [ | eapply make_program_oplus_right]; eassumption |
    inv_link_impl H; assumption ].

Ltac cl_backward_simulation init_correct lc :=
  let H := fresh in
  intros ? ? ? ? ? ? H;
  intros;
  eapply soundness;
  try eassumption;
  try decision;
  [ eapply lc; now eauto |
    eapply init_correct; [ | eapply make_program_oplus_right]; eassumption |
    inv_link_impl H; assumption ].

Ltac make_program_exists lc :=
  let H := fresh in
  let Hmkp := fresh "Hmkp" in
  intros ? ? ? ? H Hmkp;
  exploit lc; [eassumption | ];
  inv_link_impl H;
  eapply make_program_vertical' in Hmkp; [ | eassumption];
  destruct Hmkp;
  simpl;
  intros;
  eapply make_program_sim_monotonic_exists;
  [ | eassumption | eassumption];
  reflexivity.

(** ** Proof template for [init_correct] *)

(** A number of premises of [cl_init_sim_intro] have a [In i new_glbl] guard.
  We destruct it so as to get subgoals where i is actually a concrete value. *)

Ltac destruct_In H :=
  (solve [ destruct H ]) || (destruct H; [subst | destruct_In H]).

(** We also need a similar tactic to split up [~ In new_glbl] into
  individual inequalities. *)

Lemma expand_not_in {A} (x x0: A) (xs: list A):
  ~ In x (x0::xs) -> x <> x0 /\ ~ In x xs.
Proof.
  simpl.
  intros Hx.
  split; eauto.
Qed.

Ltac destruct_not_In H :=
  match type of H with
    | ~ In ?i _ =>
      let Hi := fresh "H" i in
      pose proof (expand_not_in _ _ _ H) as Hi;
      clear H;
      destruct Hi as [Hi H];
      destruct_not_In H
    | _ =>
      clear H
  end.

(** Using a [get_module_variable] equality, we can unify the value
  associated to the identifier in the module with the one stated by
  the inequality. *)

Lemma get_module_variable_le_ok (i: AST.ident) (τ: AST.globvar Ctypes.type) M:
  ModuleOK M ->
  i ↦ τ ≤ M ->
  get_module_variable i M = OK (Some τ).
Proof.
  intros HM Hi.
  apply (get_module_variable_monotonic i) in Hi.
  get_module_normalize_in Hi.
  specialize (HM i).
  destruct HM as [_ HMiOK _].
  inversion Hi; subst.
  - inversion H1.
    congruence.
  - inversion HMiOK.
    congruence.
Qed.

Ltac inv_get_module_variable H :=
  lazymatch type of H with get_module_variable ?i ?M = OK (Some ?vi) =>
    lazymatch M with context [i ↦ ?vi'] =>
      erewrite (get_module_variable_le_ok i vi') in H; [|eassumption|le_oplus];
      inversion H; clear H; subst
    end
  end.

(** Given a hypothesis involing a term of the form
  [get_module_variable M i], where M can involve compiled modules,
  we can exploit [transf_module _ = ret _] hypotheses from the context
  to boil it down further than [get_module_normalize_in] would on its
  own, allowing us to use [discriminate] in some circumstances. *)

Ltac simpl_get_compiled_variable H :=
  lazymatch type of H with
    | get_module_variable ?i _ = _ =>
      transf_none i;
      get_module_normalize_in H;
      unfold module in *;
      repeat match goal with
        | Hv: get_module_variable i _ = _ |- _ =>
          rewrite Hv in H; clear Hv
      end
  end.

(** With this in our toolbox, we can tackle the init_correct subgoal
  of the form:

    [forall i vi,
      get_module_variable i M = OK (Some vi) ->
      InitMem.Genv.init_data_list_valid ge 0 (gvar_init vi) = true].

  There are two cases: If [i] is actually a global variable
  declared in the module, we use [destruct_In] tactic to do a case
  analysis on which variable it is, and recover the corresponding,
  concrete value of [vi]. The rest is computation. On the other hand,
  if [i] is not actually declared, we can massage a contradiction out
  of the [get_module_variable] hypothesis using [destruct_not_In] and
  [simpl_get_compiled_variable]. *)

Ltac init_correct_data_list_valid :=
  lazymatch goal with
    | Hvi: get_module_variable ?i _ = OK (Some ?vi) |-
      InitMem.Genv.init_data_list_valid ?ge _ (AST.gvar_init ?vi) = true =>
      let H := fresh in
      destruct (decide (In i new_glbl)) as [H|H];
      [ destruct_In H;
        inv_get_module_variable Hvi;
        reflexivity
      | destruct_not_In H;
        simpl_get_compiled_variable Hvi;
        discriminate Hvi ]
  end.

(** Do introductions, splitting up [In i new_glbl] guards into subcases. *)

Ltac init_correct_glbl_intros :=
  match goal with
    | |- In _ _ -> _  =>
      let H := fresh in
      intros H;
      destruct_In H;
      init_correct_glbl_intros
    | |- _ =>
      intro;
      init_correct_glbl_intros
    | |- _ =>
      idtac
  end.

(** Put all of this together *)

Ltac init_correct_sim_mem :=
  constructor; econstructor;
  simpl; trivial using FlatMem.flatmem_empty_inj;
  match goal with
    | |- kctxt_inj _ _ _ _ =>
      repeat intro;
      unfold Pregmap.get;
      rewrite ?Maps.ZMap.gi, ?Pregmap.gi;
      constructor
    | |- uctxt_inj _ _ _ =>
      repeat intro;
      unfold Pregmap.get;
      rewrite ?Maps.ZMap.gi, ?Pregmap.gi;
      constructor
    | |- VMCS_inj _ _ _ =>
      constructor;
      repeat intro;
      unfold Pregmap.get;
      rewrite ?Maps.ZMap.gi, ?Pregmap.gi;
      constructor
    | |- VMX_inj _ _ _ =>
      constructor;
      repeat intro;
      unfold Pregmap.get;
      rewrite ?Maps.ZMap.gi, ?Pregmap.gi;
      constructor
    | |- _ =>
      idtac
  end.

Ltac init_correct_glbl :=
  init_correct_glbl_intros;
  match goal with
    | |- InitMem.Genv.init_data_list_valid _ _ _ = true =>
      init_correct_data_list_valid
    | |- isOKNone _ =>
      reflexivity
    | |- isOKNone (get_layer_globalvar ?i _) =>
      revert i;
      decision
   | H: context [?i ↦ ?vi]
     |- exists vi, get_module_variable ?i ?M = OK (Some vi) =>
     exists vi;
     eapply (get_module_variable_le_ok i); [ assumption | le_oplus ]
    | |- _ =>
      idtac
  end.

Ltac init_correct :=
  let HM := fresh "HM" in
  intros ? HM ?;
  inv_link_impl HM;
  subst;
  apply cl_init_sim_intro; [ init_correct_sim_mem | init_correct_glbl .. ].
