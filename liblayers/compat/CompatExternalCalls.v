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
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import liblayers.lib.Decision.
Require Import liblayers.compat.CompatLayers.
Require Import compcertx.driver.CompCertBuiltins.
Require Import liblayers.compcertx.Observation.

Section WITH_MEMORY_MODEL.
Context `{Hobs: Observation}.
Context `{Hstencil: Stencil}.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.

(** We cannot use [Inductive] here, because [Events.extcall_sem]
introduces dependency on the type of [ge], which cannot be inverted
properly. *)

Definition compatsem_extcall {D: compatdata}:
  compatsem D -> signature -> Events.extcall_sem (mem := mwd D) :=
  fun f sg WB F V ge vargs m t vres m' =>
    exists s (σ: sextcall_primsem D),
      stencil_matches s ge /\
      sextcall_step σ s WB vargs m vres m' /\
      f = inl σ /\
      sg = sextcall_sig σ /\
      t = E0.

Lemma compatsem_extcall_intro {D: compatdata}
      (σ: sextcall_primsem D) s WB F V ge vargs m vres m':
        stencil_matches s ge ->
        sextcall_step σ s WB vargs m vres m' ->
        compatsem_extcall (inl σ) (sextcall_sig σ) WB F V ge vargs m E0 vres m'.
Proof.
  unfold compatsem_extcall; eauto 7.
Qed.

Lemma compatsem_extcall_le {D: compatdata}
      (σ1 σ2: compatsem D)
      (LE: σ1 ≤ σ2)
      sg WB F V ge vargs m t vres m'
      (Hsem: compatsem_extcall σ1 sg WB F V ge vargs m t vres m')
      (Hvalid_ge: forall s, stencil_matches s ge -> 
                         match σ2 with
                           | inl s2 => sextcall_valid s2 s = true
                           | _ => True
                         end)
:
  compatsem_extcall σ2 sg WB F V ge vargs m t vres m'.
Proof.
  destruct Hsem as (s & σ & Hmatch & Hstep & ? & ? & ?); subst.
  inversion LE; subst; clear LE.
  destruct H0 as [[Hstep' Hsig Hvalid] Hinvs].
  destruct σ as [sem1 csig1 valid1]; subst; simpl in *.
  destruct y as [sem2 csig2 valid2]; subst; simpl in *.
  subst; simpl in *.
  repeat (econstructor; eauto).
  (** XXX only true if σ2 valid for all stencils; fortunately only used
    in I64Layers where it's probably true. *)
  * simpl; eauto.
    intros. eapply Hstep'; eauto.
  * simpl; unfold sextcall_sig; congruence.
Qed.

Local Instance compatlayer_extcall_ops_x {D} (L: compatlayer D):
  ExternalCallsOpsX (mwd D) :=
  {|
    external_functions_sem i sg WB F V ge vargs m t vres m' :=
      exists σ,
        get_layer_primitive i L = Errors.OK (Some σ) /\
        compatsem_extcall σ sg WB _ _ ge vargs m t vres m'
  |}.

Local Instance compatlayer_extcall_ops {D} (L: compatlayer D):
  ExternalCallsOps (mwd D) :=
  external_calls_ops_x_to_external_calls_ops (mwd D) (external_calls_ops_x := compatlayer_extcall_ops_x L).

Local Instance compatlayer_compiler_config_ops {D} (L: compatlayer D):
  CompilerConfigOps _
      (external_calls_ops := compatlayer_extcall_ops L)
 :=
  {|
    (** We want to follow the calling conventions when calling an
    external function which will be replaced later with code. This is
    not possible if EF_extcall are enabled at builtin call sites. *)
    cc_enable_external_as_builtin := false
  |}.

(** To prove that a layer can provide external function properties
suitable to CompCert, we need a "strong layer" premise. *)

Definition sextcall_props_defined {D} (σ: res (option (compatsem D))): bool :=
  match σ with
    | OK (Some (inl f)) =>
      match sextcall_props _ f with
        | Error _ => false
        | _ => true
      end
    | _ => true
  end.

Definition ExternalCallsXDefined {D} (L: compatlayer D): Prop :=
  forall i, (fun f => sextcall_props_defined f = true) (get_layer_primitive i L).

(* Declaring this instance is necessary to avoid [Existing Class]
getting in the way of instance resolution *)
Global Instance external_calls_x_defined_dec: forall {D} (L: _ D), Decision (ExternalCallsXDefined L) := _.

Existing Class ExternalCallsXDefined.

Local Instance compatlayer_extcall_x_strong:
  forall {D} (L: compatlayer D),
  forall (DEF: ExternalCallsXDefined L),
    ExternalCallsX _
                   (external_calls_ops_x := compatlayer_extcall_ops_x L).
Proof.

Ltac t DEF id H :=
  let σ := fresh "σ" in
  let Hget := fresh "Hget" in
  let Hsem := fresh "Hsem" in
  let s := fresh "s" in
  let σf := fresh "σf" in
  let Hmatch := fresh "Hmatch" in
  let Hdef := fresh "Hdef" in
  let Hprop := fresh "Hprop" in
  destruct H as (σ & Hget & Hsem);
    destruct Hsem as (s & σf & Hmatch & Hsem & ? & ? & ?);
    subst;
    generalize (DEF id); rewrite Hget; intro Hdef; simpl in Hdef;
    destruct (sextcall_props _ σf) as [Hprop | ]; try discriminate
.

  intros.
  constructor.
  constructor;
    intros; try (t DEF id H).
  * replace (proj_sig_res (sextcall_sig σf)) with (Ctypes.typ_of_type (sextcall_res σf)).
    + eapply external_call_well_typed; eauto.
    + unfold proj_sig_res, sextcall_sig, sextcall_res.
      destruct (sextcall_csig σf); simpl.
      destruct csig_res; simpl; try reflexivity.
      destruct f; reflexivity.
  * t DEF id H1.
    econstructor. split; eauto.
    esplit. esplit.
    split; eauto.
    eapply stencil_matches_preserves_symbols.
      - symmetry; eauto.
      - auto.
      - auto.
      - eassumption.
  * eapply external_call_valid_block; eauto.
  * eapply external_call_max_perm; eauto.
  * eapply external_call_readonly; eauto.
  * exploit external_call_mem_extends; eauto.
    destruct 1 as (? & ? & ? & ?).
    esplit. esplit.
    split; eauto.
    econstructor.
    split; eauto.
    esplit. esplit; eauto.
  * t DEF id H0.
    exploit external_call_mem_inject; eauto.
    {
      destruct H. unfold meminj_preserves_stencil.
      intro; erewrite <- stencil_matches_symbols; eauto.
    }
    destruct 1 as (? & ? & ? & ? & ?).
    esplit. esplit. esplit.
    split; eauto.
    econstructor; eauto.
    split; eauto.
    esplit. esplit; eauto.
  * simpl; omega.
  * inversion H0; subst.
    esplit. esplit. econstructor; eauto. split; eauto.
    esplit. esplit; eauto.
  * t DEF id H0.
    split.
    + constructor.
    + replace s0 with s in * by (eapply stencil_matches_unique; eauto).
      replace σf0 with σf in * by congruence.
      intro; eapply external_call_determ; eauto.
  * econstructor; eauto.
    split; eauto.
    esplit. esplit.
    eauto 6 using external_call_writable_block_weak.
  * eapply external_call_not_writable; eauto.
Qed.

Local Instance compatlayer_extcall_strong :
  forall `{builtin_norepet: BuiltinIdentsNorepet},
  forall {D} (L: compatlayer D),
    forall (DEF: ExternalCallsXDefined L),
    ExternalCalls _
      (external_calls_ops := compatlayer_extcall_ops L)
  := _.

Local Instance compatlayer_compiler_config :
  forall `{builtin_norepet: BuiltinIdentsNorepet},
  forall {D} (L: compatlayer D),
    forall (DEF: ExternalCallsXDefined L),
    CompilerConfiguration _
      (external_calls_ops := compatlayer_extcall_ops L).
Proof.
  constructor.
  typeclasses eauto.
  apply compatlayer_extcall_strong.
  assumption.
Qed.

End WITH_MEMORY_MODEL.
