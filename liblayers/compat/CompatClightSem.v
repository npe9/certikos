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
Require Import compcert.common.Values.
Require Import compcert.common.Memtype.
Require Import compcert.common.Globalenvs.
Require Import compcertx.common.EventsX.
Require Import compcert.common.Smallstep.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.
Require Import compcertx.cfrontend.ClightBigstepX.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.ClightModules.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require compcertx.cfrontend.ClightXFacts.
Require Import liblayers.compcertx.Observation.

Section WITH_MEMORY_MODEL.
Context `{Hobs: Observation}.
Context `{Hstencil: Stencil}.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.


(** * Building Clight programs *)

(** How to construct a C signature from an assembly signature for assembly primitives *)

Definition type_of_typ (t: AST.typ): Ctypes.type :=
  match t with
    | AST.Tsingle => Ctypes.Tfloat Ctypes.F32 Ctypes.noattr
    | AST.Tfloat  => Ctypes.Tfloat Ctypes.F64 Ctypes.noattr
    | AST.Tlong   => Ctypes.Tlong Ctypes.Signed Ctypes.noattr
    | AST.Tint    => Ctypes.Tint  Ctypes.I32 Ctypes.Signed Ctypes.noattr
  end.

Definition type_of_opttyp (t: option AST.typ): Ctypes.type :=
  match t with
    | Some t' => type_of_typ t'
    | None    => Tvoid
  end.

Fixpoint typelist_of_typlist (l: list AST.typ): typelist :=
  match l with
    | nil => Ctypes.Tnil
    | t :: l' => Ctypes.Tcons (type_of_typ t) (typelist_of_typlist l')
  end.

Lemma typ_of_type_of_typ t:
  typ_of_type (type_of_typ t) = t.
Proof.
  destruct t; reflexivity.
Qed.

Lemma opttyp_of_type_of_opttyp t:
  opttyp_of_type (type_of_opttyp t) = t.
Proof.
  destruct t; try reflexivity.
  destruct t; reflexivity.
Qed.

Lemma typlist_of_typelist_of_typlist l:
  typlist_of_typelist (typelist_of_typlist l) = l.
Proof.
  induction l; simpl; f_equal; eauto using typ_of_type_of_typ.
Qed.

Lemma signature_of_type_correct s:
  signature_of_type (typelist_of_typlist (AST.sig_args s)) (type_of_opttyp (AST.sig_res s)) (AST.sig_cc s) = s.
Proof.
  unfold signature_of_type.
  destruct s; simpl.
  rewrite typlist_of_typelist_of_typlist.
  rewrite opttyp_of_type_of_opttyp.
  reflexivity.
Qed.

Definition make_external {D} (i: ident) (σ: compatsem D): Clight.fundef :=
  match σ with
    | inl σe =>
      External
        (EF_external i (sextcall_sig σe))
        (sextcall_args σe)
        (sextcall_res σe)
        (sextcall_cc σe)
    | inr σp =>
      External
        (EF_external i (sprimcall_sig σp))
        (typelist_of_typlist (AST.sig_args (sprimcall_sig σp)))
        (type_of_opttyp (AST.sig_res (sprimcall_sig σp)))
        (AST.sig_cc (sprimcall_sig σp))
  end.

Global Instance make_clight_fundef_varinfo_ops:
  ProgramFormatOps Clight.function Ctypes.type Clight.fundef Ctypes.type :=
  {
    make_internal κ := OK (Clight.Internal κ);
    make_external D i σ := OK (make_external i σ);
    make_varinfo := (fun x => x)
  }.

Global Instance make_clight_fundef_varinfo_prf:
  ProgramFormat Clight.function Ctypes.type Clight.fundef Ctypes.type.
Proof.
  constructor.
  * intro D. intros i ? ?; subst. intro σ1. intro σ2. intro LE.
    simpl.
    unfold make_external.
    inversion LE; subst.
    + destruct H as [[Hstep Hsig Hvalid] Hinvs].
      destruct x; simpl in *; subst.
      destruct y0; simpl in *; subst.
      unfold sextcall_sig, sextcall_args, sextcall_res, sextcall_cc.
      rewrite !Hsig.
      reflexivity.
    + destruct H as [[Hstep Hsig Hvalid] Hinvs].
      simpl.
      rewrite !Hsig.
      reflexivity.
Qed.

Context `{mkp_ops: !MakeProgramOps _ _ _ _}.
Context `{Hmkp: !MakeProgram _ _ _ _}.


(** * Semantics of internal functions *)

Definition clight_step {D} (M: cmodule) (L: compatlayer D) i f s (WB: block -> Prop) vargs m vres m' :=
  exists ge b,
    make_globalenv s M L = ret ge /\
    Genv.find_symbol ge i = Some b /\
    Genv.find_funct_ptr ge b = Some (Internal f) /\
    star (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                       (WB := Events.writable_block_with_init_mem m))
         ge
         (Callstate (Internal f) vargs Kstop m) E0
         (Returnstate vres Kstop m').

Local Existing Instance extcall_invariants_defined_dec.
Local Existing Instance primcall_invariants_defined_dec.

Local Existing Instance prim_valid_dec.

Definition clight_info {D} (M: cmodule) (L: compatlayer D) i f: sextcall_info :=
  {|
    sextcall_step := clight_step M L i f;
    sextcall_csig :=
      {|
        csig_args := type_of_params (fn_params f);
        csig_res := fn_return f;
        csig_cc := fn_callconv f
      |};
    sextcall_valid s :=
      if decide (ExtcallInvariantsDefined L) then
        if decide (PrimcallInvariantsDefined L) then
          if decide (get_layer_prim_valid L s) then
            match make_program s M L with
              | OK _ => true
              | _ => false
            end
          else false
        else false
      else false
  |}.

Definition sextcall_invs_defined {D} (f: res (option (compatsem D))): bool :=
  match f with
    | OK (Some (inl σ)) =>
      match sextcall_invs _ σ with
        | Error _ => false
        | _ => true
      end
    | _ => true
  end.

Definition sextcall_invs_defined_all {D} (L: compatlayer D): Prop :=
  forall i: ident, (fun f => sextcall_invs_defined f = true) (get_layer_primitive (primsem := compatsem) i L).

(** XXX: need to know that the layer preserves invariants asa a premise. *)
(* In fact, we don't, because invariants are only needed at assembly level, 
and  we will never consider anything like 〚M〛(〚N〛L) where M is assembly and N is Clight.
Section WITHINVARIANTS.

Context {D} (L: _ D)
        (HL_inv: sextcall_invs_defined_all L).

Local Instance sextcall_invs_get_layer_primitive:
  forall i f,
    get_layer_primitive i L = OK (Some (inl f)) ->
    ExtcallInvariants (sextcall_primsem_step _ f).
Proof.
  intros.
  generalize (HL_inv i).
  rewrite H.
  simpl.
  destruct (sextcall_invs D f) eqn:?; try discriminate.
  auto.
Qed.

Lemma assign_loc_data `{HWB: WritableBlockOps} ge ty (m: mwd D) loc ofs v m':
  assign_loc ge ty m loc ofs v m' ->
  π_data m' = π_data m.
Proof.
  inversion 1; subst; symmetry;
  lift_unfold; tauto.
Qed.

Lemma free_list_data l:
  forall (m: mwd D) m',
  Mem.free_list m l = Some m' ->
  π_data m' = π_data m.
Proof.
  induction l.
  * simpl; congruence.
  * Opaque Mem.free. simpl. destruct a. destruct p.
    intros. destruct (Mem.free m b z0 z) eqn:HFREE; try discriminate.
    Transparent Mem.free. lift_unfold.
    destruct HFREE.
    etransitivity. eapply IHl; eauto.
    auto.
Qed.

Lemma alloc_variables_data:
  forall l e (m: mwd D) e' m',
    alloc_variables e m l e' m' ->
    π_data m' = π_data m.
Proof.
  induction 1; auto.
  lift_unfold. destruct H. congruence.
Qed.

Lemma builtin_data {WB F V} ef (ge: _ F V) vargs (m: mwd D) t vres m':
  external_call (external_calls_ops := compatlayer_extcall_ops L) ef WB ge vargs m t vres m' ->
  builtin_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) ef ->
  π_data m' = π_data m.
Proof.
  destruct ef; try contradiction.
  * inversion 1; subst; auto.
  * inversion 1; subst; auto.
  * inversion 1; subst; auto.
    inversion H0; subst; auto.
    lift_unfold. intuition congruence.
  * inversion 1; subst; auto.
  * inversion 1; subst; auto.
    inversion H1; subst; auto.
    lift_unfold. intuition congruence.
  * inversion 1; subst.
    lift_unfold. destruct H0. destruct H1. congruence.
  * inversion 1; subst.
    lift_unfold. intuition congruence.
  * inversion 1; subst.
    lift_unfold. intuition congruence.
  * inversion 1; subst; auto.
  * inversion 1; subst; auto.
Qed.

Lemma step2_high_level_invariant {WB} {HWB: WritableBlockOps WB} ge s t s':
  (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  high_level_invariant (π_data (ClightXFacts.state_mem s)) ->
  high_level_invariant (π_data (ClightXFacts.state_mem s')).
Proof.
  inversion 1; subst; simpl; try tauto.
  * erewrite <- assign_loc_data; eauto.
  * (* builtin *) erewrite <- builtin_data; eauto.
  * erewrite <- free_list_data; eauto.
  * erewrite <- free_list_data; eauto.
  * erewrite <- free_list_data; eauto.
  * inversion H0. erewrite <- alloc_variables_data; eauto.
  * destruct (ClightXFacts.builtin_is_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) (refl_equal _) ef).
    + (* builtin *) erewrite <- builtin_data; eauto.
    + destruct ef; simpl in n; try tauto.
      clear n.
      destruct H0; subst.
      destruct H0.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H2.
      destruct H3.
      subst.
      destruct m; destruct m'; unfold π_data, snd in *.
      eapply @external_call_high_level_invariant.
       eapply sextcall_invs_get_layer_primitive. eassumption.
      eassumption.
Qed.

Lemma star2_high_level_invariant {WB} {HWB: WritableBlockOps WB} ge s t s':
  star (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  high_level_invariant (π_data (ClightXFacts.state_mem s)) ->
  high_level_invariant (π_data (ClightXFacts.state_mem s')).
Proof.
  induction 1; eauto using step2_high_level_invariant.
Qed.

Lemma step2_kernel_mode {WB} {HWB: WritableBlockOps WB} ge s t s':
  (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  kernel_mode (π_data (ClightXFacts.state_mem s)) ->
  kernel_mode (π_data (ClightXFacts.state_mem s')).
Proof.
  inversion 1; subst; simpl; try tauto.
  * erewrite <- assign_loc_data; eauto.
  * (* builtin *) erewrite <- builtin_data; eauto.
  * erewrite <- free_list_data; eauto.
  * erewrite <- free_list_data; eauto.
  * erewrite <- free_list_data; eauto.
  * inversion H0. erewrite <- alloc_variables_data; eauto.
  * destruct (ClightXFacts.builtin_is_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) (refl_equal _) ef).
    + (* builtin *) erewrite <- builtin_data; eauto.
    + destruct ef; simpl in n; try tauto.
      clear n.
      destruct H0; subst.
      destruct H0.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H2.
      destruct H3.
      subst.
      destruct m; destruct m'; unfold π_data, snd in *.
      eapply @external_call_kernel_mode.
       eapply sextcall_invs_get_layer_primitive. eassumption.
      eassumption.
Qed.

Lemma star2_kernel_mode {WB} {HWB: WritableBlockOps WB} ge s t s':
  star (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  kernel_mode (π_data (ClightXFacts.state_mem s)) ->
  kernel_mode (π_data (ClightXFacts.state_mem s')).
Proof.
  induction 1; eauto using step2_kernel_mode.
Qed.

Lemma assign_loc_nextblock `{HWB: WritableBlockOps} ge ty (m: mwd D) loc ofs v m':
  assign_loc ge ty m loc ofs v m' ->
  Mem.nextblock (π_mem m') = Mem.nextblock (π_mem m).
Proof.
  inversion 1; subst; symmetry;
  lift_unfold; unfold π_mem.
  * destruct H1. erewrite <- Mem.nextblock_store; eauto.
  * destruct H5. erewrite <- Mem.nextblock_storebytes; eauto.
Qed.

Lemma builtin_nextblock {WB F V} ef (ge: _ F V) vargs (m: mwd D) t vres m':
  external_call (external_calls_ops := compatlayer_extcall_ops L) ef WB ge vargs m t vres m' ->
  builtin_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) ef ->
  (Mem.nextblock (π_mem m) <= Mem.nextblock (π_mem m'))%positive.
Proof.
  destruct ef; try contradiction.
  * inversion 1; subst; xomega.
  * inversion 1; subst; xomega.
  * inversion 1; subst; try xomega.
    inversion H0; subst; try xomega.
    lift_unfold. unfold π_mem. destruct H2.
    erewrite <- Mem.nextblock_store; eauto. intros; simpl in *; xomega.
  * inversion 1; subst; xomega.
  * inversion 1; subst; try xomega.
    inversion H1; subst; try xomega.
    lift_unfold. unfold π_mem. destruct H3.
    erewrite <- Mem.nextblock_store; eauto. intros; simpl in *; xomega.
  * inversion 1; subst.
    apply Mem.nextblock_alloc in H0.
    apply Mem.nextblock_store in H1.    
    lift_unfold. unfold π_mem. intros; simpl in *.
    rewrite H1. rewrite H0. xomega.
  * inversion 1; subst.
    apply Mem.nextblock_free in H2.
    lift_unfold. unfold π_mem. simpl in *. rewrite H2. xomega.
  * inversion 1; subst.
    apply Mem.nextblock_storebytes in H7.
    lift_unfold. unfold π_mem. simpl in *. rewrite H7. xomega.
  * inversion 1; subst; xomega.
  * inversion 1; subst; xomega.
Qed.

Lemma free_list_nextblock l:
  forall (m: mwd D) m',
  Mem.free_list m l = Some m' ->
  Mem.nextblock (π_mem m') = Mem.nextblock (π_mem m).
Proof.
  induction l.
  * simpl; congruence.
  * Opaque Mem.free. simpl. destruct a. destruct p.
    intros. destruct (Mem.free m b z0 z) eqn:HFREE; try discriminate.
    etransitivity. eapply IHl; eauto.
    Transparent Mem.free. lift_unfold.
    destruct HFREE.
    eapply Mem.nextblock_free; eauto.
Qed.

Lemma alloc_variables_nextblock:
  forall l e (m: mwd D) e' m',
    alloc_variables e m l e' m' ->
    (Mem.nextblock (π_mem m) <= Mem.nextblock (π_mem m'))%positive.
Proof.
  induction 1.
  * xomega.
  * apply Mem.nextblock_alloc in H. lift_unfold.
    unfold π_mem in *. simpl in *. rewrite H in IHalloc_variables.
    xomega.
Qed.

Lemma step2_low_level_invariant {WB} {HWB: WritableBlockOps WB} ge s t s':
  (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  forall VALID_GENV_NEXT: Genv.genv_next ge <= Mem.nextblock (π_mem (ClightXFacts.state_mem s)),
    low_level_invariant (Mem.nextblock (π_mem (ClightXFacts.state_mem s))) (π_data (ClightXFacts.state_mem s)) ->
    low_level_invariant (Mem.nextblock (π_mem (ClightXFacts.state_mem s'))) (π_data (ClightXFacts.state_mem s')).
Proof.
  inversion 1; subst; simpl; try tauto.
  * erewrite <- assign_loc_data; eauto. erewrite <- assign_loc_nextblock; eauto.
  * (* builtin *) erewrite <- builtin_data; eauto.
                  intros Hvalid_genv.
                  eapply low_level_invariant_incr. eapply builtin_nextblock; eauto.
  * erewrite <- free_list_data; eauto. erewrite <- free_list_nextblock; eauto.
  * erewrite <- free_list_data; eauto. erewrite <- free_list_nextblock; eauto.
  * erewrite <- free_list_data; eauto. erewrite <- free_list_nextblock; eauto.
  * inversion H0. erewrite <- alloc_variables_data; eauto.
    intros Hvalid_genv. eapply low_level_invariant_incr. eapply alloc_variables_nextblock; eauto.
  * destruct (ClightXFacts.builtin_is_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) (refl_equal _) ef).
    + (* builtin *) erewrite <- builtin_data; eauto.
                    intros Hvalid_genv. eapply low_level_invariant_incr. eapply builtin_nextblock; eauto.
    + destruct ef; simpl in n; try tauto.
      clear n.
      destruct H0; subst.
      destruct H0.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H2.
      destruct H3.
      subst.
      destruct m; destruct m'; unfold π_data, snd in *.
      intros Hvalid_genv.
      eapply @external_call_low_level_invariant.
       eapply sextcall_invs_get_layer_primitive. eassumption.
      eassumption.
      inv H1. rewrite <- stencil_matches_genv_next; assumption.
Qed.

(* This lemma is added to support the low_level_invariant proofs*)
Lemma step2_nextblock {WB} {HWB: WritableBlockOps WB} ge s t s':
  (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  Mem.nextblock (π_mem (ClightXFacts.state_mem s)) <= Mem.nextblock (π_mem (ClightXFacts.state_mem s')).
Proof.
  inversion 1; subst; simpl; try tauto; try reflexivity.
  * erewrite <- assign_loc_nextblock; eauto. reflexivity.
  * (* builtin *)
    eapply builtin_nextblock; eauto.
  * erewrite <- free_list_nextblock; eauto. reflexivity.
  * erewrite <- free_list_nextblock; eauto. reflexivity.
  * erewrite <- free_list_nextblock; eauto. reflexivity.
  * inversion H0. 
    eapply alloc_variables_nextblock; eauto.
  * destruct (ClightXFacts.builtin_is_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) (refl_equal _) ef).
    + (* builtin *) 
      eapply builtin_nextblock; eauto.
    + destruct ef; simpl in n; try tauto.
      clear n.
      destruct H0; subst.
      destruct H0.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H2.
      destruct H3.
      subst.
      destruct m; destruct m'; unfold π_data, snd in *.
      eapply @external_call_nextblock.
       eapply sextcall_invs_get_layer_primitive. eassumption.
      eassumption.
Qed.

(* This lemma is added to support the low_level_invariant proofs*)
Lemma star2_nextblock {WB} {HWB: WritableBlockOps WB} ge s t s':
  star (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  Mem.nextblock (π_mem (ClightXFacts.state_mem s)) <= Mem.nextblock (π_mem (ClightXFacts.state_mem s')).
Proof.
  induction 1. reflexivity.  
  eapply step2_nextblock in H; eauto. xomega.
Qed.

Lemma star2_low_level_invariant {WB} {HWB: WritableBlockOps WB} ge s t s':
  star (Clight.step2 (compiler_config_ops := compatlayer_compiler_config_ops L)
                (WB := WB))
    ge s t s' ->
  forall VALID_GENV_NEXT: Genv.genv_next ge <= Mem.nextblock (π_mem (ClightXFacts.state_mem s)),
    low_level_invariant (Mem.nextblock (π_mem (ClightXFacts.state_mem s))) (π_data (ClightXFacts.state_mem s)) ->
    low_level_invariant (Mem.nextblock (π_mem (ClightXFacts.state_mem s'))) (π_data (ClightXFacts.state_mem s')).
Proof.
  induction 1. eauto.
  intros. eapply IHstar; eauto.
  erewrite <- step2_nextblock; eauto.
  eapply step2_low_level_invariant; eauto.
Qed.

End WITHINVARIANTS.

Instance clight_step_properties {D} (M: cmodule) (L: compatlayer D)
         (invs_defined: sextcall_invs_defined_all L)
         i f:
  ExtcallInvariants (clight_info M L i f).
Proof.
  constructor.
  * destruct 1.
    destruct H.
    destruct H.
    destruct H0.
    destruct H1.
    intros; eapply star2_low_level_invariant in H2; eauto.
    lift_simpl. 
    eapply make_globalenv_stencil_matches in H.
    inv H. rewrite stencil_matches_genv_next.
    assumption.
  * destruct 1.
    destruct H.
    destruct H.
    destruct H0.
    destruct H1.
    intros; eapply star2_high_level_invariant in H2; eauto.
  * destruct 1.
    destruct H.
    destruct H.
    destruct H0.
    destruct H1.
    intros; eapply star2_kernel_mode in H2; eauto.

  * destruct 1.
    destruct H.
    destruct H.
    destruct H0.
    destruct H1.
    intros; eapply star2_nextblock in H2; eauto.
  * destruct 1.
    destruct H.
    destruct H.
    destruct H0.
    destruct H1.
    (*intros; eapply star2_inejct_neutral in H2; eauto.*)
  * 
Qed.
*)

Definition clight_primsem D (M: cmodule) (L: compatlayer D) i f: compatsem D :=
  inl {|
    sextcall_primsem_step := clight_info M L i f;
    sextcall_props := Error nil;
    sextcall_invs := Error nil
(*
      match Decision.decide (sextcall_invs_defined_all L) with
        | left H => Some (clight_step_properties M L H i f)
        | _ => None
      end
*)
  |}.


(** * Semantics of whole modules *)

Local Instance clight_ptree_sem_ops: FunctionSemanticsOps _ _ _ _ _ _ :=
  {
    semof_fundef D M L i f := OK (clight_primsem D M L i f)
  }.

(** NB: we're not going to prove this before POPL. Instead, we will
  compile everything by function, and so won't need a [Semantics]
  instance at all. *)

(*
Local Instance clight_ptree_sem_prf: PTreeSemantics.
Proof.
  split.
  (** monotonicity *)
  * 
  (** vertical composition *)
  *
Qed.
*)

Global Instance clight_semantics_ops:
  SemanticsOps _ _ _ _ cmodule compatlayer :=
  compat_semantics_ops.

(** In fact, we already need monotonicity wrt. [cl_le] *)

Lemma make_program_monotonic_exists {D: compatdata}
      `{L1: compatlayer D} `{L2: compatlayer D}:
  forall M1 M2 s p,
    M1 ≤ M2 ->
    L1 ≤ L2 ->
    make_program s M2 L2 = OK p ->
    exists p', make_program s M1 L1 = OK p'.
Proof.
  intros M1 M2 s p LEM SIM MKP.
  assert (LEP: res_le program_le (make_program s M1 L1) (make_program s M2 L2))
    by (eapply make_program_monotonic; eauto; typeclasses eauto).
  rewrite MKP in LEP.
  inversion LEP; subst.
  eauto.
Qed.

Lemma clight_semantics_monotonic
  {NOREPET: CompCertBuiltins.BuiltinIdentsNorepet}
  {D}:
  @Proper (cmodule -> compatlayer D -> compatlayer D) ((≤) ==> (≤) ==> (≤)) 〚-〛.
Proof.  
    eapply compat_semantics_monotonic.
    clear D.
    intros D M1 M2 M_le L1 L2 L_le i f.
    econstructor; simpl.
    econstructor; simpl.
    econstructor; simpl; [| econstructor; reflexivity].
    econstructor; simpl; [| reflexivity |].
    + intros. 
      (*destruct (Decision.decide (LayerOK L2)); try discriminate.*)
      destruct (Decision.decide (ExtcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L2 s)); try discriminate.
      match goal with H: match ?m with | OK _ => true | Error _ => false end = true |- _ =>
                      destruct m eqn:Hmake; try discriminate
      end.
      assert (Hmake_: make_program s M2 L2 = OK p0) by assumption.
      assert (OKmake: isOK (make_program s M2 L2)).
      {
        rewrite Hmake_.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK L2).
      {
        eapply make_program_layer_ok; eauto.
      }
      assert (Hge': exists ge', make_globalenv s M2 L2 = ret ge').
      {
        eapply make_program_make_globalenv in Hmake.
        eauto.
      }
      destruct Hge' as [ge' Hge'].
      destruct 1
        as (ge & b & Hge & Hsymb & Hfunc & Hstar).

      assert (Hgele: res_le (≤) (make_globalenv s M1 L1) (make_globalenv s M2 L2)).
      {
        exploit @make_globalenv_monotonic; eauto.
      }
      rewrite Hge' in Hgele.
      inversion Hgele; subst.
      replace x with ge in * by (vm_compute in Hge, H0; congruence).
      generalize (fun b f => genv_le_find_funct_ptr_some ge ge' b f H2).
      intro HF.
      
      econstructor; eauto.
      esplit. split.
      { eassumption. }
      split.
      {
       erewrite stencil_matches_symbols in Hsymb by eauto using make_globalenv_stencil_matches.
       erewrite stencil_matches_symbols by eauto using make_globalenv_stencil_matches.
       eassumption.
      }
      split; eauto.
      eapply (@ClightXFacts.star2_mono NOREPET _ _ (mwd_memory_model D)
                                       (compatlayer_extcall_ops_x L1) (compatlayer_extcall_ops_x L2)
                                       ge ge'); eauto.
      * intro.
        erewrite stencil_matches_symbols by eauto using make_globalenv_stencil_matches.
        erewrite stencil_matches_symbols by eauto using make_globalenv_stencil_matches.
        reflexivity.
      * intro.
        erewrite stencil_matches_volatile by eauto using make_globalenv_stencil_matches.
        erewrite stencil_matches_volatile by eauto using make_globalenv_stencil_matches.
        reflexivity.
      * 
        erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
        erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
        reflexivity.
      * intros until m'.
        destruct (ClightXFacts.builtin_is_enabled (compiler_config_ops := compatlayer_compiler_config_ops L1) (refl_equal _) ef).
        {
          exploit (@ClightXFacts.external_call_spec _ _ _ (compatlayer_compiler_config_ops L2)); eauto.
          { eapply CompCertBuiltins.builtin_functions_properties; eauto. }
          { constructor; intros; contradiction. }
          intro PROP.
          intro K.
          eapply @ec_symbols_preserved.
          { eassumption. }
          {
            instantiate (1 := ge). intro.
            erewrite stencil_matches_symbols by eauto using make_globalenv_stencil_matches.
            erewrite stencil_matches_symbols by eauto using make_globalenv_stencil_matches.
            reflexivity.
          }            
          {
            intro.
            erewrite stencil_matches_volatile by eauto using make_globalenv_stencil_matches.
            erewrite stencil_matches_volatile by eauto using make_globalenv_stencil_matches.
            reflexivity.
          }            
          {
            erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
            erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
            reflexivity.
          }
          eapply @ec_writable_block_weak.
          { eassumption. }
          { instantiate (1 := writable_block a1 ge).
            destruct ef; try assumption.
            contradiction.
          }
          unfold writable_block.
          erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
          erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
          tauto.
        }
        destruct ef; simpl in n; try (exfalso; tauto).
        destruct 1.
        destruct H1.
        generalize (get_layer_primitive_sim_monotonic _ _ id name _ _ L_le).
        rewrite H1.
        inversion 1; subst.
        {
          inversion H7; subst.
          destruct H3
          as (st & PR & MATCH & HPRIM & ? & ? & ?); subst.
          inversion H8; subst.
          replace st with s in * by eauto using stencil_matches_unique, make_globalenv_stencil_matches.
          revert HPRIM.
          unfold writable_block.
          erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
          erewrite stencil_matches_genv_next by eauto using make_globalenv_stencil_matches.
          intros.
          esplit.
          split; eauto.
          esplit.
          exists y.
          split.
          { eapply make_globalenv_stencil_matches; eauto. }
          split.
          {
            eapply sextcall_info_le_sem.
            { eapply sextcall_primsem_le_step; eauto. }
            { symmetry in H6. exact (g _ _ H6). }
            assumption.
          }
          split; auto.
          split; auto.
          generalize (sextcall_info_le_sig _ _ (sextcall_primsem_le_step _ _ H5)).
          unfold sextcall_sig. congruence.
        }
        exfalso.
        destruct (OKLayer name) as [[σ Hσ] _ _].
        simpl in Hσ.
        rewrite Hσ in H7.
        discriminate.
    + intros.
      (*destruct (Decision.decide (LayerOK L2)); try discriminate.*)
      destruct (Decision.decide (ExtcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L2 s)); try discriminate.
      assert (Hmake: isOK (make_program s M2 L2)).
      {
        match goal with H: match ?m with | OK _ => true | Error _ => false end = true |- _ =>
                        destruct m eqn:Hmake; try discriminate
        end.
        assert (Hmake_: make_program s M2 L2 = OK p0) by assumption.
        rewrite Hmake_. unfold isOK. eauto.
      }
      assert (OKLayer: LayerOK L2).
      {
        eapply make_program_layer_ok; eauto.
      }
      destruct Hmake as [pr Hmake].
      destruct (Decision.decide (ExtcallInvariantsDefined L1)).
      destruct (Decision.decide (PrimcallInvariantsDefined L1)).
      destruct (Decision.decide (get_layer_prim_valid L1 s)).      
      * destruct (make_program_monotonic_exists (L1:=L1) (L2:=L2) M1 M2 s pr); eauto 1.
        rewrite H0. reflexivity.
      * elim n.
        eapply (cl_le_get_layer_prim_valid _ L_le); try eassumption.
      * (* Instance of PrimcallInvariantsDefined L1*)
        elim n.
        eapply (cl_le_invs_prim _ L_le); eassumption.
      * (* Instance of ExtcallInvariantsDefined L1*)
        elim n.
        eapply (cl_le_invs_ext _ L_le); eassumption.
Qed.

(** The following are no longer needed
(** And also semantics of global variables. *)

Lemma clight_globvar_le {D} (L: _ D) (i: ident) (t: AST.globvar Ctypes.type):
 i ↦ t ≤  〚i ↦ t〛 L.
Proof.

(** And also vertical composition... *)

Lemma clight_vertical_composition {D} (L: _ D) M1 M2:
〚 M1 〛 ( (〚 M2 〛 L ) ⊕ L) ≤ 〚 M1 ⊕ M2 〛 L.
Proof.
*)

(*
Global Instance clight_semantics:
  Semantics ident Clight.function compatsem (globvar Ctypes.type) cmodule compatlayer :=
  compat_semantics_prf.
*)


(** * Relate to ClightBigstepX *)

Inductive primitive_le {D}: relation (compatsem D) :=
| primitive_le_sextcall:
    forall (σ1 σ2: sextcall_primsem D)
           (VALID: forall s, sextcall_valid σ2 s = true -> sextcall_valid σ1 s = true)
           (SIG: sextcall_sig σ2 = sextcall_sig σ1)
           (SEM: forall m,
                   high_level_invariant (snd m) ->
                   forall (s: stencil),
                     sextcall_valid σ2 s = true ->
                     forall WB vargs vres m',
                       sextcall_step σ1 s WB vargs m vres m' ->
                       sextcall_step σ2 s WB vargs m vres m'),
      primitive_le (compatsem_inl σ1) (compatsem_inl σ2).

Record spec_le {D} (L1 L2: compatlayer D): Prop :=
  {
    spec_le_primitive:
      forall i,
        res_le (option_le primitive_le) (get_layer_primitive i L1) (get_layer_primitive i L2)
    ;
    spec_le_globalvars:
      forall i,
        res_le (option_le eq) (get_layer_globalvar i L1) (get_layer_globalvar i L2)
    ;
    spec_le_load:
      res_le (option_le eq) (cl_exec_load L1) (cl_exec_load L2)
    ;
    spec_le_store:
      res_le (option_le eq) (cl_exec_store L1) (cl_exec_store L2)

  }.

Lemma clight_sem_intro {D} (i: ident) (f: Clight.function) (L: compatlayer D) (σ: sextcall_primsem D):
  (forall s WB vargs m vres m' p,
     let ec_ops := compatlayer_extcall_ops L in
     let cc_ops := compatlayer_compiler_config_ops L in
     let WRITABLE_BLOCK_OPS := EventsX.writable_block_ops m in
     let WRITABLE_BLOCK_ALLOW_GLOBALS := EventsX.Hwritable_block_allow_globals m in
     sextcall_step σ s WB vargs m vres m' ->
     make_program s (i ↦ f) L = ret p ->
     (high_level_invariant (snd m) ->
      bigstep_function_terminates2 p i (sextcall_sig σ) vargs m E0 vres m')) ->
  (** NB: we could do with a [res_le] version of compat_semantics_spec_some as well. *)
  forall NOCONFLICT: get_layer_primitive i L = OK None,
  forall VALID: forall s p, make_program s (i ↦ f) L = ret p -> sextcall_valid σ s = true,
  forall SIG: sextcall_sig σ = Ctypes.signature_of_type (type_of_params (fn_params f)) (fn_return f) (fn_callconv f),
  spec_le (i ↦ compatsem_inl σ) (〚i ↦ f〛 L).
Proof.
  intros.
  constructor.
{ (* primitives *)
  intros.  
  destruct (Coqlib.peq i0 i).
  * subst.
    rewrite get_layer_primitive_mapsto.
    generalize (get_module_function_mapsto i f).
    intro MODULE.
    pose proof (ptree_get_semof_primitive i (i ↦ f) L) as Hi.
    unfold cmodule; simpl in *.
    rewrite Hi; clear Hi.
    unfold semof_function; simpl.
    get_module_normalize; monad_norm.
    repeat constructor.
    - (* valid *) simpl.
      intro s. 
      destruct (decide (ExtcallInvariantsDefined L)); try discriminate.
      destruct (decide (PrimcallInvariantsDefined L)); try discriminate.
      destruct (decide (get_layer_prim_valid L s)); try discriminate.
      destruct (make_program s (i ↦ f) L) eqn:Heqr; simpl in *; try discriminate.
      eauto.
    - (* sig *) auto.
    - simpl. 
      intros.
      destruct (decide (ExtcallInvariantsDefined L)) as [ Hext | ] ; try discriminate.
      destruct (decide (PrimcallInvariantsDefined L)) as [ Hprim | ]; try discriminate.
      destruct (decide (get_layer_prim_valid L s)) as [ Hlayerprim | ]; try discriminate.
      destruct (make_program _ _ _) eqn:MAKEPROG; try discriminate.
      generalize MAKEPROG.
      intro MAKEGENV.
      apply make_program_make_globalenv in MAKEGENV.
      generalize (H _ _ _ _ _ _ _ H2 MAKEPROG H0).
      revert MAKEGENV.
      pose proof Hmkp as Hmkp'.
      revert Hmkp'.
      clear.
      intros.
      inversion H; subst.
      unfold ge in *. clear ge.
      assert (MAKEGENV': (make_globalenv s (i ↦ f) L = ret (Genv.globalenv p))) by assumption.
      inv_make_globalenv MAKEGENV'.
      replace f0 with (Internal f) in * by congruence; clear f0.
      econstructor.
      esplit.
      split.
      eassumption.
      split.
      eassumption.
      split.
      assumption.
      eapply ClightBigstep.eval_funcall_steps; eauto.
      repeat constructor.
  * (* none *)
    rewrite get_layer_primitive_mapsto_other_primitive; eauto.
    apply lower_bound.
}
{ (* variables *)
  intro i0.
  rewrite get_layer_globalvar_mapsto_primitive.
  match goal with
    | |- res_le _ _ ?x => destruct x as  [ [ ? | ] | ?]
  end;
    repeat constructor.
}
{ (* exec_load *)
  reflexivity.
}
{ (* exec_store *)
  reflexivity.
}

Qed.

Lemma primitive_le_compatsem_le_right {D} (σ1 σ2 σ3: compatsem D):
  primitive_le σ1 σ2 ->
  compatsem_le D σ2 σ3 ->
  primitive_le σ1 σ3.
Proof.
  intros Hσ12 Hσ23.
  destruct Hσ12 as [σe1 σe2 Hvalid12 Hsig12 Hstep12].
  inversion Hσ23 as [σe2' σe3 Hσe23 | ]; clear Hσ23; subst.
  destruct σe1 as [σe1 props1 invs1]; simpl in *.
  destruct σe2 as [σe2 props2 invs2]; simpl in *.
  destruct σe3 as [σe3 props3 invs3]; simpl in *.
  destruct Hσe23 as [[Hstep23 Hsig23 Hvalid23] Hinvs23].
  constructor; simpl in *; try rel_auto.
  unfold sextcall_sig in *. congruence.
Qed.

Lemma spec_le_right {D}
      (L1 L2 L3: _ D)
      (Hspec12: spec_le L1 L2)
      (Hle23: cl_sim _ _ id L2 L3)
:
  spec_le L1 L3.
Proof.
  destruct Hspec12 as [Hprim12 Hvar12 Hload12 Hstore12].
  destruct Hle23 as [Hbase23 Hload23 Hstore23].
  apply cl_le_layer_pointwise in Hbase23.
  destruct Hbase23 as [Hprim23 Hvar23].

  constructor. 
{ (* primitives *)
  intros i.
  specialize (Hprim12 i); specialize (Hprim23 i).
  clear Hvar12 Hvar23 Hload12 Hload23 Hstore12 Hstore23.
  revert Hprim12 Hprim23.
  generalize (get_layer_primitive i L1), (get_layer_primitive i L2), (get_layer_primitive i L3).
  intros prim1 prim2 prim3 Hprim12 Hprim23.
  (* XXX: this should be general theorems about [res_le], [option_le]. *)
  destruct Hprim23 as [σ2 σ3 Hσ23 Hσ3 | ]; try constructor.
  inversion Hprim12 as [σ1 σ2' Hσ12 | σ1 Hσ1]; subst.
  constructor.
  destruct Hσ12 as [σ2 | σ1 σ2 Hσ12]; try constructor.
  inversion Hσ23 as [σ3' | σ2' σ3' Hσ23']; subst.
  constructor.
  eapply primitive_le_compatsem_le_right;
  eassumption.
}
{ (* variables *)
  intro; etransitivity; eauto.
}
{ (* exec_load *)
  etransitivity; eauto.
}
{ (* exec_store *)
  etransitivity; eauto.
}

Qed.

End WITH_MEMORY_MODEL.
