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
(** I64 builtins layer *)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcertx.backend.I64helpers.
Require Import compcert.backend.SelectLong.
Require Import compcertx.backend.SelectLongproofX.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.compcertx.Observation.

(** Missing lemma from [PseudoJoin] *)

Section WITHPSEUDOJOIN.
  Context `{PseudoJoin}.

  Lemma split_le_left:
    forall a b c,
      (a ⊕ b) ≤ c ->
      a ≤ c.
  Proof.
    intros. etransitivity. eapply left_upper_bound. eassumption.
  Qed.

  Lemma split_le_right:
    forall a b c,
      (a ⊕ b) ≤ c ->
      b ≤ c.
  Proof.
    intros until c.
    rewrite commutativity.
    eapply split_le_left.
  Qed.
End WITHPSEUDOJOIN.

Ltac split_le :=
  match goal with
    | [ H: ?a ⊕ ?b ≤ ?c |- _ ] =>
      let Hl := fresh H "l" in
      let Hr := fresh H "r" in
      generalize (split_le_left _ _ _ H);
        generalize (split_le_right _ _ _ H);
        clear H;
        intros Hr Hl
  end.   

Section WITHSTENCIL.
Context `{Hobs: Observation}.
Context `{Hstencil: Stencil}.

Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.

Context {D: compatdata}.

  Definition csem_info step args res: sextcall_info (mem := mwd D) :=
    {|
      sextcall_step := step;
      sextcall_csig := mkcsig args res;
      sextcall_valid := const (B := stencil) true
    |}.

  Definition csem_full (sem: sextcall_info (mem := mwd D)) :=
    fun `{!ExtcallProperties sem} `{!ExtcallInvariants sem} =>
      {|
        sextcall_primsem_step := sem;
        sextcall_props := OK _;
        sextcall_invs := OK _
      |}.

  (** longoffloat *)

  Inductive sextcall_longoffloat_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_longoffloat_step_intro
      x z
      (Hxz: Val.longoffloat x = Some z)
      m :
      sextcall_longoffloat_step s WB (x :: nil) m z m
  .

  Definition sextcall_longoffloat_info :=
    csem_info
      sextcall_longoffloat_step
      (Tcons (Tfloat F64 noattr) Tnil)
      (Tlong Signed noattr).

  Instance sextcall_longoffloat_properties:
    ExtcallProperties sextcall_longoffloat_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longoffloat f); try discriminate.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longoffloat f); try discriminate.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longoffloat f0); try discriminate.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_longoffloat_invariants:
    ExtcallInvariants sextcall_longoffloat_info.
  Proof.
    constructor; inversion 1; try congruence; try reflexivity.
    * (* inject neutral *)
      subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longoffloat f); try discriminate.
      inv Hxz. constructor.
    * (* type *)
      subst.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longoffloat f); try discriminate.
      inv Hxz.
      constructor.
  Qed.

  Definition sextcall_longoffloat_primsem: sextcall_primsem D :=
    csem_full sextcall_longoffloat_info.

  Definition sextcall_longoffloat_compatsem: compatsem D :=
    inl sextcall_longoffloat_primsem.

  (** longuoffloat *)

  Inductive sextcall_longuoffloat_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_longuoffloat_step_intro
      x z
      (Hxz: Val.longuoffloat x = Some z)
      m :
      sextcall_longuoffloat_step s WB (x :: nil) m z m
  .

  Definition sextcall_longuoffloat_info :=
    csem_info
      sextcall_longuoffloat_step
      (Tcons (Tfloat F64 noattr) Tnil)
      (Tlong Unsigned noattr).

  Instance sextcall_longuoffloat_properties:
    ExtcallProperties sextcall_longuoffloat_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longuoffloat f); try discriminate.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longuoffloat f); try discriminate.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longuoffloat f0); try discriminate.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_longuoffloat_invariants:
    ExtcallInvariants sextcall_longuoffloat_info.
  Proof.
    constructor; inversion 1; try congruence; try reflexivity.
    * (* inject neutral *)
      subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longuoffloat f); try discriminate.
      inv Hxz. constructor.
    * (* type *)
      subst.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct (Float.longuoffloat f); try discriminate.
      inv Hxz.
      constructor.
  Qed.


  Definition sextcall_longuoffloat_primsem: sextcall_primsem D :=
    csem_full sextcall_longuoffloat_info.

  Definition sextcall_longuoffloat_compatsem: compatsem D :=
    inl sextcall_longuoffloat_primsem.

  (** floatoflong *)

  Inductive sextcall_floatoflong_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_floatoflong_step_intro
      x z
      (Hxz: Val.floatoflong x = Some z)
      m :
      sextcall_floatoflong_step s WB (x :: nil) m z m
  .

  Definition sextcall_floatoflong_info :=
    csem_info
      sextcall_floatoflong_step
      (Tcons (Tlong Signed noattr) Tnil)
      (Tfloat F64 noattr).

  Instance sextcall_floatoflong_properties:
    ExtcallProperties sextcall_floatoflong_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_floatoflong_invariants:
    ExtcallInvariants sextcall_floatoflong_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      constructor.
  Qed.

  Definition sextcall_floatoflong_primsem: sextcall_primsem D :=
    csem_full sextcall_floatoflong_info.

  Definition sextcall_floatoflong_compatsem: compatsem D :=
    inl sextcall_floatoflong_primsem.

  (** floatoflongu *)
  
  Inductive sextcall_floatoflongu_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_floatoflongu_step_intro
      x z
      (Hxz: Val.floatoflongu x = Some z)
      m :
      sextcall_floatoflongu_step s WB (x :: nil) m z m
  .

  Definition sextcall_floatoflongu_info :=
    csem_info
      sextcall_floatoflongu_step
      (Tcons (Tlong Unsigned noattr) Tnil)
      (Tfloat F64 noattr).

  Instance sextcall_floatoflongu_properties:
    ExtcallProperties sextcall_floatoflongu_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_floatoflongu_invariants:
    ExtcallInvariants sextcall_floatoflongu_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      constructor.
  Qed.

  Definition sextcall_floatoflongu_primsem: sextcall_primsem D :=
    csem_full sextcall_floatoflongu_info.

  Definition sextcall_floatoflongu_compatsem: compatsem D :=
    inl sextcall_floatoflongu_primsem.
  
  (** singleoflong *)

  Inductive sextcall_singleoflong_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_singleoflong_step_intro
      x z
      (Hxz: Val.singleoflong x = Some z)
      m :
      sextcall_singleoflong_step s WB (x :: nil) m z m
  .

  Definition sextcall_singleoflong_info :=
    csem_info
      sextcall_singleoflong_step
      (Tcons (Tlong Signed noattr) Tnil)
      (Tfloat F32 noattr).

  Instance sextcall_singleoflong_properties:
    ExtcallProperties sextcall_singleoflong_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      simpl. rewrite <- Float.singleoflong_idem. apply Float.singleoffloat_is_single.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_singleoflong_invariants:
    ExtcallInvariants sextcall_singleoflong_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      simpl. rewrite <- Float.singleoflong_idem. apply Float.singleoffloat_is_single.
  Qed.

  Definition sextcall_singleoflong_primsem: sextcall_primsem D :=
    csem_full sextcall_singleoflong_info.

  Definition sextcall_singleoflong_compatsem: compatsem D :=
    inl sextcall_singleoflong_primsem.

  (** singleoflongu *)
  
  Inductive sextcall_singleoflongu_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_singleoflongu_step_intro
      x z
      (Hxz: Val.singleoflongu x = Some z)
      m :
      sextcall_singleoflongu_step s WB (x :: nil) m z m
  .

  Definition sextcall_singleoflongu_info :=
    csem_info
      sextcall_singleoflongu_step
      (Tcons (Tlong Unsigned noattr) Tnil)
      (Tfloat F32 noattr).

  Instance sextcall_singleoflongu_properties:
    ExtcallProperties sextcall_singleoflongu_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      simpl.
      unfold Float.singleoflongu.
      esplit. reflexivity.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_singleoflongu_invariants:
    ExtcallInvariants sextcall_singleoflongu_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      simpl in Hxz.
      inv Hxz.
      simpl.
      unfold Float.singleoflongu.
      esplit. reflexivity.
  Qed.

  Definition sextcall_singleoflongu_primsem: sextcall_primsem D :=
    csem_full sextcall_singleoflongu_info.

  Definition sextcall_singleoflongu_compatsem: compatsem D :=
    inl sextcall_singleoflongu_primsem.

  (** divls *)

  Inductive sextcall_divls_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_divls_step_intro
      x y z
      (Hxz: Val.divls x y = Some z)
      m :
      sextcall_divls_step s WB (x :: y :: nil) m z m
  .

  Definition sextcall_divls_info :=
    csem_info
      sextcall_divls_step
      (Tcons (Tlong Signed noattr) (Tcons (Tlong Signed noattr) Tnil))
      (Tlong Signed noattr).

  Instance sextcall_divls_properties:
    ExtcallProperties sextcall_divls_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4. inv H5. inv H8.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      inv H5. inv H8.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_divls_invariants:
    ExtcallInvariants sextcall_divls_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct y; try discriminate.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      constructor.
  Qed.

  Definition sextcall_divls_primsem: sextcall_primsem D :=
    csem_full sextcall_divls_info.

  Definition sextcall_divls_compatsem: compatsem D :=
    inl sextcall_divls_primsem.

  (** divlu *)

  Inductive sextcall_divlu_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_divlu_step_intro
      x y z
      (Hxz: Val.divlu x y = Some z)
      m :
      sextcall_divlu_step s WB (x :: y :: nil) m z m
  .

  Definition sextcall_divlu_info :=
    csem_info
      sextcall_divlu_step
      (Tcons (Tlong Unsigned noattr) (Tcons (Tlong Unsigned noattr) Tnil))
      (Tlong Unsigned noattr).

  Instance sextcall_divlu_properties:
    ExtcallProperties sextcall_divlu_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4. inv H5. inv H8.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      inv H5. inv H8.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_divlu_invariants:
    ExtcallInvariants sextcall_divlu_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct y; try discriminate.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      constructor.
  Qed.

  Definition sextcall_divlu_primsem: sextcall_primsem D :=
    csem_full sextcall_divlu_info.

  Definition sextcall_divlu_compatsem: compatsem D :=
    inl sextcall_divlu_primsem.

  (** modls *)

  Inductive sextcall_modls_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_modls_step_intro
      x y z
      (Hxz: Val.modls x y = Some z)
      m :
      sextcall_modls_step s WB (x :: y :: nil) m z m
  .

  Definition sextcall_modls_info :=
    csem_info
      sextcall_modls_step
      (Tcons (Tlong Signed noattr) (Tcons (Tlong Signed noattr) Tnil))
      (Tlong Signed noattr).

  Instance sextcall_modls_properties:
    ExtcallProperties sextcall_modls_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4. inv H5. inv H8.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      inv H5. inv H8.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_modls_invariants:
    ExtcallInvariants sextcall_modls_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct y; try discriminate.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (
          Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) &&
               Int64.eq i0 Int64.mone
        ); try discriminate.
      inv Hxz.
      constructor.
  Qed.

  Definition sextcall_modls_primsem: sextcall_primsem D :=
    csem_full sextcall_modls_info.

  Definition sextcall_modls_compatsem: compatsem D :=
    inl sextcall_modls_primsem.

  (** modlu *)

  Inductive sextcall_modlu_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_modlu_step_intro
      x y z
      (Hxz: Val.modlu x y = Some z)
      m :
      sextcall_modlu_step s WB (x :: y :: nil) m z m
  .

  Definition sextcall_modlu_info :=
    csem_info
      sextcall_modlu_step
      (Tcons (Tlong Unsigned noattr) (Tcons (Tlong Unsigned noattr) Tnil))
      (Tlong Unsigned noattr).

  Instance sextcall_modlu_properties:
    ExtcallProperties sextcall_modlu_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      constructor.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      inversion 2; subst. inv H6.
      inv H4. inv H5. inv H8.
      esplit. esplit. split.
      econstructor; eauto.
      split; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      generalize Hxz.
      intro Hy.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      inversion 2; subst.
      inv H5. inv H7.
      inv H5. inv H8.
      intros.
      esplit. esplit. esplit. split.
      econstructor; eauto.
      split. econstructor.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_modlu_invariants:
    ExtcallInvariants sextcall_modlu_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; try discriminate.
      simpl in Hxz.
      destruct y; try discriminate.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz. constructor.  
    * (* type *)
      subst.
      destruct x; try discriminate.
      destruct y; try discriminate.
      simpl in Hxz.
      destruct (Int64.eq i0 Int64.zero); try discriminate.
      inv Hxz.
      constructor.
  Qed.

  Definition sextcall_modlu_primsem: sextcall_primsem D :=
    csem_full sextcall_modlu_info.

  Definition sextcall_modlu_compatsem: compatsem D :=
    inl sextcall_modlu_primsem.

  (** shll *)

  Inductive sextcall_shll_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_shll_step_intro
      x y z
      (Hxz: Val.shll x y = z)
      m :
      sextcall_shll_step s WB (x :: y :: nil) m z m
  .

  Definition sextcall_shll_info :=
    csem_info
      sextcall_shll_step
      (Tcons (Tlong Signed noattr) (Tcons (Tint I32 Unsigned noattr) Tnil))
      (Tlong Signed noattr).
    
  Instance sextcall_shll_properties:
    ExtcallProperties sextcall_shll_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; simpl; auto.
      destruct y; simpl; auto.
      destruct (Int.ltu i0 Int64.iwordsize'); simpl; auto.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      inversion 2; subst. inv H6. inv H8.
      esplit. esplit. split.
      econstructor. reflexivity.
      split. 
      inv H4; simpl; auto.
      destruct v2; simpl; auto.
      inv H5; simpl; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      inversion 2; subst.
      inv H7. inv H9.
      esplit. esplit. esplit.
      split. econstructor. reflexivity.
      instantiate (1 := f).
      split.
       inv H5; simpl; auto.
       inv H6; simpl; auto.
       destruct (Int.ltu i0 Int64.iwordsize'); auto.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_shll_invariants:
    ExtcallInvariants sextcall_shll_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; simpl; try (constructor; fail).
      destruct y; simpl; try (constructor; fail).
      destruct (Int.ltu i0 Int64.iwordsize'); constructor.
    * (* type *)
      subst.
      destruct x; simpl; auto.
      destruct y; simpl; auto.
      destruct (Int.ltu i0 Int64.iwordsize'); simpl; auto.
  Qed.

  Definition sextcall_shll_primsem: sextcall_primsem D :=
    csem_full sextcall_shll_info.

  Definition sextcall_shll_compatsem: compatsem D :=
    inl sextcall_shll_primsem.
  
  (** shrlu *)

  Inductive sextcall_shrlu_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_shrlu_step_intro
      x y z
      (Hxz: Val.shrlu x y = z)
      m :
      sextcall_shrlu_step s WB (x :: y :: nil) m z m
  .

  Definition sextcall_shrlu_info :=
    csem_info
      sextcall_shrlu_step
      (Tcons (Tlong Unsigned noattr) (Tcons (Tint I32 Unsigned noattr) Tnil))
      (Tlong Signed noattr).
    
  Instance sextcall_shrlu_properties:
    ExtcallProperties sextcall_shrlu_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; simpl; auto.
      destruct y; simpl; auto.
      destruct (Int.ltu i0 Int64.iwordsize'); simpl; auto.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      inversion 2; subst. inv H6. inv H8.
      esplit. esplit. split.
      econstructor. reflexivity.
      split. 
      inv H4; simpl; auto.
      destruct v2; simpl; auto.
      inv H5; simpl; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      inversion 2; subst.
      inv H7. inv H9.
      esplit. esplit. esplit.
      split. econstructor. reflexivity.
      instantiate (1 := f).
      split.
       inv H5; simpl; auto.
       inv H6; simpl; auto.
       destruct (Int.ltu i0 Int64.iwordsize'); auto.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_shrlu_invariants:
    ExtcallInvariants sextcall_shrlu_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; simpl; try (constructor; fail).
      destruct y; simpl; try (constructor; fail).
      destruct (Int.ltu i0 Int64.iwordsize'); constructor.
    * (* type *)
      subst.
      destruct x; simpl; auto.
      destruct y; simpl; auto.
      destruct (Int.ltu i0 Int64.iwordsize'); simpl; auto.
  Qed.

  Definition sextcall_shrlu_primsem: sextcall_primsem D :=
    csem_full sextcall_shrlu_info.

  Definition sextcall_shrlu_compatsem: compatsem D :=
    inl sextcall_shrlu_primsem.

  (** shrl *)

  Inductive sextcall_shrl_step (s: stencil) (WB: block -> Prop):
    list val -> mwd D -> val -> mwd D -> Prop :=
  | sextcall_shrl_step_intro
      x y z
      (Hxz: Val.shrl x y = z)
      m :
      sextcall_shrl_step s WB (x :: y :: nil) m z m
  .

  Definition sextcall_shrl_info :=
    csem_info
      sextcall_shrl_step
      (Tcons (Tlong Signed noattr) (Tcons (Tint I32 Unsigned noattr) Tnil))
      (Tlong Signed noattr).
    
  Instance sextcall_shrl_properties:
    ExtcallProperties sextcall_shrl_info.
  Proof.
    constructor; try (inversion 1; congruence).
    * (* type *)
      inversion 1; subst.
      destruct x; simpl; auto.
      destruct y; simpl; auto.
      destruct (Int.ltu i0 Int64.iwordsize'); simpl; auto.
    * (* unchanged_on loc_not_writable *)
      inversion 1; subst. apply Mem.unchanged_on_refl.
    * (* extends *)
      inversion 1; subst.
      inversion 2; subst. inv H6. inv H8.
      esplit. esplit. split.
      econstructor. reflexivity.
      split. 
      inv H4; simpl; auto.
      destruct v2; simpl; auto.
      inv H5; simpl; auto.
      split; auto.
      apply Mem.unchanged_on_refl.
    * (* injects *)
      inversion 2; subst.
      inversion 2; subst.
      inv H7. inv H9.
      esplit. esplit. esplit.
      split. econstructor. reflexivity.
      instantiate (1 := f).
      split.
       inv H5; simpl; auto.
       inv H6; simpl; auto.
       destruct (Int.ltu i0 Int64.iwordsize'); auto.
      split. eassumption.
      split. apply Mem.unchanged_on_refl.
      split. apply Mem.unchanged_on_refl.
      split. apply inject_incr_refl.
      intro. congruence.
    * (* determ *)
      inversion 1; inversion 1; split; congruence.
    * (* WB weak *)
      inversion 2; subst; econstructor; eauto.
  Qed.

  Instance sextcall_shrl_invariants:
    ExtcallInvariants sextcall_shrl_info.
  Proof.
    constructor; inversion 1; try congruence; try xomega.
    * (* inject neutral *)
      inversion 1; subst.
      split; auto.
      destruct x; simpl; try (constructor; fail).
      destruct y; simpl; try (constructor; fail).
      destruct (Int.ltu i0 Int64.iwordsize'); constructor.
    * (* type *)
      subst.
      destruct x; simpl; auto.
      destruct y; simpl; auto.
      destruct (Int.ltu i0 Int64.iwordsize'); simpl; auto.
  Qed.

  Definition sextcall_shrl_primsem: sextcall_primsem D :=
    csem_full sextcall_shrl_info.

  Definition sextcall_shrl_compatsem: compatsem D :=
    inl sextcall_shrl_primsem.

  (** Pack everything in a single layer *)

  Definition L64: compatlayer D :=
    ((i64_dtos hf) ↦ sextcall_longoffloat_compatsem)
      ⊕ ((i64_dtou hf) ↦ sextcall_longuoffloat_compatsem)
      ⊕ ((i64_stod hf) ↦ sextcall_floatoflong_compatsem)
      ⊕ ((i64_utod hf) ↦ sextcall_floatoflongu_compatsem)
      ⊕ ((i64_stof hf) ↦ sextcall_singleoflong_compatsem)
      ⊕ ((i64_utof hf) ↦ sextcall_singleoflongu_compatsem)
      ⊕ ((i64_sdiv hf) ↦ sextcall_divls_compatsem)
      ⊕ ((i64_udiv hf) ↦ sextcall_divlu_compatsem)
      ⊕ ((i64_smod hf) ↦ sextcall_modls_compatsem)
      ⊕ ((i64_umod hf) ↦ sextcall_modlu_compatsem)
      ⊕ ((i64_shl hf) ↦ sextcall_shll_compatsem)
      ⊕ ((i64_shr hf) ↦ sextcall_shrlu_compatsem)
      ⊕ ((i64_sar hf) ↦ sextcall_shrl_compatsem).

  (** Prove that any layer [L ≥ L64] *which has no "magic"* yields a
  correct [ExternalCallI64helpers].*)

(** We guarantee that I64 helpers have a well-defined (and correct)
semantics only if the global environment matches some stencil. To this
end, we specified the [GenvValidOps] and [GenvValid] classes, which we
now need to instantiate accordingly. *)

  Definition stencil_valid {D} (s: stencil) (p: compatsem D): Prop :=
    match p with
      | inl p' => sextcall_valid p' s = true
      | _ => True
    end.

  Global Instance stencil_matches_genv_valid_ops {D} (L: _ D): GenvValidOps :=
    {
      genv_valid F V ge :=
        exists s, stencil_matches s ge /\
                  forall (i: ident) p, get_layer_primitive i L = OK (Some p) ->
                                       stencil_valid s p

    }.
  
  Global Instance stencil_matches_genv_valid {D} (L: _ D): GenvValid (genv_valid_ops := stencil_matches_genv_valid_ops L).
  Proof.
    constructor.
    intros.
    destruct VALID as (s & ? & ?).
    exists s.
    split; eauto; eapply stencil_matches_preserves_symbols; try eassumption; eauto.
  Qed.

  Theorem L64_correct:
    forall L, L64 ≤ L ->
              LayerOK L ->
              ExternalCallI64Helpers (genv_valid_ops := stencil_matches_genv_valid_ops L) (CompCertBuiltins.external_functions_sem (ExternalCallsOpsX := compatlayer_extcall_ops_x L)) hf.
  Proof.
    Opaque hf get_layer_primitive.
    unfold L64.
    intros.
    repeat split_le.
    constructor; simpl; intros; intro; intros;
    destruct VALID as (s & Hs & PRIMVALID);
    unfold stencil_valid in PRIMVALID;
    match goal with
      | [ H: ?i ↦ ?σ ≤ L |- context [ get_layer_primitive ?i L ] ] =>
        destruct (get_layer_primitive_mapsto_le_ok L i σ H) as (σ' & Hσ'eq & Hσ'le);
          rewrite Hσ'eq
    end;
    esplit; split; eauto;
    eapply compatsem_extcall_le; eauto;
    repeat (econstructor; eauto);
    try (intros s' Hmatch'; replace s' with s in * by (eapply stencil_matches_unique; eauto);
    eapply PRIMVALID; eauto; fail);
    econstructor; eauto.
  Qed.

End WITHSTENCIL.
