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
Require Import compcert.common.Memtype.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MemWithData.
Require Export liblayers.compcertx.GenSem.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.


(** * Generic [compatsem] *)

Section SEMANTICS.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel} `{Hmwd: UseMemWithData mem}.
  Context {D} `{HD: CompatData D}.
  Context `{Tsemof: Semof (cdata D)} `{Hsemof: !Semprops T}.


  (** ** Using [extcall_sem] *)

  Inductive sextcall_generic_sem (f: T) (s: stencil) (WB: block -> Prop):
    list val -> mwd (cdata D) -> val -> mwd (cdata D) -> Prop :=
      extcall_generic_sem_intro l m d v d':
        semof f l d v d' ->
        sextcall_generic_sem f s WB l (m, d) v (m, d').

  Ltac inv_extcall_generic :=
    match goal with
      [ H: sextcall_generic_sem _ _ _ _ _ _ _ _ |- _ ] => inversion H; subst
    end.

  Definition sextcall_generic_info (f: T) :=
    {|
      sextcall_step := sextcall_generic_sem f;
      sextcall_csig := mkcsig targs tres;
      sextcall_valid s := true
    |}.

  Local Instance extcall_generic_properties (f: T):
    ExtcallProperties (sextcall_generic_info f).
  Proof.
    split.
    * intros s WB _ _ _ _ [l m d v d' H].
      eapply semprops_well_typed.
      eassumption.
    * intros s WB _ _ _ _ b [l m d v d' H] Hb.
      exact Hb.
    * intros s WB _ _ _ _ b ofs p [l m d v d' H] Hvalid Hperm.
      exact Hperm.
    * intros s WB _ _ _ _ [l m d v d' H].
      simpl.
      eauto with mem.
    * intros s WB _ _ _ _ [m2 d2] vargs2 [vargs1 m1 d1 v d' H] Hm2 Hvargs2.
      lift_auto. subst. (* d1 = d2 *)
      exists v, (m2, d').
      repeat split.
      + eapply semprops_lessdef in Hvargs2; eauto.
        subst.
        assumption.
      + apply Val.lessdef_refl.
      + change (m2, d') with ((fun m => set fst m (m1, d')) m2).
        constructor.
        assumption.
      + apply Mem.unchanged_on_refl.
    * intros s WB WB' _ _ _ _ ι [m2 d2] vargs2 Hι [vargs1 m1 d1 v d' H].
      intros Hm Hvargs HWB.
      lift_auto. subst. (* d1 = d2 *)
      exists ι, v, (m2, d').
      repeat split.
      + eapply semprops_inject in Hvargs; eauto.
        subst.
        assumption.
      + eapply semprops_inject_neutral.
        eassumption.
      + change (m2, d') with ((fun m => set fst m (m1, d')) m2).
        constructor.
        assumption.
      + apply Mem.unchanged_on_refl.
      + apply Mem.unchanged_on_refl.
      + apply inject_incr_refl.
      + rewrite H0 in H1; discriminate.
      + rewrite H0 in H1; discriminate.
    * intros s WB _ _ _ _ v2 [m2 d2] [l m1 d v1 d1 Ha] H.
      simpl in H.
      inversion H as [xl xm2 xd xv1 xd2 Hb]; subst.
      edestruct semprops_determ; [apply Ha | apply Hb | ].
      subst; eauto.
    * intros s WB1 WB2 _ _ _ _ HWB [l m d v d' H].
      constructor.
      assumption.
    * intros s WB _ _ _ _ b chunk o [l m d v d' H] Hvalid Hb.
      reflexivity.
  Qed.

  (** Preservation of the low-level and high-level invariants cannot
    be shown in a generic way since they involves abstract
    data. Instead, we expect the user to provide an instance of the
    following class. *)

  Class PreservesInvariants (f: T) :=
    {
      semprops_low_level_invariant vargs m d vres d':
        semof f vargs d vres d' ->
        low_level_invariant m d ->
        low_level_invariant m d';
      semprops_high_level_invariant vargs d vres d':
        semof f vargs d vres d' ->
        high_level_invariant d ->
        high_level_invariant d';
      semprops_kernel_mode vargs d vres d':
        semof f vargs d vres d' ->
        kernel_mode d ->
        kernel_mode d'
    }.

  Local Instance extcall_generic_invariants f:
    PreservesInvariants f ->
    ExtcallInvariants (D := cdata D) (sextcall_generic_info f).
  Proof.
    intros Hf.
    split.
    * intros s WB vargs m d m' d' vres H Hd.
      inversion H; subst.
      eapply semprops_low_level_invariant;
      eassumption.
    * intros s WB vargs m d m' d' vres H Hd.
      inversion H; subst.
      eapply semprops_high_level_invariant;
      eassumption.
    * intros s WB vargs m d m' d' vres H Hd.
      inversion H; subst.
      eapply semprops_kernel_mode;
      eassumption.
    * intros s WB vargs m d m' d' vres H.
      inversion H; subst.
      reflexivity.
    * intros s WB l m d v m' d' H.
      inversion H; subst.
      intros; split.
      + eapply semprops_inject_neutral.
        eassumption.
      + assumption.
    * intros s WB _ _ _ _ [l m d v d' H].
      eapply semprops_well_typed.
      eassumption.
  Qed.

  Definition gensem (f: T) `{PreservesInvariants f}: compatsem (cdata D) :=
    inl {|
      sextcall_primsem_step := sextcall_generic_info f;
      sextcall_props := OK _;
      sextcall_invs := OK _
    |}.

  (** ** Using [primcall_sem] *)

  Inductive primcall_generic_sem (f: T) (s: stencil):
    Asm.regset -> mwd (cdata D) -> Asm.regset -> mwd (cdata D) -> Prop :=
      primcall_generic_sem_intro rs m d d':
        semof f nil d Vundef d' ->
        primcall_generic_sem f s rs (m, d) (Asm.nextinstr rs) (m, d').

  Lemma primcall_generic_determ (f: T) s rs m rs1 rs2 m1 m2:
    primcall_generic_sem f s rs m rs1 m1 ->
    primcall_generic_sem f s rs m rs2 m2 ->
    m1 = m2 /\ rs1 = rs2.
  Proof.
    intros H1 H2.
    inv H1.
    inv H2.
    exploit semprops_determ.
    eexact H.
    eexact H6.
    intros [_ Hd]; subst.
    tauto.
  Qed.
End SEMANTICS.


(** * Tactics *)

(** This tactic is used to prove [extcall_generic_sem] goals. *)

Ltac extcall_generic_sem_intro :=
  repeat econstructor; autorewrite with monad.

(** Inversion tactic for extcall_generic_sem and the like *)

Ltac inv_generic_sem H :=
  lazymatch type of H with

    (** FIXME: probably not the right number of arguments *)
    | external_call _ _ _ _ _ _ _ =>

      simpl in H;
      inv_generic_sem H

    | sextcall_generic_sem ?f _ _ _ _ _ _ =>

      let args := fresh "args" in
      let m := fresh "m" in
      let v := fresh "v" in
      let d' := fresh "d'" in
      let Hsemof := fresh "Hsemof" in
      let Hargs := fresh "Hargs" in
      let Hm := fresh "Hm" in
      let Hv := fresh "Hv" in
      let Ht := fresh "Ht" in
      let Hd' := fresh "Hd'" in
      inversion H as [args m d v d' Hsemof Hargs Hm Hv Hm'];

      (** For pure functions, it will be the case that [m = m'].
        Then, we can replace [d'] with [Mem.get_abstract_data m]
        with no loss of information. Once we move to lens, we can
        actually use [same_context] to relate [m] and [m'] in a
        generic way, and do that all the time. *)
      (** FIXME: this needs to be updated <<
      try match type of Hd' with
            Mem.put_abstract_data ?m ?d' = ?m =>
              apply (f_equal Mem.get_abstract_data) in Hd';
              rewrite Mem.get_put_abstract_data in Hd'
          end; >> *)

      subst;
      clear H;
      rename Hsemof into H;
      inv_generic_sem H

    | primcall_generic_sem ?f _ _ _ _ _ _ _ _ _ _ =>

      let rs := fresh "rs" in
      let m := fresh "m" in
      let d' := fresh "d'" in
      let Hsemof := fresh "Hsemof" in
      let Hargs := fresh "Hargs" in
      let Hrs := fresh "Hrs" in
      let Hm := fresh "Hm" in
      let Hv := fresh "Hv" in
      let Ht := fresh "Ht" in
      let Hrs' := fresh "Hrs'" in
      let Hm' := fresh "Hm'" in
      inversion H as [m d' rs Hsemof Hargs Hrs Hm Ht Hv Hrs' Hm'];
      subst;
      clear H;
      rename Hsemof into H;
      inv_generic_sem H

    | semof ?f _ _ _ _ =>

      unfold semof in H;
      inv_generic_sem H

    | semof_nil_void _ _ _ _ _ =>

      let f := fresh "f" in
      let d := fresh "d" in
      let d' := fresh "d'" in
      let Hfd := fresh "Hfd" in
      let Hf := fresh "Hf" in
      let Hargs := fresh "Hargs" in
      let Hd := fresh "Hd" in
      let Hv := fresh "Hv" in
      let Hd' := fresh "Hd'" in
      inversion H as [f d d' Hfd Hf Hargs Hd Hv Hd'];
      subst;
      clear H;
      rename Hfd into H;
      inv_generic_sem H

    | semof_nil_int _ _ _ _ _ =>

      let f := fresh "f" in
      let d := fresh "d" in
      let z := fresh "z" in
      let d' := fresh "d'" in
      let Hfd := fresh "Hfd" in
      let Hf := fresh "Hf" in
      let Hargs := fresh "Hargs" in
      let Hd := fresh "Hd" in
      let Hv := fresh "Hv" in
      let Hd' := fresh "Hd'" in
      inversion H as [f d z d' Hfd Hf Hargs Hd Hv Hd'];
      subst;
      clear H;
      rename Hfd into H;
      inv_generic_sem H

    | semof_nil_int_pure _ _ _ _ _ =>

      unfold semof_nil_int_pure in H;
      inv_generic_sem H

    | semof_nil_int_pure_total _ _ _ _ _ =>

      unfold semof_nil_int_pure_total in H;
      inv_generic_sem H

    | semof_cons _ _ _ _ _ =>

      let f := fresh "f" in
      let i := fresh "i" in
      let args := fresh "args" in
      let d := fresh "d" in
      let v := fresh "v" in
      let d' := fresh "d'" in
      let Hfd := fresh "Hfd" in
      let Hf := fresh "Hf" in
      let Hargs := fresh "Hargs" in
      let Hd := fresh "Hd" in
      let Hv := fresh "Hv" in
      let Hd' := fresh "Hd'" in
      inversion H as [f i args d v d' Hfd Hf Hargs Hd Hv Hd'];
      subst;
      clear H;
      rename Hfd into H;
      inv_generic_sem H

    | semof_nil_int64 _ _ _ _ _ =>

      let f := fresh "f" in
      let d := fresh "d" in
      let z := fresh "z" in
      let d' := fresh "d'" in
      let Hfd := fresh "Hfd" in
      let Hf := fresh "Hf" in
      let Hargs := fresh "Hargs" in
      let Hd := fresh "Hd" in
      let Hv := fresh "Hv" in
      let Hd' := fresh "Hd'" in
      inversion H as [f d z d' Hfd Hf Hargs Hd Hv Hd'];
      subst;
      clear H;
      rename Hfd into H;
      inv_generic_sem H

    | semof_nil_int64_pure _ _ _ _ _ =>

      unfold semof_nil_int64_pure in H;
      inv_generic_sem H

    | semof_nil_int64_pure_total _ _ _ _ _ =>

      unfold semof_nil_int64_pure_total in H;
      inv_generic_sem H

    | semof_cons64 _ _ _ _ _ =>

      let f := fresh "f" in
      let i := fresh "i" in
      let args := fresh "args" in
      let d := fresh "d" in
      let v := fresh "v" in
      let d' := fresh "d'" in
      let Hfd := fresh "Hfd" in
      let Hf := fresh "Hf" in
      let Hargs := fresh "Hargs" in
      let Hd := fresh "Hd" in
      let Hv := fresh "Hv" in
      let Hd' := fresh "Hd'" in
      inversion H as [f i args d v d' Hfd Hf Hargs Hd Hv Hd'];
      subst;
      clear H;
      rename Hfd into H;
      inv_generic_sem H

    (** When all else fail, fall back on more generic inversion
      tactics. This is useful not only as a base case, but sometimes
      we mix generic semantics with manually defined ones in a given
      layer, in which case it's more convenient if a single inversion
      tactic works and yield similar results for both kinds. *)

    | _ =>

      try (inv_monad H);
      try inv H

  end.


(** * Effect-free functions preserve invariants *)

Section PRESERVES_INVARIANTS.
  Context `{Hmem: Mem.MemoryModel}.
  Context {D} `{HD: CompatData D}.

  Global Instance semof_nil_int_pure_invar (f: D -> option Z):
    PreservesInvariants f.
  Proof.
    split.
    * intros vargs m d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
  Qed.

  Global Instance semof_nil_int_pure_total_invar (f: D -> Z):
    PreservesInvariants f.
  Proof.
    split.
    * intros vargs m d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
  Qed.

  Global Instance semof_cons_invar `{Tsemof: Semof D} (f: Z -> T):
    (forall n, PreservesInvariants (f n)) ->
    PreservesInvariants f.
  Proof.
    intros Hf.
    split.
    * intros vargs m d vres d' H Hinv.
      inv_generic_sem H.
      eapply semprops_low_level_invariant;
      eassumption.
    * intros vargs d vres d' H Hinv.
      inv_generic_sem H.
      eapply semprops_high_level_invariant;
      eassumption.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      eapply semprops_kernel_mode;
      eassumption.
  Qed.

  Global Instance semof_nil_int64_pure_invar (f: D -> option Z64):
    PreservesInvariants f.
  Proof.
    split.
    * intros vargs m d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
  Qed.

  Global Instance semof_nil_int64_pure_total_invar (f: D -> Z64):
    PreservesInvariants f.
  Proof.
    split.
    * intros vargs m d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      tauto.
  Qed.

  Global Instance semof_cons64_invar `{Tsemof: Semof D} (f: Z64 -> T):
    (forall n, PreservesInvariants (f n)) ->
    PreservesInvariants f.
  Proof.
    intros Hf.
    split.
    * intros vargs m d vres d' H Hinv.
      inv_generic_sem H.
      eapply semprops_low_level_invariant;
      eassumption.
    * intros vargs d vres d' H Hinv.
      inv_generic_sem H.
      eapply semprops_high_level_invariant;
      eassumption.
    * intros vargs d vres d' H.
      inv_generic_sem H.
      eapply semprops_kernel_mode;
      eassumption.
  Qed.

End PRESERVES_INVARIANTS.
