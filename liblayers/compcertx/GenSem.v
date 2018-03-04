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
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Memtype.
Require Import compcert.cfrontend.Ctypes.
Require Export liblayers.lib.OptionMonad.

(** * Generic semantics from abstract functions *)

Inductive Z64 := VZ64 (z: Z).

Function Z642Z (z: Z64) :=
  match z with
    | VZ64 z' => z'
  end.


Class Semof (data: Type) T (targs: typelist) (tres: type) :=
  semof : T -> (list val -> data -> val -> data -> Prop).

Class Semprops {data} T `{Tsemof: Semof data T} :=
{
  semprops_well_typed f vargs d vres d':
    semof f vargs d vres d' ->
    Val.has_type vres (typ_of_type tres);

  semprops_arity f vargs d vres d':
    semof f vargs d vres d' ->
    length vargs = length (typlist_of_typelist targs);

  semprops_lessdef f vargs vargs' d vres d':
    semof f vargs d vres d' ->
    Val.lessdef_list vargs vargs' ->
    vargs' = vargs;

  semprops_inject_neutral f vargs d vres d' j:
    semof f vargs d vres d' ->
    val_inject j vres vres;

  semprops_determ f vargs d vres1 vres2 d1 d2:
    semof f vargs d vres1 d1 ->
    semof f vargs d vres2 d2 ->
    vres1 = vres2 /\ d1 = d2;

  semprops_inject f ι vargs vargs' d vres d':
    semof f vargs d vres d' ->
    val_list_inject ι vargs vargs' ->
    vargs' = vargs
}.

(** ** Basic instances *)

Section INSTANCES.
  Context {data : Type}.

  Notation type_int32u := (Tint I32 Unsigned noattr).
  Notation type_int64u := (Tlong Unsigned noattr).

  Inductive semof_nil_void: Semof data (data -> option data) Tnil Tvoid :=
    | semof_nil_void_intro f d d':
        f d = ret d' ->
        semof f nil d Vundef d'.

  Global Existing Instance semof_nil_void.

  Global Instance semof_nil_void_props: Semprops (data -> option data).
  Proof.
    split.
    + (* semprops_well_typed *)
      intros ? ? ? ? ? H.
      inv H.
      simpl.
      tauto.
    + (* semprops_arity *)
      intros ? ? ? ? ? H.
      inv H;
      reflexivity.
    + (* semprops_lessdef *)
      intros ? ? ? ? ? ? H Hl.
      inv H;
      inv Hl;
      reflexivity.
    + (* semprops_inject_neutral *)
      inversion 1; subst.
      constructor.
    + (* semprops_determ *)
      inversion 1.
      inversion 1.
      unfold bind, ret in *; simpl in *.
      split; congruence.
    + (* semprops_inject *)
      inversion 1.
      inversion 1.
      reflexivity.
  Qed.


  Inductive semof_nil_int: Semof data (data -> option (data * Z)) Tnil type_int32u :=
    | semof_nil_int_intro f d z d':
        f d = ret (d', Int.unsigned z) ->
        semof f nil d (Vint z) d'.

  Global Existing Instance semof_nil_int.

  Global Instance semof_nil_int_props: Semprops (data -> option (data * Z)).
  Proof.
    split.
    + (* semprops_well_typed *)
      intros ? ? ? ? ? H.
      inv H.
      simpl.
      tauto.
    + (* semprops_arity *)
      intros ? ? ? ? ? H.
      inv H;
      reflexivity.
    + (* semprops_lessdef *)
      intros ? ? ? ? ? ? H Hl.
      inv H;
      inv Hl;
      reflexivity.
    + (* semprops_inject_neutral *)
      inversion 1; subst.
      constructor.
    + (* semprops_determ *)
      inversion 1.
      inversion 1.
      unfold bind, ret in *; simpl in *.
      split; try congruence.
      rewrite H0 in H7.
      inv H7.
      rewrite <- Int.repr_unsigned with z.
      rewrite <- Int.repr_unsigned with z0.
      congruence.
    + (* semprops_inject *)
      inversion 1.
      inversion 1.
      reflexivity.
  Qed.

  (* Special case for pure functions *)

  Local Notation lift_nil_int_pure f :=
    (fun d => z <- f d; ret (d, z)).

  Global Instance semof_nil_int_pure: Semof data (data -> option Z) Tnil type_int32u :=
    fun f => semof (lift_nil_int_pure f).

  Global Instance semof_nil_int_pure_props: Semprops (data -> option Z).
  Proof.
    split; intro f.
    + exact (semprops_well_typed (lift_nil_int_pure f)).
    + exact (semprops_arity (lift_nil_int_pure f)).
    + exact (semprops_lessdef (lift_nil_int_pure f)).
    + exact (semprops_inject_neutral (lift_nil_int_pure f)).
    + exact (semprops_determ (lift_nil_int_pure f)).
    + exact (semprops_inject (lift_nil_int_pure f)).
  Qed.

  (* Special case for pure total functions *)

  Local Notation lift_nil_int_pure_total f :=
    (fun d => ret (f d)).

  Global Instance semof_nil_int_pure_total: Semof data (data -> Z) Tnil type_int32u :=
    fun f => semof (lift_nil_int_pure_total f).

  Global Instance semof_nil_int_pure_total_props: Semprops (data -> Z).
  Proof.
    split; intro f.
    + exact (semprops_well_typed (lift_nil_int_pure_total f)).
    + exact (semprops_arity (lift_nil_int_pure_total f)).
    + exact (semprops_lessdef (lift_nil_int_pure_total f)).
    + exact (semprops_inject_neutral (lift_nil_int_pure_total f)).
    + exact (semprops_determ (lift_nil_int_pure_total f)).
    + exact (semprops_inject (lift_nil_int_pure_total f)).
  Qed.

  Inductive semof_cons `{Semof data}: Semof data (Z -> T) (Tcons type_int32u targs) tres :=
    semof_cons_intro f (i: int) l d v d':
      semof (f (Int.unsigned i)) l d v d' ->
      semof f (Vint i :: l) d v d'.

  Global Existing Instance semof_cons.

  Global Instance semof_cons_props {T} `(HT: Semprops data T): Semprops (Z -> T).
  Proof.
    split.
    + (* semprops_well_typed *)
      intros ? ? ? ? ? H.
      inv H.
      apply (semprops_well_typed (targs := targs) (f (Int.unsigned i)) l d vres d').
      eassumption.
    + (* semprops_arity *)
      intros ? ? ? ? ? H.
      inv H.
      simpl.
      f_equal.
      eapply semprops_arity.
      eassumption.
    + (* semprops_lessdef *)
      intros until d'.
      intros H Hl.
      inv H.
      inv Hl.
      inv H2.
      f_equal.
      eapply semprops_lessdef;
      eassumption.
    + (* semprops_inject_neutral *)
      inversion 1; subst.
      eapply semprops_inject_neutral.
      eassumption.
    + (* semprops_determ *)
      inversion 1.
      inversion 1.
      eapply semprops_determ; eassumption.
    + (* semprops_inject *)
      intros.
      inv H.
      inv H0.
      inv H3.
      f_equal.
      eapply semprops_inject; eassumption.
  Qed.

  Inductive semof_nil_int64: Semof data (data -> option (data * Z64)) Tnil type_int64u :=
    | semof_nil_int64_intro f d z d':
        f d = ret (d', VZ64 (Int64.unsigned z)) ->
        semof f nil d (Vlong z) d'.

  Global Existing Instance semof_nil_int64.

  Global Instance semof_nil_int64_props: Semprops (data -> option (data * Z64)).
  Proof.
    split.
    + (* semprops_well_typed *)
      intros ? ? ? ? ? H.
      inv H.
      simpl.
      tauto.
    + (* semprops_arity *)
      intros ? ? ? ? ? H.
      inv H;
      reflexivity.
    + (* semprops_lessdef *)
      intros ? ? ? ? ? ? H Hl.
      inv H;
      inv Hl;
      reflexivity.
    + (* semprops_inject_neutral *)
      inversion 1; subst.
      constructor.
    + (* semprops_determ *)
      inversion 1.
      inversion 1.
      unfold bind, ret in *; simpl in *.
      split; try congruence.
      rewrite H0 in H7.
      inv H7.
      rewrite <- Int64.repr_unsigned with z.
      rewrite <- Int64.repr_unsigned with z0.
      congruence.
    + (* semprops_inject *)
      inversion 1.
      inversion 1.
      reflexivity.
  Qed.

  (* Special case for pure functions *)
  Global Instance semof_nil_int64_pure: Semof data (data -> option Z64) Tnil type_int64u :=
    fun f => semof (lift_nil_int_pure f).

  Global Instance semof_nil_int64_pure_props: Semprops (data -> option Z64).
  Proof.
    split; intro f.
    + exact (semprops_well_typed (lift_nil_int_pure f)).
    + exact (semprops_arity (lift_nil_int_pure f)).
    + exact (semprops_lessdef (lift_nil_int_pure f)).
    + exact (semprops_inject_neutral (lift_nil_int_pure f)).
    + exact (semprops_determ (lift_nil_int_pure f)).
    + exact (semprops_inject (lift_nil_int_pure f)).
  Qed.

  (* Special case for pure total functions *)
  Global Instance semof_nil_int64_pure_total: Semof data (data -> Z64) Tnil type_int64u :=
    fun f => semof (lift_nil_int_pure_total f).

  Global Instance semof_nil_int64_pure_total_props: Semprops (data -> Z64).
  Proof.
    split; intro f.
    + exact (semprops_well_typed (lift_nil_int_pure_total f)).
    + exact (semprops_arity (lift_nil_int_pure_total f)).
    + exact (semprops_lessdef (lift_nil_int_pure_total f)).
    + exact (semprops_inject_neutral (lift_nil_int_pure_total f)).
    + exact (semprops_determ (lift_nil_int_pure_total f)).
    + exact (semprops_inject (lift_nil_int_pure_total f)).
  Qed.

  Inductive semof_cons64 `{Semof data}: Semof data (Z64 -> T) (Tcons type_int64u targs) tres :=
    semof_cons64_intro f (i: int64) l d v d':
      semof (f (VZ64 (Int64.unsigned i))) l d v d' ->
      semof f (Vlong i :: l) d v d'.

  Global Existing Instance semof_cons64.

  Global Instance semof_cons64_props {T} `(HT: Semprops data T): Semprops (Z64 -> T).
  Proof.
    split.
    + (* semprops_well_typed *)
      intros ? ? ? ? ? H.
      inv H.
      apply (semprops_well_typed (targs := targs) (f (VZ64 (Int64.unsigned i))) l d vres d').
      eassumption.
    + (* semprops_arity *)
      intros ? ? ? ? ? H.
      inv H.
      simpl.
      f_equal.
      eapply semprops_arity.
      eassumption.
    + (* semprops_lessdef *)
      intros until d'.
      intros H Hl.
      inv H.
      inv Hl.
      inv H2.
      f_equal.
      eapply semprops_lessdef;
      eassumption.
    + (* semprops_inject_neutral *)
      inversion 1; subst.
      eapply semprops_inject_neutral.
      eassumption.
    + (* semprops_determ *)
      inversion 1.
      inversion 1.
      eapply semprops_determ; eassumption.
    + (* semprops_inject *)
      intros.
      inv H.
      inv H0.
      inv H3.
      f_equal.
      eapply semprops_inject; eassumption.
  Qed.

End INSTANCES.
