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
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import AsmX.
Require Import Conventions.
Require Import Machregs.
Require Import AuxLemma.
Require Import CommonTactic.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import CompCertBuiltins.
Require Import LAsm.
Require Import MemoryExtra.
Require Import Observation.

Require Export LAsmModuleSemDef.
Require Export LAsmModuleSemProp.
Require Import LAsmModuleSemHighInv.
Require Import LAsmModuleSemLowInv.
Require Import LAsmModuleSemAsmInv.
Require Import LAsmModuleSemAux.
Require Import LAsmModuleSemMonotonic.
Require Import LAsmModuleSemSim.
Require Import LAsmModuleSemMakeProgram.
Require Import LAsmModuleSem.

(** * LAsm semantics preserve invariants *)

Section INVARIANTS.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Lemma asm_invariant_d_iff {D: compatdata}:
    forall s rs m d,
      asm_invariant s rs m <->
      asm_invariant (mem:= mwd D) s rs (m, d).
  Proof.
    split.
    * intros. inversion H.
      econstructor; eauto.
      inversion inv_inject_neutral.
      econstructor; eauto.
    * intros. inversion H.
      econstructor; eauto.
      inversion inv_inject_neutral.
      econstructor; eauto.
  Qed.

  Lemma plus_ind_preserves_lasm (D: compatdata):
    forall (step: genv -> state (mem := mwd D) -> trace -> state (mem := mwd D) -> Prop),
    forall ge,
    forall (P : regset -> mem -> D -> Prop),
      (forall rs1 m1 d1 rs2 m2 d2,
         step ge (State rs1 (m1, d1)) E0 (State rs2 (m2, d2)) ->
         P rs1 m1 d1 ->
         P rs2 m2 d2) ->
      (forall rs1 m1 d1 rs2 m2 d2,
         plus step ge (State rs1 (m1, d1)) E0 (State rs2 (m2, d2)) ->
         P rs1 m1 d1 ->
         P rs2 m2 d2).
  Proof.
    (** First, put things in terms of states rather than rs/m/d. *)
    intros step ge P Hstep.
    set (P' := fun s : state => match s with State rs (m, d) => P rs m d end).
    assert (HP': forall rs m d, P rs m d <-> P' (State rs (m, d))). {
      reflexivity.
    }
    assert (Hstep': forall s1 s2, step ge s1 E0 s2 -> P' s1 -> P' s2). {
      intros [rs1 [m1 d1]] [rs2 [m2 s2]].
      unfold P'.
      eauto.
    }
    setoid_rewrite HP'.
    generalize P' Hstep'.
    clear P Hstep P' HP' Hstep'.

    (** Now, the induction is fairly easy. *)
    intros P' Hstep'.
    intros rs1 m1 d1 rs2 m2 d2.
    generalize (eq_refl E0).
    generalize (State rs1 (m1, d1)) (State rs2 (m2, d2)).
    clear rs1 m1 d1 rs2 m2 d2.
    generalize E0 at 1 3.
    intros t s1 s2 Ht Hplus.
    destruct Hplus as [s1 t1 s2 t2 s3 t H12 H23 Ht12].
    intros H1.
    subst.
    destruct t1; try discriminate.
    destruct t2; try discriminate.
    assert (H2: P' s2). {
      eapply Hstep'.
      eassumption.
      assumption.
    }
    clear s1 H12 H1.
    revert H2.
    induction H23.
    * tauto.
    * destruct t; try discriminate.
      destruct t1; try discriminate.
      destruct t2; try discriminate.
      intros Hs1.
      apply IHstar.
      + reflexivity.
      + eauto.
  Qed.

  Global Instance lasm_primcall_invariants {D} M (L: compatlayer D):
    forall
      `{extcall_inv_avail_prf: !ExtcallInvariantsAvailable L}
      `{primcall_inv_avail_prf: !PrimcallInvariantsAvailable L}
      `{builtin_idents_norepet_prf: !BuiltinIdentsNorepet},
    PrimcallInvariantsAvailable (〚M〛 L).
  Proof.
    intros ? ? ? ? ? HMLi.
    rewrite get_semof_primitive in HMLi.
    unfold semof_function in HMLi.
    destruct (get_module_function i M) as [[|]|]; try discriminate; monad_norm.
    simpl in HMLi; monad_norm.
    unfold lasm_primsem in *.
    inversion HMLi; subst; clear HMLi.
    simpl.

    (** First, I'll show that [asm_invariant] is preserved. *)

    assert (Hasm: forall s rs1 m1 d1 rs2 m2 d2,
                    lasm_step M L i s rs1 (m1, d1) rs2 (m2, d2) ->
                    asm_invariant s rs1 (m1, d1) ->
                    asm_invariant s rs2 (m2, d2)).
    {
      intros s rs1 m1 d1 rs2 m2 d2 Hstep.
      destruct Hstep.
      eapply plus_ind_preserves_lasm
        with (P := fun rs m d => asm_invariant s rs (m, d));
        try eassumption.
      clear rs1 m1 d1 rs2 m2 d2 PC_VAL STAR.
      pose proof (make_globalenv_stencil_matches _ _ _ _ Hge) as Hsge.
      intros rs1 m1 d1 rs2 m2 d2 Hstep Hasm.
      pose proof (fun rs m (d:D) => asm_invariant_equiv ge s rs (m, d) Hsge) as Hiwd.
      erewrite Hiwd in *.
      eapply step_asm_invariant; try eassumption.
      eapply ge_external_valid.
      eassumption.
    }

    set (low_invariant_plus (s: stencil) (rs: regset) (m: mem) (d: D) :=
           asm_invariant s rs (m, d) /\
           low_level_invariant (Mem.nextblock m) d).

    assert (Hlow: forall s rs1 m1 d1 rs2 m2 d2,
                    lasm_step M L i s rs1 (m1, d1) rs2 (m2, d2) ->
                    low_invariant_plus s rs1 m1 d1 ->
                    low_invariant_plus s rs2 m2 d2).
    {
      intros s rs1 m1 d1 rs2 m2 d2 Hstep.
      destruct Hstep.
      eapply plus_ind_preserves_lasm; try eassumption.
      clear rs1 m1 d1 rs2 m2 d2 PC_VAL STAR.
      pose proof (make_globalenv_stencil_matches _ _ _ _ Hge) as Hsge.
      intros rs1 m1 d1 rs2 m2 d2 Hstep (Ha & Hl).
      pose proof (fun rs (m: mwd D) => asm_invariant_equiv ge s rs m Hsge) as Hieq.
      pose proof (fun rs m (d:D) => asm_invariant_equiv ge s rs (m, d) Hsge) as Hiwd.
      red.
      erewrite Hiwd in *.
      split.
      * eapply step_asm_invariant; try eassumption.
        eapply ge_external_valid.
        eassumption.
      * eapply step_low_level_invariant; try eassumption.
        eapply ge_external_valid.
        eassumption.
    }

    assert (Hhigh: forall s rs1 m1 d1 rs2 m2 d2,
                     lasm_step M L i s rs1 (m1, d1) rs2 (m2, d2) ->
                     high_level_invariant d1 ->
                     high_level_invariant d2).
    {
      intros s rs1 m1 d1 rs2 m2 d2 Hstep.
      destruct Hstep.
      eapply plus_ind_preserves_lasm
        with (P := fun rs m d => high_level_invariant d);
        try eassumption.
      clear rs1 m1 d1 rs2 m2 d2 PC_VAL STAR.
      intros rs1 m1 d1 rs2 m2 d2.
      eapply step_high_level_invariant; eauto.
      eapply ge_external_valid.
      eassumption.
    }

    split.
    * intros s rs [m d] rs' [m' d'].
      apply Hasm.
    * intros s rs m d rs' m' d' Hstep Ha Hl.
      specialize (Hlow _ _ _ _ _ _ _ Hstep).
      destruct Hlow as [_ Hlow']; eauto.
      split; eauto.
      apply asm_invariant_d_iff.
      assumption.
    * apply Hhigh.
  Qed.

  Global Instance lasm_extcall_invariants {D} M (L: compatlayer D):
    forall
      `{extcall_inv_def_prf: !ExtcallInvariantsAvailable L}
      `{primcall_inv_def_prf: !PrimcallInvariantsAvailable L}
      `{builtin_idents_norepet_prf: !BuiltinIdentsNorepet},
    ExtcallInvariantsAvailable (〚M〛 L).
  Proof.
    intros ? ? ? ? ? HMLi.
    rewrite get_semof_primitive in HMLi.
    destruct (get_module_function i M) as [[|]|]; discriminate.
  Qed.
End INVARIANTS.
