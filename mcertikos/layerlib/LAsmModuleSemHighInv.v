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
(** This file provide the semantics for the [Asm] instructions. Since we introduce paging mechanisms, the semantics of memory load and store are different from [Compcert Asm]*)
Require Import Coqlib.
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
Require Import LAsmModuleSemDef.
Require Import Observation.
(** ** Invariants preserved by LAsm modules *)

Section ModuleSemantics_High_Invariant.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

Section HIGH_INVARIANT.

  Lemma exec_load_high_level_invariant {D: compatdata}
        {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
    forall {F V} (ge: Genv.t F V) d rs rs' m m' d' rd chunk a,
      high_level_invariant d ->
      (acc_exec_load L) F V ge chunk (m, d) a rs rd = Next rs' (m', d') ->
      high_level_invariant d'.
  Proof.
    unfold acc_exec_load; intros.
    destruct (acc_exec_load_strong (acc_def:= acc_def_prf) L).
    destruct x. simpl in *.
    exploit (exec_load_high_level_invariant ge); simpl; eauto.
  Qed.

  Lemma exec_store_high_level_invariant {D: compatdata}
        {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
    forall {F V} (ge: Genv.t F V) d rs rs' m m' d' rd chunk a rl,
      high_level_invariant d ->
      (acc_exec_store L) F V ge chunk (m, d) a rs rd rl = Next rs' (m', d') ->
      high_level_invariant d'.
  Proof.
    unfold acc_exec_store; intros.
    destruct (acc_exec_store_strong (acc_def:= acc_def_prf) L).
    destruct x. simpl in *.
    exploit (exec_store_high_level_invariant ge); simpl; eauto.
  Qed.

  Lemma goto_label_high_level_invariant {D: compatdata}
        {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
    forall d rs m rs' m' d' f0 l,
      high_level_invariant d ->
      goto_label (Hfl:= FindLabels_instance_0) f0 l rs (m, d) = 
      Next (mem:= mwd D) rs' (m', d') ->
      high_level_invariant d'.
  Proof.
    unfold goto_label; intros.
    destruct (label_pos l 0 (fn_code f0)); try discriminate.
    destruct (rs PC); contra_inv.
    inv H0; trivial.
  Qed.

  Lemma exec_instr_high_level_invariant {D: compatdata}
        {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
    forall ge rs rs' m m' d d' f0 i, 
      (exec_instr (lcfg_ops:= LC L)) ge f0 i rs (m, d) = Next rs' (m', d') ->
      high_level_invariant d ->
      high_level_invariant d'.
  Proof.
    intros. unfold exec_instr in *.
    destruct i;
      lazymatch goal with
    | H: context[exec_loadex _ _ _ _ _ _] |- _ => simpl in *; eapply exec_load_high_level_invariant; eauto 1
    | H: context[exec_storeex _ _ _ _ _ _ _] |- _ => simpl in *; eapply exec_store_high_level_invariant; eauto 1
    | H: context[Asm.exec_instr _ _ _ _ _] |- _ => idtac
    | [HW: _ = Next _ _ |- _]=> 
      inv HW; eauto
    end.
    destruct i; simpl in *;
    match goal with
      | H: context[(acc_exec_load _)] |-_ => eapply exec_load_high_level_invariant; eauto 1
      | H: context[(acc_exec_store _)] |- _ => eapply exec_store_high_level_invariant; eauto 1
      | HW: _ = Next _ _ |- _ => try (inv HW; trivial; fail)
      | _ => idtac
    end; 
    lift_unfold; subdestruct;
    match goal with
      | HW: _ = Next _ _ |- _ => 
        inv HW; trivial;
        eapply goto_label_high_level_invariant; eauto 1
    end.
  Qed.

  Lemma external_call_high_level_invariant'  {D: compatdata}
        {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
    forall {F V} (ge: Genv.t F V) ef
           args m m' t vl d d'
           (BUILTIN_ENABLED : match ef with
                                | EF_external _ _ => False
                                | _ => True
                              end),
      external_call' (mem:= mwd D)
                     (external_calls_ops:= (compatlayer_extcall_ops L))
                     (fun b => True) ef ge args (m, d) t vl (m', d') ->
      high_level_invariant d ->
      high_level_invariant d'.
  Proof.
    intros. 
    Opaque decode_longs encode_long.
    destruct ef; inv BUILTIN_ENABLED; inv H; simpl in *;
    inv H1; trivial.
    
    - (* volatile store *)
      exploit (volatile_store_without_d (D:=D) ge); eauto.
      intros [_ ?]; subst; trivial.
    - (* volatile store global *)
      exploit (volatile_store_without_d (D:=D) ge); eauto.
      intros [_ ?]; subst; trivial.
    - (* malloc *)
      lift_unfold. destruct H2 as [_ ?].
      destruct H3 as [_ ?]. congruence.
    - (* mfree *)
      lift_unfold. destruct H4 as [_ ?]. congruence.
    - (* memcpy *)
      lift_unfold. destruct H9 as [_ ?]. congruence.
  Qed.

  Lemma step_high_level_invariant {D: compatdata}
        {L} `{acc_def_prf: !AccessorsDefined L}:
    forall `{extcall_inv_avail_prf: !ExtcallInvariantsAvailable L},
    forall `{primcall_inv_avail_prf: !PrimcallInvariantsAvailable L},
    forall ge rs rs' m m' d d' t, 
    forall (Hge_external: 
              forall b ef, 
                Genv.find_funct_ptr ge b = Some (External ef) ->
                exists i sg, ef = EF_external i sg),
      (step (mem:= mwd D) (lcfg_ops:= LC L)) 
        ge (State rs (m, d)) t (State rs' (m', d')) ->
      high_level_invariant d ->
      high_level_invariant d'.
  Proof.
    intros until ge.
    inversion 2; subst.
    - (* exec_instr *)
      eapply exec_instr_high_level_invariant; eauto.
    - (* builtin *)
      eapply external_call_high_level_invariant'; eauto.
    - (* annot *)
      eapply external_call_high_level_invariant'; eauto.
    - (* external call *)
      destruct (Hge_external _ _ H5) as [i[sg ?]]; subst.
      inv H8. inv H0.
      destruct H1 as [? Hsem].
      inv Hsem. destruct H1 as [?[_[Hsem'[?[? ?]]]]]; subst.
      pose proof (extcall_invariants_available _ _ H0).
      eapply external_call_high_level_invariant; eauto.
    - (* prim call *)
      destruct (Hge_external _ _ H6) as [i[sg ?]]; subst.
      inv H7.
      destruct H0 as [?[?[?[? Hsem]]]]; subst.
      inv Hsem. 
      pose proof (primcall_invariants_available _ _ H1).
      eapply primitive_call_high_level_invariant; eauto.
  Qed.

  End HIGH_INVARIANT.

End ModuleSemantics_High_Invariant.
