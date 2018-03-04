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

Section ModuleSemantics_Low_Invariant.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Section LOW_INVARIANT.

    Lemma exec_load_low_level_invariant {D: compatdata}
          {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
      forall {F V} (ge: Genv.t F V) d rs rs' m m' d' rd chunk a,
        AsmX.asm_invariant ge rs (m, d) ->
        low_level_invariant (Mem.nextblock m) d ->
        (acc_exec_load L) F V ge chunk (m, d) a rs rd = Next rs' (m', d') ->
        low_level_invariant (Mem.nextblock m') d'.
    Proof.
      unfold acc_exec_load; intros.
      destruct (acc_exec_load_strong (acc_def:= acc_def_prf) L).
      destruct x. simpl in *.
      exploit (exec_load_low_level_invariant ge); simpl; eauto.
    Qed.

    Lemma exec_store_low_level_invariant {D: compatdata}
          {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
      forall {F V} (ge: Genv.t F V) d rs rs' m m' d' rd chunk a rl,
        AsmX.asm_invariant ge rs (m, d) ->
        low_level_invariant (Mem.nextblock m) d ->
        (acc_exec_store L) F V ge chunk (m, d) a rs rd rl = Next rs' (m', d') ->
        low_level_invariant (Mem.nextblock m') d'.
    Proof.
      unfold acc_exec_store; intros.
      destruct (acc_exec_store_strong (acc_def:= acc_def_prf) L).
      destruct x. simpl in *.
      exploit (exec_store_low_level_invariant ge); simpl; eauto.
    Qed.

    Lemma goto_label_low_level_invariant {D: compatdata}
          {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
      forall d rs m rs' m' d' f0 l,
        low_level_invariant (Mem.nextblock m) d ->
        goto_label (Hfl:= FindLabels_instance_0) f0 l rs (m, d) = 
        Next (mem:= mwd D) rs' (m', d') ->
        low_level_invariant (Mem.nextblock m') d'.
    Proof.
      unfold goto_label; intros.
      destruct (label_pos l 0 (fn_code f0)); try discriminate.
      destruct (rs PC); contra_inv.
      inv H0; trivial.
    Qed.

    Lemma exec_instr_low_level_invariant {D: compatdata}
          {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
      forall ge rs rs' m m' d d' f0 i, 
        (exec_instr (lcfg_ops:= LC L)) ge f0 i rs (m, d) = Next rs' (m', d') ->
        AsmX.asm_invariant ge rs (m, d) ->
        low_level_invariant (Mem.nextblock m) d ->
        low_level_invariant (Mem.nextblock m') d'.
    Proof.
      intros. unfold exec_instr in *.
      destruct i;
        lazymatch goal with
          | H: context[exec_loadex _ _ _ _ _ _] |- _ => 
            simpl in *; eapply (exec_load_low_level_invariant ge); eauto 1
          | H: context[exec_storeex _ _ _ _ _ _ _] |- _ => 
            simpl in *; eapply (exec_store_low_level_invariant ge); eauto 1
          | H: context[Asm.exec_instr _ _ _ _ _] |- _ => idtac
          | [HW: _ = Next _ _ |- _]=> 
            inv HW; eauto
        end.

      destruct i; simpl in *;
      lazymatch goal with
        | H: context[(acc_exec_load _)] |-_ => eapply exec_load_low_level_invariant; eauto 1
        | H: context[(acc_exec_store _)] |- _ => eapply exec_store_low_level_invariant; eauto 1
        | HW: _ = Next _ _ |- _ => try (inv HW; trivial; fail)
        | _ => idtac
      end;
      lift_unfold; 
      try (subdestruct;
           match goal with
             | HW: _ = Next _ _ |- _ => 
               inv HW; trivial;
             eapply goto_label_low_level_invariant; eauto 1
           end; fail).

    - (* Pallocframe *)
      case_eq (Mem.alloc m 0 sz); intros; rewrite H2 in H; simpl in H.
      case_eq (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP));
        intros; rewrite H3 in H; contra_inv; simpl in H.
      case_eq(Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA));
        intros; rewrite H4 in H; contra_inv; simpl in H. inv H.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
      rewrite (Mem.nextblock_alloc _ _ _ _ _ H2).
      eapply low_level_invariant_incr; eauto.
      xomega.

    - (* Pfreeframe *)
      lift_unfold. simpl in *.
      destruct (Mem.loadv (mem:= mwd D) Mint32 (m, d) (Val.add (rs ESP) (Vint ofs_ra))); contra_inv.
      destruct (Mem.loadv (mem:= mwd D) Mint32 (m, d) (Val.add (rs ESP) (Vint ofs_link))); contra_inv.
      destruct (rs ESP); contra_inv.
      case_eq(Mem.free m b 0 sz); intros; rewrite H2 in H; contra_inv. inv H.
      erewrite Mem.nextblock_free; eauto.

    Qed.

    Lemma volatile_store_nextblock {D: compatdata}:
      forall {F V} (ge: Genv.t F V) WB m m' d d' b ofs t v chunk,
        volatile_store (mem:= mwd D) WB ge chunk (m, d) b ofs t v (m', d')
        -> Mem.nextblock m' = Mem.nextblock m.
    Proof.
      intros. inv H. 
      - split; trivial; try constructor; eauto.
      - lift_unfold. destruct H1 as [H1 _].
        erewrite (Mem.nextblock_store _ _ _ _ _ _ H1); eauto.
    Qed.

    Lemma external_call_low_level_invariant'  {D: compatdata}
          {L} `{acc_def_prf: !AccessorsDefined (D:= D) L}:
      forall {F V} (ge: Genv.t F V) ef
             args m m' t vl d d' rs
             (BUILTIN_ENABLED : match ef with
                                  | EF_external _ _ => False
                                  | _ => True
                                end),
        external_call' (mem:= mwd D)
                       (external_calls_ops:= (compatlayer_extcall_ops L))
                       (fun b => True) ef ge args (m, d) t vl (m', d') ->
        AsmX.asm_invariant ge rs (m, d) ->
        low_level_invariant (Mem.nextblock m) d ->
        low_level_invariant (Mem.nextblock m') d'.
    Proof.
      intros. 
      Opaque decode_longs encode_long.
      destruct ef; inv BUILTIN_ENABLED; inv H; simpl in *;
      inv H2; trivial.
      
      - (* volatile store *)
        exploit (volatile_store_without_d (D:=D) ge); eauto.
        intros [_ ?]; subst; trivial.
        erewrite (volatile_store_nextblock (D:=D) ge); eauto.
      - (* volatile store global *)
        exploit (volatile_store_without_d (D:=D) ge); eauto.
        intros [_ ?]; subst; trivial.
        erewrite (volatile_store_nextblock (D:=D) ge); eauto.
      - (* malloc *)
        lift_unfold. destruct m'0; simpl in *; destruct H3 as [Halloc ?]; subst.
        destruct H4 as [Hstore ?]; subst. 
        rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ Halloc).
        eapply low_level_invariant_incr; eauto.
        xomega.
      - (* mfree *)
        lift_unfold. destruct H5 as [Hfree ?]; subst. 
        erewrite Mem.nextblock_free; eauto.
      - (* memcpy *)
        lift_unfold. destruct H10 as [Hstore ?]; subst. 
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ Hstore).
        trivial.
    Qed.

    Lemma asm_invariant_without_d {D: compatdata}:
      forall s rs m d,
        asm_invariant (mem:= mwd D) s rs (m, d) ->
        asm_invariant s rs m.
    Proof.
      intros. inv H.
      econstructor; eauto.
      inv inv_inject_neutral.
      econstructor; eauto.
    Qed.

    Lemma asm_invariant_equiv' {D}:
      forall {F V} (ge: Genv.t F V) s rs (m: mwd D),
        stencil_matches s ge ->
        (asm_invariant s rs m <-> AsmX.asm_invariant ge rs m).
    Proof.                    
      split; inversion 1; split; auto;
      inv inv_inject_neutral; split; auto;
      inv H; congruence.
    Qed.

    Lemma step_low_level_invariant {D: compatdata}
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
        AsmX.asm_invariant ge rs (m, d) ->
        low_level_invariant (Mem.nextblock m) d ->
        low_level_invariant (Mem.nextblock m') d'.
    Proof.
      intros until ge.
      inversion 2; subst.
      - (* exec_instr *)
        eapply exec_instr_low_level_invariant; eauto.
      - (* builtin *)
        eapply external_call_low_level_invariant'; eauto.
      - (* annot *)
        eapply external_call_low_level_invariant'; eauto.
      - (* external call *)
        destruct (Hge_external _ _ H5) as [i[sg ?]]; subst.
        inv H8. inv H0.
        destruct H1 as [? Hsem].
        inv Hsem. destruct H1 as [?[Hmatch[Hsem'[?[? ?]]]]]; subst.
        pose proof (extcall_invariants_available _ _ H0) as Hinvs.
        intros. inv H1. inv inv_inject_neutral.
        inv Hmatch.
        eapply external_call_low_level_invariant; eauto.
        rewrite <- stencil_matches_genv_next. eauto.
      - (* prim call *)
        destruct (Hge_external _ _ H6) as [i[sg ?]]; subst.
        inv H7.
        destruct H0 as [?[?[?[? Hsem]]]]; subst.
        inv Hsem. 
        pose proof (primcall_invariants_available _ _ H1) as Hinvs.
        intros; eapply primitive_call_low_level_invariant; eauto.
        eapply asm_invariant_equiv' in H4; eauto.
        eapply asm_invariant_without_d; eauto.
    Qed.

  End LOW_INVARIANT.

End ModuleSemantics_Low_Invariant.
