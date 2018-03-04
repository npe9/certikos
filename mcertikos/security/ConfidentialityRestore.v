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
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.

Require Import compcert.cfrontend.Ctypes.
Require Import Conventions.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.

Require Import AbstractDataType.
Require Import Soundness.
Require Import TSysCall.
Require Import I64Layer.
Require Import LoadStoreSem2.
Require Import MakeProgram.

Require Import SecurityCommon.
Require Import ObsEq.
Require Import SecurityInv1.
Require Import SecurityInv2.
Require Import SecurityInv.
Require Import FunctionalExtensionality.

(* This file proves the confidentiality restore lemma over the TSysCall semantics, 
   saying that if observably equivalent and inactive states s1 and s2 both take a 
   step to active states s1' and s2' (i.e., both executions just yielded back to
   the observer process), then s1' and s2' are also observably equivalent.
   Paper Reference: Section 5 *)

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Local Instance : ExternalCallsOps (mwd (cdata RData)) := 
    CompatExternalCalls.compatlayer_extcall_ops tsyscall_layer.
  Local Instance : LayerConfigurationOps := compatlayer_configuration_ops tsyscall_layer.

  Section WITHIMPL.

    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Variables (s : stencil) (M : module) (ge : genv) (b : block).
    Hypothesis (Hmake : make_globalenv s M tsyscall_layer = OK ge).
    Hypothesis (Hpsu : Genv.find_symbol ge proc_start_user = Some b).

    (* needed so that the inv_spec tactic doesn't interpret find_symbol as a spec *)
    Opaque Genv.find_symbol find_symbol.

    Let local_stencil_matches : stencil_matches s ge.
    Proof.
      eapply make_globalenv_stencil_matches; eauto.
    Qed.

    Let local_find_symbol : find_symbol s proc_start_user = Some b.
    Proof.
      erewrite <- stencil_matches_symbols; eauto.
    Qed.

    (* id is the observer principal. Proofs apply to any principal with large-enough ID.
       Principals with small IDs such as 0 and 1 are considered to be trusted processes. *)
    Variable id : Z.
    Variable id_prop : id > high_id.

    Instance user_observer : Observer _ := user_observer id id_prop.
    Notation obs_eq := (my_obs_eq id).

    Instance user_obs_eq_equiv : Equivalence obs_eq.
    Proof.
      constructor.
      - intro x; rewrite my_obs_eq_convert; auto.
      - intros x y; rewrite 2 my_obs_eq_convert; auto.
      - intros x y z; rewrite 3 my_obs_eq_convert; congruence.
    Qed.

    Ltac sapply H :=
      repeat match goal with
               | [ H' : _ |- _ ] => apply H in H'; auto
             end.

    Ltac solve_cid_contr :=
      repeat match goal with
               | [ H : appcontext [syscall_spec] |- _ ] => inv H
               | [ H : proc_start_user_spec _ = _ /\ _ |- _ ] => destruct H
               | [ H : appcontext [trap_into_kernel_spec] |- _ ] => 
                 sapply trap_into_kernel_usermode_cid
               | [ H : appcontext [sys_dispatch_c_spec] |- _ ] => 
                 sapply sys_dispatch_usermode; destruct H as (H & _)
               | [ H : appcontext [ptfault_resv_spec] |- _ ] => 
                 sapply ptfault_resv_usermode; destruct H as (H & _)
               | [ H : appcontext [proc_start_user_spec] |- _ ] => 
                 sapply proc_start_user_usermode_cid
             end.

    Ltac solve_regs_eq :=
      repeat match goal with
               | [ |- Pregmap.set ?r _ _ _ = Pregmap.set ?r _ _ _ ] => 
                 rewrite 2 Pregmap.gss
               | [ |- Pregmap.set ?r ?v _ _ = Pregmap.set ?r ?v _ _ ] => 
                 rewrite 2 (@Pregmap.gso _ _ r v); try discriminate
             end; reflexivity.

    (* a few proofs that some steps don't change the currently-running process, and
       are therefore not applicable to the confidentiality restore lemma *)

    Lemma exec_loadex_cid :
      forall chunk m m' d d' a rs rd rs',
        exec_loadex ge chunk (m, d) a rs rd = Next rs' (m', d') ->
        cid d = cid d'.
    Proof.
      unfold exec_loadex, exec_loadex2; intros; subdestruct; rename H into Hexec.
      - unfold Asm.exec_load in *; subdestruct; congruence.
      - unfold HostAccess2.exec_host_load2 in Hexec; subdestruct;
          try solve [inv Hexec; constructor; intros; rewrites; eauto].
        unfold PageFault.exec_pagefault in *; subdestruct; inv Hexec.
        constructor; simpl; auto; intros; rewrites.
      - unfold Asm.exec_load in *; subdestruct; congruence.
      - unfold GuestAccessIntel1.exec_guest_intel_load1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.load_accessor1 in *; subdestruct; inv Hexec; auto.
      - unfold GuestAccessIntel1.exec_guest_intel_load1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.load_accessor1 in *; subdestruct; inv Hexec; auto.
    Qed.

    Lemma exec_storeex_cid :
      forall chunk m m' d d' a rs rs0 l rs',
        exec_storeex ge chunk (m, d) a rs rs0 l = Next rs' (m', d') ->
        cid d = cid d'.
    Proof.
      unfold exec_storeex, exec_storeex2; intros; subdestruct; rename H into Hexec.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - unfold HostAccess2.exec_host_store2 in Hexec; subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in Hexec; subdestruct; inv Hexec; auto.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - unfold GuestAccessIntel1.exec_guest_intel_store1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.store_accessor1 in *; subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_store in *; elim_stuck_eqn Hstore; inv Hexec.
        unfold flatmem_store in *; subdestruct; inv Hstore; auto.
      - unfold GuestAccessIntel1.exec_guest_intel_store1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.store_accessor1 in *; subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_store in *; elim_stuck_eqn Hstore; inv Hexec.
        unfold flatmem_store in *; subdestruct; inv Hstore; auto.
    Qed.

    Lemma external_call_cid :
      forall (m m' : mem) (d d' : cdata RData) t WB name sg args res rs,
        external_call' WB (EF_external name sg) ge args (m, d) t res (m', d') ->
        secure_inv b id d -> secure_inv' b id rs d -> cid d = cid d'.
    Proof.
      intros m m' d d' t WB name sg args res rs Hext Hinv Hinv'; inv Hext.
      destruct H as [? [Hl [? [? [? [Hsem1 [Hsem2 [? ?]]]]]]]].
      inv_layer Hl; try solve [inv Hsem2 | inv Hsem1; auto].
      inv Hsem1; inv H4; inv H2.
      unfold proc_init_spec, ret in *; subdestruct.
      inv Hinv; inv Hinv'.
      inv sec_high_inv.
      rewrite valid_preinit_container in sec_used; auto; try congruence.
      eapply cvalid_id; eauto.
    Qed.

    (* proof that yielding changes the currently-running process *)

    Lemma thread_yield_new_cid :
      forall d d' rs rs',
        high_level_invariant d -> 
        thread_yield_spec d rs = Some (d', rs') -> cid d <> cid d'.
    Proof.
      intros d d' rs rs' Hinv Hspec.
      destruct Hinv; inv_spec; inv_somes; simpl.
      assert (Hin: In (last l num_id) l) by (eapply last_correct; eauto).
      intro Hcon; rewrite <- Hcon in Hin.
      apply (valid_inQ eq_refl (cid d)) in Hdestruct3; auto; try omega; destruct Hdestruct3.
      destruct (correct_curid eq_refl); rewrites.
    Qed.

    (* proof that any step that changes the currently-running process must be
       a call to the yield primitive (essentially the inverse of the previous lemma) *)

    Lemma new_cid_thread_yield :
      forall m m' d d' rs rs' t,
        LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
        secure_inv b id d -> secure_inv' b id rs d -> cid d <> cid d' ->
        exists b, rs PC = Vptr b Int.zero /\ Genv.find_symbol ge sys_yield = Some b.
    Proof.
      intros m m' d d' rs rs' t Hstep.
      eapply (step_P (fun d d' : cdata RData => 
                        secure_inv b id d -> secure_inv' b id rs d ->
                        cid d <> cid d' ->
                        exists b0 : block,
                          rs PC = Vptr b0 Int.zero /\ 
                          Genv.find_symbol ge sys_yield = Some b0)); eauto.
      - congruence.
      - simpl; intros ? ? ? ? ? ? Hcon; contradiction Hcon.
        eapply exec_loadex_cid; eauto.
      - simpl; intros ? ? ? ? ? ? ? Hcon; contradiction Hcon.
        eapply exec_storeex_cid; eauto.
      - intros ? ? ? ? ? ? ? Hcon; contradiction Hcon.
        eapply external_call_cid; eauto.
      - intros ef [x [sg [σ [Hef [Hl Hsem]]]]] Hinv Hinv' Hid; subst.
        inv_layer Hl; inv Hsem; simpl in *; inv H1.
        + (* dispatch *)
          inv H6.
          destruct H1; contradiction Hid.
          transitivity (cid labd0).
          eapply trap_into_kernel_usermode_cid; eauto.
          transitivity (cid labd1).
          eapply sys_dispatch_usermode; eauto.
          eapply proc_start_user_usermode_cid; eauto.
        + (* ptfault_resv *)
          inv H7.
          destruct H1; contradiction Hid.
          transitivity (cid labd0).
          eapply trap_into_kernel_usermode_cid; eauto.
          transitivity (cid labd1).
          eapply ptfault_resv_usermode; eauto.
          eapply proc_start_user_usermode_cid; eauto.
        + (* yield *)
          inv H5.
          decompose [and] H1; clear H1.
          exists b0; split; auto.
          erewrite stencil_matches_symbols; eauto.
        + (* proc_start_user *)
          contradiction Hid; eapply proc_start_user_usermode_cid; eauto.
    Qed.

    (* proof that we never simultaneously change the currently-running process
       and produce output (for technical reasons, this would cause trouble) *)

    Lemma new_cid_no_output :
      forall m m' d d' rs rs' t,
        LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
        secure_inv b id d -> secure_inv' b id rs d -> cid d <> cid d' ->
        devout d = devout d'.
    Proof.
      intros m m' d d' rs rs' t Hstep.
      eapply (step_P (fun d d' : cdata RData => 
                        secure_inv b id d -> secure_inv' b id rs d ->
                        cid d <> cid d' ->
                        devout d = devout d')); eauto.
      - simpl; intros ? ? ? ? ? ? Hcon; contradiction Hcon.
        eapply exec_loadex_cid; eauto.
      - simpl; intros ? ? ? ? ? ? ? Hcon; contradiction Hcon.
        eapply exec_storeex_cid; eauto.
      - intros ? ? ? ? ? ? ? Hcon; contradiction Hcon.
        eapply external_call_cid; eauto.
      - intros ef [x [sg [σ [Hef [Hl Hsem]]]]] Hinv Hinv' Hid; subst.
        inv_layer Hl; inv Hsem; simpl in *; inv H1.
        + (* dispatch *)
          inv H6.
          destruct H1; contradiction Hid.
          transitivity (cid labd0).
          eapply trap_into_kernel_usermode_cid; eauto.
          transitivity (cid labd1).
          eapply sys_dispatch_usermode; eauto.
          eapply proc_start_user_usermode_cid; eauto.
        + (* ptfault_resv *)
          inv H7.
          destruct H1; contradiction Hid.
          transitivity (cid labd0).
          eapply trap_into_kernel_usermode_cid; eauto.
          transitivity (cid labd1).
          eapply ptfault_resv_usermode; eauto.
          eapply proc_start_user_usermode_cid; eauto.
        + (* yield *)
          inv H5.
          decompose [and] H1; clear H1.
          inv_spec; inv_somes; auto.
        + (* proc_start_user *)
          contradiction Hid; eapply proc_start_user_usermode_cid; eauto.
    Qed.

    (* confidentiality restore for yielding *)

    Lemma conf_thread_yield_restore :
      forall d1 d2 d1' d2' rs1 rs2 rs1' rs2',
        high_level_invariant d1 -> high_level_invariant d2 ->
        id = cid d1' -> id = cid d2' ->
        thread_yield_spec d1 rs1 = Some (d1',rs1') ->
        thread_yield_spec d2 rs2 = Some (d2',rs2') ->
        id <> cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2' /\ rs1' = rs2'.
    Proof.
      intros d1 d2 d1' d2' rs1 rs2 rs1' rs2' Hinv1 Hinv2 Hcid1 Hcid2 Hspec1 Hspec2 Hcid Hobs_eq.
      assert (Hcid2new:= Hspec2); apply thread_yield_new_cid in Hcid2new; auto.
      inv_spec; inv_somes; split.
      solve_obs_eq Hobs_eq; simpl in *; try congruence; try tauto.
      rewrite (valid_init_pg _ Hinv1), (valid_init_pg _ Hinv2); congruence.
      inv Hobs_eq; simpl in *. rewrite <- Hcid1.
      trivial.
    Qed.

    (* confidentiality restore for system call trapping *)

    Lemma conf_proc_exit_user_restore :
      forall d1 d2 d1' d2' uc1 uc2,
        proc_exit_user_spec d1 uc1 = Some d1' ->
        proc_exit_user_spec d2 uc2 = Some d2' ->
        id <> cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
    Proof.
      intros d1 d2 d1' d2' uc1 uc2 Hspec1 Hspec2 Hid Hobs_eq.
      inv_spec; inv_somes; solve_obs_eq Hobs_eq.
      subst; contradiction n; apply (proj2 obs_eq_cid eq_refl).
    Qed.

    Lemma conf_trap_into_kernel_restore :
      forall d1 d2 d1' d2' f1 f2 s1 s2 m1 m2 rs1 rs2 vargs vargs' sg sg' b b'
             v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
             v0' v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' v11' v12' v13' v14' v15' v16',
        trap_into_kernel_spec f1 s1 m1 rs1 d1 d1' vargs sg b
               v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        trap_into_kernel_spec f2 s2 m2 rs2 d2 d2' vargs' sg' b'
               v0' v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' v11' v12' v13' v14' v15' v16' ->
        id <> cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
    Proof.
      intros until v16'; intros Hspec1 Hspec2 Hid Hobs_eq.
      unfold trap_into_kernel_spec in *.
      decompose [and] Hspec1; decompose [and] Hspec2; clear Hspec1 Hspec2; rewrites'.
      apply (conf_proc_exit_user_restore _ _ _ _ _ _ H4 H12 Hid Hobs_eq).
    Qed.

    (* Confidentiality restore for the entire tsyscall semantics. 
       Combines all the main lemmas in this file.  *)

    Theorem confidentiality_restore :
      forall m m1' m2' d1 d2 d1' d2' rs1 rs2 rs1' rs2' t1 t2,
        secure_inv b id d1 -> secure_inv' b id rs1 d1 ->
        secure_inv b id d2 -> secure_inv' b id rs2 d2 ->
        LAsm.step ge (State rs1 (m,d1)) t1 (State rs1' (m1',d1')) -> 
        LAsm.step ge (State rs2 (m,d2)) t2 (State rs2' (m2',d2')) -> 
        id <> cid d1 -> id = cid d1' -> id = cid d2' -> obs_eq d1 d2 -> 
        obs_eq d1' d2' /\ (id = cid d1' -> rs1' = rs2') /\ m1' = m2'.
    Proof.
      intros m m1' m2' d1 d2 d1' d2' rs1 rs2 rs1' rs2' t1 t2 Hinv1 Hinv1' 
             Hinv2 Hinv2' Hstep1 Hstep2 Hid Hid1 Hid2 Hobs_eq.
      assert (Hinv1t:= Hinv1); assert (Hinv1t':= Hinv1').
      assert (Hinv2t:= Hinv2); assert (Hinv2t':= Hinv2').
      destruct Hinv1; destruct Hinv1'; destruct Hinv2; destruct Hinv2'.
      destruct sec_usermode; destruct sec_usermode0.
      assert (id <> cid d2) by (intro Hcon; contradiction Hid;
                                destruct Hobs_eq; rewrite (proj2 obs_eq_cid); auto).
      (* deal with kernel mode as a special case *)
      destruct (ikern d1) eqn:Hkern1.
      eapply startuser_step_d in Hstep1; eauto. rewrite Hstep1 in Hid1. 
      simpl in Hid1. congruence.
      destruct (ikern d2) eqn:Hkern2.
      eapply startuser_step_d in Hstep2; eauto.
      rewrite Hstep2 in Hid2.
      simpl in Hid2. congruence.

      (* now we can assume we're in user mode *)
      destruct (new_cid_thread_yield _ _ _ _ _ _ _ Hstep1) as [b1 [? ?]]; auto; try congruence.
      destruct (new_cid_thread_yield _ _ _ _ _ _ _ Hstep2) as [b2 [? ?]]; auto; try congruence.
      generalize Hid Hid1 Hid2; clear Hid Hid1 Hid2; inv Hstep1; 
        try solve [destruct EXT_ALLOWED; simpl in *; congruence].
      {
        (* Case 1: internal step (assembly command) *)
        rename H12 into Hexec1.
        destruct i; 
          try solve [simpl in Hexec1; inv Hexec1; congruence |
                     inv Hexec1; sapply exec_loadex_cid; congruence |
                     inv Hexec1; sapply exec_storeex_cid; congruence]. 
        destruct i; simpl in *;
        try solve [subdestruct; inv Hexec1; congruence |
                   sapply exec_loadex_cid; congruence |
                   sapply exec_storeex_cid; congruence |
                   destruct (INSTR_ALLOWED eq_refl); congruence |
                   unfold goto_label in *; subdestruct; inv Hexec1; congruence].
      }
      {
        (* Case 2: primitive call *)
        destruct H11 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
        inv Hstep2; try solve [destruct EXT_ALLOWED; simpl in *; congruence]; rewrites.
        
        destruct H13 as [x' [sg' [σ' [Hef' [Hl' Hsem']]]]]; subst.
        inv Hef'; rewrites.
        inv_layer Hl; inv Hsem; inv Hsem'; simpl in *; inv H2.
        - (* dispatch *)
          inv H13.
          destruct H2; intros Hid ?; subst; contradiction Hid; symmetry.
          transitivity (cid labd0).
          eapply trap_into_kernel_usermode_cid; eauto.
          transitivity (cid labd1).
          eapply sys_dispatch_usermode; eauto.
          eapply proc_start_user_usermode_cid; eauto.
        - (* ptfault_resv *)
          inv H14.
          destruct H2; intros Hid ?; subst; contradiction Hid; symmetry.
          transitivity (cid labd0).
          eapply trap_into_kernel_usermode_cid; eauto.
          transitivity (cid labd1).
          eapply ptfault_resv_usermode; eauto.
          eapply proc_start_user_usermode_cid; eauto.
        - (* yield *)
          inv H5; intros; rewrite <- and_assoc; split; auto.      
          edestruct conf_thread_yield_restore; [| | | | eapply H17 | eapply H19 | idtac..]; try assumption.
          + exploit trap_into_kernel_inv1; eauto. intros (HP & _). eapply HP; eauto.
          + clear H10.  exploit trap_into_kernel_inv1; eauto. intros (HP & _). eapply HP; eauto.
          + sapply trap_into_kernel_usermode_cid; congruence.
          + eapply conf_trap_into_kernel_restore; eauto.
          + split; [auto|]; intro; simpl.
            clear id_prop H0. subst.
            (* sys_yield starts with the original registers and writes new values.
               However, it writes a new value to EVERY register, so the original register 
               values are actually irrelevant. This part of the proof shows this fact. *)
            extensionality r'; destruct r'; try solve [solve_regs_eq].
            destruct i; solve_regs_eq.
            destruct f; solve_regs_eq.
            destruct c; solve_regs_eq.
        - intros Hid ?; subst; contradiction Hid; symmetry.
          eapply proc_start_user_usermode_cid; eauto.
      }
    Qed.

  End WITHIMPL.

End WITHMEM.