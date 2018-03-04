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

(* Confidentiality is needed to chain the SafeSecure property across 
   sequential composition. *)
Require Import Confidentiality.

(** This file contains a proof of safety sensitivity. That is, if two 
    states where p is active have equal observations for p, then the TSysCall 
    semantics will either safely take a step from both states, or will get stuck
    and be unable to step from either state. 

    The point of this proof is to mitigate the strength of assuming the
    hypothesis active_forever in Security.v. We still need the hypothesis
    for liveness reasons (we must assume all user processes eventually call
    yield since our kernel is non-preemptive, and we must assume the
    scheduler is fair), but the proof in this file demonstrates that we 
    do not need the hypothesis for safety reasons, as a user process can
    never leak sensitive information by getting stuck. *)

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

    Ltac obs_eq_rewrite Hobs_eq :=
      try rewrite <- (obs_eq_HP _ _ _ Hobs_eq) in *;
      try rewrite quota_convert' in *;
      try rewrite <- (obs_eq_AC_quota _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_AC_nchildren _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_AC_used _ _ _ Hobs_eq) in *;
      try match goal with
            | [ H : id = cid ?d |- _ ] =>
              try rewrite <- H in *;
              rewrite <- (proj1 (obs_eq_cid _ _ _ Hobs_eq)) in *; auto
          end;
      auto; try rewrite <- (obs_eq_kctxt _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_uctxt _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_OUT _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_ti _ _ _ Hobs_eq) in *; 
      try rewrite <- (obs_eq_ikern _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_ihost _ _ _ Hobs_eq) in *; 
      try rewrite <- (obs_eq_pg _ _ _ Hobs_eq) in *; 
      try rewrite <- (obs_eq_ipt _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_init _ _ _ Hobs_eq) in *; auto.

    Ltac obs_eq_rewrites Hobs_eq := repeat obs_eq_rewrite Hobs_eq.
    
    Ltac solve_obs_eq Hobs_eq := 
      destruct Hobs_eq; constructor; simpl; auto; zmap_solve; try congruence.

    Ltac except H tac := generalize H; clear H; tac; intro H.

    Section SAFESEC_LEMMAS.

      Section SAFESEC_UCTX.

        (* SafeSecure for system call arguments and return values *)

        Lemma safesec_uctx_set_errno :
          forall d1 d2 d1' n,
            uctx_set_errno_spec n d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              uctx_set_errno_spec n d2 = Some d2'.              
        Proof.
          unfold uctx_set_errno_spec; intros; inv_spec; inv_somes.
          obs_eq_rewrites H1; rewrites; eauto.
        Qed.

        Lemma safesec_uctx_arg1 :
          forall d1 d2 r,
            uctx_arg1_spec d1 = Some r ->
            id = cid d1 -> obs_eq d1 d2 ->
            uctx_arg1_spec d2 = Some r.
        Proof.
          unfold uctx_arg1_spec; intros; obs_eq_rewrites H1.
        Qed.

        Lemma safesec_uctx_arg2 :
          forall d1 d2 r,
            uctx_arg2_spec d1 = Some r ->
            id = cid d1 -> obs_eq d1 d2 ->
            uctx_arg2_spec d2 = Some r.
        Proof.
          unfold uctx_arg2_spec; intros; obs_eq_rewrites H1.
        Qed.

        Lemma safesec_uctx_arg3 :
          forall d1 d2 r,
            uctx_arg3_spec d1 = Some r ->
            id = cid d1 -> obs_eq d1 d2 ->
            uctx_arg3_spec d2 = Some r.
        Proof.
          unfold uctx_arg3_spec; intros; obs_eq_rewrites H1.
        Qed.

        Lemma safesec_uctx_arg4 :
          forall d1 d2 r,
            uctx_arg4_spec d1 = Some r ->
            id = cid d1 -> obs_eq d1 d2 ->
            uctx_arg4_spec d2 = Some r.
        Proof.
          unfold uctx_arg4_spec; intros; obs_eq_rewrites H1.
        Qed.

        Lemma safesec_uctx_arg5 :
          forall d1 d2 r,
            uctx_arg5_spec d1 = Some r ->
            id = cid d1 -> obs_eq d1 d2 ->
            uctx_arg5_spec d2 = Some r.
        Proof.
          unfold uctx_arg5_spec; intros; obs_eq_rewrites H1.
        Qed.

        Lemma safesec_uctx_set_retval1 :
          forall d1 d2 d1' n,
            uctx_set_retval1_spec n d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              uctx_set_retval1_spec n d2 = Some d2'.
        Proof.
          unfold uctx_set_retval1_spec; intros; inv_spec; inv_somes.
          obs_eq_rewrites H1; rewrites; eauto.
        Qed.

        Lemma safesec_uctx_set_retval2 :
          forall d1 d2 d1' n,
            uctx_set_retval2_spec n d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              uctx_set_retval2_spec n d2 = Some d2'.
        Proof.
          unfold uctx_set_retval2_spec; intros; inv_spec; inv_somes.
          obs_eq_rewrites H1; rewrites; eauto.
        Qed.

        Lemma safesec_uctx_set_retval3 :
          forall d1 d2 d1' n,
            uctx_set_retval3_spec n d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              uctx_set_retval3_spec n d2 = Some d2'.
        Proof.
          unfold uctx_set_retval3_spec; intros; inv_spec; inv_somes.
          obs_eq_rewrites H1; rewrites; eauto.
        Qed.

        Lemma safesec_uctx_set_retval4 :
          forall d1 d2 d1' n,
            uctx_set_retval4_spec n d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              uctx_set_retval4_spec n d2 = Some d2'.
        Proof.
          unfold uctx_set_retval4_spec; intros; inv_spec; inv_somes.
          obs_eq_rewrites H1; rewrites; eauto.
        Qed.

        Lemma safesec_uctx_set_retval5 :
          forall d1 d2 d1' n,
            uctx_set_retval5_spec n d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              uctx_set_retval5_spec n d2 = Some d2'.
        Proof.
          unfold uctx_set_retval5_spec; intros; inv_spec; inv_somes.
          obs_eq_rewrites H1; rewrites; eauto.
        Qed.

      End SAFESEC_UCTX.

      Ltac safesec_uctx_simpl :=
          match goal with
            | [ |- context [match ?f ?d' with Some _ => _ | None => _ end] ] => 
              match goal with
                | [ H : f ?d = Some _ |- _ ] => 
                  match f with 
                    | uctx_arg1_spec => rewrite (safesec_uctx_arg1 _ d' _ H); auto
                    | uctx_arg2_spec => rewrite (safesec_uctx_arg2 _ d' _ H); auto
                    | uctx_arg3_spec => rewrite (safesec_uctx_arg3 _ d' _ H); auto
                    | uctx_arg4_spec => rewrite (safesec_uctx_arg4 _ d' _ H); auto
                    | uctx_arg5_spec => rewrite (safesec_uctx_arg5 _ d' _ H); auto
                  end 
              end 
          end.

    Section SAFESEC_ACCESSORS.

      (* SafeSecure for load and store primitives *)

      Lemma safesec_exec_loadex :
        forall (m m1' : mem) (d1 d2 d1' : cdata RData) rs rs1' chunk a rd, 
          exec_loadex ge chunk (m, d1) a rs rd = Next rs1' (m1', d1') ->          
          high_level_invariant d1 -> high_level_invariant d2 -> 
          ikern d1 = false -> ikern d2 = false -> ihost d1 = true -> ihost d2 = true ->
          id = cid d1 -> obs_eq d1 d2 ->
          exists rs2' m2' d2',
            exec_loadex ge chunk (m, d2) a rs rd = Next rs2' (m2', d2').
      Proof.
        intros m m1' d1 d2 d1' rs rs1' chunk a rd Hstep Hinv1 Hinv2 
               Hkern1 Hkern2 Hhost1 Hhost2 Hid Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
        (* These hypotheses make omega really slow for some reason... *)
        clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
        unfold exec_loadex, exec_loadex2 in *; subdestruct; simpl in *; try congruence.
        rewrite Hkern2, Hhost2, (valid_kern _ Hinv2); auto.
        unfold HostAccess2.exec_host_load2, snd in *.
        elim_stuck_eqn' Hstep Hpdx.

        rename pi into pti1, pte into pte1.
        assert (Husr: adr_low <= Int.unsigned i < adr_high).
        {             
          eapply PDEValid_usr; [eapply Hinv1 | eauto..].
          destruct Hinv1; auto.
        }
        unfold vread in *; specialize (obs_eq_HP (Int.unsigned i)).
        unfold vread_perm in *; specialize (obs_eq_perm (Int.unsigned i)).
        destruct (zle_lt adr_low (Int.unsigned i) adr_high); try omega.
        rewrite (valid_init_PT_cid _ Hinv1) in Hpdx; auto; rewrite <- Hid in Hpdx.
        rewrite obs_eq_cid in Hid.
        rewrite <- (valid_init_PT_cid _ Hinv2) in Hid; auto; rewrite <- Hid.
        rewrite Hpdx in obs_eq_perm, obs_eq_HP.
        destruct (ZMap.get (PDX (Int.unsigned i)) (ZMap.get id (ptpool d2))) 
          as [pti2 pte2 | | |]; try solve [subdestruct].

        elim_stuck; elim_stuck.
        elim_stuck_eqn Hptx1.
        - symmetry in obs_eq_HP; elim_none_eqn' obs_eq_HP Hptx2; rewrites.
          inv obs_eq_HP; inv obs_eq_perm.
          subdestruct; unfold FlatLoadStoreSem.exec_flatmem_load; eauto.
        - rewrites; subdestruct.
          unfold PageFault.exec_pagefault in *; subdestruct; eauto.
      Qed.

      Lemma safesec_exec_storeex :
        forall (m m1' : mem) (d1 d2 d1' : cdata RData) rs rs1' chunk a rs0 l, 
          exec_storeex ge chunk (m, d1) a rs rs0 l = Next rs1' (m1', d1') ->
          high_level_invariant d1 -> high_level_invariant d2 -> 
          ikern d1 = false -> ikern d2 = false -> ihost d1 = true -> ihost d2 = true ->
          id = cid d1 -> obs_eq d1 d2 ->
          exists rs2' m2' d2',
            exec_storeex ge chunk (m, d2) a rs rs0 l = Next rs2' (m2', d2').
      Proof.
        intros m m1' d1 d2 d1' rs rs1' chunk a rs0 l Hstep Hinv1 Hinv2 
               Hkern1 Hkern2 Hhost1 Hhost2 Hid Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
        (* These hypotheses make omega really slow for some reason... *)
        clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
        unfold exec_storeex, exec_storeex2 in *; subdestruct; simpl in *; try congruence.
        rewrite Hkern2, Hhost2, (valid_kern _ Hinv2); auto.
        unfold HostAccess2.exec_host_store2, snd in *.
        elim_stuck_eqn' Hstep Hpdx.

        rename pi into pti1, pte into pte1.
        assert (Husr: adr_low <= Int.unsigned i < adr_high).
        {             
          eapply PDEValid_usr; [eapply Hinv1 | eauto..].
          destruct Hinv1; auto.
        }
        unfold vread in *; specialize (obs_eq_HP (Int.unsigned i)).
        unfold vread_perm in *; specialize (obs_eq_perm (Int.unsigned i)).
        destruct (zle_lt adr_low (Int.unsigned i) adr_high); try omega.
        rewrite (valid_init_PT_cid _ Hinv1) in Hpdx; auto; rewrite <- Hid in Hpdx.
        rewrite obs_eq_cid in Hid.
        rewrite <- (valid_init_PT_cid _ Hinv2) in Hid; auto; rewrite <- Hid.
        rewrite Hpdx in obs_eq_perm, obs_eq_HP.
        destruct (ZMap.get (PDX (Int.unsigned i)) (ZMap.get id (ptpool d2))) 
          as [pti2 pte2 | | |]; try solve [subdestruct].

        elim_stuck; elim_stuck.
        elim_stuck_eqn Hptx1.
        - symmetry in obs_eq_HP; elim_none_eqn' obs_eq_HP Hptx2; rewrites.
          inv obs_eq_HP; inv obs_eq_perm.
          unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in *; subdestruct.
          rewrite pagei_ptaddr in *; rewrites; eauto.
          rewrite pagei_ptaddr in *; rewrites; eauto.
        - unfold PageFault.exec_pagefault in *; subdestruct; eauto.
      Qed.

    End SAFESEC_ACCESSORS.
    
    Section SAFESEC_PRIMS.

      (* SafeSecure for process spawning *)

      Lemma safesec_proc_create :
        forall d1 d2 d1' b1 b2 b3 ofs q r1,
          high_level_invariant d2 ->
          proc_create_spec d1 b1 b2 b3 ofs q = Some (d1', r1) ->          
          id = cid d1 -> obs_eq d1 d2 ->
          exists d2' r2,
            proc_create_spec d2 b1 b2 b3 ofs q = Some (d2', r2).
      Proof.
        intros d1 d2 d1' b1 b2 b3 ofs q r1 Hinv2 Hstep Hid Hobs_eq.
        unfold proc_create_spec in *.
        obs_eq_rewrites Hobs_eq; subdestruct; inv_somes.
        erewrite obs_eq_pg in Hdestruct1; eauto.
        edestruct (valid_TDQ _ Hinv2 Hdestruct1 num_id) as [? [? _]]; try omega.
        rewrites; eauto.
      Qed.

      Lemma safesec_trap_proc_create :
        forall d1 d2 d1' s m,
          high_level_invariant d2 ->
          trap_proc_create_spec s m d1 = Some d1' ->
          id = cid d1 -> obs_eq d1 d2 -> 
          exists d2',
            trap_proc_create_spec s m d2 = Some d2'.
      Proof.
        intros d1 d2 d1' s' m Hinv2 Hstep Hid Hobs_eq.
        unfold trap_proc_create_spec in *.
        obs_eq_rewrites Hobs_eq; subdestruct; 
          try solve [repeat safesec_uctx_simpl; rewrites;
                     eapply safesec_uctx_set_errno; eauto].
        repeat safesec_uctx_simpl; rewrites.
        rename r into d1'', z1 into r1.
        edestruct safesec_proc_create as [d2'' [r2 ?]]; eauto; rewrites.
        assert (Hobs': obs_eq d1'' d2'' /\ r1 = r2)
          by (exploit conf_proc_create; [| eapply Hdestruct15 | eapply H |..]; eauto; intuition).
        assert (id = cid d1'') by (unfold proc_create_spec in *; subdestruct; inv_somes; auto).
        assert (id = cid r0) by (unfold uctx_set_retval1_spec in *; subdestruct; inv_somes; auto).
        destruct Hobs'; subst r1; edestruct safesec_uctx_set_retval1 as [? Hret]; eauto.
        rewrite Hret.
        eapply safesec_uctx_set_errno; eauto.
        exploit conf_uctx_set_retval1; [| eapply Hdestruct17 | eapply Hret |..]; eauto.
      Qed.

      (* SafeSecure for getting quota *)

      Lemma safesec_trap_get_quota :
        forall d1 d2 d1',
          trap_get_quota_spec d1 = Some d1' ->
          id = cid d1 -> obs_eq d1 d2 -> 
          exists d2',
            trap_get_quota_spec d2 = Some d2'.
      Proof.
        unfold trap_get_quota_spec; intros d1 d2 d1' Hstep Hid Hobs_eq.
        subdestruct; inv_spec; except Hid inv_somes; simpl in *.
        unfold get_curid_spec, container_get_quota_spec, container_get_usage_spec,
               uctx_set_retval1_spec, uctx_set_errno_spec.
        obs_eq_rewrites Hobs_eq; except Hid rewrites; simpl.
        obs_eq_rewrite Hobs_eq; rewrites; eauto.
      Qed.

      (* SafeSecure for setting up shared memory. The proof is just a 
         contradiction since shared memory is only allowed for trusted processes,
         but id = cid d1 and id is assumed to be an untrusted process. *)

      Lemma safesec_trap_offer_shared_mem :
        forall d1 d2 d1',
          trap_offer_shared_mem_spec d1 = Some d1' ->
          id = cid d1 -> obs_eq d1 d2 ->
          exists d2',
            trap_offer_shared_mem_spec d2 = Some d2'.
      Proof.
        unfold trap_offer_shared_mem_spec; intros d1 d2 d1' Hstep Hid Hobs_eq.
        subdestruct; try omega.
        safesec_uctx_simpl; obs_eq_rewrites Hobs_eq.
        destruct (zeq id 1); try omega; eapply safesec_uctx_set_errno; eauto.
      Qed.

      (* SafeSecure for printing output. *)

      Lemma safesec_print :
        forall d1 d2 d1',
          print_spec d1 = Some d1' ->
          id = cid d1 -> obs_eq d1 d2 ->
          exists d2',
            print_spec d2 = Some d2'.
      Proof.
        intros d1 d2 d1' Hstep Hid Hobs_eq.
        unfold print_spec in *; subdestruct.
        safesec_uctx_simpl.
        eapply safesec_uctx_set_errno; eauto.
        obs_eq_rewrites Hobs_eq.
        unfold DeviceOutput_update; obs_eq_rewrites Hobs_eq.
        destruct Hobs_eq; constructor; simpl; auto; zmap_solve.
      Qed.

      (* SafeSecure for the system call dispatcher. *)

      Lemma safesec_sys_dispatch_c :
        forall d1 d2 d1' s m,
          high_level_invariant d2 ->
          sys_dispatch_c_spec s m d1 = Some d1' ->
          id = cid d1 -> obs_eq d1 d2 ->
          exists d2',
            sys_dispatch_c_spec s m d2 = Some d2'.
      Proof.
        intros d1 d2 d1' s' m Hinv2 Hstep Hid Hobs_eq.
        unfold sys_dispatch_c_spec in *.
        subdestruct; safesec_uctx_simpl; rewrites; try solve [eapply safesec_uctx_set_errno; eauto].
        eapply safesec_trap_proc_create; eauto.
        eapply safesec_trap_get_quota; eauto.
        eapply safesec_trap_offer_shared_mem; eauto.
        eapply safesec_print; eauto.
      Qed.

      Section SAFESEC_PTFAULT.

        (* SafeSecure for page fault handling. *)

        Lemma safesec_alloc :
          forall d1 d2 d1' r1,
            high_level_invariant d2 ->
            alloc_spec id d1 = Some (d1', r1) ->
            id = cid d1 -> obs_eq d1 d2 -> 
            exists d2' r2,
              alloc_spec id d2 = Some (d2', r2).
        Proof.
          intros d1 d2 d1' r1 Hinv2 Hstep Hid Hobs_eq.
          unfold alloc_spec in *; subdestruct; except Hid inv_somes.
          - obs_eq_rewrites Hobs_eq; rewrites; destruct Hinv2.
            edestruct quota_bounded_first_free with (ac:= AC d2) (i:= id) as [[? ?] ?]; eauto.
            obs_eq_rewrites Hobs_eq.
            rewrite <- Z.ltb_lt, quota_convert'; obs_eq_rewrites Hob_eq;
            try (rewrite <- (obs_eq_AC_quota _ _ _ Hobs_eq); assumption).
            rewrites; eauto.
          - obs_eq_rewrites Hobs_eq; rewrites; eauto.
        Qed.

        Lemma safesec_ptAllocPDE0 :
          forall d1 d2 d1' r1 v,
            high_level_invariant d2 ->
            ptAllocPDE0_spec id v d1 = Some (d1', r1) ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2' r2,
              ptAllocPDE0_spec id v d2 = Some (d2', r2).
        Proof.
          intros d1 d2 d1' r1 v Hinv2 Hstep Hid Hobs_eq.
          unfold ptAllocPDE0_spec in *; subdestruct; except Hid inv_somes.
          - obs_eq_rewrites Hobs_eq; rewrites; destruct Hinv2.
            edestruct quota_bounded_first_free with (ac:= AC d2) (i:= id) as [[? ?] ?]; eauto.
            obs_eq_rewrites Hobs_eq.
            rewrite <- Z.ltb_lt, quota_convert'; obs_eq_rewrites Hob_eq;
            try (rewrite <- (obs_eq_AC_quota _ _ _ Hobs_eq); assumption).            
            rewrites; destruct Hobs_eq.
            unfold vread_perm in *; specialize (obs_eq_perm v).
            unfold pt_Arg' in *; subdestruct; eauto.
          - obs_eq_rewrites Hobs_eq; rewrites; destruct Hobs_eq.
            unfold vread_perm in *; specialize (obs_eq_perm v).
            unfold pt_Arg' in *; subdestruct; eauto.
        Qed.

        Lemma safesec_ptInsertPTE0 :
          forall d1 d2 d1' vadr padr1 padr2 pm l,
            0 < padr2 < nps d2 -> ZMap.get padr2 (LAT d2) = LATValid true ATNorm l ->
            0 <= Z.of_nat (length l) < Int.max_unsigned ->
            ZMap.get padr2 (pperm d2) = PGAlloc -> 
            ptInsertPTE0_spec id vadr padr1 pm d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              ptInsertPTE0_spec id vadr padr2 pm d2 = Some d2'.
        Proof.
          intros d1 d2 d1' vadr padr1 padr2 pm l Hnps Hlat Hlt Hperm Hstep Hid Hobs_eq.
          unfold ptInsertPTE0_spec in *; subdestruct; except Hid inv_somes.
          - obs_eq_rewrites Hobs_eq; rewrites.
            unfold pt_Arg in *; subdestruct.
            destruct (zlt_lt 0 padr2 (nps d2)); [|omega].
            assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
            unfold vread_perm in *; specialize (obs_eq_perm vadr).
            (* These hypotheses make omega really slow for some reason... *)
            clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
            rewrites; subdestruct; [|unfold pt_Arg' in *; subdestruct; omega].
            destruct (zle_lt 0 (Z.of_nat (length l)) Int.max_unsigned); [|omega]; eauto.
          - obs_eq_rewrites Hobs_eq; rewrites.
            unfold pt_Arg in *; subdestruct.
            destruct (zlt_lt 0 padr2 (nps d2)); [|omega].
            assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
            unfold vread_perm in *; specialize (obs_eq_perm vadr).
            (* These hypotheses make omega really slow for some reason... *)
            clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
            rewrites; subdestruct; [|unfold pt_Arg' in *; subdestruct; omega].
            destruct (zle_lt 0 (Z.of_nat (length l)) Int.max_unsigned); [|omega]; eauto.
        Qed.

        Lemma safesec_ptInsert0 :
          forall d1 d2 d1' r1 vadr padr1 padr2 pm l,
            high_level_invariant d1 -> high_level_invariant d2 ->
            0 < padr2 < nps d2 -> ZMap.get padr2 (LAT d2) = LATValid true ATNorm l ->
            0 <= Z.of_nat (length l) < Int.max_unsigned ->
            ZMap.get padr2 (pperm d2) = PGAlloc -> 
            ptInsert0_spec id vadr padr1 pm d1 = Some (d1', r1) ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2' r2,
              ptInsert0_spec id vadr padr2 pm d2 = Some (d2', r2).
        Proof.
          intros d1 d2 d1' r1 vadr padr1 padr2 pm l Hinv1 Hinv2 
                 Hnps Hlat Hlt Hperm Hstep Hid Hobs_eq.
          unfold ptInsert0_spec in *; subdestruct; except Hid inv_somes.
          - obs_eq_rewrites Hobs_eq; rewrites.
            unfold pt_Arg in *; subdestruct.
            destruct (zlt_lt 0 padr2 (nps d2)); [|omega].
            assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
            unfold vread_perm in *; specialize (obs_eq_perm vadr).
            (* These hypotheses make omega really slow for some reason... *)
            clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
            rewrites; subdestruct; 
              try solve [edestruct safesec_ptInsertPTE0; eauto; rewrites; eauto].
            unfold pt_Arg' in *; subdestruct; omega.
          - obs_eq_rewrites Hobs_eq; rewrites.
            unfold pt_Arg in *; subdestruct.
            destruct (zlt_lt 0 padr2 (nps d2)); [|omega].
            assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
            unfold vread_perm in *; specialize (obs_eq_perm vadr).
            (* These hypotheses make omega really slow for some reason... *)
            clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
            rewrites; subdestruct; [|unfold pt_Arg' in *; subdestruct; omega].
            edestruct safesec_ptAllocPDE0 as [? [? ?]]; eauto; rewrites.
            destruct (zeq x0 0); eauto.
            exploit conf_ptAllocPDE0; [| | | eapply Hdestruct6 | eapply H |..]; auto; omega.
          - obs_eq_rewrites Hobs_eq; rewrites.
            unfold pt_Arg in *; subdestruct.
            destruct (zlt_lt 0 padr2 (nps d2)); [|omega].
            assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
            unfold vread_perm in *; specialize (obs_eq_perm vadr).
            (* These hypotheses make omega really slow for some reason... *)
            clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
            rewrites; subdestruct; [|unfold pt_Arg' in *; subdestruct; omega].
            edestruct safesec_ptAllocPDE0 as [? [? ?]]; eauto; rewrites.
            destruct (zeq x0 0); eauto.
            rename r into d1'', x into d2''.
            assert (Hobs_eq': obs_eq d1'' d2'')
              by (exploit conf_ptAllocPDE0; [| | | eapply Hdestruct6 | eapply H |..]; 
                  auto; intuition).
            assert (cid d1 = cid d1'') 
              by (unfold ptAllocPDE0_spec in Hdestruct6; subdestruct; inv_somes; auto).
            unfold ptAllocPDE0_spec in H.
            edestruct safesec_ptInsertPTE0; [| | | | eauto | | eapply Hobs_eq' |]; eauto.
            + subdestruct; inv_somes; simpl; eauto.
            + subdestruct; inv_somes; simpl in *; zmap_solve; auto.
              subst; destruct a2 as [? [? ?]]; congruence.
            + subdestruct; inv_somes; simpl in *; zmap_solve; auto.
              subst; destruct a2 as [? [? ?]]; congruence.
            + congruence.
            + rewrite H1; eauto.
        Qed.

        Lemma safesec_ptfault_resv :
          forall d1 d2 d1' v,
            high_level_invariant d1 -> high_level_invariant d2 ->
            ptfault_resv_spec v d1 = Some d1' ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2',
              ptfault_resv_spec v d2 = Some d2'.
        Proof.
          intros d1 d2 d1' v Hinv1 Hinv2 Hstep Hid Hobs_eq.
          unfold ptfault_resv_spec, ptResv_spec in *.
          obs_eq_rewrites Hobs_eq; subdestruct; except Hid inv_somes; eauto.
          - edestruct safesec_alloc as [d2'' [r2 Hstep2]]; [|eauto| |eauto|..]; auto; rewrites.
            destruct (zeq r2 0); eauto.
            exploit conf_alloc; [| | | eapply Hdestruct3 | eapply Hstep2 |..]; auto; intuition.
          - edestruct safesec_alloc as [d2'' [r2 Hstep2]]; eauto; rewrites.
            destruct (zeq r2 0).
            exploit conf_alloc; [| | | eapply Hdestruct3 | eapply Hstep2 |..]; auto; intuition.
            assert (Hcid: id = cid r)
              by (clear Hdestruct6 Hdestruct2 Hstep2; repeat inv_spec; inv_somes; auto).
            assert (obs_eq r d2'')
              by (eapply conf_alloc; [| | | eapply Hdestruct3 | eapply Hstep2 |..]; auto).
            edestruct safesec_ptInsert0 as [d2''' [r2' Hstep2']]; [| | | | | | eapply Hdestruct6 |..].
            + eapply alloc_high_level_inv; eauto.
            + eapply alloc_high_level_inv; eauto.
            + clear Hdestruct3 Hdestruct6.
              inv_spec; inv_somes; simpl; try congruence.
              destruct a0; eauto.
            + clear Hdestruct3 Hdestruct6.
              inv_spec; inv_somes; simpl; try congruence.
              zmap_simpl; eauto.
            + simpl; rewrite int_max; omega.
            + clear Hdestruct3 Hdestruct6.
              inv_spec; inv_somes; simpl; try congruence.
              zmap_simpl; auto.
            + auto.
            + auto.
            + rewrite Hstep2'; eauto.
        Qed.

      End SAFESEC_PTFAULT.

      Section SAFESEC_YIELD. 

        (* SafeSecure for yielding. *)

        Lemma last_default {A} :
          forall (l : list A) d,
            last l d = d -> ~ In d l -> l = nil.
        Proof.
          induction l; simpl; auto.
          intros d ? ?; destruct l; [intuition|].
          ediscriminate IHl; eauto.
        Qed.

        Lemma safesec_thread_yield :
          forall d1 d2 d1' r1 rs l,
            high_level_invariant d1 -> high_level_invariant d2 -> 
            ZMap.get num_id (abq d2) = AbQValid l -> l <> nil ->
            thread_yield_spec d1 rs = Some (d1', r1) ->
            id = cid d1 -> obs_eq d1 d2 ->
            exists d2' r2,
              thread_yield_spec d2 rs = Some (d2', r2).
        Proof.
          intros d1 d2 d1' r1 rs l Hinv1 Hinv2 Habq Hnil Hstep Hid Hobs_eq.
          unfold thread_yield_spec in *.
          subdestruct; except Hid inv_somes; obs_eq_rewrites Hobs_eq; rewrites.
          - (* show by contradiction that cid d1 cannot be in the ready queue *)
            edestruct (valid_inQ _ Hinv1); eauto; try omega.
            eapply valid_curid; [apply Hinv1|..].
            rewrite <- e; apply last_correct; auto.
            edestruct (valid_TCB _ Hinv1) as [? [? [? [? _]]]]; eauto.
            eapply valid_curid; eauto.
            edestruct (correct_curid _ Hinv1); eauto; rewrites.
          - edestruct (valid_TDQ _ Hinv2) with (i:= num_id) as [l' [? Hin]]; try omega.
            obs_eq_rewrites Hobs_eq.
            rewrites; destruct (zeq (last l num_id) num_id); [|eauto].
            contradiction Hnil; eapply last_default; eauto.
            intro Hcon; specialize (Hin _ Hcon); omega.
        Qed.

      End SAFESEC_YIELD.

    End SAFESEC_PRIMS.

    Section SAFESEC_SYSCALL.
      
      (* SafeSecure for system call trapping. *)

      Lemma safesec_proc_exit_user :
        forall d1 d2 d1' uc uc',
          proc_exit_user_spec d1 uc = Some d1' ->
          id = cid d1 -> obs_eq d1 d2 ->
          exists d2',
            proc_exit_user_spec d2 uc' = Some d2'.
      Proof.
        intros d1 d2 d1' uc uc' Hstep Hid Hobs_eq.
        unfold proc_exit_user_spec in *; subdestruct; except Hid inv_somes.
        obs_eq_rewrites Hobs_eq; rewrites; eauto.
      Qed.
      
      Lemma safesec_proc_start_user :
        forall d1 d2 d1' r1,
          proc_start_user_spec d1 = Some (d1', r1) ->
          id = cid d1 -> obs_eq d1 d2 -> 
          exists d2' r2,
            proc_start_user_spec d2 = Some (d2', r2).
      Proof.
        intros d1 d2 d1' r1 Hstep Hid Hobs_eq.
        unfold proc_start_user_spec in *; subdestruct; except Hid inv_somes.
        obs_eq_rewrites Hobs_eq; rewrites; eauto.
      Qed.

      Lemma safesec_trap_into_kernel :
        forall d1 d2 d1' f s m rs vargs sg b
               v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
          trap_into_kernel_spec f s m rs d1 d1' vargs sg b
                                v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
          id = cid d1 -> obs_eq d1 d2 ->
          exists d2' vargs' sg' b' v0' v1' v2' v3' v4' v5' v6' v7' v8' 
                 v9' v10' v11' v12' v13' v14' v15' v16',
            trap_into_kernel_spec f s m rs d2 d2' vargs' sg' b'
                                  v0' v1' v2' v3' v4' v5' v6' v7' v8' v9' 
                                  v10' v11' v12' v13' v14' v15' v16'.
      Proof.
        intros until v16; intros Hstep Hid Hobs_eq.
        unfold trap_into_kernel_spec in *.
        decompose [and] Hstep; clear Hstep.
        edestruct safesec_proc_exit_user as [d2' ?]; eauto.
        exists d2'; repeat (eexists; eauto).
      Qed.

    End SAFESEC_SYSCALL.

    Ltac exists_simpl :=
      repeat (match goal with
                | Hex : exists _, _ |- _ => destruct Hex as [? Hex]
              end).

    (* SafeSecure for the entire tsyscall semantics. 
       Combines all the previous SafeSecure lemmas.

       Note that the low_level_invariant is already provided by mCertiKOS (just
       like the high_level_invariant). We could add it as a field to 
       secure_inv, but this is the only proof that needs it, so we felt 
       it was not worth the effort. *)

    Theorem safe_secure :
      forall m m1' d1 d2 d1' rs rs1' t1,
        low_level_invariant (Mem.nextblock m) d2 ->
        secure_inv b id d1 -> secure_inv' b id rs d1 ->
        secure_inv b id d2 -> secure_inv' b id rs d2 ->
        LAsm.step ge (State rs (m,d1)) t1 (State rs1' (m1',d1')) -> 
        id = cid d1 -> obs_eq d1 d2 ->
        exists t2 rs2' m2' d2',
          LAsm.step ge (State rs (m,d2)) t2 (State rs2' (m2',d2')).
    Proof.
      intros m m1' d1 d2 d1' rs rs1' t1 Hlow2 Hinv1 Hinv1' Hinv2 Hinv2' Hstep Hid Hobs_eq.
      destruct Hinv1, Hinv1', Hinv2, Hinv2'.
      destruct sec_usermode, sec_usermode0.

      assert (Hcases: rs PC = Vptr b Int.zero \/ (ikern d1 = false /\ ikern d2 = false))
        by (destruct (ikern d1); destruct (ikern d2); auto); destruct Hcases as [Hcase|Hcase].

      (* deal with kernel mode as a special case *)
      generalize Hid; clear Hid.
      assert (Hmake': make_globalenv s M tsyscall_layer = ret ge) by auto.
      unfold tsyscall_layer in Hmake'; inv_make_globalenv Hmake'.
      unfold tsyscall, tsyscall_passthrough in HLge0; inv_make_globalenv HLge0.
      assert (b1 = b).
      {
        inv HLge0le.
        specialize (genv_le_find_symbol proc_start_user).
        rewrite Hb1fs, Hpsu in genv_le_find_symbol; inv genv_le_find_symbol; auto.
      }
      subst.
      assert (Genv.find_funct_ptr ge b = Some (External (EF_external proc_start_user null_signature))).
      {
        inv HLge0le.
        specialize (genv_le_find_funct_ptr b).
        rewrite Hb1fp in genv_le_find_funct_ptr; inv genv_le_find_funct_ptr; auto.
      }
      eapply startuser_step in Hstep; eauto; destruct Hstep as [Hstep Ht1]; inv Hstep.
      intro Hid; rename H4 into Hstep1.
      assert (Hstep2:= Hstep1); apply safesec_proc_start_user with (d2:= d2) in Hstep2; auto.
      exists_simpl; rename x into d2', x0 into rs2'.
      assert (rs' = rs2')
        by (exploit conf_proc_start_user; [| eapply Hstep1 | eapply Hstep2 |..]; 
            auto; instantiate; try congruence; tauto).
      repeat eexists; eapply exec_step_prim_call; [|eauto|]; auto.
      econstructor.
      exists null_signature, (primcall_start_user_compatsem proc_start_user_spec); repeat (split; auto).
      econstructor; eauto.
      simpl; econstructor; eauto; subst; auto.

      (* now we can assume that we are not in kernel mode *)
      destruct Hcase as [Hkern1 Hkern2]; generalize Hid; clear Hid; inv Hstep; 
        try solve [destruct EXT_ALLOWED; simpl in *; congruence].
      {
        destruct i; inv H7;
          try solve [repeat eexists; eapply exec_step_internal; 
                     eauto; try discriminate; simpl; eauto];
          try solve [intro Hid; edestruct safesec_exec_loadex as [? [? [? ?]]]; eauto;
                     repeat eexists; eapply exec_step_internal; eauto; try discriminate];
          try solve [intro Hid; edestruct safesec_exec_storeex as [? [? [? ?]]]; eauto;
                     repeat eexists; eapply exec_step_internal; eauto; try discriminate];
          try solve [intro Hid; exists E0, rs1', m1'; eexists;
                     eapply exec_step_internal; eauto; try discriminate; simpl;
                     unfold goto_label in *; subdestruct; inv H1; eauto];
          try solve [destruct (INSTR_ALLOWED eq_refl); simpl in *; congruence].
        destruct i; inv H0;
          try solve [repeat eexists; eapply exec_step_internal; 
                     eauto; try discriminate; simpl; eauto];
          try solve [intro Hid; edestruct safesec_exec_loadex as [? [? [? ?]]]; eauto;
                     repeat eexists; eapply exec_step_internal; eauto; try discriminate];
          try solve [intro Hid; edestruct safesec_exec_storeex as [? [? [? ?]]]; eauto;
                     repeat eexists; eapply exec_step_internal; eauto; try discriminate];
          try solve [intro Hid; exists E0, rs1', m1'; eexists;
                     eapply exec_step_internal; eauto; try discriminate; simpl;
                     unfold goto_label in *; subdestruct; inv H1; eauto];
          try solve [destruct (INSTR_ALLOWED eq_refl); simpl in *; congruence].
      }
      {
        (* Case 2: primitive call *)
        destruct H6 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
        set (σ':= σ); inv_layer Hl; inv Hsem.
        {
          (* dispatch *)
          inv H1.
          inv H8.
          intro Hid; destruct H1 as [Hproc1 ?]; rename H into Htrap1, H10 into Hstep1.
          assert (id = cid labd0) by (apply trap_into_kernel_usermode_cid in Htrap1; congruence).
          assert (id = cid labd1) by (edestruct sys_dispatch_usermode; eauto; instantiate; congruence).
          assert (Htrap2:= Htrap1); apply safesec_trap_into_kernel with (d2:= d2) in Htrap2; auto.
          exists_simpl; rename x into d2''.
          assert (obs_eq labd0 d2'')
            by (eapply conf_trap_into_kernel; [| eapply Htrap1 | eapply Htrap2 |..]; auto).
          assert (high_level_invariant d2'') by (eapply trap_into_kernel_high_inv; eauto).
          assert (Hstep2:= Hstep1); apply safesec_sys_dispatch_c with (d2:= d2'') in Hstep2; auto.
          destruct Hstep2 as [d2''' Hstep2].
          assert (obs_eq labd1 d2''')
            by (eapply conf_sys_dispatch_c; [| eapply Hstep1 | eapply Hstep2 |..]; auto).
          assert (Hproc2:= Hproc1); apply safesec_proc_start_user with (d2:= d2''') in Hproc2; auto.
          exists_simpl; rename x into d2', x20 into rs2'.
          assert (rs' = rs2')
            by (exploit conf_proc_start_user; [| eapply Hproc1 | eapply Hproc2 |..]; 
                auto; instantiate; try congruence; tauto).
          repeat eexists; eapply exec_step_prim_call; eauto.
          econstructor.
          exists sg, σ'; repeat (split; auto).
          econstructor; eauto.
          simpl; econstructor; eauto.
          constructor; [eauto | split; eauto].
          split; eauto; subst; tauto.
        }
        {
          (* page fault handler *)
          inv H1.
          inv H9.
          intro Hid; destruct H1 as [Hproc1 ?]; rename H into Htrap1, H11 into Hstep1.
          assert (id = cid labd0) by (apply trap_into_kernel_usermode_cid in Htrap1; congruence).
          assert (id = cid labd1) by (edestruct ptfault_resv_usermode; eauto; instantiate; congruence).
          assert (Htrap2:= Htrap1); apply safesec_trap_into_kernel with (d2:= d2) in Htrap2; auto.
          exists_simpl; rename x into d2''.
          assert (Hobs_eq': obs_eq labd0 d2'')
            by (eapply conf_trap_into_kernel; [| eapply Htrap1 | eapply Htrap2 |..]; auto).
          assert (high_level_invariant labd0) by (eapply trap_into_kernel_high_inv; eauto).
          assert (high_level_invariant d2'') by (eapply trap_into_kernel_high_inv; eauto).
          assert (Hstep2:= Hstep1); apply safesec_ptfault_resv with (d2:= d2'') in Hstep2; auto.
          destruct Hstep2 as [d2''' Hstep2].
          assert (obs_eq labd1 d2''')
            by (eapply conf_ptfault_resv; [| | | eapply Hstep1 | eapply Hstep2 |..]; auto).
          assert (Hproc2:= Hproc1); apply safesec_proc_start_user with (d2:= d2''') in Hproc2; auto.
          exists_simpl; rename x into d2', x20 into rs2'.
          assert (rs' = rs2')
            by (exploit conf_proc_start_user; [| eapply Hproc1 | eapply Hproc2 |..]; 
                auto; instantiate; try congruence; tauto).
          repeat eexists; eapply exec_step_prim_call; eauto.
          econstructor.
          exists sg, σ'; repeat (split; auto).
          econstructor; eauto.
          clear Hstep1; simpl; econstructor; eauto.
          constructor; [eauto | split; eauto].
          split; eauto; subst; tauto.
          obs_eq_rewrites Hobs_eq'.
        }
        {
          (* yield *)
          inv H1.
          intro Hid; rename H7 into Htrap1, H12 into Hstep1.
          assert (id = cid labd0) by (apply trap_into_kernel_usermode_cid in Htrap1; congruence).
          assert (Htrap2:= Htrap1); apply safesec_trap_into_kernel with (d2:= d2) in Htrap2; auto.
          exists_simpl; rename x into d2''.
          assert (obs_eq labd0 d2'')
            by (eapply conf_trap_into_kernel; [| eapply Htrap1 | eapply Htrap2 |..]; auto).
          assert (high_level_invariant labd0) by (eapply trap_into_kernel_high_inv; eauto).
          assert (high_level_invariant d2'') by (eapply trap_into_kernel_high_inv; eauto).
          assert (Hrdy: exists l, ZMap.get num_id (abq d2'') = AbQValid l /\ l <> nil /\ 0 <= last l num_id < num_id).
          {
            erewrite <- trap_into_kernel_usermode_abq; eauto.
            destruct (valid_TDQ _ sec_high_inv0 (valid_kern _ sec_high_inv0 Hkern2) num_id) as [l [? Hlt]]; [omega|].
            exists l; split; [auto|]; split.
            destruct (usermode_abq0 l); auto.
            apply Hlt; apply last_correct; intro Hcon.
            symmetry in Hcon; apply last_default in Hcon.
            destruct (usermode_abq0 l); congruence.
            intro Hcon'; specialize (Hlt _ Hcon'); omega.
          }
          destruct Hrdy as [l [Hrdy [Hnil Hlt]]].
          assert (Hstep2:= Hstep1); apply safesec_thread_yield with (d2:= d2'') (l:= l) in Hstep2; auto.
          exists_simpl; rename x into d2', x20 into rs2'.
          repeat eexists; eapply exec_step_prim_call; eauto.
          econstructor.
          exists sg, σ'; repeat (split; auto).
          econstructor; eauto.
          exploit trap_into_kernel_low_inv; eauto; intro Hlow; inv Hlow.
          assert (rs2' = ZMap.get (last l num_id) (kctxt d2''))
            by (unfold thread_yield_spec in Hstep2; subdestruct; inv_somes; inv Hrdy; auto).
          clear Hstep1; simpl; econstructor; eauto; unfold kctxt_inject_neutral in *.
          intros; subst; exploit (kctxt_INJECT (last l num_id)); eauto; tauto.
          intros; subst; exploit (kctxt_INJECT (last l num_id)); eauto; tauto.
        }
        {
          (* proc_start_user *)
          inv H1.
          intro Hid; rename H7 into Hstep1.
          assert (Hstep2:= Hstep1); apply safesec_proc_start_user with (d2:= d2) in Hstep2; auto.
          exists_simpl; rename x into d2', x0 into rs2'.
          assert (rs' = rs2')
            by (exploit conf_proc_start_user; [| eapply Hstep1 | eapply Hstep2 |..]; 
                auto; instantiate; try congruence; tauto).
          repeat eexists; eapply exec_step_prim_call; [|eauto|]; auto.
          econstructor.
          exists sg, σ'; repeat (split; auto).
          econstructor; eauto.
          simpl; econstructor; eauto; subst; auto.
        }
      }
    Qed.

    End SAFESEC_LEMMAS.

  End WITHIMPL.

End WITHMEM.  