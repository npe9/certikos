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
Require Import I64Layer.
Require Import LoadStoreSem2.
Require Import MakeProgram.

Require Import SecurityCommon.
Require Import Observation.
Require Import ObservationImpl.
Require Import Behavior.

(* Proofs of extra properties needed by end-to-end security.
   Main properties:
   1.)  Behavioral instances for tsyscall and mboot (which allows us to define
        whole-execution behaviors for these layers)
   2.)  proof that tsyscall never produces traces after initialization (traces 
        are a relic of CompCert that we ignore in mCertiKOS, but they need to be
        mentioned in various places in order to interface everything with CompCert) 

   Paper Reference: Section 3 *)

Section WITHMEM.

  Local Open Scope nat_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Lemma no_output_props :
    forall d d' p,
      devout d = devout d' ->
      obs_leq (observe p d) (observe p d') /\
      obs_measure (observe p d') <= S (obs_measure (observe p d)).
  Proof.
    unfold observe; intros d d' p Heq.
    rewrite Heq; split; auto; apply obs_leq_refl.
  Qed.

  Ltac no_out H := apply no_output_props; eapply H; eauto.

  Section TSYSCALL.

    (* proof that tsyscall is behavioral *)

    Require Import TSysCall.

    Local Instance : ExternalCallsOps (mwd (cdata RData)) := 
      CompatExternalCalls.compatlayer_extcall_ops (tsyscall ⊕ L64).
    Local Instance : LayerConfigurationOps := compatlayer_configuration_ops (tsyscall ⊕ L64).

    Lemma tsyscall_exec_load_no_output {F V} :
      forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd,
        exec_loadex(F:=F)(V:=V) ge chunk (m,d) a rs rd = Next rs' (m',d') ->
        devout d = devout d'.
    Proof.
      unfold exec_loadex, exec_loadex2; intros; subdestruct; rename H into Hexec.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - unfold HostAccess2.exec_host_load2 in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in *; subdestruct; inv H0; auto.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - unfold GuestAccessIntel1.exec_guest_intel_load1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.load_accessor1 in *; subdestruct; inv Hexec; auto.
      - unfold GuestAccessIntel1.exec_guest_intel_load1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.load_accessor1 in *; subdestruct; inv Hexec; auto.
    Qed.

    Lemma tsyscall_exec_store_no_output {F V} :
      forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd rds,
        exec_storeex(F:=F)(V:=V) ge chunk (m,d) a rs rd rds = Next rs' (m',d') ->
        devout d = devout d'.
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

    Lemma tsyscall_external_call_no_output {F V} :
      forall (m m' : mem) (d d' : cdata RData) t WB ge name sg args res,
        external_call'(F:=F)(V:=V) WB (EF_external name sg) ge args (m, d) t res (m', d') ->
        devout d = devout d'.
    Proof.
      intros m m' d d' t WB ge name sg args res Hext; inv Hext.
      destruct H as [? [Hl [? [? [? [Hsem1 [Hsem2 [? ?]]]]]]]].
      inv_layer Hl; try solve [inv Hsem2 | inv Hsem1; auto].
      inv Hsem1; inv H4; inv H2.
      unfold proc_init_spec, ret in *; simpl in *.
      repeat elim_none; inv H1; auto.
    Qed.

    Lemma trap_into_kernel_no_output :
      forall id s' m' rs d d' vargs sg0 b0 v0
             v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
        trap_into_kernel_spec id s' m' rs d d' vargs sg0 b0 v0
          v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> 
        devout d = devout d'.
    Proof.
      intros until v16; intro Hspec; inv Hspec.
      decompose [and] H0; inv_spec; inv_somes; auto.
    Qed.

    Lemma proc_start_user_no_output :
      forall d d' rs,
        proc_start_user_spec d = Some (d', rs) ->
        devout d = devout d'.
    Proof.
      unfold proc_start_user_spec; intros; subdestruct.
      inv H; auto.
    Qed.

    Lemma uctx_set_errno_no_output :
      forall r d d',
        uctx_set_errno_spec r d = Some d' ->
        devout d = devout d'.
    Proof.
      unfold uctx_set_errno_spec; intros; subdestruct.
      inv H; auto.
    Qed.

    Lemma uctx_set_retval1_no_output :
      forall r d d',
        uctx_set_retval1_spec r d = Some d' ->
        devout d = devout d'.
    Proof.
      unfold uctx_set_retval1_spec; intros; subdestruct.
      inv H; auto.
    Qed.

    Lemma proc_create_no_output :
      forall d d' b1 b2 b3 n z r,
        proc_create_spec d b1 b2 b3 n z = Some (d', r) ->
        devout d = devout d'.
    Proof.
      unfold proc_create_spec; intros; subdestruct.
      inv H; auto.
    Qed.

    Lemma trap_proc_create_no_output :
      forall s m d d',
        trap_proc_create_spec s m d = Some d' ->
        devout d = devout d'.
    Proof.
      unfold trap_proc_create_spec; intros; subdestruct;
        try solve [eapply uctx_set_errno_no_output; eauto].
      transitivity (devout r).
      eapply proc_create_no_output; eauto.
      transitivity (devout r0).
      eapply uctx_set_retval1_no_output; eauto.
      eapply uctx_set_errno_no_output; eauto.
    Qed.

    Lemma trap_get_quota_no_output :
      forall d d',
        trap_get_quota_spec d = Some d' ->
        devout d = devout d'.
    Proof.
      unfold trap_get_quota_spec; intros; subdestruct.
      transitivity (devout r).
      eapply uctx_set_retval1_no_output; eauto.
      eapply uctx_set_errno_no_output; eauto.
    Qed.

    Section PTRESV.

      Lemma ptInsertPTE0_no_output :
        forall i vadr padr pm d d',
          ptInsertPTE0_spec i vadr padr pm d = Some d' ->
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto. 
      Qed.

      Lemma ptAllocPDE0_no_output :
        forall i1 i2 n d d',
          ptAllocPDE0_spec i1 i2 d = Some (d', n) ->
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
      Qed.

      Lemma ptInsert0_no_output :
        forall i1 i2 b i3 d d' v,
          ptInsert0_spec i1 i2 b i3 d = Some (d', v) ->
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
        - eapply ptInsertPTE0_no_output; eauto.
        - eapply ptAllocPDE0_no_output; eauto.
        - transitivity (devout r).
          eapply ptAllocPDE0_no_output; eauto.
          eapply ptInsertPTE0_no_output; eauto.
      Qed.

      Lemma alloc_no_output :
        forall i r d d',
          alloc_spec i d = Some (d', r) ->
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
      Qed.

      Lemma ptResv2_no_output :
        forall i1 i2 i3 i4 i5 i6 n d d',
          ptResv2_spec i1 i2 i3 i4 i5 i6 d = Some (d', n) ->
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
        - transitivity (devout r).
          eapply alloc_no_output; eauto.
          eapply ptInsert0_no_output; eauto.
        - transitivity (devout r).
          eapply alloc_no_output; eauto.
          transitivity (devout r0).
          eapply ptInsert0_no_output; eauto.
          eapply ptInsert0_no_output; eauto.
      Qed.

    End PTRESV.

    Lemma offer_shared_mem_no_output :
      forall d d' i1 i2 i3 r,
        offer_shared_mem_spec i1 i2 i3 d = Some (d', r) ->
        devout d = devout d'.
    Proof.
      intros; inv_spec; inv_somes; auto.
      - transitivity (devout r0); auto.
        eapply ptResv2_no_output; eauto.
      - transitivity (devout r0); auto.
        eapply ptResv2_no_output; eauto.
    Qed.
    
    Lemma trap_offer_shared_mem_no_output :
      forall d d',
        trap_offer_shared_mem_spec d = Some d' ->
        devout d = devout d'.
    Proof.
      intros; inv_spec; inv_somes; try solve [eapply uctx_set_errno_no_output; eauto].
      transitivity (devout r).
      eapply offer_shared_mem_no_output; eauto.
      transitivity (devout r0).
      eapply uctx_set_retval1_no_output; eauto.
      eapply uctx_set_errno_no_output; eauto.
    Qed.

    Lemma print_behavioral_props :
      forall d d' p,
        print_spec d = Some d' ->
        obs_leq (observe p d) (observe p d') /\
        obs_measure (observe p d') <= S (obs_measure (observe p d)).
    Proof.
      intros; inv_spec; inv_somes; unfold observe.
      inv_spec; inv_somes; simpl.
      unfold DeviceOutput_update; zmap_solve; split; auto.
      apply list_leq_app.
      apply list_leq_refl.
    Qed.

    Local Opaque obs_leq obs_measure.

    Section PRIMCALLS.

      Lemma sys_dispatch_behavioral_props :
        forall s m d d' p,
          sys_dispatch_c_spec s m d = Some d' -> 
          obs_leq (observe p d) (observe p d') /\
          obs_measure (observe p d') <= S (obs_measure (observe p d)).
      Proof.
        intros; inv_spec; inv_somes; try solve [no_out uctx_set_errno_no_output].
        no_out trap_proc_create_no_output.
        no_out trap_get_quota_no_output.
        no_out trap_offer_shared_mem_no_output.
        eapply print_behavioral_props; eauto.
      Qed.

      Lemma ptResv_no_output :
        forall n v pm r d d',
          ptResv_spec n v pm d = Some (d',r) -> 
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
        transitivity (devout r0).
        eapply alloc_no_output; eauto.
        eapply ptInsert0_no_output; eauto.
      Qed.

      Lemma ptfault_resv_no_output :
        forall v d d',
          ptfault_resv_spec v d = Some d' -> 
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
        eapply ptResv_no_output; eauto.
      Qed.

      Lemma thread_yield_no_output :
        forall rs rs' d d',
          thread_yield_spec d rs = Some (d',rs') ->
          devout d = devout d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
      Qed.

    End PRIMCALLS.

    Section BEHAVIORAL.

      Lemma tsyscall_behavioral_props :
        forall ge rs rs' (m m' : mem) (d d' : cdata RData) t p,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) ->
          obs_leq (observe p d) (observe p d') /\
          obs_measure (observe p d') <= S (obs_measure (observe p d)).
      Proof.
        intros; pattern d, d'; eapply step_P; eauto.
        - intros; apply no_output_props; auto.
        - simpl; intros; no_out (tsyscall_exec_load_no_output(F:=fundef)(V:=unit)).
        - simpl; intros; no_out (tsyscall_exec_store_no_output(F:=fundef)(V:=unit)).
        - simpl; intros; no_out (tsyscall_external_call_no_output(F:=fundef)(V:=unit)).
        - intros ef [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
          inv_layer Hl; inv Hsem.
          + (* dispatch *)
            inv H2.
            inv H7.
            unfold observe; erewrite trap_into_kernel_no_output; eauto.
            destruct H2; erewrite <- (proc_start_user_no_output labd1 d'); eauto.
            eapply sys_dispatch_behavioral_props; eauto.
          + (* pagefault *)
            inv H2.
            inv H8.
            unfold observe; erewrite trap_into_kernel_no_output; eauto.
            destruct H2; erewrite <- (proc_start_user_no_output labd1 d'); eauto.
            no_out ptfault_resv_no_output.
          + (* yield *)
            inv H2.
            unfold observe; erewrite trap_into_kernel_no_output; eauto.
            no_out thread_yield_no_output.
          + (* proc_start_user *)
            inv H2.
            no_out proc_start_user_no_output.
      Qed.

      Instance tsyscall_behavioral : 
        forall prog p,
          Behavioral (LAsm.semantics prog) (observe_lasm _ p).
      Proof.
        intros prog p; unfold observe_lasm; constructor.
        - intros t [rs1 [m1 d1]] [rs2 [m2 d2]] Hstep.
          eapply proj1; eapply tsyscall_behavioral_props; eauto.
        - intros t [rs1 [m1 d1]] [rs2 [m2 d2]] Hstep.
          eapply proj2; eapply tsyscall_behavioral_props; eauto.
      Qed.

    End BEHAVIORAL.

    Section NOTRACE.

      (* proof that tsyscall produces no traces after proper initialization *)

      Require Import SecurityInv1.
      Require Import SecurityInv2.
      Require Import SecurityInv.

      Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
      Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

      Variables (s : stencil) (M : module) (ge : genv) (b : block).
      Hypothesis (Hmake : make_globalenv s M tsyscall_layer = OK ge).
      Hypothesis (Hpsu : Genv.find_symbol ge proc_start_user = Some b).

      Lemma tsyscall_notrace :
        forall rs rs' (m m' : mem) (d d' : cdata RData) t p,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) ->
          secure_inv' b p rs d -> t = E0.
      Proof.
        intros rs rs' m m' d d' t p Hstep Hinv.
        assert (Hstept:= Hstep); inv Hstep; auto.
        - inv H7.
          inv Hinv; inv sec_usermode.
          destruct EXT_ALLOWED as [Hkern ?]; simpl in Hkern; specialize (usermode_ikern Hkern).
          assert (Hsem:= startuser_step _ _ _ _ Hmake Hpsu _ _ _ 
                                        _ _ _ _ Hstept usermode_ikern); inv Hsem; auto.
        - inv H8.
          inv Hinv; inv sec_usermode.
          destruct EXT_ALLOWED as [Hkern ?]; simpl in Hkern; specialize (usermode_ikern Hkern).
          assert (Hsem:= startuser_step _ _ _ _ Hmake Hpsu _ _ _ 
                                        _ _ _ _ Hstept usermode_ikern); inv Hsem; auto.
        - inv H7.
          inv Hinv; inv sec_usermode.
          destruct EXT_ALLOWED as [Hkern ?]; simpl in Hkern; specialize (usermode_ikern Hkern).
          assert (Hsem:= startuser_step _ _ _ _ Hmake Hpsu _ _ _ 
                                        _ _ _ _ Hstept usermode_ikern); inv Hsem; auto.
        - destruct H6 as [? [? [? [? [? Hsem]]]]]; inv Hsem; auto.
      Qed.

    End NOTRACE.

  End TSYSCALL.

  Section MBOOT.

    (* proof that mboot is behavioral *)

    Local Open Scope nat_scope.

    Require Import MBoot.

    (* These instances need names for some reason or Coq doesn't accept them.
       Pretty sure this is a Coq bug. *)
    Local Instance mboot_ext : ExternalCallsOps (mwd (cdata RData)) := 
      CompatExternalCalls.compatlayer_extcall_ops (mboot ⊕ L64).
    Local Instance mboot_lcfg : LayerConfigurationOps := 
      compatlayer_configuration_ops (mboot ⊕ L64).

    Lemma mboot_exec_load_no_output {F V} :
      forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd,
        exec_loadex(F:=F)(V:=V) ge chunk (m,d) a rs rd = Next rs' (m',d') ->
        devout d = devout d'.
    Proof.
      unfold exec_loadex, LoadStoreSem1.exec_loadex1; intros; subdestruct; rename H into Hexec.
      - unfold HostAccess1.exec_host_load1 in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in *; subdestruct; inv H0; auto.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - unfold HostAccess1.exec_host_load1 in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in *; subdestruct; inv H0; auto.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - unfold GuestAccessIntel1.exec_guest_intel_load1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.load_accessor1 in *; subdestruct; inv Hexec; auto.
      - unfold GuestAccessIntel1.exec_guest_intel_load1,
               GuestAccessIntelDef0.exec_guest_intel_accessor1 in *; subdestruct.
        unfold GuestAccessIntel1.load_accessor1 in *; subdestruct; inv Hexec; auto.
    Qed.

    Lemma mboot_exec_store_no_output {F V} :
      forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd rds,
        exec_storeex(F:=F)(V:=V) ge chunk (m,d) a rs rd rds = Next rs' (m',d') ->
        devout d = devout d'.
    Proof.
      unfold exec_storeex, LoadStoreSem1.exec_storeex1; intros; subdestruct; rename H into Hexec.
      - unfold HostAccess1.exec_host_store1 in Hexec; subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec.
        inv Hdestruct11; auto.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec.
        inv Hdestruct12; auto.
        unfold PageFault.exec_pagefault in Hexec; subdestruct; inv Hexec; auto.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - unfold HostAccess1.exec_host_store1 in Hexec; subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec.
        inv Hdestruct11; auto.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec.
        inv Hdestruct12; auto.
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

    Local Opaque obs_leq obs_measure.

    Lemma mboot_external_call_behavioral_props {F V} :
      forall (m m' : mem) (d d' : cdata RData) t WB ge name sg args res p,
        external_call'(F:=F)(V:=V) WB (EF_external name sg) ge args (m, d) t res (m', d') ->
        obs_leq (observe p d) (observe p d') /\
        obs_measure (observe p d') <= S (obs_measure (observe p d)).
    Proof.
      intros m m' d d' t WB ge name sg args res p Hext; inv Hext.
      destruct H as [? [Hl [? [? [? [Hsem1 [Hsem2 [? ?]]]]]]]].
      inv_layer Hl;
        try solve [apply no_output_props; inv Hsem1; auto |
                   apply no_output_props; inv Hsem1; gensem_simpl; inv_monad H1; congruence].
      - (* fstore *)
        apply no_output_props; inv Hsem1; gensem_simpl.
        unfold fstore'_spec in *; subdestruct.
        inv H2; auto.
      - (* flatmem_copy *)
        apply no_output_props; inv Hsem1; gensem_simpl.
        unfold flatmem_copy'_spec in *; subdestruct.
        inv H1; auto.
      - (* device_output *) 
        inv Hsem1; gensem_simpl.
        inv H1; unfold observe, DeviceOutput_update; simpl; split; zmap_solve.
        Local Transparent obs_leq.
        simpl; apply list_leq_app.
        simpl; apply list_leq_refl.
      - (* set_pg *)
        apply no_output_props; inv Hsem1; gensem_simpl.
        unfold setPG_spec in *; subdestruct; inv H0; auto.
      - (* clear_cr2 *)
        apply no_output_props; inv Hsem1; gensem_simpl.
        unfold clearCR2_spec in *; subdestruct; inv H0; auto.
      - (* set_cr3 *)
        apply no_output_props; inv Hsem1; gensem_simpl.
        unfold setCR3_spec in *; subdestruct; inv_somes; auto.
      - (* get_size *)
        apply no_output_props; inv Hsem1; gensem_simpl.
        inv_monad H0; congruence.
      - (* boot_loader *)
        apply no_output_props; inv Hsem1; gensem_simpl.
        unfold bootloader0_spec in *; subdestruct; inv H1; auto.
    Qed.

    Lemma mboot_primitive_call_no_output :
      forall (m m' : mem) (d d' : cdata RData) ef ge rs rs' t,      
        primitive_call ef ge rs (m, d) t rs' (m', d') ->
        devout d = devout d'.
    Proof.
      intros m m' d d' ef ge rs rs' t [? [? [? [? [Hl Hsem]]]]].
      inv_layer Hl; inv Hsem; inv H1; inv_spec; inv_somes; auto.
    Qed.

    Lemma mboot_behavioral_props :
      forall ge rs rs' (m m' : mem) (d d' : cdata RData) t p,
        LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) ->
        obs_leq (observe p d) (observe p d') /\
        obs_measure (observe p d') <= S (obs_measure (observe p d)).
    Proof.
      intros; pattern d, d'; eapply step_P; eauto.
      - intros; apply no_output_props; auto.
      - intros; simpl in * |-; no_out (mboot_exec_load_no_output(F:=fundef)(V:=unit)).
      - intros; simpl in * |-; no_out (mboot_exec_store_no_output(F:=fundef)(V:=unit)).
      - intros; eapply mboot_external_call_behavioral_props; eauto.
      - intros; no_out mboot_primitive_call_no_output.
    Qed.

    Instance mboot_behavioral : 
      forall prog p,
        Behavioral (LAsm.semantics prog) (observe_lasm _ p).
    Proof.
      intros prog p; unfold observe_lasm; constructor.
      - intros t [rs1 [m1 d1]] [rs2 [m2 d2]] Hstep.
        eapply proj1; eapply mboot_behavioral_props; eauto.
      - intros t [rs1 [m1 d1]] [rs2 [m2 d2]] Hstep.
        eapply proj2; eapply mboot_behavioral_props; eauto.
    Qed.

  End MBOOT.

End WITHMEM.