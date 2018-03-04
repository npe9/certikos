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

(* This file proves the integrity lemma over the TSysCall semantics, saying that
   if state s takes a step to state s', and both states are inactive (i.e., the 
   currently-running process is not the observer), then s and s' are observably
   equivalent. 
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

    Ltac solve_integ := constructor; simpl; auto; zmap_solve; try reflexivity; try congruence.

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

    Section INTEG_LEMMAS.

      Section INTEG_UCTX.

        (* Integrity for setting system call arguments and return values *)

        Lemma integ_uctx_set_errno :
          forall d d' n,
            uctx_set_errno_spec n d = Some d' ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
        Qed.

        Lemma integ_uctx_set_retval1 :
          forall d d' n,
            uctx_set_retval1_spec n d = Some d' ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
        Qed.

        Lemma integ_uctx_set_retval2 :
          forall d d' n,
            uctx_set_retval2_spec n d = Some d' ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
        Qed.

        Lemma integ_uctx_set_retval3 :
          forall d d' n,
            uctx_set_retval3_spec n d = Some d' ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
        Qed.

        Lemma integ_uctx_set_retval4 :
          forall d d' n,
            uctx_set_retval4_spec n d = Some d' ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
        Qed.

        Lemma integ_uctx_set_retval5 :
          forall d d' n,
            uctx_set_retval5_spec n d = Some d' ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
        Qed.

      End INTEG_UCTX.

    Section INTEG_ACCESSORS.

      (* Integrity for load and store primitives *)

      Lemma PDEValid_usr :
        forall id i d pti pte,
          high_level_invariant d -> ikern d = false -> 0 <= id < num_id ->
          ZMap.get (PDX (Int.unsigned i)) (ZMap.get id (ptpool d)) = PDEValid pti pte ->
          adr_low <= Int.unsigned i < adr_high.
      Proof.
        intros id0 i d pti pte Hinv Hkern Hid Hpdx.
        assert (Hrange:= Int.unsigned_range_2 i).
        assert (Hmax:= max_unsigned_val).
        destruct Hinv.
        destruct (valid_PMap (valid_kern Hkern) id0 Hid) as [Hpmap _].
        assert (Hcases: adr_low <= Int.unsigned i < adr_high \/
                (0 <= Int.unsigned i < 262144*PgSize \/ 
                 983040*PgSize <= Int.unsigned i < 1048576*PgSize)) by omega.
        destruct Hcases as [|Hcases]; auto.
        assert (Hk: 0 <= Int.unsigned i / PgSize < 262144 \/
                983040 <= Int.unsigned i / PgSize < 1048576) 
          by  (destruct Hcases; [left|right]; split;
               try (apply Zdiv_le_lower_bound; omega); 
               try (apply Zdiv_lt_upper_bound; omega)).
        specialize (Hpmap _ Hk); unfold PDE_kern in Hpmap.
        replace (PDX (Int.unsigned i / 4096 * 4096)) with (PDX (Int.unsigned i)) in Hpmap.
        rewrites.
        unfold PDX.
        rewrite (Z_div_mod_eq (Int.unsigned i) PgSize); try omega.
        repeat rewrite <- Zdiv.Zdiv_Zdiv; try omega.
        rewrite Z.mul_comm.
        rewrite Z_div_plus_full_l; try omega.
        rewrite (Zdiv_small (Int.unsigned i mod PgSize) PgSize).
        rewrite Zplus_0_r.
        rewrite Z_div_mult_full; try omega.
        apply Z_mod_lt; omega.
      Qed.

      Lemma size_chunk_range' :
      forall chunk, 1 <= size_chunk chunk <= 8.
      Proof.
        destruct chunk; simpl; omega.
      Qed.

      Lemma integ_exec_loadex :
        forall m m' d d' rs rs' chunk a rd, 
          exec_loadex ge chunk (m, d) a rs rd = Next rs' (m', d') ->
          ikern d = false -> ihost d = true ->
          id <> cid d -> obs_eq d d' /\ m = m'.
      Proof.
        intros m m' d d' rs rs' chunk a rd Hstep Hkern Hhost Hid.
        unfold exec_loadex, exec_loadex2 in *; subdestruct; simpl in *; try congruence.
        unfold HostAccess2.exec_host_load2, snd in *; subdestruct; try (inv Hstep; split; reflexivity).
        unfold PageFault.exec_pagefault in *; subdestruct; inv Hstep.
        split; auto; unfold trapinfo_set; solve_integ.
      Qed.

      Lemma integ_exec_storeex :
        forall m m' d d' rs rs' chunk a rs0 l, 
          exec_storeex ge chunk (m, d) a rs rs0 l = Next rs' (m', d') ->
          high_level_invariant d -> ikern d = false -> 
          ihost d = true -> unshared (LAT d) (nps d) id ->
          0 <= id < num_id -> id <> cid d -> obs_eq d d' /\ m = m'.
      Proof.
        intros m m' d d' rs rs' chunk a rs0 l Hstep Hinv Hkern Hhost Hunsh Hrange Hid.
        unfold exec_storeex, exec_storeex2 in *; subdestruct; simpl in *; try congruence.
        unfold HostAccess2.exec_host_store2, snd in *.
        elim_stuck_eqn' Hstep Hpdx.
        rename pi into pti.
        assert (Hcases: (exists v pm, ZMap.get (PTX (Int.unsigned i)) pte = PTEValid v pm) \/ 
                         ZMap.get (PTX (Int.unsigned i)) pte = PTEUnPresent)
          by (subdestruct; [left|left|right]; eauto).
        assert (Husr: adr_low <= Int.unsigned i < adr_high)
          by (clear Hrange; eapply PDEValid_usr; eauto; destruct Hinv; rewrite valid_init_PT_cid; auto).
        destruct Hcases as [[pi [pm Hvalid]]|Hunp].
        {
          assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte with
                        | PTEValid v PTP =>
                          FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                            (m, d) (PTADDR v (Int.unsigned i)) rs rs0 l
                        | PTEValid v PTU =>
                          FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                            (m, d) (PTADDR v (Int.unsigned i)) rs rs0 l
                        | PTEValid v (PTK _) => Stuck
                        | PTEUnPresent => PageFault.exec_pagefault ge (m, d) i rs
                        | PTEUndef => Stuck
                      end = FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                              (m, d) (PTADDR pi (Int.unsigned i)) rs rs0 l)
            by (destruct pm; rewrites; subdestruct; auto).
          rewrite Hm in Hstep; clear Hm.          
          unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in *; subdestruct; inv Hstep.
          split; auto; clear Hdestruct3; solve_integ.
          unfold vread; simpl; intro vadr; destructgoal; f_equal.
          assert (Hcases: PTADDR pi (Int.unsigned i) <= PTADDR v vadr < PTADDR pi (Int.unsigned i) + 
                                  Z.of_nat (length (encode_val chunk (rs rs0))) \/ 
                             (PTADDR v vadr < PTADDR pi (Int.unsigned i) \/
                              PTADDR v vadr >= PTADDR pi (Int.unsigned i) + 
                                  Z.of_nat (length (encode_val chunk (rs rs0))))) by omega.
          unfold FlatMem.store; destruct Hcases as [Hcase|Hcase].
          assert (Hpi: PTADDR pi (Int.unsigned i) / PgSize <= PTADDR v vadr / PgSize <=
                       (PTADDR pi (Int.unsigned i) + Z.of_nat (length (encode_val chunk (rs rs0))) - 1) / PgSize)
            by (split; apply Z.div_le_mono; omega).                
          unfold PTADDR in Hpi.
          assert (Hmod: forall x, 0 <= x mod PgSize < PgSize) by (intros; apply Z.mod_pos_bound; omega).
          rewrite (Zdiv_unique _ _ pi (Int.unsigned i mod PgSize)) in Hpi; auto.
          rewrite (Zdiv_unique _ _ v (vadr mod PgSize)) in Hpi; auto.
          rewrite (Zdiv_unique _ _ pi (Int.unsigned i mod PgSize +
                                    Z.of_nat (length (encode_val chunk (rs rs0))) - 1)) in Hpi; try omega.
          assert (v = pi) by omega; subst; assert (Hinv':= Hinv); destruct Hinv'.
          rewrite valid_init_PT_cid in *; auto; contradiction Hid.
          eapply (Hunsh pi); try (eapply pmap_owners_consistent; eauto; try omega).
          edestruct valid_pmap_domain as [? [? [? [? ?]]]]; eauto; try omega.
          assert (Hcases: 0 < pi < kern_low \/ kern_low <= pi < nps d) by omega.
          destruct Hcases; auto.
          assert (ZMap.get pi (LAT d) = LATValid false ATKern nil) by (apply valid_AT_kern; auto; omega).
          rewrites.
          assumption.
          rewrite encode_val_length.
          rewrite <- size_chunk_conv.
          assert (Hch:= size_chunk_range' chunk); specialize (Hmod (Int.unsigned i)); omega.
          rewrite FlatMem.setN_outside; auto.
        }
        {
          unfold PageFault.exec_pagefault in *; rewrites; subdestruct; inv Hstep.
          split; auto; unfold trapinfo_set; solve_integ.
        }
      Qed.

    End INTEG_ACCESSORS.
    
    Section INTEG_PRIMS.

      (* Integrity for spawning processes *)

      Lemma integ_proc_create :
        forall d d' b1 b2 b3 ofs q r,
          high_level_invariant d -> cused (ZMap.get id (AC d)) = true -> pg d = true ->
          proc_create_spec d b1 b2 b3 ofs q = Some (d',r) ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros d d' b1 b2 b3 ofs q r Hinv Hused Hpg Hspec Hid.
        destruct Hinv.
        destruct (correct_curid Hpg) as [Hused' _].
        assert (Hmc:= cvalid_max_children _ valid_container _ Hused').
        assert (Hcases: Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d)))) < 3 \/
                        Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d)))) = 3) by omega.
        destruct Hcases as [Hcase|Hcase].
        - assert (Hcon:= cvalid_unused_next_child _ valid_container _ Hused' Hcase).
          inv_spec; inv_somes; simpl in *; unfold update_cusage, update_cchildren; solve_integ.
        - inv_spec; omega.
      Qed.

      Lemma integ_trap_proc_create :
        forall d d' s m,
          high_level_invariant d -> cused (ZMap.get id (AC d)) = true -> pg d = true ->
          trap_proc_create_spec s m d = Some d' ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; try solve [eapply integ_uctx_set_errno; eauto].
        transitivity r.
        eapply integ_proc_create; eauto.
        assert (Hcid: cid d = cid r) by (clear Hdestruct17 H2 Hdestruct11; inv_spec; inv_somes; auto).
        rewrite Hcid in H3; transitivity r0.
        eapply integ_uctx_set_retval1; eauto.
        assert (Hcid': cid r = cid r0) by (clear Hdestruct15 H2 Hdestruct11; inv_spec; inv_somes; auto).
        rewrite Hcid' in H3; eapply integ_uctx_set_errno; eauto.
      Qed.

      (* Integrity for getting quota *)

      Lemma integ_trap_get_quota :
        forall d d',
          trap_get_quota_spec d = Some d' ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; repeat inv_spec; inv_somes; solve_integ.
      Qed.

      (* Integrity for shared memory allocation and setup
         (only allowed between trusted processes) *)

      Lemma integ_alloc' :
        forall i d d' r,
          high_level_invariant d -> 0 <= id < num_id ->
          alloc_spec i d = Some (d',r) ->
          i <= high_id ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; solve_integ.
        intro vadr; unfold vread_perm; eqdestruct; zmap_solve; subst.
        destruct H.
        edestruct (valid_pmap_domain id H0 vadr) as [_ [? _]]; eauto; try omega.
        congruence.
      Qed.

      Lemma integ_ptInsertPTE0':
        forall i vadr padr pm d d',
          ptInsertPTE0_spec i vadr padr pm d = Some d' ->
          i <= high_id ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; solve_integ.
        - intros. unfold vread. rewrite ZMap.gso; auto. red; intros; subst. omega.
        - intros. unfold vread_perm. rewrite ZMap.gso; auto. red; intros; subst; omega.
        - intros. unfold vread. rewrite ZMap.gso; auto. red; intros; subst. omega.
        - intros. unfold vread_perm. rewrite ZMap.gso; auto. red; intros; subst; omega.
      Qed.

      Lemma integ_ptAllocPDE0':
        forall i i2 n d d',
          high_level_invariant d -> 0 <= id < num_id ->
          ptAllocPDE0_spec i i2 d = Some (d', n) ->
          i <= high_id ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; solve_integ.
        - intro vadr; unfold vread.
          rewrite ZMap.gso.
          destruct (zle_lt adr_low vadr adr_high) eqn:Hr; [|trivial]. zmap_simpl.
          destruct (ZMap.get (PDX vadr) (ZMap.get id (ptpool d))) eqn: Hp;
          unfold PMap, ZMap.t, PMap.t in Hp; rewrite Hp; [| reflexivity|reflexivity|reflexivity].
          destruct (ZMap.get (PTX vadr) pte) eqn: Ht; [|reflexivity|reflexivity].
          rewrite FlatMem.free_page_gso; auto.
          assert (Hown: isOwner (LAT d) id v). {
            eapply pmap_owners_consistent; eauto. omega.
          }
          inv Hown; destruct a as [Ha1 [Hlat Ha2]]; rewrites.
          rewrite pagei_ptaddr; auto.
          red; intros; subst. rewrite Hlat in H1. inv H1.
          inv H4.
          red; intros; subst. omega.
        - intro vadr; unfold vread_perm.
          eqdestruct; zmap_solve; try congruence.
          eqdestruct; zmap_solve; subst.
          destruct H.
          edestruct (valid_pmap_domain id H0 vadr) as [_ [_ [? [? _]]]]; eauto; try omega.
          destruct a as [? [? ?]]; congruence.
      Qed.

      Lemma integ_ptInsert0':
        forall i1 i2 b i3 d d' v,
          high_level_invariant d -> 0 <= id < num_id ->
          ptInsert0_spec i1 i2 b i3 d = Some (d', v) ->
          i1 <= high_id ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; clear Hdestruct4.
        - eapply integ_ptInsertPTE0'; eauto.
        - eapply integ_ptAllocPDE0'; eauto. 
        - transitivity r.
          + eapply integ_ptAllocPDE0'; eauto. 
          + exploit ptAllocPDE0_cid; eauto. intros (Heq & _).
            eapply integ_ptInsertPTE0'; eauto.
            rewrite <- Heq. trivial.
      Qed.

      Lemma integ_ptResv2:
        forall i2 i3 i5 i6 n d d',
          high_level_invariant d -> 0 <= id < num_id ->
          ptResv2_spec 1 i2 i3 2 i5 i6 d = Some (d', n) ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros. functional inversion H1; subst; clear H1.
        - solve_integ.
        - transitivity abd'.
          + eapply integ_alloc'; eauto. omega.
          + eapply integ_ptInsert0'; eauto.
            * eapply alloc_high_level_inv; eauto.
            * omega.
            * exploit alloc_cid; eauto. intros (HP & _).
              rewrite <- HP. assumption.
        - transitivity abd'.
          + eapply integ_alloc'; eauto. omega.
          + exploit alloc_cid; eauto. intros (HP & _).
            rewrite HP in H2. 
            exploit alloc_high_level_inv; eauto.             
            intros.
            transitivity abd''.
            * eapply integ_ptInsert0'; eauto. omega.
            * eapply integ_ptInsert0'; eauto. 
              eapply ptInsert_high_level_inv; eauto.
              omega.
              clear H3.
              exploit ptInsert0_cid; eauto. intros (HP' & _).
              rewrite <- HP'. trivial.
      Qed.

      Lemma obs_eq_impl_smsp:
        forall d d' smsp,
          obs_eq d d' ->
          obs_eq d d' {smspool : smsp}.
      Proof.
        intros. inv H; solve_integ.
      Qed.

      Lemma integ_offer_shared_mem :
        forall i3 d d' z,
          high_level_invariant d -> 0 <= id < num_id ->
          offer_shared_mem_spec 1 2 i3 d = Some (d', z) ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros. functional inversion H1; subst.
        - solve_integ.
        - eapply obs_eq_impl_smsp.
          eapply integ_ptResv2; eauto.
        - eapply obs_eq_impl_smsp.
          eapply integ_ptResv2; eauto.
        - solve_integ.
      Qed.

      Lemma offer_shared_mem_cid :
        forall i1 i2 i3 d d' z,
          offer_shared_mem_spec i1 i2 i3 d = Some (d', z) ->
          cid d = cid d'.
      Proof.
        intros. functional inversion H; subst; simpl; eauto.
        - eapply ptResv2_cid; eauto.
        - eapply ptResv2_cid; eauto.
      Qed.

      Lemma integ_trap_offer_shared_mem :
        forall d d',
          high_level_invariant d -> 0 <= id < num_id ->
          trap_offer_shared_mem_spec d = Some d' ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; try solve [eapply integ_uctx_set_errno; eauto].
        transitivity r.
        eapply integ_offer_shared_mem; eauto.
        eapply offer_shared_mem_cid in Hdestruct1; eauto.
        rewrite Hdestruct1 in H2.
        transitivity r0.
        eapply integ_uctx_set_retval1; eauto.
        eapply integ_uctx_set_errno; eauto.
        functional inversion Hdestruct3; trivial.
      Qed.

      (* Integrity for printing output *)

      Lemma obs_eq_impl_devout:
        forall d d' out,
          obs_eq d {devout: DeviceOutput_update (devout d) (cid d) (cid d) out} d'->
          id <> cid d ->
          obs_eq d d'.
      Proof.
        intros. inv H; solve_integ.
        simpl in obs_eq_OUT.
        unfold DeviceOutput_update in obs_eq_OUT.
        rewrite ZMap.gso in obs_eq_OUT; auto.
      Qed.

      Lemma integ_print :
        forall d d',
          high_level_invariant d -> 0 <= id < num_id ->
          print_spec d = Some d' ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes.
        eapply obs_eq_impl_devout; eauto.
        exploit integ_uctx_set_errno; eauto.
      Qed.

      (* Integrity for the system call dispatcher *)

      Lemma integ_sys_dispatch_c :
        forall d d' s m,
          high_level_invariant d -> cused (ZMap.get id (AC d)) = true -> pg d = true ->
          0 <= id < num_id ->
          sys_dispatch_c_spec s m d = Some d' ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; try solve [eapply integ_uctx_set_errno; eauto].
        eapply integ_trap_proc_create; eauto.
        eapply integ_trap_get_quota; eauto.
        eapply integ_trap_offer_shared_mem; eauto.
        eapply integ_print; eauto.
      Qed.

      Section INTEG_PTFAULT.

        (* Integrity for page fault handling *)

        Lemma integ_alloc :
          forall d d' r,
            high_level_invariant d -> 0 <= id < num_id ->
            alloc_spec (cid d) d = Some (d',r) ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
          intro vadr; unfold vread_perm; eqdestruct; zmap_solve; subst.
          destruct H.
          edestruct (valid_pmap_domain id H0 vadr) as [_ [? _]]; eauto; try omega.
          congruence.
        Qed.

        Lemma integ_ptAllocPDE0 :
          forall d d' v r,
            high_level_invariant d -> 0 <= id < num_id ->
            ptAllocPDE0_spec (cid d) v d = Some (d', r) ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
          - intro vadr; unfold vread; simpl; zmap_simpl; unfold PMap.
            repeat match goal with
            | |- match ?a with
                   | _ => _
                 end = 
                 match ?a with
                 | _ => _
                 end => let H := fresh "Hdestruct" in destruct a eqn:H; try apply (eq_refl None)
            end; f_equal.
            destruct (zeq r v0); subst.
            assert (Hown: isOwner (LAT d) id v0) by (eapply pmap_owners_consistent; eauto; omega).
            inv Hown; destruct a as [Ha1 [Hlat Ha2]]; rewrites.
            inv H3.
            rewrite FlatMem.free_page_gso; auto.
            rewrite pagei_ptaddr; auto.
          - intro vadr; unfold vread_perm; simpl; zmap_simpl; eqdestruct; zmap_solve; subst.
            destruct H.
            edestruct (valid_pmap_domain id H0 vadr) as [_ [_ [? [? _]]]]; eauto; try omega.
            destruct a as [? [? ?]]; congruence.
        Qed.

        Lemma integ_ptInsertPTE0 :
          forall d d' vadr padr pm,
            ptInsertPTE0_spec (cid d) vadr padr pm d = Some d' ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ.
          - intro v; unfold vread; simpl; zmap_simpl; eqdestruct.
          - intro v; unfold vread_perm; simpl; zmap_simpl; eqdestruct.
          - intro v; unfold vread; simpl; zmap_simpl; eqdestruct.
          - intro v; unfold vread_perm; simpl; zmap_simpl; eqdestruct.
        Qed.

        Lemma integ_ptInsert0 :
          forall d d' vadr padr pm r,
            high_level_invariant d -> 0 <= id < num_id ->
            ptInsert0_spec (cid d) vadr padr pm d = Some (d',r) ->
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes.
          - eapply integ_ptInsertPTE0; eauto.
          - eapply integ_ptAllocPDE0; eauto.
          - transitivity r0.
            eapply integ_ptAllocPDE0; eauto.
            assert (Hcid: cid d = cid r0) by (clear Hdestruct9; inv_spec; inv_somes; auto).
            rewrite Hcid in *; eapply integ_ptInsertPTE0; eauto.
        Qed.

        Lemma integ_ptResv :
          forall d d' v pm r,
            high_level_invariant d -> 0 <= id < num_id ->
            ptResv_spec (cid d) v pm d = Some (d',r) -> 
            id <> cid d -> obs_eq  d d'.
        Proof.
          intros; inv_spec; inv_somes; [solve_integ|].
          transitivity r0.
          eapply integ_alloc; eauto.
          assert (Hcid: cid d = cid r0) by (clear H1; inv_spec; inv_somes; auto).
          rewrite Hcid in *; eapply integ_ptInsert0; eauto.
          eapply alloc_high_level_inv; eauto.
        Qed.

        Lemma integ_ptfault_resv :
          forall d d' v,
            high_level_invariant d -> 0 <= id < num_id ->
            ptfault_resv_spec v d = Some d' -> 
            id <> cid d -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; [|reflexivity].
          eapply integ_ptResv; eauto.
        Qed.

      End INTEG_PTFAULT.

      Section INTEG_YIELD.        

        (* Integrity for yield *)

        Lemma integ_thread_yield :
          forall d d' rs r,
            thread_yield_spec d rs = Some (d',r) ->
            id <> cid d -> id <> cid d' -> obs_eq d d'.
        Proof.
          intros; inv_spec; inv_somes; solve_integ; simpl in *; intuition.
        Qed.

      End INTEG_YIELD.

    End INTEG_PRIMS.

    Section INTEG_SYSCALL.
      
      (* Integrity for system call trapping *)

      Lemma integ_proc_exit_user :
        forall d d' uc,
          proc_exit_user_spec d uc = Some d' ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; solve_integ.
      Qed.
      
      Lemma integ_proc_start_user :
        forall d d' r,
          proc_start_user_spec d = Some (d',r) ->
          id <> cid d -> obs_eq d d'.
      Proof.
        intros; inv_spec; inv_somes; solve_integ.
      Qed.

      Lemma integ_trap_into_kernel :
        forall d d' f s m rs vargs sg b
               v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
          trap_into_kernel_spec f s m rs d d' vargs sg b
                                v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
          id <> cid d -> obs_eq d d'.
      Proof.
        unfold trap_into_kernel_spec; intros until v16; intros Hspec Hcid.
        decompose [and] Hspec; clear Hspec.
        eapply integ_proc_exit_user; eauto.
      Qed.

    End INTEG_SYSCALL.

    (* Integrity for the entire tsyscall semantics. 
       Combines all the previous integrity lemmas.  *)

    Theorem integrity :
      forall m m' d d' rs rs' t,
        secure_inv b id d -> secure_inv' b id rs d ->
        LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
        id <> cid d -> id <> cid d' -> obs_eq d d' /\ m = m'.
    Proof.
      intros m m' d d' rs rs' t Hinv Hinv' Hstep Hid Hid'.
      destruct Hinv; destruct Hinv'; destruct sec_usermode.
      assert (Hrange: 0 <= id < num_id) by (destruct sec_high_inv; destruct valid_container; auto).
      destruct (ikern d) eqn:Hkern.
      (* deal with kernel mode as a special case *)
      eapply startuser_step in Hstep; eauto; destruct Hstep as [Hstep ?]; inv Hstep.
      split; auto; eapply integ_proc_start_user; eauto.
      (* now we can assume we're in user mode *)
      assert (Hinv:= sec_high_inv); destruct sec_high_inv; inv Hstep; 
      try solve [destruct EXT_ALLOWED; simpl in *; congruence].
      {
        (* Case 1: internal step (assembly command) *)
        rename H7 into Hexec.
        destruct i;
          try solve [inv Hexec; split; reflexivity |
                     inv Hexec; eapply integ_exec_loadex; eauto |
                     inv Hexec; eapply integ_exec_storeex; eauto].
        destruct i; simpl in *;
        try solve [inv Hexec; split; reflexivity |
                   inv Hexec; eapply integ_exec_loadex; eauto |
                   inv Hexec; eapply integ_exec_storeex; eauto |
                   unfold goto_label in *; unfold_lift; subdestruct; 
                   inv Hexec; unfold_lift; simpl in *; rewrites; split; reflexivity |
                   destruct (INSTR_ALLOWED eq_refl); congruence].
      }
      {
        (* Case 2: primitive call *)
        destruct H6 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
        inv_layer Hl; inv Hsem; simpl in *.
        {
          (* dispatch *)
          inv H1.
          inv H8.
          decompose [and] H1; subst; clear H1.
          split; auto; transitivity labd0.
          eapply integ_trap_into_kernel; eauto.
          erewrite trap_into_kernel_usermode_cid in Hid; eauto.
          transitivity labd1.
          assert (Hhigh:= H); apply trap_into_kernel_inv1 in Hhigh; auto.
          destruct Hhigh as (Hhigh & Hcused).
          destruct Hcused as (Hcused & _).
          assert (Hpg': pg labd0 = true)
            by (unfold trap_into_kernel_spec in *; decompose [and] H;
                clear H10 H2; inv_spec; inv_somes; auto).
          eapply integ_sys_dispatch_c; eauto.
          
          exploit sys_dispatch_usermode; eauto.
          intros (Heq & _). rewrite Heq in Hid.
          eapply integ_proc_start_user; eauto.
        }
        {       
          (* pagefault handler *)
          inv H1.
          inv H9.
          decompose [and] H1; subst; clear H1.
          split; auto; transitivity labd0.
          eapply integ_trap_into_kernel; eauto.
          erewrite trap_into_kernel_usermode_cid in Hid; eauto.
          transitivity labd1.
          assert (Hhigh:= H); apply trap_into_kernel_inv1 in Hhigh; auto.
          destruct Hhigh as (Hhigh & Hcused).
          eapply integ_ptfault_resv; eauto.
          exploit ptfault_resv_usermode; eauto.
          intros (Heq & _). rewrite Heq in Hid.        
          eapply integ_proc_start_user; eauto.
        }
        {
          (* yield *)
          inv H1.
          split; auto; transitivity labd0.
          eapply integ_trap_into_kernel; eauto.
          erewrite trap_into_kernel_usermode_cid in Hid; eauto.
          eapply integ_thread_yield; eauto.
        }
        {
          (* proc_start_user *)
          inv H1.
          split; auto; eapply integ_proc_start_user; eauto.
        }
      }
    Qed.

    End INTEG_LEMMAS.

  End WITHIMPL.

End WITHMEM.