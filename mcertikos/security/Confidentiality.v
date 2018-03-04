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

(* This file proves the confidentiality lemma over the TSysCall semantics, saying that
   if observably equivalent and active states s1 and s2 both take a step to s1' and s2',
   respectively, then s1' and s2' are also observably equivalent.
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
    Variable id_prop: id > high_id.

    Instance user_observer : Observer _ := user_observer id id_prop.
    Notation obs_eq := (my_obs_eq id).

    Instance user_obs_eq_equiv : Equivalence obs_eq.
    Proof.
      constructor.
      - intro x; rewrite my_obs_eq_convert; auto.
      - intros x y; rewrite 2 my_obs_eq_convert; auto.
      - intros x y z; rewrite 3 my_obs_eq_convert; congruence.
    Qed.

    (* For some reason I need to redefine these tactics here for
       them to work correctly. *)
    Ltac obs_eq_rewrite Hobs_eq :=
      try rewrite <- (obs_eq_HP _ _ _ Hobs_eq) in *;
      try rewrite quota_convert' in *;
      try rewrite <- (obs_eq_AC_quota _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_AC_nchildren _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_AC_used _ _ _ Hobs_eq) in *;
      try match goal with
            | [ H : id = cid ?d |- _ ] =>
              rewrite <- H in *;
              rewrite <- (proj1 (obs_eq_cid _ _ _ Hobs_eq)) in *; auto
          end;
      auto; try rewrite <- (obs_eq_kctxt _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_uctxt _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_OUT _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_ti _ _ _ Hobs_eq) in *; auto.

    Ltac obs_eq_rewrites Hobs_eq := repeat obs_eq_rewrite Hobs_eq.
    
    Ltac solve_obs_eq Hobs_eq := 
      destruct Hobs_eq; constructor; simpl; auto; zmap_solve; try congruence.

    Section CONF_LEMMAS.

      Hint Unfold uctx_arg1_spec uctx_arg2_spec uctx_arg3_spec 
           uctx_arg4_spec uctx_arg5_spec uctx_arg6_spec uctx_set_retval1_spec
           uctx_set_retval2_spec uctx_set_retval3_spec uctx_set_retval4_spec
           uctx_set_retval5_spec uctx_set_errno_spec 
           trap_proc_create_spec proc_create_spec 
           trap_get_quota_spec get_curid_spec container_get_quota_spec container_get_usage_spec
           thread_yield_spec : specs.

      Section CONF_UCTX.
        
        (* Confidentiality for system call arguments and return values *)

        Lemma conf_uctx_set_errno :
          forall d1 d2 d1' d2' n,
            uctx_set_errno_spec n d1 = Some d1' ->
            uctx_set_errno_spec n d2 = Some d2' ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros d1 d2 d1' d2' n Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; solve_obs_eq Hobs_eq.
        Qed.

        Lemma conf_uctx_arg1 :
          forall d1 d2 r1 r2,
            uctx_arg1_spec d1 = Some r1 ->
            uctx_arg1_spec d2 = Some r2 ->
            id = cid d1 -> obs_eq d1 d2 -> r1 = r2.
        Proof.
          intros d1 d2 r1 r2 Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; auto.
        Qed.

        Lemma conf_uctx_arg2 :
          forall d1 d2 r1 r2,
            uctx_arg2_spec d1 = Some r1 ->
            uctx_arg2_spec d2 = Some r2 ->
            id = cid d1 -> obs_eq d1 d2 -> r1 = r2.
        Proof.
          intros d1 d2 r1 r2 Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; auto.
        Qed.

        Lemma conf_uctx_arg3 :
          forall d1 d2 r1 r2,
            uctx_arg3_spec d1 = Some r1 ->
            uctx_arg3_spec d2 = Some r2 ->
            id = cid d1 -> obs_eq d1 d2 -> r1 = r2.
        Proof.
          intros d1 d2 r1 r2 Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; auto.
        Qed.

        Lemma conf_uctx_arg4 :
          forall d1 d2 r1 r2,
            uctx_arg4_spec d1 = Some r1 ->
            uctx_arg4_spec d2 = Some r2 ->
            id = cid d1 -> obs_eq d1 d2 -> r1 = r2.
        Proof.
          intros d1 d2 r1 r2 Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; auto.
        Qed.

        Lemma conf_uctx_arg5 :
          forall d1 d2 r1 r2,
            uctx_arg5_spec d1 = Some r1 ->
            uctx_arg5_spec d2 = Some r2 ->
            id = cid d1 -> obs_eq d1 d2 -> r1 = r2.
        Proof.
          intros d1 d2 r1 r2 Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; auto.
        Qed.

        Lemma conf_uctx_set_retval1 :
          forall d1 d2 d1' d2' n,
            uctx_set_retval1_spec n d1 = Some d1' ->
            uctx_set_retval1_spec n d2 = Some d2' ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros d1 d2 d1' d2' n Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; solve_obs_eq Hobs_eq.
        Qed.

        Lemma conf_uctx_set_retval2 :
          forall d1 d2 d1' d2' n,
            uctx_set_retval2_spec n d1 = Some d1' ->
            uctx_set_retval2_spec n d2 = Some d2' ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros d1 d2 d1' d2' n Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; solve_obs_eq Hobs_eq.
        Qed.

        Lemma conf_uctx_set_retval3 :
          forall d1 d2 d1' d2' n,
            uctx_set_retval3_spec n d1 = Some d1' ->
            uctx_set_retval3_spec n d2 = Some d2' ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros d1 d2 d1' d2' n Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; solve_obs_eq Hobs_eq.
        Qed.

        Lemma conf_uctx_set_retval4 :
          forall d1 d2 d1' d2' n,
            uctx_set_retval4_spec n d1 = Some d1' ->
            uctx_set_retval4_spec n d2 = Some d2' ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros d1 d2 d1' d2' n Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; solve_obs_eq Hobs_eq.
        Qed.

        Lemma conf_uctx_set_retval5 :
          forall d1 d2 d1' d2' n,
            uctx_set_retval5_spec n d1 = Some d1' ->
            uctx_set_retval5_spec n d2 = Some d2' ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros d1 d2 d1' d2' n Hspec1 Hspec2 Hid Hobs_eq.
          autounfold with specs in *.
          obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; solve_obs_eq Hobs_eq.
        Qed.

      End CONF_UCTX.

    Section CONF_ACCESSORS.

      (* Confidentiality for load and store primitives *)

      Lemma PDEValid_usr :
        forall id i d pti pte,
          high_level_invariant d -> ikern d = false -> 0 <= id < num_id ->
          ZMap.get (PDX (Int.unsigned i)) (ZMap.get id (ptpool d)) = PDEValid pti pte ->
          adr_low <= Int.unsigned i < adr_high.
      Proof.
        intros id' i d pti pte Hinv Hkern Hid Hpdx.
        assert (Hrange:= Int.unsigned_range_2 i).
        assert (Hmax:= max_unsigned_val).
        destruct Hinv.
        destruct (valid_PMap (valid_kern Hkern) _ Hid) as [Hpmap _].
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

      Lemma conf_exec_loadex :
        forall (m m1' m2' : mem) (d1 d2 d1' d2': cdata RData) rs rs1' rs2' chunk a rd, 
          exec_loadex ge chunk (m, d1) a rs rd = Next rs1' (m1', d1') ->
          exec_loadex ge chunk (m, d2) a rs rd = Next rs2' (m2', d2') ->
          high_level_invariant d1 -> high_level_invariant d2 -> 
          ikern d1 = false -> ikern d2 = false -> ihost d1 = true -> ihost d2 = true ->
          id = cid d1 -> obs_eq d1 d2 -> (obs_eq d1' d2' /\ rs1' = rs2') /\ m1' = m2'.
      Proof.
        intros m m1' m2' d1 d2 d1' d2' rs rs1' rs2' chunk a rd
               Hstep1 Hstep2 Hinv1 Hinv2 Hkern1 Hkern2 Hhost1 Hhost2 Hid Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
        unfold exec_loadex, exec_loadex2 in *; subdestruct; simpl in *; try congruence.
        unfold HostAccess2.exec_host_load2, snd in *.
        elim_stuck_eqn' Hstep1 Hpdx1; elim_stuck_eqn' Hstep2 Hpdx2.
        rename pi into pti1, pi0 into pti2, pte into pte1, pte0 into pte2.
        assert (Hcases1: (exists v pm, ZMap.get (PTX (Int.unsigned i)) pte1 = PTEValid v pm) \/ 
                         ZMap.get (PTX (Int.unsigned i)) pte1 = PTEUnPresent)
          by (clear Hstep2; subdestruct; [left|left|right]; eauto).
        assert (Hcases2: (exists v pm, ZMap.get (PTX (Int.unsigned i)) pte2 = PTEValid v pm) \/ 
                         ZMap.get (PTX (Int.unsigned i)) pte2 = PTEUnPresent)
          by (clear Hstep1; subdestruct; [left|left|right]; eauto).
        assert (Husr: adr_low <= Int.unsigned i < adr_high).
        {             
          eapply PDEValid_usr; eauto.
          destruct Hinv2; rewrite valid_init_PT_cid; auto.
        }
        (* These hypotheses make omega really slow for some reason... *)
        clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
        destruct Hcases1 as [[pi1 [pm1 Hvalid1]]|Hunp1].
        {
          assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte1 with
                        | PTEValid v PTP =>
                          FlatLoadStoreSem.exec_flatmem_load chunk 
                            (m, d1) (PTADDR v (Int.unsigned i)) rs rd
                        | PTEValid v PTU =>
                          FlatLoadStoreSem.exec_flatmem_load chunk 
                            (m, d1) (PTADDR v (Int.unsigned i)) rs rd
                        | PTEValid v (PTK _) => Stuck
                        | PTEUnPresent => PageFault.exec_pagefault ge (m, d1) i rs
                        | PTEUndef => Stuck
                      end = FlatLoadStoreSem.exec_flatmem_load chunk 
                              (m, d1) (PTADDR pi1 (Int.unsigned i)) rs rd)
            by (clear Hstep2; destruct pm1; rewrite Hvalid1 in Hstep1; 
                subdestruct; rewrite Hvalid1; auto).
          rewrite Hm in Hstep1; clear Hm.          
          destruct Hcases2 as [[pi2 [pm2 Hvalid2]]|Hunp2].
          {
            assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte2 with
                          | PTEValid v PTP =>
                            FlatLoadStoreSem.exec_flatmem_load chunk 
                              (m, d2) (PTADDR v (Int.unsigned i)) rs rd
                          | PTEValid v PTU =>
                            FlatLoadStoreSem.exec_flatmem_load chunk 
                              (m, d2) (PTADDR v (Int.unsigned i)) rs rd
                          | PTEValid v (PTK _) => Stuck
                          | PTEUnPresent => PageFault.exec_pagefault ge (m, d2) i rs
                          | PTEUndef => Stuck
                        end = FlatLoadStoreSem.exec_flatmem_load chunk 
                                (m, d2) (PTADDR pi2 (Int.unsigned i)) rs rd)
              by (clear Hstep1; destruct pm2; rewrite Hvalid2 in Hstep2; 
                  subdestruct; rewrite Hvalid2; auto).
            rewrite Hm in Hstep2; clear Hm.
            unfold FlatLoadStoreSem.exec_flatmem_load in *; subdestruct; inv Hstep1; inv Hstep2.
            clear Hdestruct6.
            replace (FlatMem.load chunk (HP d1') (PTADDR pi1 (Int.unsigned i))) 
               with (FlatMem.load chunk (HP d2') (PTADDR pi2 (Int.unsigned i))); auto.
            eapply FlatMem.load_rep'; [|eauto|eauto].
            intros z Hchunk.
            assert (Hmax:= max_unsigned_val).
            assert (Hch:= size_chunk_range chunk).
            assert (Hmath: forall p, PTADDR p (Int.unsigned i) + z = PTADDR p (Int.unsigned i + z)).
            {
              unfold PTADDR; intro p.
              rewrite <- Zplus_assoc; rewrite <- Zplus_mod_idemp_l.
              rewrite (Zmod_small (Int.unsigned i mod PgSize + z)); auto.
              assert (Hlt: 0 < PgSize) by omega.
              assert (Hpos := Z.mod_pos_bound (Int.unsigned i) _ Hlt); omega.
            }
            assert (Hiz: (Int.unsigned i + z) / PgSize = Int.unsigned i / PgSize).
            {
              apply Zdiv_unique with (b:= Int.unsigned i mod PgSize + z).
              rewrite Z.mod_eq; omega.
              assert (Hrange:= Z.mod_pos_bound (Int.unsigned i) PgSize); omega.
            }
            assert (Hzpdx: PDX (Int.unsigned i + z) = PDX (Int.unsigned i))
              by (unfold PDX; rewrite <- 2 Zdiv_Zdiv; try omega; f_equal; auto).
            assert (Hzptx: PTX (Int.unsigned i + z) = PTX (Int.unsigned i))
              by (unfold PTX; rewrite Hiz; auto).
            rewrite 2 Hmath.
            unfold vread in obs_eq_HP; specialize (obs_eq_HP (Int.unsigned i + z)).
            repeat rewrite Hzpdx, Hzptx in obs_eq_HP.
            assert (adr_low <= Int.unsigned i + z < adr_high).
            {
              assert (Hizeq: Int.unsigned i + z = Int.unsigned (Int.add i (Int.repr z))).
              rewrite Int.add_unsigned.
              repeat rewrite Int.unsigned_repr; try omega.
              destruct Hinv1; rewrite Hizeq; eapply PDEValid_usr; eauto.
              rewrite <- Hizeq.
              replace (PDX (Int.unsigned i + z)) with (PDX (Int.unsigned i)).
              destruct Hinv2; rewrite (proj1 obs_eq_cid); auto.
              rewrite <- valid_init_PT_cid0; eauto.
            }
            rewrite 2 zle_lt_true in obs_eq_HP; auto.
            destruct Hinv1; destruct Hinv2.
            rewrite valid_init_PT_cid in Hpdx1; rewrite valid_init_PT_cid0 in Hpdx2; auto.
            rewrite <- (proj1 obs_eq_cid) in Hpdx2; auto.
            unfold PMap in *; rewrite Hpdx1, Hpdx2, Hvalid1, Hvalid2 in obs_eq_HP; inv_somes; auto.
          }
          {
            unfold vread in obs_eq_HP; specialize (obs_eq_HP (Int.unsigned i)).
            rewrite 2 zle_lt_true in obs_eq_HP; auto.
            destruct Hinv1; destruct Hinv2.
            rewrite valid_init_PT_cid in Hpdx1; rewrite valid_init_PT_cid0 in Hpdx2; auto.
            rewrite <- (proj1 obs_eq_cid) in Hpdx2; auto.
            rewrites. discriminate.
          }
        }
        {
          destruct Hcases2 as [[pi2 [pm2 Hvalid2]]|Hunp2].
          {            
            unfold vread in obs_eq_HP; specialize (obs_eq_HP (Int.unsigned i)).
            rewrite 2 zle_lt_true in obs_eq_HP; auto.
            destruct Hinv1; destruct Hinv2.
            rewrite valid_init_PT_cid in Hpdx1; rewrite valid_init_PT_cid0 in Hpdx2; auto.
            rewrite <- (proj1 obs_eq_cid) in Hpdx2; auto.
            rewrites. discriminate.
          }
          {
            unfold PageFault.exec_pagefault in *; subdestruct; inv Hstep1; inv Hstep2.
            unfold trapinfo_set; repeat (apply conj; auto).
            constructor; simpl; auto; try congruence.
            destruct Hobs_eq; assumption.
          }
        }
      Qed.

      Lemma at_most_one_occ_single_mapped :
        forall l id pdi1 pdi2 pti1 pti2,
          In (LATO id pdi1 pti1) l -> In (LATO id pdi2 pti2) l ->
          at_most_one_occ l id -> pdi1 = pdi2 /\ pti1 = pti2.
      Proof.
        induction l; simpl; intros.
        inv H0.
        destruct H0; subst.
        - destruct H; subst.
          inv H; auto.
          subdestruct.
          apply zero_occ_notin in H; auto; inv H.
          contradiction n; auto.
        - destruct H; subst.
          subdestruct.
          apply zero_occ_notin in H0; auto; inv H0.
          contradiction n; auto.
          subdestruct; subst; eauto.
          apply zero_occ_notin in H; auto; inv H.
      Qed.

      Lemma count_occ_single_mapped :
        forall l id d p b t pdi1 pdi2 pti1 pti2,
          high_level_invariant d -> pg d = true -> 0 <= p < nps d ->
          ZMap.get p (LAT d) = LATValid b t l ->
          count_occ LATOwner_dec l (LATO id pdi1 pti1) = 1%nat ->
          count_occ LATOwner_dec l (LATO id pdi2 pti2) = 1%nat ->
          single_mapped (LAT d) (nps d) id -> pdi1 = pdi2 /\ pti1 = pti2.
      Proof.
        intros until pti2; intros Hinv Hpg Hp Hget Hc1 Hc2 Hsm.
        assert (Hgt1: (count_occ LATOwner_dec l (LATO id0 pdi1 pti1) > O)%nat) by omega.
        assert (Hgt2: (count_occ LATOwner_dec l (LATO id0 pdi2 pti2) > O)%nat) by omega.
        apply count_occ_In in Hgt1; apply count_occ_In in Hgt2.
        eapply at_most_one_occ_single_mapped; eauto.
        eapply Hsm; eauto.
        assert (Hcases: p < kern_low \/ kern_low <= p < nps d) by omega.
        destruct Hcases; auto; destruct Hinv.
        assert (ZMap.get p (LAT d) = LATValid false ATKern nil) by (apply valid_AT_kern; auto; omega).        
        rewrites; inv Hgt1.
      Qed.

      Lemma conf_exec_storeex :
        forall (m m1' m2' : mem) (d1 d2 d1' d2': cdata RData) rs rs1' rs2' chunk a rs0 l, 
          exec_storeex ge chunk (m, d1) a rs rs0 l = Next rs1' (m1', d1') ->
          exec_storeex ge chunk (m, d2) a rs rs0 l = Next rs2' (m2', d2') ->
          high_level_invariant d1 -> high_level_invariant d2 -> 
          ikern d1 = false -> ikern d2 = false -> ihost d1 = true -> ihost d2 = true ->
          single_mapped (LAT d1) (nps d1) (cid d1) -> single_mapped (LAT d2) (nps d2) (cid d2) ->
          id = cid d1 -> obs_eq d1 d2 -> (obs_eq d1' d2' /\ rs1' = rs2') /\ m1' = m2'.
      Proof.
        intros m m1' m2' d1 d2 d1' d2' rs rs1' rs2' chunk a rs0 l
               Hstep1 Hstep2 Hinv1 Hinv2 Hkern1 Hkern2 Hhost1 Hhost2 Hmap1 Hmap2 Hid Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
        unfold exec_storeex, exec_storeex2 in *; subdestruct; simpl in *; try congruence.
        unfold HostAccess2.exec_host_store2, snd in *.
        elim_stuck_eqn' Hstep1 Hpdx1; elim_stuck_eqn' Hstep2 Hpdx2.
        rename pi into pti1, pi0 into pti2, pte into pte1, pte0 into pte2.
        assert (Hcases1: (exists v pm, ZMap.get (PTX (Int.unsigned i)) pte1 = PTEValid v pm) \/ 
                         ZMap.get (PTX (Int.unsigned i)) pte1 = PTEUnPresent)
          by (clear Hstep2; subdestruct; [left|left|right]; eauto).
        assert (Hcases2: (exists v pm, ZMap.get (PTX (Int.unsigned i)) pte2 = PTEValid v pm) \/ 
                         ZMap.get (PTX (Int.unsigned i)) pte2 = PTEUnPresent)
          by (clear Hstep1; subdestruct; [left|left|right]; eauto).
        assert (Husr: adr_low <= Int.unsigned i < adr_high).
        {             
          eapply PDEValid_usr; eauto.
          destruct Hinv2; rewrite valid_init_PT_cid; auto.
        }
        destruct Hcases1 as [[pi1 [pm1 Hvalid1]]|Hunp1].
        {
          assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte1 with
                        | PTEValid v PTP =>
                          FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                            (m, d1) (PTADDR v (Int.unsigned i)) rs rs0 l
                        | PTEValid v PTU =>
                          FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                            (m, d1) (PTADDR v (Int.unsigned i)) rs rs0 l
                        | PTEValid v (PTK _) => Stuck
                        | PTEUnPresent => PageFault.exec_pagefault ge (m, d1) i rs
                        | PTEUndef => Stuck
                      end = FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                              (m, d1) (PTADDR pi1 (Int.unsigned i)) rs rs0 l)
            by (clear Hstep2; destruct pm1; rewrite Hvalid1 in Hstep1; 
                subdestruct; rewrite Hvalid1; auto).
          rewrite Hm in Hstep1; clear Hm.          
          destruct Hcases2 as [[pi2 [pm2 Hvalid2]]|Hunp2].
          {
            assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte2 with
                          | PTEValid v PTP =>
                            FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                              (m, d2) (PTADDR v (Int.unsigned i)) rs rs0 l
                          | PTEValid v PTU =>
                            FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                              (m, d2) (PTADDR v (Int.unsigned i)) rs rs0 l
                          | PTEValid v (PTK _) => Stuck
                          | PTEUnPresent => PageFault.exec_pagefault ge (m, d2) i rs
                          | PTEUndef => Stuck
                        end = FlatLoadStoreSem.exec_flatmem_store(flatmem_store:= flatmem_store) chunk 
                                (m, d2) (PTADDR pi2 (Int.unsigned i)) rs rs0 l)
              by (clear Hstep1; destruct pm2; rewrite Hvalid2 in Hstep2; 
                  subdestruct; rewrite Hvalid2; auto).
            rewrite Hm in Hstep2; clear Hm.
            unfold FlatLoadStoreSem.exec_flatmem_store, snd in *; subdestruct; inv Hstep1; inv Hstep2.            
            clear Hdestruct6.
            (* These hypotheses make omega really slow for some reason... *)
            clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
            unfold flatmem_store in *; subdestruct; inv_somes.
            repeat (split; simpl; auto); try congruence.
            intro vadr; unfold vread; simpl.
            unfold vread in obs_eq_HP; specialize (obs_eq_HP vadr).
            subdestruct; auto; f_equal.
            rename v into pi1', v0 into pi2'.
            assert (Hcases1: PTADDR pi1 (Int.unsigned i) <= PTADDR pi1' vadr < PTADDR pi1 (Int.unsigned i) + 
                                  Z.of_nat (length (encode_val chunk (rs rs0))) \/ 
                             (PTADDR pi1' vadr < PTADDR pi1 (Int.unsigned i) \/
                              PTADDR pi1' vadr >= PTADDR pi1 (Int.unsigned i) + 
                                  Z.of_nat (length (encode_val chunk (rs rs0))))) by omega.
            assert (Hcases2: PTADDR pi2 (Int.unsigned i) <= PTADDR pi2' vadr < PTADDR pi2 (Int.unsigned i) + 
                                  Z.of_nat (length (encode_val chunk (rs rs0))) \/ 
                             (PTADDR pi2' vadr < PTADDR pi2 (Int.unsigned i) \/
                              PTADDR pi2' vadr >= PTADDR pi2 (Int.unsigned i) + 
                                  Z.of_nat (length (encode_val chunk (rs rs0))))) by omega.
            unfold FlatMem.store; destruct Hcases1 as [Hcase1|Hcase1].
            {
              rewrite (get_setN_charact _ _ _ _ Hcase1).
              assert (pi1' = pi1).
              {
                assert (Hpi: PTADDR pi1 (Int.unsigned i) / PgSize <= PTADDR pi1' vadr / PgSize <=
                             (PTADDR pi1 (Int.unsigned i) + Z.of_nat (length (encode_val chunk (rs rs0))) - 1) / PgSize)
                  by (split; apply Z.div_le_mono; omega).                
                unfold PTADDR in Hpi.
                assert (Hmod: forall x, 0 <= x mod PgSize < PgSize) by (intros; apply Zmod_pos_bound; omega).
                rewrite (Zdiv_unique _ _ pi1 (Int.unsigned i mod PgSize)) in Hpi; auto.
                rewrite (Zdiv_unique _ _ pi1' (vadr mod PgSize)) in Hpi; auto.
                rewrite (Zdiv_unique _ _ pi1 (Int.unsigned i mod PgSize +
                                              Z.of_nat (length (encode_val chunk (rs rs0))) - 1)) in Hpi; try omega.
                rewrite encode_val_length.
                unfold size_chunk_nat; specialize (Hmod (Int.unsigned i)).
                assert (Hch:= size_chunk_range' chunk); rewrite nat_of_Z_eq; omega.
              }
              subst; destruct Hcases2 as [Hcase2|Hcase2].
              {
                rewrite (get_setN_charact _ _ _ _ Hcase2).
                assert (pi2' = pi2).
                {
                  assert (Hpi: PTADDR pi2 (Int.unsigned i) / PgSize <= PTADDR pi2' vadr / PgSize <=
                               (PTADDR pi2 (Int.unsigned i) + Z.of_nat (length (encode_val chunk (rs rs0))) - 1) / PgSize)
                    by (split; apply Z.div_le_mono; omega).                
                  unfold PTADDR in Hpi.
                  assert (Hmod: forall x, 0 <= x mod PgSize < PgSize) by (intros; apply Zmod_pos_bound; omega).
                  rewrite (Zdiv_unique _ _ pi2 (Int.unsigned i mod PgSize)) in Hpi; auto.
                  rewrite (Zdiv_unique _ _ pi2' (vadr mod PgSize)) in Hpi; auto.
                  rewrite (Zdiv_unique _ _ pi2 (Int.unsigned i mod PgSize +
                                                Z.of_nat (length (encode_val chunk (rs rs0))) - 1)) in Hpi; try omega.
                  rewrite encode_val_length.
                  unfold size_chunk_nat; specialize (Hmod (Int.unsigned i)).
                  assert (Hch:= size_chunk_range' chunk); rewrite nat_of_Z_eq; omega.
                }
                subst; unfold PTADDR.
                apply get_setN_charact_pi'; auto.
                f_equal; omega.
              }
              {
                assert (Hv_range: 0 <= vadr < adr_max) by omega.
                assert (Hi_range: 0 <= Int.unsigned i < adr_max) by omega.
                assert (Hinv1':= Hinv1); destruct Hinv1'.
                rewrite valid_init_PT_cid in *; auto.
                destruct (valid_pmap_domain _ valid_curid _ Hv_range _ _ Hdestruct9 _ _ Hdestruct11)
                  as [_ [_ [l1 [Hl1 Hlin1]]]].
                destruct (valid_pmap_domain _ valid_curid _ Hi_range _ _ Hpdx1 _ _ Hvalid1)
                  as [_ [_ [l2 [Hl2 Hlin2]]]]; rewrites.
                assert (Hpi: 0 <= pi1 < nps d1) by (edestruct valid_pmap_domain; eauto; omega).
                destruct (count_occ_single_mapped _ _ _ _ _ _ _ _ _ _ Hinv1 Hdestruct3 Hpi Hl2 Hlin1 Hlin2 Hmap1) 
                  as [Hpdx_eq Hptx_eq].
                rewrite Hpdx_eq, Hptx_eq in *.
                destruct Hinv2.
                rewrite valid_init_PT_cid0 in *; rewrite <- (proj1 obs_eq_cid eq_refl) in *; auto.
                unfold PMap in *; rewrites; unfold PTADDR in *; destruct Hcase2; try omega.
              }
            }
            {
              destruct Hcases2 as [Hcase2|Hcase2].
              {
                assert (pi2' = pi2).
                {
                  assert (Hpi: PTADDR pi2 (Int.unsigned i) / PgSize <= PTADDR pi2' vadr / PgSize <=
                               (PTADDR pi2 (Int.unsigned i) + Z.of_nat (length (encode_val chunk (rs rs0))) - 1) / PgSize)
                    by (split; apply Z.div_le_mono; omega).                
                  unfold PTADDR in Hpi.
                  assert (Hmod: forall x, 0 <= x mod PgSize < PgSize) by (intros; apply Zmod_pos_bound; omega).
                  rewrite (Zdiv_unique _ _ pi2 (Int.unsigned i mod PgSize)) in Hpi; auto.
                  rewrite (Zdiv_unique _ _ pi2' (vadr mod PgSize)) in Hpi; auto.
                  rewrite (Zdiv_unique _ _ pi2 (Int.unsigned i mod PgSize +
                                                Z.of_nat (length (encode_val chunk (rs rs0))) - 1)) in Hpi; try omega.
                  rewrite encode_val_length.
                  unfold size_chunk_nat; specialize (Hmod (Int.unsigned i)).
                  assert (Hch:= size_chunk_range' chunk); rewrite nat_of_Z_eq; omega.
                }
                assert (Hv_range: 0 <= vadr < adr_max) by omega.
                assert (Hi_range: 0 <= Int.unsigned i < adr_max) by omega.
                subst; assert (Hinv2':= Hinv2); destruct Hinv2'.
                rewrite valid_init_PT_cid in *; rewrite <- (proj1 obs_eq_cid eq_refl) in *; auto.
                destruct (valid_pmap_domain _ valid_curid _ Hv_range _ _ Hdestruct12 _ _ Hdestruct13)
                  as [_ [_ [l1 [Hl1 Hlin1]]]].
                destruct (valid_pmap_domain _ valid_curid _ Hi_range _ _ Hpdx2 _ _ Hvalid2)
                  as [_ [_ [l2 [Hl2 Hlin2]]]]; rewrites.
                assert (Hpi: 0 <= pi2 < nps d2) by (edestruct valid_pmap_domain; eauto; omega).
                destruct (count_occ_single_mapped _ _ _ _ _ _ _ _ _ _ Hinv2 Hdestruct0 Hpi Hl2 Hlin1 Hlin2 Hmap2) 
                  as [Hpdx_eq Hptx_eq].
                rewrite Hpdx_eq, Hptx_eq in *.
                destruct Hinv1.
                rewrite valid_init_PT_cid0 in *; auto.
                unfold PMap in *; rewrites; unfold PTADDR in *; destruct Hcase1; omega.
              }
              {
                rewrite 2 FlatMem.setN_outside; auto; inv_rewrite.
              }
            }
            destruct Hobs_eq; assumption.
          }
          {            
            unfold vread in obs_eq_HP; specialize (obs_eq_HP (Int.unsigned i)).
            rewrite 2 zle_lt_true in obs_eq_HP; auto.
            destruct Hinv1; destruct Hinv2.
            rewrite valid_init_PT_cid in Hpdx1; rewrite valid_init_PT_cid0 in Hpdx2; auto.
            rewrite <- (proj1 obs_eq_cid) in Hpdx2; auto.
            rewrites. discriminate.
          }
        }
        {
          destruct Hcases2 as [[pi2 [pm2 Hvalid2]]|Hunp2].
          {
            unfold vread in obs_eq_HP; specialize (obs_eq_HP (Int.unsigned i)).
            rewrite 2 zle_lt_true in obs_eq_HP; auto.
            destruct Hinv1; destruct Hinv2.
            rewrite valid_init_PT_cid in Hpdx1; rewrite valid_init_PT_cid0 in Hpdx2; auto.
            rewrite <- (proj1 obs_eq_cid) in Hpdx2; auto.
            rewrites. discriminate.
          }
          {
            unfold PageFault.exec_pagefault in *; subdestruct; inv Hstep1; inv Hstep2.
            unfold trapinfo_set; repeat (apply conj; auto).
            constructor; simpl; auto; congruence.
          }
        }
      Qed.

    End CONF_ACCESSORS.

    Ltac obs_eq_destruct Hobs_eq Hspec1 Hspec2 Hid :=
    match type of Hspec1 with
    | context [match uctx_arg1_spec ?d1 with _ => _ end] => 
      match type of Hspec2 with
      | context [match uctx_arg1_spec ?d2 with _ => _ end] =>
        let H1 := fresh in let H2 := fresh in
        elim_none_eqn' Hspec1 H1; elim_none_eqn' Hspec2 H2;
        rewrite (conf_uctx_arg1 _ _ _ _ H1 H2 Hid Hobs_eq) in Hspec1; clear H1 H2
      end
    | context [match uctx_arg2_spec ?d1 with _ => _ end] => 
      match type of Hspec2 with
      | context [match uctx_arg2_spec ?d2 with _ => _ end] =>
        let H1 := fresh in let H2 := fresh in
        elim_none_eqn' Hspec1 H1; elim_none_eqn' Hspec2 H2;
        rewrite (conf_uctx_arg2 _ _ _ _ H1 H2 Hid Hobs_eq) in Hspec1; clear H1 H2
      end
    | context [match uctx_arg3_spec ?d1 with _ => _ end] => 
      match type of Hspec2 with
      | context [match uctx_arg3_spec ?d2 with _ => _ end] =>
        let H1 := fresh in let H2 := fresh in
        elim_none_eqn' Hspec1 H1; elim_none_eqn' Hspec2 H2;
        rewrite (conf_uctx_arg3 _ _ _ _ H1 H2 Hid Hobs_eq) in Hspec1; clear H1 H2
      end
    | context [match ?a with _ => _ end] => 
      match type of Hspec2 with
      | context [match a with _ => _ end] => let H := fresh "Hdestruct" in elim_none_eqn' Hspec1 H
      end
    end.
    
    Section CONF_PRIMS.
      
      (* Confidentiality for process spawning *)

      Lemma conf_proc_create :
        forall d1 d2 d1' d2' b1 b2 b3 ofs q r1 r2,
          proc_create_spec d1 b1 b2 b3 ofs q = Some (d1', r1) ->
          proc_create_spec d2 b1 b2 b3 ofs q = Some (d2', r2) ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2' /\ r1 = r2.
      Proof.
        intros d1 d2 d1' d2' b1 b2 b3 ofs q r1 r2 Hspec1 Hspec2 Hid Hobs_eq.
        unfold proc_create_spec in *.
        obs_eq_rewrites Hobs_eq; subdestruct; inv_somes; split; auto.
        unfold update_cusage, update_cchildren; solve_obs_eq Hobs_eq; simpl; subst.
        omega.
      Qed.

      Lemma conf_trap_proc_create :
        forall d1 d2 d1' d2' s m,
          trap_proc_create_spec s m d1 = Some d1' ->
          trap_proc_create_spec s m d2 = Some d2' ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
      Proof.
        intros d1 d2 d1' d2' s' m Hspec1 Hspec2 Hid Hobs_eq.
        unfold trap_proc_create_spec in *.
        obs_eq_rewrites Hobs_eq.
        repeat obs_eq_destruct Hobs_eq Hspec1 Hspec2 Hid; try solve [eapply conf_uctx_set_errno; eauto].
        generalize Hid; clear Hid; subdestruct; inv_somes; intros.
        edestruct conf_proc_create; [eapply Hdestruct16 | eapply Hdestruct13 | | |]; auto.
        assert (id = cid r1) by (unfold proc_create_spec in *; subdestruct; inv_somes; auto).
        assert (id = cid r2) by (unfold uctx_set_retval1_spec in *; subdestruct; inv_somes; auto).
        clear Hid; eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_retval1; eauto.
        subst z4; trivial.
      Qed.

      (* Confidentiality for getting quota *)

      Lemma conf_trap_get_quota :
        forall d1 d2 d1' d2',
          trap_get_quota_spec d1 = Some d1' ->
          trap_get_quota_spec d2 = Some d2' ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
      Proof.
        intros d1 d2 d1' d2' Hspec1 Hspec2 Hid Hobs_eq.
        repeat autounfold with specs in *.
        subdestruct; inv_somes; obs_eq_rewrites Hobs_eq; solve_obs_eq Hobs_eq.
        intuition.
      Qed.

      (* Confidentiality for setting up shared memory. The proof is just a 
         contradiction since shared memory is only allowed for trusted processes,
         but id = cid d1 and id is assumed to be an untrusted process. *)

      Lemma conf_trap_offer_shared_mem :
        forall d1 d2 d1' d2',
          trap_offer_shared_mem_spec d1 = Some d1' ->
          trap_offer_shared_mem_spec d2 = Some d2' ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
      Proof.
        intros d1 d2 d1' d2' Hspec1 Hspec2 Hid Hobs_eq.
        unfold_specs.
        repeat obs_eq_destruct Hobs_eq Hspec1 Hspec2 Hid. 
        rewrite zeq_false in *.
        try solve [eapply conf_uctx_set_errno; eauto].
        rewrite <- Hid. omega.
        inversion Hobs_eq. eapply obs_eq_cid in Hid.
        rewrite <- Hid. omega.
        rewrite <- Hid. omega.
      Qed.

      (* Confidentiality for printing output *)

      Lemma conf_print :
        forall d1 d2 d1' d2',
          print_spec d1 = Some d1' ->
          print_spec d2 = Some d2' ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
      Proof.
        intros d1 d2 d1' d2' Hspec1 Hspec2 Hid Hobs_eq.
        unfold_specs.
        repeat obs_eq_destruct Hobs_eq Hspec1 Hspec2 Hid. 
        eapply conf_uctx_set_errno; eauto.        
        inversion Hobs_eq; solve_obs_eq Hobs_eq.
        rewrite <- Hid.
        eapply obs_eq_cid in Hid.
        rewrite <- Hid.
        unfold DeviceOutput_update.
        repeat rewrite ZMap.gss.
        rewrite obs_eq_OUT. trivial.
      Qed.

      (* Confidentiality for the system call dispatcher *)

      Lemma conf_sys_dispatch_c :
        forall d1 d2 d1' d2' s m,
          sys_dispatch_c_spec s m d1 = Some d1' ->
          sys_dispatch_c_spec s m d2 = Some d2' ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
      Proof.
        intros d1 d2 d1' d2' s' m Hspec1 Hspec2 Hid Hobs_eq.
        unfold_specs.
        repeat obs_eq_destruct Hobs_eq Hspec1 Hspec2 Hid; try solve [eapply conf_uctx_set_errno; eauto].
        eapply conf_trap_proc_create; eauto.
        eapply conf_trap_get_quota; eauto.
        eapply conf_trap_offer_shared_mem; eauto.
        eapply conf_print; eauto.
      Qed.

      Section CONF_PTFAULT.

        (* Confidentiality for page fault handling *)

        Lemma conf_alloc :
          forall r1 r2 d1 d2 d1' d2',
            high_level_invariant d1 -> high_level_invariant d2 ->
            alloc_spec id d1 = Some (d1', r1) ->
            alloc_spec id d2 = Some (d2', r2) ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2' /\ (r1 = 0 <-> r2 = 0).
        Proof.
          intros r1 r2 d1 d2 d1' d2' Hinv1 Hinv2 Hspec1 Hspec2 Hid Hobs_eq.
          unfold_specs; repeat obs_eq_rewrites Hobs_eq.
          subdestruct; inv_somes; try rewrite <- Hid.
          - split; [|omega].
            solve_obs_eq Hobs_eq; [|omega].
            intro vadr; specialize (obs_eq_perm vadr); unfold vread_perm in *.
            subdestruct; auto.
            inv obs_eq_perm; zmap_solve; try congruence; subst.
            + destruct Hinv1, Hinv2.
              edestruct (valid_pmap_domain0 (cid d1) valid_curid vadr) as [_ [? _]]; eauto; try omega.
              congruence.
            + destruct Hinv1, Hinv2.
              edestruct (valid_pmap_domain (cid d1) valid_curid vadr) as [_ [? _]]; eauto; try omega.
              congruence.
          - split; auto; reflexivity.
        Qed.

        Lemma conf_ptAllocPDE0 :
          forall v r1 r2 d1 d2 d1' d2',
            high_level_invariant d1 -> high_level_invariant d2 ->
            ptAllocPDE0_spec id v d1 = Some (d1', r1) ->
            ptAllocPDE0_spec id v d2 = Some (d2', r2) ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2' /\ (r1 = 0 <-> r2 = 0).
        Proof.
          intros v r1 r2 d1 d2 d1' d2' Hinv1 Hinv2 Hspec1 Hspec2 Hid Hobs_eq.
          unfold_specs; repeat obs_eq_rewrites Hobs_eq.
          subdestruct; inv_somes.
          - split; [|omega].            
            destruct Hobs_eq; constructor; simpl; zmap_simpl; subst; [| |auto..];
              (* These hypotheses make omega really slow for some reason... *)
              clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
            + unfold vread; simpl; intro v'; zmap_simpl.
              destruct (zeq (PDX v') (PDX v)) as [Heq|Hneq]; zmap_simpl.
              * destruct (zle_lt adr_low v' adr_high); [|auto].
                rewrite CalRealInitPTE.real_init_PTE_unp; auto.
                unfold PTX; apply Z.mod_bound_pos; try omega.
                apply Z.div_pos; omega.
              * unfold PMap in *; unfold vread in obs_eq_HP.
                specialize (obs_eq_HP v').
                destruct (zle_lt adr_low v' adr_high) eqn: Hr; [| trivial].
                destruct (ZMap.get (PDX v') (ZMap.get (cid d1) (ptpool d1))) eqn: Hp1; unfold PMap in Hp1; rewrite Hp1;
                destruct (ZMap.get (PDX v') (ZMap.get (cid d1) (ptpool d2))) eqn: Hp2; unfold PMap in Hp2; rewrite Hp2; 
                try (inversion obs_eq_HP; fail); try apply (eq_refl None);
                try (destruct (ZMap.get (PTX v') pte));
                try (destruct (ZMap.get (PTX v') pte0));
                inv obs_eq_HP; try apply (eq_refl None).

                destruct Hinv1, Hinv2.
                rewrite <- valid_dirty, <- valid_dirty0; auto. rewrite H0. trivial.
                intro Hcon.
                assert (Hr1: exists n, ZMap.get r2 (LAT d2) = LATValid true ATNorm n)
                  by (apply valid_pperm_ppage0; try omega; intro; rewrites).
                destruct Hr1; decompose [and] a; rewrites.
                intro Hcon.
                assert (Hr1: exists n, ZMap.get r1 (LAT d1) = LATValid true ATNorm n)
                  by (apply valid_pperm_ppage; try omega; intro; rewrites).
                destruct Hr1; decompose [and] a0; rewrites.
            + intro v'; specialize (obs_eq_perm v').
              unfold vread_perm in *; simpl; zmap_solve.
              * destruct (zle_lt adr_low v' adr_high) eqn: Hr; [| trivial].
                rewrite CalRealInitPTE.real_init_PTE_unp; auto.
                unfold PTX; apply Z.mod_bound_pos; try omega.
                apply Z.div_pos; omega.
              * destruct (zle_lt adr_low v' adr_high) eqn: Hr; [| trivial].
                subdestruct; auto; subst.
                inv obs_eq_perm; zmap_solve.
                destruct Hinv1, Hinv2.
                edestruct (valid_pmap_domain (cid d1) valid_curid v') as [_ [_ [? [? _]]]]; eauto; try omega.
                destruct a0 as [? [? ?]]; congruence.
                destruct Hinv1, Hinv2.
                edestruct (valid_pmap_domain0 (cid d1) valid_curid v') as [_ [_ [? [? _]]]]; eauto; try omega.
                destruct a as [? [? ?]]; congruence.
                congruence.
              * destruct (zle_lt adr_low v' adr_high) eqn: Hr; [| trivial].
                subdestruct; auto; subst.
                inv obs_eq_perm; zmap_solve.
                destruct Hinv1, Hinv2.
                edestruct (valid_pmap_domain (cid d1) valid_curid v') as [_ [_ [? [? _]]]]; eauto; try omega.
                destruct a0 as [? [? ?]]; congruence.
                congruence.
            + simpl; omega.
          - split; auto; reflexivity.
        Qed.

        Lemma conf_ptInsertPTE0 :
          forall vadr padr1 padr2 pm d1 d2 d1' d2',
            (forall adr, ZMap.get adr (HP d1) = ZMap.get adr (FlatMem.free_page padr1 (HP d1))) ->
            (forall adr, ZMap.get adr (HP d2) = ZMap.get adr (FlatMem.free_page padr2 (HP d2))) ->
            ptInsertPTE0_spec id vadr padr1 pm d1 = Some d1' ->
            ptInsertPTE0_spec id vadr padr2 pm d2 = Some d2' ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros vadr padr1 padr2 pm d1 d2 d1' d2' Hfree1 Hfree2 Hspec1 Hspec2 Hid Hobs_eq.
          unfold_specs; repeat obs_eq_rewrites Hobs_eq.
          unfold PMap in *; subdestruct; inv_somes; solve_obs_eq Hobs_eq; subst;
            try solve [
              intro v; specialize (obs_eq_HP v);
              unfold vread in *; simpl;
              eqdestruct; zmap_solve;
               [rewrite Hfree1, Hfree2;
                rewrite <- (pagei_ptaddr padr1 v) at 2;
                rewrite <- (pagei_ptaddr padr2 v) at 2;
                rewrite 2 FlatMem.free_page_gss; auto |
                rewrite e0 in obs_eq_HP; unfold PMap in *;
                rewrite Hdestruct16, Hdestruct9 in obs_eq_HP; auto]];
            try solve [
              intro v; specialize (obs_eq_perm v);
              unfold vread_perm in *; simpl;
              eqdestruct; zmap_solve;
              rewrite e0 in obs_eq_perm;
              unfold PMap in *; rewrite Hdestruct16, Hdestruct9 in obs_eq_perm; congruence].
        Qed.

        Lemma ptAllocPDE0_free_page_inv :
          forall id v d d' r p,
            ptAllocPDE0_spec id v d = Some (d', r) ->
            (forall adr, ZMap.get adr (HP d) = ZMap.get adr (FlatMem.free_page p (HP d))) ->
            (forall adr, ZMap.get adr (HP d') = ZMap.get adr (FlatMem.free_page p (HP d'))).
        Proof.
          intros id' v d d' r p Hspec Hfree.
          inv_spec; inv_somes; simpl.
          - intro adr; destruct (zeq r (PageI adr)); subst.
            + rewrite FlatMem.free_page_gss.
              destruct (zeq p (PageI adr)); subst.
              rewrite FlatMem.free_page_gss; auto.
              rewrite FlatMem.free_page_gso; auto.
              rewrite FlatMem.free_page_gss; auto.
            + rewrite (FlatMem.free_page_gso _ _ _ n).
              rewrite Hfree.
              destruct (zeq p (PageI adr)); subst.
              rewrite 2 FlatMem.free_page_gss; auto.
              rewrite 2 (FlatMem.free_page_gso _ _ _ n0).
              rewrite (FlatMem.free_page_gso _ _ _ n); auto.
          - auto.
        Qed.

        Lemma conf_ptInsert0 :
          forall vadr padr1 padr2 pm d1 d2 d1' d2' r1 r2,
            (forall adr, ZMap.get adr (HP d1) = ZMap.get adr (FlatMem.free_page padr1 (HP d1))) ->
            (forall adr, ZMap.get adr (HP d2) = ZMap.get adr (FlatMem.free_page padr2 (HP d2))) ->
            high_level_invariant d1 -> high_level_invariant d2 ->
            ptInsert0_spec id vadr padr1 pm d1 = Some (d1',r1) ->
            ptInsert0_spec id vadr padr2 pm d2 = Some (d2',r2) ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros vadr padr1 padr2 pm d1 d2 d1' d2' r1 r2 Hfree1 Hfree2 
                 Hinv1 Hinv2 Hspec1 Hspec2 Hid Hobs_eq.
          unfold_specs; repeat obs_eq_rewrites Hobs_eq.
          assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
          (* These hypotheses make omega really slow for some reason... *)
          clear obs_eq_ikern obs_eq_ihost obs_eq_pg obs_eq_ipt.
          generalize Hid; clear Hid; specialize (obs_eq_perm vadr);
            unfold PMap in *; subdestruct; inv_somes;
            unfold vread_perm in obs_eq_perm; unfold PMap in *;
            intro Hid; rewrite Hid in obs_eq_perm; 
            try solve [rewrite Hid in *; unfold pt_Arg, pt_Arg' in *; subdestruct]. 
          - apply (conf_ptInsertPTE0 _ _ _ _ _ _ _ _ Hfree1 Hfree2 Hdestruct13 Hdestruct11 Hid Hobs_eq).
          - eapply conf_ptAllocPDE0; [| | eauto | eauto | |]; auto.
          - destruct (conf_ptAllocPDE0 _ _ _ _ _ _ _ Hinv1 Hinv2 
                                       Hdestruct15 Hdestruct11 Hid Hobs_eq); omega.
          - destruct (conf_ptAllocPDE0 _ _ _ _ _ _ _ Hinv1 Hinv2 
                                       Hdestruct16 Hdestruct11 Hid Hobs_eq); omega.
          - assert (Hobs_eq': obs_eq r3 r) by (eapply conf_ptAllocPDE0; [| | eauto | eauto | |]; auto).
            assert (Hcid: cid d1 = cid r3)
              by (clear Hdestruct11 Hdestruct14 Hdestruct19; repeat inv_spec; inv_somes; auto).
            rewrite Hcid in *; clear Hcid.
            apply (conf_ptInsertPTE0 _ _ _ _ _ _ _ _ 
                                     (ptAllocPDE0_free_page_inv _ _ _ _ _ _ Hdestruct16 Hfree1) 
                                     (ptAllocPDE0_free_page_inv _ _ _ _ _ _ Hdestruct11 Hfree2) 
                                     Hdestruct19 Hdestruct14 Hid Hobs_eq').
        Qed.

        Lemma alloc_free_page :
          forall id d d' r,
            high_level_invariant d ->
            alloc_spec id d = Some (d',r) -> r <> 0 ->
            (forall adr, ZMap.get adr (HP d') = ZMap.get adr (FlatMem.free_page r (HP d'))).
        Proof.
          intros id' d d' r Hinv Hspec Hr adr.
          inv_spec; inv_somes; try omega; simpl.
          destruct Hinv.
          rewrite <- valid_dirty; auto.
          intro Hcon.
          assert (Hex: exists n, ZMap.get r (LAT d) = LATValid true ATNorm n)
            by (apply valid_pperm_ppage; try omega; intro; rewrites).
          destruct Hex; decompose [and] a; rewrites.
        Qed.

        Lemma conf_ptfault_resv :
          forall v d1 d2 d1' d2',
            high_level_invariant d1 -> high_level_invariant d2 ->
            ptfault_resv_spec v d1 = Some d1' -> 
            ptfault_resv_spec v d2 = Some d2' -> 
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros v d1 d2 d1' d2' Hinv1 Hinv2 Hspec1 Hspec2 Hid Hobs_eq.
          unfold_specs; unfold ptResv_spec in *; repeat obs_eq_rewrites Hobs_eq.
          subdestruct; generalize Hid; clear Hid; inv_somes; intro Hid; auto.
          - destruct (conf_alloc _ _ _ _ _ _ Hinv1 Hinv2 Hdestruct9 Hdestruct6 Hid Hobs_eq); omega.
          - destruct (conf_alloc _ _ _ _ _ _ Hinv1 Hinv2 Hdestruct11 Hdestruct6 Hid Hobs_eq); omega.
          - assert (Hcid1: cid d1 = cid r1)
              by (clear Hdestruct8 Hdestruct9 Hdestruct14; 
                  repeat inv_spec; inv_somes; auto).
            assert (Hobs_eq': obs_eq r1 r) by (eapply conf_alloc; [| | eauto | eauto |..]; auto).
            rewrite Hcid1 in *; eapply conf_ptInsert0; [| | | | eauto | eauto | |]; auto.
            eapply alloc_free_page; [| eauto |]; auto.
            eapply alloc_free_page; [| eauto |]; auto.
            eapply alloc_high_level_inv; eauto.
            eapply alloc_high_level_inv; eauto.
        Qed.

      End CONF_PTFAULT.

      Section CONF_YIELD.

        (* Confidentiality for yielding *)

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

        Lemma conf_thread_yield :
          forall d1 d2 d1' d2' rs r1 r2,
            high_level_invariant d1 -> high_level_invariant d2 ->
            thread_yield_spec d1 rs = Some (d1',r1) ->
            thread_yield_spec d2 rs = Some (d2',r2) ->
            id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
        Proof.
          intros d1 d2 d1' d2' rs r1 r2 Hinv1 Hinv2 Hspec1 Hspec2 Hid Hobs_eq.
          assert (Hcid1:= Hspec1); apply thread_yield_new_cid in Hcid1; auto.
          assert (Hcid2:= Hspec2); apply thread_yield_new_cid in Hcid2; auto.
          inv_spec; inv_somes; solve_obs_eq Hobs_eq; simpl in *.
          rewrite <- (proj1 obs_eq_cid eq_refl) in Hcid2.
          split; intro; congruence.
          contradiction n1; subst; tauto.
        Qed.

      End CONF_YIELD.

    End CONF_PRIMS.

    Section CONF_SYSCALL.

      (* Confidentiality for system call trapping *)
      
      Lemma conf_proc_exit_user :
        forall d1 d2 d1' d2' uc,
          proc_exit_user_spec d1 uc = Some d1' ->
          proc_exit_user_spec d2 uc = Some d2' ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
      Proof.
        intros d1 d2 d1' d2' uc Hspec1 Hspec2 Hid Hobs_eq.
        inv_spec; inv_somes; solve_obs_eq Hobs_eq.
        subst; contradiction n; apply (proj1 obs_eq_cid eq_refl).
      Qed.
      
      Lemma conf_proc_start_user :
        forall d1 d2 d1' d2' r1 r2,
          proc_start_user_spec d1 = Some (d1',r1) ->
          proc_start_user_spec d2 = Some (d2',r2) ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2' /\ r1 = r2.
      Proof.
        intros d1 d2 d1' d2' r1 r2 Hspec1 Hspec2 Hid Hobs_eq.
        inv_spec; inv_somes; obs_eq_rewrites Hobs_eq; split.
        solve_obs_eq Hobs_eq.
        inv Hobs_eq.
        rewrite <- (proj1 obs_eq_cid eq_refl); auto.
      Qed.

      Lemma conf_trap_into_kernel :
        forall d1 d2 d1' d2' f s m rs vargs vargs' sg sg' b b'
               v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
               v0' v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' v11' v12' v13' v14' v15' v16',
          trap_into_kernel_spec f s m rs d1 d1' vargs sg b
                                v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
          trap_into_kernel_spec f s m rs d2 d2' vargs' sg' b'
                                v0' v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' v11' v12' v13' v14' v15' v16' ->
          id = cid d1 -> obs_eq d1 d2 -> obs_eq d1' d2'.
      Proof.
        intros until v16'; intros Hspec1 Hspec2 Hid Hobs_eq.
        unfold trap_into_kernel_spec in *.
        decompose [and] Hspec1; decompose [and] Hspec2; clear Hspec1 Hspec2.
        generalize Hid; clear Hid; rewrites'.
        apply extcall_arguments_determ with 
        (args1:= (Vint v0 :: Vint v1 :: Vint v2 :: Vint v3 :: Vint v4 :: Vint v5 :: Vint v6
                       :: Vint v7 :: Vint v8 :: Vint v9 :: Vint v10 :: Vint v11 :: Vint v12
                       :: Vint v13 :: Vint v14 :: Vint v15 :: Vint v16 :: nil)) in H8; auto; inv' H8.
        intro Hid; apply (conf_proc_exit_user _ _ _ _ _ H4 H12 Hid Hobs_eq).
      Qed.

    End CONF_SYSCALL.

    (* Confidentiality for the entire tsyscall semantics. 
       Combines all the previous confidentiality lemmas.  *)

    Theorem confidentiality :
      forall m m1' m2' d1 d2 d1' d2' rs rs1' rs2' t1 t2,
        secure_inv b id d1 -> secure_inv' b id rs d1 ->
        secure_inv b id d2 -> secure_inv' b id rs d2 ->
        LAsm.step ge (State rs (m,d1)) t1 (State rs1' (m1',d1')) -> 
        LAsm.step ge (State rs (m,d2)) t2 (State rs2' (m2',d2')) -> 
        id = cid d1 -> obs_eq d1 d2 -> 
        obs_eq d1' d2' /\ (id = cid d1' -> rs1' = rs2') /\ m1' = m2'.
    Proof.
      intros m m1' m2' d1 d2 d1' d2' rs rs1' rs2' t1 t2 Hinv1 Hinv1' 
             Hinv2 Hinv2' Hstep1 Hstep2 Hid Hobs_eq.
      destruct Hinv1; destruct Hinv1'; destruct Hinv2; destruct Hinv2'.
      destruct sec_usermode; destruct sec_usermode0.
      assert (Hcases: rs PC = Vptr b Int.zero \/ (ikern d1 = false /\ ikern d2 = false))
        by (destruct (ikern d1); destruct (ikern d2); auto); destruct Hcases as [Hcase|Hcase].
      (* deal with kernel mode as a special case *)
      eapply startuser_step in Hstep1; eauto; destruct Hstep1 as [Hstep1 Ht1].
      eapply startuser_step in Hstep2; eauto; destruct Hstep2 as [Hstep2 Ht2].
      generalize Hid; clear Hid; inversion Hstep1; inversion Hstep2; rewrites.
      intro Hid; destruct (conf_proc_start_user _ _ _ _ _ _ H3 H10); auto.
      repeat (split; auto); congruence.
      (* now we can assume we're in user mode *)
      destruct Hcase as [Hkern1 Hkern2]; generalize Hid; clear Hid; inv Hstep1; 
      try solve [destruct EXT_ALLOWED; simpl in *; congruence].
      {
        (* Case 1: internal step (assembly command) *)
        inv Hstep2; rewrites; try solve [inv H7].
        rename H7 into Hexec1, H11 into Hexec2.

        destruct i; 
          try solve [simpl in Hexec1, Hexec2; inv Hexec1; inv Hexec2; auto |
                     inv Hexec1; inv Hexec2; intro Hid;
                     decompose [and] (conf_exec_loadex _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 
                                                       sec_high_inv sec_high_inv0 Hkern1 Hkern2
                                                       sec_ihost_inv sec_ihost_inv0 Hid Hobs_eq); auto |
                     inv Hexec1; inv Hexec2; intro Hid1; assert (Hid2: id = cid d2) by (obs_eq_rewrites Hobs_eq);
                     rewrite Hid1 in sec_single_mapped_inv; rewrite Hid2 in sec_single_mapped_inv0;
                     decompose [and] (conf_exec_storeex _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 
                                                        sec_high_inv sec_high_inv0 Hkern1 Hkern2
                                                        sec_ihost_inv sec_ihost_inv0 
                                                        sec_single_mapped_inv sec_single_mapped_inv0 Hid1 Hobs_eq); auto].

        destruct i; simpl in *;
        try solve [subdestruct; inv Hexec1; inv Hexec2; auto |
                   intro Hid;
                     decompose [and] (conf_exec_loadex _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec1 Hexec2 
                                                       sec_high_inv sec_high_inv0 Hkern1 Hkern2
                                                       sec_ihost_inv sec_ihost_inv0 Hid Hobs_eq); auto |
                   intro Hid1; assert (Hid2: id = cid d2) by (obs_eq_rewrites Hobs_eq);
                   rewrite Hid1 in sec_single_mapped_inv; rewrite Hid2 in sec_single_mapped_inv0;
                   decompose [and] (conf_exec_storeex _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec1 Hexec2
                                                      sec_high_inv sec_high_inv0 Hkern1 Hkern2
                                                      sec_ihost_inv sec_ihost_inv0 
                                                      sec_single_mapped_inv sec_single_mapped_inv0 Hid1 Hobs_eq); auto |
                   destruct (INSTR_ALLOWED eq_refl); congruence |
                   unfold goto_label in *; subdestruct; inv Hexec1; inv Hexec2; auto].
      }
      {
        (* Case 2: primitive call *)
        destruct H6 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
        inv Hstep2; rewrites.

        (* rule out the case when one execution makes
           a primcall and the other an external call *)
        inv H9.
        destruct H as [σ' [Hl' Hsem']]; determ_simpl.
        inv Hsem.
        destruct Hsem' as [s' [σ' [Hmatch [Hsem [Hcon _]]]]]; inv Hcon.
        
        destruct H8 as [x' [sg' [σ' [Hef' [Hl' Hsem']]]]]; subst.
        inv Hef'; rewrites.
        inv_layer Hl; inv Hsem.
        {
          (* dispatch *)
          inv Hsem'; simpl in *.
          inv H1; inv H3.
          inv H9; inv H10.
          decompose [and] H1; decompose [and] H4; subst; clear H1 H4; intro Hid.
          destruct (conf_proc_start_user _ _ _ _ _ _ H10 H5).
          exploit sys_dispatch_usermode; eauto. intros (Heq & _).
          rewrite <- Heq.
          subst; eapply trap_into_kernel_usermode_cid; eauto.
          rewrite (stencil_matches_unique _ _ _ H2 H0) in H13, H.
          apply (conf_sys_dispatch_c _ _ _ _ _ _ H12 H13).
          subst; eapply trap_into_kernel_usermode_cid; eauto.
          eapply conf_trap_into_kernel; eauto.
          repeat (split; auto); auto. subst rs'. trivial.
        }
        {       
          (* pagefault handler *)
          inv Hsem'; simpl in *.
          inv H1; inv H3.
          inv H11; inv H10.
          decompose [and] H1; decompose [and] H4; subst; clear H1 H4; intro Hid.
          destruct (conf_proc_start_user _ _ _ _ _ _ H5 H10).
          revert H13. intros.
          exploit ptfault_resv_usermode; eauto. intros (Heq & _).
          rewrite <- Heq.
          subst; eapply trap_into_kernel_usermode_cid; eauto.
          assert (Hobs_eq': obs_eq labd0 labd2).
          rewrite (stencil_matches_unique _ _ _ H2 H0) in H3.
          eapply conf_trap_into_kernel; eauto.
          assert (Hid': id = cid labd0).
          {
            rewrite Hid.
            eapply trap_into_kernel_usermode_cid; eauto.
          }
          obs_eq_rewrite Hobs_eq'.
          exploit trap_into_kernel_inv1; eauto.
          intros (Hinv1 & _).
          clear H3.
          exploit trap_into_kernel_inv1; eauto.
          intros (Hinv2 & _).
          specialize (Hinv2 sec_high_inv).
          specialize (Hinv1 sec_high_inv0).
          apply (conf_ptfault_resv _ _ _ _ _ Hinv2 Hinv1 H13 H14 Hid' Hobs_eq').
          repeat (split; auto); auto. subst rs'. trivial.
        }        
        {
          (* yield *)
          inv Hsem'; simpl in *.
          inv H1; inv H3.
          inv H8; inv H9.
          decompose [and] H1; decompose [and] H3; subst; clear H1 H3; intro Hid.
          assert (Hid': id = cid labd0) by (clear H9 H14 H16; inv_spec; inv_somes; auto).
          assert (Hinv1: high_level_invariant labd0)
            by (clear H9 H14 H16; inv_spec; inv_somes; destruct sec_high_inv; 
                constructor; simpl; auto; try discriminate; try omega).
          assert (Hinv2: high_level_invariant labd1)
            by (clear H20 H14 H16; inv_spec; inv_somes; destruct sec_high_inv0; 
                constructor; simpl; auto; try discriminate; try omega).
          split; [|split]; auto.
          - generalize Hid Hid'; clear Hid Hid'.
            apply extcall_arguments_determ with 
            (args1:= (Vint v0 :: Vint v1 :: Vint v2 :: Vint v3 :: Vint v4 :: Vint v5 :: Vint v6
                           :: Vint v7 :: Vint v8 :: Vint v9 :: Vint v10 :: Vint v11 :: Vint v12
                           :: Vint v13 :: Vint v14 :: Vint v15 :: Vint v16 :: nil)) in H5; auto; inv H5.
            rewrite (stencil_matches_unique _ _ _ H2 H0) in H11; rewrites.
            intros Hid Hid'; assert (Hobs_eq':= conf_proc_exit_user _ _ _ _ _ H20 H9 Hid Hobs_eq).
            eapply conf_thread_yield; [| | eapply H14 | eapply H16 |..]; auto.
          - intro Hcon; apply thread_yield_new_cid in H14; auto; congruence.
        }
        {
          (* proc_start_user *)
          inv Hsem'; simpl in *.
          inv H1; inv H3; intro Hid.
          destruct (conf_proc_start_user _ _ _ _ _ _ H9 H10 Hid Hobs_eq); repeat (split; auto); auto.
          subst rs'. trivial.
        }
      }
    Qed.

    End CONF_LEMMAS.

  End WITHIMPL.

End WITHMEM.