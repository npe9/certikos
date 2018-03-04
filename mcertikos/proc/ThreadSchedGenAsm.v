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
(* *********************************************************************)
(*                                                                     *)
(*           Layers of PM: Assembly Verification for ThreadSched       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Locations.
Require Import AuxStateDataType.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import FlatMemory.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import Constant.
Require Import AsmImplLemma.
Require Import AsmImplTactic.
Require Import GlobIdent.
Require Import CommonTactic.

Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compcertx.MakeProgram.
Require Import LAsmModuleSem.
Require Import LAsm.
Require Import liblayers.compat.CompatGenSem.
Require Import PrimSemantics.
Require Import Conventions.

Require Import PCurID.
Require Import ThreadSchedGenSpec.
Require Import ThreadSchedGenAsmSource.
Require Import ThreadSchedGenAsmData.

Require Import LAsmModuleSemSpec.
Require Import LRegSet.
Require Import AbstractDataType.

Section ASM_VERIFICATION.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

    (*	
	.globl thread_sched
thread_sched:

        movr    num_chan, %eax
        movl    %eax, (%esp) // arguments for dequeue (num_chan)
        call    dequeue

        movl    %eax, 0(%esp) // return vaule :last l, also the arguments
        movr    1, %eax
        movl    %eax, 4(%esp) // arguements for set_state (last l, 1)
        call    set_state

        call    get_curid   
        movl    %eax, 4(%esp) // save cid

        call    set_curid // argument is already there, set_curid (last l)

        call    clear_cr2 // clear part of the trapinfo for security reasons
        
        movl    0(%esp), %edx
        movl    4(%esp), %eax
        jmp kctxt_switch

     *)

    Notation LDATA := RData.
    Notation LDATAOps := (cdata (cdata_ops := pcurid_data_ops) LDATA).

    Section WITHMEM.

      Context `{Hstencil: Stencil}.
      Context `{Hmem: Mem.MemoryModel}.
      Context `{Hmwd: UseMemWithData mem}.
      Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
      Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

      Ltac accessors_simpl:=
        match goal with
          | |- exec_storeex _ _ _ _ _ _ _ = _ =>
            unfold exec_storeex, LoadStoreSem2.exec_storeex2; 
              simpl; Lregset_simpl_tac; 
              match goal with
                | |- context [Asm.exec_store _ _ _ _ _ _ _] =>
                  unfold Asm.exec_store; simpl; 
                  Lregset_simpl_tac; lift_trivial
              end
          | |- exec_loadex _ _ _ _ _ _ = _ =>
            unfold exec_loadex, LoadStoreSem2.exec_loadex2; 
              simpl; Lregset_simpl_tac; 
              match goal with
                | |- context[Asm.exec_load _ _ _ _ _ _] =>
                  unfold Asm.exec_load; simpl; 
                  Lregset_simpl_tac; lift_trivial
              end
        end.

      Lemma threadsched_spec:
        forall ge (s: stencil) (rs rs0 rs': regset) b m0 labd labd',
          find_symbol s thread_sched = Some b ->
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          rs PC = Vptr b Int.zero ->
          thread_sched_spec labd ((Pregmap.init Vundef) # ESP <- (rs ESP) # EDI <- (rs EDI)
                                                               # ESI <- (rs ESI) # EBX <- (rs EBX) # EBP <- 
                                                               (rs EBP) # RA <- (rs RA)) = Some (labd', rs0) ->
          asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
          low_level_invariant (Mem.nextblock m0) labd ->
          high_level_invariant labd ->
          let rs' := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                            (undef_regs (List.map preg_of destroyed_at_call) rs)) in

          exists f' m0' r_, 
            lasm_step (thread_sched ↦ threadsched_function) (pcurid (Hmwd:= Hmwd) (Hmem:= Hmem)) thread_sched s rs 
                      (m0, labd) r_ (m0', labd')
            /\ inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
            /\ Memtype.Mem.inject f' m0 m0'
            /\ (Mem.nextblock m0 <= Mem.nextblock m0')%positive
            /\ (forall l,
                  Val.lessdef (Pregmap.get l (rs'#ESP<- (rs0#ESP)#EDI <- (rs0#EDI)#ESI <- (rs0#ESI)#EBX <- (rs0#EBX)
                                                 #EBP <- (rs0#EBP)#PC <- (rs0#RA)))
                              (Pregmap.get l r_)).
      Proof.
        intros. inv H3.
        rename H4 into HLOW. rename H5 into Hhigh.
        assert (HOS': 0 <= 64 <= Int.max_unsigned) by
            (rewrite int_max; omega).        
        
        caseEq(Mem.alloc m0 0 16).
        intros m1 b0 HALC.
        exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
        intros Hstencil_matches.

        assert (Hblock: Ple (Genv.genv_next ge) b0 /\ Plt b0 (Mem.nextblock m1)).
        {
          erewrite Mem.nextblock_alloc; eauto.
          apply Mem.alloc_result in HALC.
          rewrite HALC. 
          inv inv_inject_neutral.
          inv Hstencil_matches.
          rewrite stencil_matches_genv_next.
          lift_unfold.
          split; xomega.
        }

        exploit Hdequeue; eauto. 
        intros [[b_dequeue [Hdequeue_symbol Hdequeue_fun] prim_dequeue]].
        exploit Hkctxt_switch; eauto.
        intros [[b_kctxt_switch [Hswitch_symbol Hswitch_fun]] prim_kctxt_switch].
        exploit Hget_curid; eauto.
        intros [[b_get_cid [Hcid_symbol Hcid_fun]] prim_get_curid].
        exploit Hset_curid; eauto.
        intros [[b_set_cid [Hscid_symbol Hscid_fun]] prim_set_curid].
        exploit Hset_state; eauto.
        intros [[b_set_state [Hstate_symbol Hstate_fun]] prim_set_state].
        exploit Hclear_cr2; eauto.
        intros [[b_clear_cr2 [Hclear_symbol Hclear_fun]] prim_clear_cr2].
        
        specialize (Mem.valid_access_alloc_same _ _ _ _ _ HALC). intros.
        assert (HV1: Mem.valid_access m1 Mint32 b0 8 Freeable).
        {
          eapply H3; auto; simpl; try omega. unfold Z.divide.
          exists 2; omega.
        }
        eapply Mem.valid_access_implies with (p2:= Writable) in HV1; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (rs ESP) HV1) as [m2 HST1].
        assert (HV2: Mem.valid_access m2 Mint32 b0 12 Freeable).
        {
          eapply Mem.store_valid_access_1; eauto.
          eapply H3; auto; simpl; try omega.
          unfold Z.divide. exists 3; omega.
        }
        eapply Mem.valid_access_implies with (p2:= Writable) in HV2; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (rs RA) HV2) as [m3 HST2].
        destruct (threadsched_generate _ _ _ _ _ H2 HLOW Hhigh) as 
            [labd0[labd1[labd2[labd3[last_l[HEX1[HEX3[HEX2[HEX4[HEX5 HP]]]]]]]]]].
        destruct HP as 
            [HP[HM1[HM2[HIK[HIH[HIK0[HIH0[HIK1[HIH1[HIK2[HIH2[HIK3[HIH3 HCID_range]]]]]]]]]]]]].
        clear H2 HLOW. 
        assert (HV3: Mem.valid_access m3 Mint32 b0 0 Freeable).
        {
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply H3; auto; simpl; try omega. apply Zdivide_0.
        }
        eapply Mem.valid_access_implies with (p2:= Writable) in HV3; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr num_chan)) HV3) as [m4 HST3].

        assert(Hnextblock4: Mem.nextblock m4 = Mem.nextblock m1).
        {
          rewrite (Mem.nextblock_store _  _ _ _ _ _ HST3); trivial.
          rewrite (Mem.nextblock_store _  _ _ _ _ _ HST2); trivial.
          rewrite (Mem.nextblock_store _  _ _ _ _ _ HST1); trivial.
        }

        assert (HV4: Mem.valid_access m4 Mint32 b0 0 Writable).
        {
          eapply Mem.store_valid_access_1; eauto.
        }
        destruct (Mem.valid_access_store _ _ _ _ (Vint last_l) HV4) as [m5 HST4].
        assert (HV5: Mem.valid_access m5 Mint32 b0 4 Freeable).
        {
          repeat (eapply Mem.store_valid_access_1; [eassumption|]).
          eapply H3; auto; simpl; try omega. apply Zdivide_refl.
        }
        eapply Mem.valid_access_implies with (p2:= Writable) in HV5; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (Vint Int.one) HV5) as [m6 HST5].

        assert(Hnextblock6: Mem.nextblock m6 = Mem.nextblock m1).
        {
          rewrite (Mem.nextblock_store _  _ _ _ _ _ HST5); trivial.
          rewrite (Mem.nextblock_store _  _ _ _ _ _ HST4); trivial.
        }

        assert (HV6: Mem.valid_access m6 Mint32 b0 4 Writable).
        {
          eapply Mem.store_valid_access_1; eauto.
        }
        destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr (cid labd1))) HV6) as [m7 HST6].
        assert (HV7: Mem.range_perm m7 b0 0 16 Cur Freeable).
        {
          unfold Mem.range_perm. intros.
          repeat (eapply Mem.perm_store_1; [eassumption|]).
          eapply Mem.perm_alloc_2; eauto.
        }

        assert(Hnextblock7: Mem.nextblock m7 = Mem.nextblock m1).
        {
          rewrite (Mem.nextblock_store _  _ _ _ _ _ HST6); trivial.
        }

        destruct (Mem.range_perm_free _ _ _ _ HV7) as [m8 HFree].

        exploit Hthread_sched; eauto 2. intros Hfunct.

        rewrite (Lregset_rewrite rs).
        refine_split'; try eassumption.
        rewrite H1.
        econstructor; eauto.

        (* Pallocframe *)         
        one_step_forward'.
        Lregset_simpl_tac.
        lift_trivial.
        change (Int.unsigned (Int.add Int.zero (Int.repr 8))) with 8.
        change (Int.unsigned (Int.add Int.zero (Int.repr 12))) with 12.
        unfold set; simpl.
        rewrite HALC. simpl.
        rewrite HST1. simpl. rewrite HST2. 
        reflexivity.

        Lregset_simpl_tac' 1.
        
        (* movr    num_chan, %eax *)
        one_step_forward'.
        Lregset_simpl_tac' 2.
        
        (* movl    %eax, 0(%esp) *)
        one_step_forward'.
        accessors_simpl.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero Int.zero))) with 0.
        unfold set; simpl. rewrite HIH, HIK, HST3. reflexivity.
        
        (* call dequeue*)
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hdequeue_symbol.          
        Lregset_simpl_tac.

        (* call dequeue body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_external _ b_dequeue); eauto; trivial. simpl; auto.
        constructor_gen_sem_intro.
        Lregset_simpl_tac. lift_trivial.
        erewrite Mem.load_store_same; eauto.
        simpl. 
        econstructor; eauto.
        repeat constructor.
        red. red. red. red. red. red.
        change positive with ident in *.
        rewrite prim_dequeue.
        refine_split'; try reflexivity.
        econstructor; eauto.
        refine_split'; try reflexivity; try eassumption.
        simpl. repeat split. eassumption.
        Lregset_simpl_tac.
        lift_trivial.
        intros. inv H2.
        rewrite Hnextblock4; assumption.
        discriminate.
        discriminate.
        Lregset_simpl_tac.
        change (Int.add (Int.add (Int.repr 2) Int.one) Int.one) with (Int.repr 4).

        (* movl    %eax, 0(%esp) *)
        one_step_forward'.
        accessors_simpl.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero Int.zero))) with 0.
        unfold set. simpl.
        rewrite HIH0, HIK0, HST4. trivial.

        (* movr    1, %eax *)
        one_step_forward'.
        Lregset_simpl_tac' 6.

        (* movl    %eax, 4(%esp) *)
        one_step_forward'.
        accessors_simpl.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero (Int.repr 4)))) with 4.
        unfold set. simpl.
        rewrite HIH0, HIK0,HST5. trivial.

        (* call set_state*)        
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hstate_symbol.
        Lregset_simpl_tac.
        change (Int.add (Int.add (Int.repr 6) Int.one) Int.one) with (Int.repr 8).

        (* call set state body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_external _ b_set_state); eauto 1; trivial; simpl; auto. 
        constructor_gen_sem_intro.
        Lregset_simpl_tac.
        lift_trivial.
        change (Int.unsigned (Int.add Int.zero (Int.repr 0))) with 0. 
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_same; eauto; simpl.
        right. left. reflexivity.

        Lregset_simpl_tac.
        simpl. lift_trivial.
        change (Int.unsigned (Int.add Int.zero (Int.repr 4))) with 4. 
        erewrite Mem.load_store_same; eauto.

        simpl. econstructor; eauto.
        red. red. red. red. red. red.
        change positive with ident in *.
        rewrite prim_set_state.
        refine_split'; try reflexivity.
        econstructor; eauto.
        refine_split'; try reflexivity; try eassumption.
        simpl. repeat split. eassumption.
        Lregset_simpl_tac.
        lift_trivial.
        intros. inv H2.
        rewrite Hnextblock6; assumption.
        discriminate.
        discriminate.
        Lregset_simpl_tac.

        (* call get_curid_1*)
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hcid_symbol.
        Lregset_simpl_tac.
        change (Int.add (Int.repr 8) Int.one) with (Int.repr 9).

        (* call get cid body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_external _ b_get_cid); eauto 1; trivial; simpl; auto.
        constructor_gen_sem_intro.
        simpl. econstructor; eauto.
        red. red. red. red. red. red.
        change positive with ident in *.
        rewrite prim_get_curid.
        refine_split'; try reflexivity.
        econstructor; eauto.
        refine_split'; try reflexivity; try eassumption.
        simpl. repeat split. 
        rewrite HEX2.
        replace (cid labd1) with (Int.unsigned(Int.repr(cid labd1))).
        reflexivity.
        rewrite Int.unsigned_repr; omega.

        Lregset_simpl_tac.
        lift_trivial.
        intros. inv H2.
        rewrite Hnextblock6; assumption.
        discriminate.
        discriminate.
        Lregset_simpl_tac.

        (* movl    %eax, 4(%esp) *)
        one_step_forward'.
        accessors_simpl.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero (Int.repr 4)))) with 4.
        unfold set. simpl.
        rewrite HIH1, HIK1, HST6. trivial.

        (* call set_curid*)
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hscid_symbol.
        Lregset_simpl_tac.
        change  (Int.add (Int.add (Int.repr 9) Int.one) Int.one) with (Int.repr 11).

        (* call set cid body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_external _ b_set_cid); eauto 1; trivial; simpl; auto.
        constructor_gen_sem_intro. 
        Lregset_simpl_tac.
        lift_trivial.
        change (Int.unsigned (Int.add Int.zero (Int.repr 0))) with 0. 
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_same; eauto; simpl.
        right. left. omega.  
        right. left. omega.

        simpl. econstructor; eauto.
        red. red. red. red. red. red.
        change positive with ident in *.
        rewrite prim_set_curid.
        refine_split'; try reflexivity.
        econstructor; eauto.
        refine_split'; try reflexivity; try eassumption.
        simpl. repeat split. eassumption.
        Lregset_simpl_tac.
        lift_trivial.
        intros. inv H2.
        rewrite Hnextblock7; assumption.
        discriminate.
        discriminate.
        Lregset_simpl_tac.

        (* call clear_cr2 *)
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hclear_symbol.
        Lregset_simpl_tac.
        change (Int.add (Int.repr 11) Int.one) with (Int.repr 12).

        (* call clear_cr2 body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_external _ b_clear_cr2); eauto 1; trivial; simpl; auto.
        constructor_gen_sem_intro.
        simpl. econstructor; eauto.
        red. red. red. red. red. red.
        change positive with ident in *.
        rewrite prim_clear_cr2.
        refine_split'; try reflexivity.
        econstructor; eauto.
        refine_split'; try reflexivity; try eassumption.
        simpl. repeat split. 
        rewrite HEX5; eauto.

        Lregset_simpl_tac.
        lift_trivial.
        intros. inv H2.
        rewrite Hnextblock7; assumption.
        discriminate.
        discriminate.
        Lregset_simpl_tac.

        (* movl    0(%esp), %edx *)
        one_step_forward'.
        accessors_simpl.
        rewrite HIH3, HIK3.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero (Int.repr 0)))) with 0.
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_same; eauto. 
        right. left. omega.  
        right. left. omega.
        Lregset_simpl_tac' 13.

        (* movl    4(%esp), %eax *)
        one_step_forward'.
        accessors_simpl.
        rewrite HIH3, HIK3.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero (Int.repr 4)))) with 4.
        erewrite Mem.load_store_same; eauto. 
        Lregset_simpl_tac' 14. simpl.

        (*freeframe*) 
        one_step_forward'.
        Lregset_simpl_tac.
        lift_trivial.
        unfold set; simpl.
        change (Int.unsigned (Int.add Int.zero (Int.repr 12))) with 12.
        change (Int.unsigned (Int.add Int.zero (Int.repr 8))) with 8.
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_other; eauto; simpl.  
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_same; eauto.
        erewrite register_type_load_result.
        
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_same; eauto.
        erewrite register_type_load_result.

        rewrite HFree. reflexivity.
        apply inv_reg_wt.
        right. left. omega.
        right. right. omega.
        right. right. omega.
        right. right. omega.
        right. right. omega.
        apply inv_reg_wt.
        right. right. omega.
        right. right. omega.
        right. right. omega.
        right. right. omega.

        Lregset_simpl_tac' 15.

        (* jmp kctxt_switch *)
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hswitch_symbol.
        Lregset_simpl_tac.

        (* call kctxt_switch body*)  
        eapply star_one; eauto.
        eapply (LAsm.exec_step_prim_call _ b_kctxt_switch); eauto 1; trivial. 
        econstructor.
        refine_split'; eauto 1.
        econstructor; eauto 1. simpl.
        econstructor.
        replace (cid labd1) with (Int.unsigned(Int.repr(cid labd1))) in HP.
        apply HP.
        rewrite Int.unsigned_repr; omega.
        eassumption.
        intros.
        rewrite (Mem.nextblock_free _ _ _ _ _ HFree); trivial.
        rewrite Hnextblock7.
        erewrite Mem.nextblock_alloc; eauto.
        specialize (HM2 _ _ H2).
        apply val_inject_incr with (Mem.flat_inj (Mem.nextblock m0)); trivial.
        eapply flat_inj_inject_incr. clear. abstract xomega.

        reflexivity.
        reflexivity.
        reflexivity.
        inv Hstencil_matches.
        rewrite <- stencil_matches_symbols.
        eassumption.
        reflexivity.
        reflexivity.
        reflexivity.

        assert (HFB: forall b1 delta, Mem.flat_inj (Mem.nextblock m0) b1 <> Some (b0, delta)).
        {
          intros. unfold Mem.flat_inj.
          red; intros.
          destruct (plt b1 (Mem.nextblock m0)). inv H2.
          rewrite (Mem.alloc_result _ _ _ _ _ HALC) in p.
          xomega. inv H2.
        }
        eapply Mem.free_right_inject; eauto; [|intros; specialize (HFB b1 delta); apply HFB; trivial].
        repeat (eapply Mem.store_outside_inject; [ | | eassumption] 
                ; [|intros b1 delta; intros; specialize (HFB b1 delta); apply HFB; trivial]).
        eapply Mem.alloc_right_inject; eauto.
        inv inv_inject_neutral.
        apply Mem.neutral_inject; trivial.
        
        rewrite (Mem.nextblock_free _ _ _ _ _ HFree); trivial.
        rewrite Hnextblock7.
        rewrite (Mem.nextblock_alloc _ _ _ _ _ HALC) ; eauto.
        clear. abstract xomega.

        simpl.
        unfold Lregset_fold; simpl.
        intros reg.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.     
        exploit reg_false; try eassumption.
        intros HF. inv HF.
      Qed.

    Lemma thread_sched_code_correct:
      asm_spec_le (thread_sched ↦ thread_sched_spec_low)
                  (〚 thread_sched ↦ threadsched_function 〛 pcurid).
    Proof.
      eapply asm_sem_intro; try solve [ reflexivity | eexists; reflexivity ].
      intros. inv H.
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b =
                     Some (Internal threadsched_function)).
      {
        assert (Hmodule:
          get_module_function thread_sched (thread_sched ↦ threadsched_function)
            = OK (Some threadsched_function)) by reflexivity.
        assert (HInternal:
          make_internal threadsched_function
            = OK (AST.Internal threadsched_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }

      exploit threadsched_spec; eauto 2.
      intros (f' & m0' & r_ & Hstep & Hincr & Hinject & Hnb & Hlessdef).

      split; [ reflexivity |].
      exists f', (m0', labd'), r_.
      repeat split; try assumption.
      simpl; unfold lift; simpl.
      exact (PowersetMonad.powerset_fmap_intro m0' Hinject).
    Qed.

  End WITHMEM.

End ASM_VERIFICATION.