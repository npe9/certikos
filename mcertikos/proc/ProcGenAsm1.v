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
(*           Layers of PM: Assembly Verification for Thread            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

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

Require Import PUCtxtIntro.
Require Import ProcGenSpec.
Require Import ProcGenAsmSource.
Require Import ProcGenAsmData.

Require Import LAsmModuleSemSpec.
Require Import LRegSet.
Require Import AbstractDataType.

Section ASM_VERIFICATION.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.
  Notation LDATAOps := (cdata LDATA).

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
              | |- context[Asm.exec_store _ _ _ _ _ _ _ ] =>
                unfold Asm.exec_store; simpl; 
                Lregset_simpl_tac; lift_trivial
            end
        | |- exec_loadex _ _ _ _ _ _ = _ =>
          unfold exec_loadex, LoadStoreSem2.exec_loadex2; 
            simpl; Lregset_simpl_tac;
            match goal with
              | |- context[Asm.exec_load _ _ _ _ _ _ ] =>
                unfold Asm.exec_load; simpl; 
                Lregset_simpl_tac; lift_trivial
            end
      end.

    Lemma procstartuser_spec:
      forall ge (s: stencil) (rs rs'': regset) rs' b m0 labd labd',
        find_symbol s proc_start_user = Some b ->
        make_globalenv s (proc_start_user ↦ proc_start_user_function) puctxtintro = ret ge ->
        rs PC = Vptr b Int.zero ->
        proc_start_user_spec labd = Some (labd', rs') ->
        asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
        low_level_invariant (Mem.nextblock m0) labd ->
        high_level_invariant labd ->
        rs'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: IR ECX :: IR EAX :: RA :: nil)
                           (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
        exists f' m0' r_, 
          lasm_step (proc_start_user ↦ proc_start_user_function) (puctxtintro (Hmwd:= Hmwd) (Hmem:= Hmem)) proc_start_user s rs 
                    (m0, labd) r_ (m0', labd')
          /\ inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
          /\ Memtype.Mem.inject f' m0 m0'
          /\ (Mem.nextblock m0 <= Mem.nextblock m0')%positive
          /\ (forall l,
                Val.lessdef (Pregmap.get l (rs''# EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                                                # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                                                # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                                                # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                                                # PC <- (ZMap.get U_EIP rs')))
                            (Pregmap.get l r_)).
  Proof.
    intros. inv H3.
    rename H4 into HLOW, H5 into Hhigh.
    assert (HOS': 0 <= 64 <= Int.max_unsigned) by (rewrite int_max; omega).
    
    caseEq(Mem.alloc m0 0 12).
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

    exploit Hrestore_uctx; eauto.
    intros [[b_restore [Hrestore Hrestore_fun]] prim_restore_uctx].
    exploit Hpt_out; eauto.
    intros [[b_ptout [Hptout_symbol Hptout_fun]] prim_ptout].
    exploit HsetPT; eauto.
    intros [[b_set_cr3 [HPT_symbol HPT_fun]] prim_set_cr3].
    exploit Hget_curid; eauto.
    intros [[b_get_cid [Hcid_symbol Hcid_fun]] prim_get_curid].

    specialize (Mem.valid_access_alloc_same _ _ _ _ _ HALC). intros.

    assert (HV1: Mem.valid_access m1 Mint32 b0 4 Freeable).
    {
      eapply H3; auto; simpl; try omega.
      apply Z.divide_refl.
    }
    eapply Mem.valid_access_implies with (p2:= Writable) in HV1; [|constructor].
    destruct (Mem.valid_access_store _ _ _ _ (rs ESP) HV1) as [m2 HST1].

    assert (HV2: Mem.valid_access m2 Mint32 b0 8 Freeable).
    {
      eapply Mem.store_valid_access_1; eauto.
      eapply H3; auto; simpl; try omega.
      unfold Z.divide.
      exists 2; omega.
    }
    eapply Mem.valid_access_implies with (p2:= Writable) in HV2; [|constructor].
    destruct (Mem.valid_access_store _ _ _ _ (rs RA) HV2) as [m3 HST2].

    assert(Hnextblock3: Mem.nextblock m3 = Mem.nextblock m1).
    {
      rewrite (Mem.nextblock_store _  _ _ _ _ _ HST2); trivial.
      rewrite (Mem.nextblock_store _  _ _ _ _ _ HST1); trivial.
    }

    destruct (startuser_generate _ _ _ _ H2 HLOW Hhigh) as 
        [HCID_range[HEX1[labd0[HEX2[labd1[HEX3[HCID[HP[HM1[HM2[HIK[HIH[HIK0[HIH0[HIK1 HIH1]]]]]]]]]]]]]]].
    clear H2 HLOW Hhigh.


    replace (cid labd) with
    (Int.unsigned (Int.repr (cid labd))) in HEX1, HEX3 by
                                           (rewrite Int.unsigned_repr; trivial; omega).

    assert (HV3: Mem.valid_access m3 Mint32 b0 0 Freeable).
    {
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply H3; auto; simpl; try omega.
      apply Zdivide_0.
    }
    eapply Mem.valid_access_implies with (p2:= Writable) in HV3; [|constructor].
    destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr (cid labd))) HV3) as [m4 HST3].

    assert(Hnextblock4: Mem.nextblock m4 = Mem.nextblock m1).
    {
      rewrite (Mem.nextblock_store _  _ _ _ _ _ HST3); trivial.
    }

    exploit Hproc_start_user; eauto 2. intros Hfunct.

    rewrite (Lregset_rewrite rs).
    refine_split'; try eassumption.
    rewrite H1.
    econstructor; eauto.

    (* Pallocframe *)
    one_step_forward'.
    Lregset_simpl_tac.
    lift_trivial.
    unfold set; simpl.
    rewrite HALC. simpl.
    change (Int.unsigned (Int.add Int.zero (Int.repr 8))) with 8.
    change (Int.unsigned (Int.add Int.zero (Int.repr 4))) with 4. 
    rewrite HST1. simpl.
    rewrite HST2.
    reflexivity. 
    Lregset_simpl_tac' 1.

    (* call get_curid3*)
    one_step_forward'.
    change (Int.add (Int.repr 1) Int.one ) with (Int.repr 2).
    unfold symbol_offset. unfold fundef.
    rewrite Hcid_symbol.
    Lregset_simpl_tac.

    (* call get cid body*)
    econstructor; eauto.
    eapply (LAsm.exec_step_external _ b_get_cid); simpl; eauto 2.
    constructor_gen_sem_intro; simpl.

    simpl. econstructor; eauto.
    red. red. red. red. red. red.
    change positive with ident in *.
    rewrite prim_get_curid.
    refine_split'; try reflexivity.
    econstructor; eauto.
    refine_split'; try reflexivity; try eassumption.
    simpl. repeat split. 
    rewrite HEX1. reflexivity.
    Lregset_simpl_tac.
    lift_trivial.
    intros. inv H2.
    rewrite Hnextblock3; assumption.
    discriminate.
    discriminate.
    Lregset_simpl_tac.

    (* movl    %eax, 0(%esp) *)
    one_step_forward'.
    accessors_simpl.
    change (Int.unsigned (Int.add Int.zero (Int.add Int.zero (Int.repr 0)))) with 0.
    rewrite HIH, HIK, HST3. reflexivity.
    unfold set; simpl.

    (* call tss_switch*)
    one_step_forward'.
    Lregset_simpl_tac' 4.

    (* call pt_out*)
    one_step_forward'.
    change (Int.add (Int.repr 4) Int.one) with (Int.repr 5).
    unfold symbol_offset. unfold fundef.
    rewrite Hptout_symbol.
    Lregset_simpl_tac.

    (* call ptout body*)
    econstructor; eauto.
    eapply (LAsm.exec_step_prim_call _ b_ptout); eauto 1.
    econstructor; eauto 1.
    instantiate (4:= pt_out).
    change positive with ident in *.
    rewrite prim_ptout; trivial.
    refine_split'; try reflexivity.
    econstructor; eauto. simpl.
    econstructor; eauto.
    erewrite <- stencil_matches_symbols; eassumption.
    reflexivity.
    Lregset_simpl_tac.

    (* call set_cr3*)
    one_step_forward'.
    change (Int.add (Int.repr 5) Int.one) with (Int.repr 6).
    unfold symbol_offset. unfold fundef.
    rewrite HPT_symbol.
    Lregset_simpl_tac.

    (* call set PT body*)
    econstructor; eauto.
    eapply (LAsm.exec_step_external _ b_set_cr3); simpl; eauto 2.
    constructor_gen_sem_intro; simpl.
    lift_trivial.
    change (Int.unsigned (Int.add Int.zero (Int.repr 0))) with 0.
    erewrite Mem.load_store_same; eauto.

    simpl. econstructor; eauto.
    red. red. red. red. red. red.
    change positive with ident in *.
    rewrite prim_set_cr3; trivial.
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

    (* jmp restore_uctx *) 
    one_step_forward'.
    unfold symbol_offset. unfold fundef.
    rewrite Hrestore.
    Lregset_simpl_tac.
    
    (* call resore_uctx body*)  
    eapply star_one; eauto.
    eapply (LAsm.exec_step_prim_call _ b_restore); eauto 1.
    econstructor.
    refine_split'; eauto 1.
    econstructor; eauto 1. simpl.
    econstructor.
    erewrite <- stencil_matches_symbols; eassumption.
    reflexivity.
    eassumption.
    reflexivity.
    constructor_gen_sem_intro; simpl.
    simpl. change (Int.unsigned (Int.add Int.zero (Int.repr 0))) with 0. 
    erewrite Mem.load_store_same; eauto.
    simpl. reflexivity.
    rewrite HCID.
    rewrite Int.unsigned_repr. reflexivity.
    omega.    

    intros.
    apply HM1.
    eassumption.
    eauto 1.
    lift_trivial.

    rewrite Hnextblock4.
    erewrite Mem.nextblock_alloc; eauto.
    intros. specialize (HM2 _ H2).
    apply val_inject_incr with (Mem.flat_inj (Mem.nextblock m0)); trivial.
    eapply flat_inj_inject_incr. clear. abstract xomega.

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

    repeat (eapply Mem.store_outside_inject; [ | | eassumption] 
            ; [|intros b1 delta; intros; specialize (HFB b1 delta); apply HFB; trivial]).
    eapply Mem.alloc_right_inject; eauto 1.
    inv inv_inject_neutral.
    apply Mem.neutral_inject; trivial.

    rewrite Hnextblock4.
    rewrite (Mem.nextblock_alloc _ _ _ _ _ HALC) ; eauto.
    clear. abstract xomega.

    Lregset_simpl_tac.
    simpl.
    Lregset_simpl_tac.
    intros.
    eapply Val.lessdef_refl.
  Qed.

    Lemma proc_start_user_code_correct:
      asm_spec_le (proc_start_user ↦ proc_start_user_spec_low)
                  (〚 proc_start_user ↦ proc_start_user_function 〛 puctxtintro).
    Proof.
      eapply asm_sem_intro; try solve [ reflexivity | eexists; reflexivity ].
      intros. inv H.
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b =
                     Some (Internal proc_start_user_function)).
      {
        assert (Hmodule:
          get_module_function proc_start_user (proc_start_user ↦ proc_start_user_function)
            = OK (Some proc_start_user_function)) by reflexivity.
        assert (HInternal:
          make_internal proc_start_user_function
            = OK (AST.Internal proc_start_user_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }

      exploit procstartuser_spec; eauto 2.
      intros (f' & m0' & r_ & Hstep & Hincr & Hinject & Hnb & Hv).

      refine_split'; try eassumption; try reflexivity.
      simpl; unfold lift; simpl.
      exact (PowersetMonad.powerset_fmap_intro m0' Hinject).
    Qed.

  End WITHMEM.

End ASM_VERIFICATION.
