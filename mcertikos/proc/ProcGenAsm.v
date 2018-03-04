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
              | |- context[Asm.exec_store _ _ _ _ _ _ _] =>
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
    
    Lemma procexituser_spec:
      forall ge (s: stencil) (rs rs': regset) b m0 labd labd' sig vargs 
             v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
        let uctx1:= ZMap.set U_EBX (Vint v4)
                             (ZMap.set U_OESP (Vint v3)
                                       (ZMap.set U_EBP (Vint v2)
                                                 (ZMap.set U_ESI (Vint v1) 
                                                           (ZMap.set U_EDI (Vint v0) (ZMap.init Vundef))))) in
        let uctx2:= ZMap.set U_ES (Vint v8)
                             (ZMap.set U_EAX (Vint v7)
                                       (ZMap.set U_ECX (Vint v6) 
                                                 (ZMap.set U_EDX (Vint v5) uctx1))) in
        let uctx3:= ZMap.set U_EIP (Vint v12)
                             (ZMap.set U_ERR (Vint v11) 
                                       (ZMap.set U_TRAPNO (Vint v10) 
                                                 (ZMap.set U_DS (Vint v9) uctx2))) in
        let uctx4:= ZMap.set U_SS (Vint v16) 
                             (ZMap.set U_ESP (Vint v15) 
                                       (ZMap.set U_EFLAGS (Vint v14)
                                                 (ZMap.set U_CS (Vint v13) uctx3))) in    
        find_symbol s proc_exit_user = Some b ->
        make_globalenv s (proc_exit_user ↦ proc_exit_user_function) puctxtintro = ret ge ->
        rs PC = Vptr b Int.zero ->
        proc_exit_user_spec labd uctx4 = Some labd' ->
        asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
        low_level_invariant (Mem.nextblock m0) labd ->
        high_level_invariant labd ->
        rs' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: IR EBX :: RA :: nil)
                          (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
        sig = mksignature (AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                   AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                   AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                   AST.Tint::nil) None cc_default ->
        vargs = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v4 :: Vint v5 :: Vint v6
                      :: Vint v7 :: Vint v8 :: Vint v9:: Vint v10 :: Vint v11 :: Vint v12
                      :: Vint v13 :: Vint v14 :: Vint v15:: Vint v16 ::nil) ->
        extcall_arguments rs m0 sig vargs ->
        rs ESP <> Vundef ->
        (forall b1 o,
           rs ESP = Vptr b1 o ->
           Ple (Genv.genv_next ge) b1 /\ Plt b1 (Mem.nextblock m0)) ->
        exists f' m0' r_, 
          lasm_step (proc_exit_user ↦ proc_exit_user_function) (puctxtintro (Hmwd:= Hmwd) (Hmem:= Hmem)) proc_exit_user s rs 
                    (m0, labd) r_ (m0', labd')
          /\ inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
          /\ Memtype.Mem.inject f' m0 m0'
          /\ (Mem.nextblock m0 <= Mem.nextblock m0')%positive
          /\ (forall l,
                Val.lessdef (Pregmap.get l (rs'# PC <- (rs RA)))
                            (Pregmap.get l r_)).
  Proof.
    intros. inv H3.
    rename H9 into HAN, H10 into HESP, H11 into HESP_range.
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

    exploit Hsave_uctx; eauto.
    intros [[b_save [Hsave Hsave_fun]] prim_save_uctx].
    exploit Hpt_in; eauto.
    intros [[b_ptin [Hptin_symbol Hptin_fun]] prim_ptin].
    exploit Htrap_in; eauto.
    intros [[b_trapin [Htrapin_symbol Htrapin_fun]] prim_trapin].
    exploit HsetPT; eauto.
    intros [[b_set_cr3 [HPT_symbol HPT_fun]] prim_set_cr3].

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

    destruct (exituser_generate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H5) as 
        [HIH[labd0[Htrapin[labd1[Hsaveu[labd2[Hsetpt[Hptin[HIK0[HIH0[HIK1[HIH1[HIK2[HIH2 [HIK' HIH']]]]]]]]]]]]]]].

    clear H2 H5.
    assert (HV3: Mem.valid_access m3 Mint32 b0 0 Freeable).
    {
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply H3; auto; simpl; try omega.
      apply Zdivide_0.
    }
    eapply Mem.valid_access_implies with (p2:= Writable) in HV3; [|constructor].
    destruct (Mem.valid_access_store _ _ _ _ (Vint Int.zero) HV3) as [m4 HST3].

    assert(Hnextblock4: Mem.nextblock m4 = Mem.nextblock m1).
    {
      rewrite (Mem.nextblock_store _  _ _ _ _ _ HST3); trivial.
      rewrite (Mem.nextblock_store _  _ _ _ _ _ HST2); trivial.
      rewrite (Mem.nextblock_store _  _ _ _ _ _ HST1); trivial.
    }

    assert (HV4: Mem.range_perm m4 b0 0 12 Cur Freeable).
    {
      unfold Mem.range_perm. intros.
      repeat (eapply Mem.perm_store_1; [eassumption|]).
      eapply Mem.perm_alloc_2; eauto.
    }
    destruct (Mem.range_perm_free _ _ _ _ HV4) as [m5 HFree].

    exploit Hproc_exit_user; eauto 2. intros Hfunct.

    rewrite (Lregset_rewrite rs).
    refine_split'; try eassumption.
    rewrite H1.
    econstructor; eauto.

    (* movr    RA, %ebx *)
    one_step_forward'.
    Lregset_simpl_tac' 1.

    (* call trap_in*)
    one_step_forward'.
    unfold symbol_offset. unfold fundef.
    rewrite Htrapin_symbol.
    change (Int.add (Int.repr 1) Int.one) with (Int.repr 2).
    Lregset_simpl_tac.

    (* call trap in body*)
    econstructor; eauto.
    eapply (LAsm.exec_step_prim_call _ b_trapin); eauto 1.
    econstructor; eauto 1.
    instantiate (4:= trap_in).
    change positive with ident in *.
    rewrite prim_trapin.
    refine_split'; try reflexivity.
    econstructor; eauto. simpl.
    econstructor; eauto.
    Lregset_simpl_tac.

    (* call save_uctx*)
    one_step_forward'.
    unfold symbol_offset. unfold fundef.
    rewrite Hsave.
    change (Int.add (Int.repr 2) Int.one) with (Int.repr 3).
    Lregset_simpl_tac.

    (* call save_uctx body*)
    econstructor; eauto.
    eapply (LAsm.exec_step_external _ b_save); simpl; eauto.
    inv HAN. 
    repeat match goal with
             | H0: extcall_arg _ _ _ _ |- _ => inv H0
             | H1: list_forall2 _ _ _  |- _ => inv H1
           end.
    constructor_gen_sem_intro.

    simpl. econstructor; eauto.
    red. red. red. red. red. red.
    change positive with ident in *.
    rewrite prim_save_uctx.
    refine_split'; try reflexivity.
    econstructor; eauto.
    refine_split'; try reflexivity; try eassumption.
    simpl. econstructor.
    eassumption.
    reflexivity.
    reflexivity.
    discriminate.
    Lregset_simpl_tac.

    (* movr    %ebx, RA *)
    one_step_forward'.
    Lregset_simpl_tac' 4.

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
    Lregset_simpl_tac' 5.

    (* movr    0, %eax *) 
    one_step_forward'.
    Lregset_simpl_tac' 6.

    (* movl    %eax, 0(%esp) *)
    one_step_forward'.
    accessors_simpl.
    rewrite HIK1, HIH1.
    change (Int.unsigned (Int.add Int.zero (Int.add Int.zero (Int.repr 0)))) with 0.
    rewrite HST3. reflexivity.
    unfold set; simpl.

    (* call set_cr3*)
    one_step_forward'.
    unfold symbol_offset. unfold fundef.
    rewrite HPT_symbol.
    change (Int.add (Int.add (Int.repr 6) Int.one) Int.one) with (Int.repr 8).
    Lregset_simpl_tac.
    
    (* call set PT body*)
    econstructor; eauto.
    eapply (LAsm.exec_step_external _ b_set_cr3); simpl; eauto.
    constructor_gen_sem_intro; simpl.
    lift_trivial.
    change (Int.unsigned (Int.add Int.zero (Int.repr 0))) with 0.
    erewrite Mem.load_store_same; eauto.

    simpl. econstructor; eauto.
    red. red. red. red. red. red.
    change positive with ident in *.
    rewrite prim_set_cr3.
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

    (* call PTin*)
    one_step_forward'.
    unfold symbol_offset. unfold fundef.
    rewrite Hptin_symbol.
    change (Int.add (Int.repr 8) Int.one) with (Int.repr 9).
    Lregset_simpl_tac.

    (* call pt in body*)
    econstructor; eauto.
    eapply (LAsm.exec_step_prim_call _ b_ptin); eauto 1.
    econstructor; eauto 1.
    instantiate (4:= pt_in).
    change positive with ident in *.
    rewrite prim_ptin.
    refine_split'; try reflexivity.
    econstructor; eauto. simpl.
    econstructor; eauto.
    erewrite <- stencil_matches_symbols; eassumption.
    reflexivity.
    Lregset_simpl_tac.

    (*freeframe*)
    one_step_forward'.
    lift_trivial.
    change (Int.unsigned (Int.add Int.zero (Int.repr 4))) with 4.
    change (Int.unsigned (Int.add Int.zero (Int.repr 8))) with 8.
    unfold set; simpl.
    erewrite Mem.load_store_other; eauto; simpl.
    erewrite Mem.load_store_same; eauto.
    erewrite register_type_load_result.

    erewrite Mem.load_store_other; eauto; simpl.
    erewrite Mem.load_store_other; eauto; simpl.  
    erewrite Mem.load_store_same; eauto.
    erewrite register_type_load_result.

    rewrite HFree. reflexivity.
    apply inv_reg_wt.
    right. left. omega.
    right. right. omega.
    apply inv_reg_wt.
    right. right. omega.
    Lregset_simpl_tac' 10.

    (* ret *) 
    one_step_forward'.
    Lregset_simpl_tac.
    econstructor.

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
    eapply Mem.free_right_inject; eauto 1; [|intros; specialize (HFB b1 delta); apply HFB; trivial].
    repeat (eapply Mem.store_outside_inject; [ | | eassumption] 
            ; [|intros b1 delta; intros; specialize (HFB b1 delta); apply HFB; trivial]).
    eapply Mem.alloc_right_inject; eauto 1.
    inv inv_inject_neutral.
    apply Mem.neutral_inject; trivial.

    rewrite (Mem.nextblock_free _ _ _ _ _ HFree); trivial.
    rewrite Hnextblock4.
    rewrite (Mem.nextblock_alloc _ _ _ _ _ HALC); eauto.
    clear. abstract xomega.

    Lregset_simpl_tac.
    intros reg.
    unfold Lregset_fold; simpl.
    repeat (rewrite Pregmap.gsspec).
    simpl_destruct_reg.     
    exploit reg_false; try eassumption.
    intros HF. inv HF.
  Qed.

    Lemma proc_exit_user_code_correct:
      asm_spec_le (proc_exit_user ↦ proc_exit_user_spec_low)
                  (〚 proc_exit_user ↦ proc_exit_user_function 〛 puctxtintro).
    Proof.
      eapply asm_sem_intro; try solve [ reflexivity | eexists; reflexivity ].
      intros. inv H.
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      rewrite <- (stencil_matches_genv_next _ _ Hstencil_matches) in H9.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b =
                     Some (Internal proc_exit_user_function)).
      {
        assert (Hmodule:
          get_module_function proc_exit_user (proc_exit_user ↦ proc_exit_user_function)
            = OK (Some proc_exit_user_function)) by reflexivity.
        assert (HInternal:
          make_internal proc_exit_user_function
            = OK (AST.Internal proc_exit_user_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }

      exploit procexituser_spec; eauto 2.
      intros HW. exploit HW; eauto; clear HW.
      intros (f' & m0' & r_ & Hstep & Hincr & Hinject & Hnb & Hv).

      refine_split'; try eassumption; try reflexivity.
      simpl; unfold lift; simpl.
      exact (PowersetMonad.powerset_fmap_intro m0' Hinject).
    Qed.

  End WITHMEM.

End ASM_VERIFICATION.
