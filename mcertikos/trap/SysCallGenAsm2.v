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

Require Import TDispatch.
Require Import TSysCall.
Require Import SysCallGenAsmSource.
Require Import SysCallGenAsmData.
Require Import SysCallGenSpec.

Require Import LRegSet.
Require Import AbstractDataType.

Section ASM_VERIFICATION.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.
  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Lemma sys_sendtochan_pre_proof:
      forall ge (s: stencil) (rs: regset) m labd labd0 labd1 labd' rs0 rs' rs2 v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 chanid vargs sg b rs_yield bs,
        make_globalenv s (sys_sendtochan_pre ↦ sys_sendtochan_pre_function) tdispatch = ret ge ->
        trap_into_kernel_spec sys_sendtochan_pre s m rs labd labd0 vargs sg b
                              v0 v1 v2 v3 v4 v5 v6 chanid v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

        (* call kernel function*)
        trap_sendtochan_pre_spec labd0 = Some (labd1, Int.unsigned chanid) ->
        (* yield *)          
        find_symbol s sys_sendtochan_post = Some bs ->
        rs_yield = (Pregmap.init Vundef)#ESP <- (Val.add (rs ESP) (Vint (Int.repr 28)))
                                        #EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                        #EBX <- Vundef#EBP <- (rs#EBP)#RA <- (Vptr bs Int.zero) ->
        thread_sleep_spec labd1 rs_yield (Int.unsigned chanid) = Some (labd', rs') ->

        rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                              :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                          (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
        rs2 = (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                  #EBP <- (rs'#EBP)#PC <- (rs'#RA)) ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        high_level_invariant labd ->
        low_level_invariant (Mem.nextblock m) labd ->

        exists r_: regset,
          lasm_step (sys_sendtochan_pre ↦ sys_sendtochan_pre_function) (tdispatch (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    sys_sendtochan_pre s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs2)
                            (Pregmap.get l r_)).
    Proof.
      intros. destruct H0 as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
      (*rename H0 into HESP_STACK.*)
      assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.
      exploit Hexit; eauto.
      intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
      exploit Hsleep; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].
      exploit Hsendpre; eauto.
      intros [[b_pre [Hpre_symbol Hpre_fun]] prim_pre].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      
      exploit Hsys_sendtochan_pre; eauto 2. intros Hfunct.

      assert (Hblock: forall b0 o,
                        rs ESP = Vptr b0 o -> Ple (Genv.genv_next ge) b0 /\ Plt b0 (Mem.nextblock m)).
      {
        intros. exploit HESP_STACK; eauto.
        inv Hstencil_matches.
        rewrite stencil_matches_genv_next.
        trivial.
      }
      clear HESP_STACK.

      rewrite (Lregset_rewrite rs).
      refine_split'; try eassumption.
      rewrite HPC.
      econstructor; eauto.

      (* call proc_exit*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hexit_symbol.

      (* call proc_exit body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_prim_call _ b_exit); eauto.  

      econstructor; eauto 1.
      instantiate (4:= proc_exit_user).
      change positive with ident in *.
      rewrite prim_exit.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      simpl. econstructor; try eassumption; try reflexivity.
      { (* genv_next s <= b1 /\ b1 < Mem.nextblock m *)
        intros b1 o rsESP.
        rewrite <- (stencil_matches_genv_next _ _ Hstencil_matches).
        apply Hblock with o.
        exact rsESP.
      }

      inv Harg.
      constructor; eauto 1;
      repeat match goal with
               | [H0: extcall_arg _ _ _ _ |- extcall_arg _ _ _ _] => inv H0; econstructor; [reflexivity| eassumption]
               | [H1: list_forall2 _ _ _  |- list_forall2 _ _ _] => inv H1; constructor
               | H1: list_forall2 _ _ _  |- _ => inv H1
             end.
      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.
      Lregset_simpl_tac.

      (* call sendto_pre*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hpre_symbol.

      (* call pre body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_external _ b_pre); simpl; eauto 1.
      unfold trap_sendtochan_pre_spec in H1; elim_none_eqn Huctx.
      unfold uctx_arg2_spec in Huctx; repeat elim_none; auto 2.
      econstructor; eauto 1.
      econstructor; eauto 1.
      red. red. red. red. red. red.
      change positive with ident in *.
      rewrite prim_pre.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      constructor_gen_sem_intro.

      Lregset_simpl_tac.
      discriminate.
      Lregset_simpl_tac.

      (* movl    sendto_chan_post, RA *)
      one_step_forward'.
      unfold symbol_offset. unfold fundef.
      pose proof Hstencil_matches as Hstencil_matches'.
      inv Hstencil_matches. erewrite stencil_matches_symbols.
      rewrite H2.
      Lregset_simpl_tac.
      
      (* lea    %esp, 28(%esp) *)
      one_step_forward'.
      Lregset_simpl_tac.

      (* call svm_yield*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_sleep body*)
      eapply star_one; eauto.
      eapply (LAsm.exec_step_prim_call _ b_check); eauto 1.
      econstructor; eauto 1.
      instantiate (4:= thread_sleep).
      change positive with ident in *.
      rewrite prim_check.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      simpl.
      (*assert (HUCTX: forall v r, ZtoPreg v = Some r -> 
                                   Val.has_type (rs' r) Tint
                                   /\  val_inject (Mem.flat_inj (Mem.nextblock m))
                                                  (rs' r) (rs' r)).
        {
          eapply sys_yield_generate; eauto.
        }*)

      assert (HUCTX: forall v r, ZtoPreg v = Some r -> 
                                 Val.has_type (rs' r) Tint
                                 /\  val_inject (Mem.flat_inj (Mem.nextblock m))
                                                (rs' r) (rs' r)).
      {
        eapply sys_sendtochan_pre_generate; eauto.
      }
      econstructor; try eassumption; try reflexivity.
      inv Harg.
      repeat lazymatch goal with
      | H0: extcall_arg _ _ _ (Vint chanid) |- _ => fail
      | _ => match goal with
               | [H0: list_forall2 _ _ _ |- _ ] => inv H0
             end
      end.
      econstructor; eauto.
      inv H16. econstructor; eauto.
      Lregset_simpl_tac.
      simpl in H18. simpl.
      destruct (rs ESP); try inv H18.
      simpl. rewrite Int.add_zero. reflexivity.
      constructor.

      apply HUCTX.
      apply HUCTX.

      erewrite <- stencil_matches_symbols; eassumption.

      reflexivity.

      Lregset_simpl_tac.
      simpl.
      Lregset_simpl_tac.
      intros reg.
      unfold Lregset_fold; simpl.
      repeat (rewrite Pregmap.gsspec).
      simpl_destruct_reg.     
      exploit reg_false; try eassumption.
      intros HF. inv HF.
    Qed.


    Require Import LAsmModuleSemSpec.

    Lemma sys_sendtochan_pre_code_correct:
      asm_spec_le (sys_sendtochan_pre ↦ sys_sendtochan_pre_spec_low) 
                  (〚sys_sendtochan_pre ↦ sys_sendtochan_pre_function〛 tdispatch).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_sendtochan_pre_function)).
      {
        assert (Hmodule: get_module_function sys_sendtochan_pre (sys_sendtochan_pre ↦ sys_sendtochan_pre_function) 
                         = OK (Some sys_sendtochan_pre_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_sendtochan_pre_function = OK (AST.Internal sys_sendtochan_pre_function)) 
          by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_sendtochan_pre_proof; eauto 2. intros HW. exploit HW; eauto 2.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H8. inv inv_inject_neutral.
        lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.
    
    Lemma sys_yield_spec:
      forall ge (s: stencil) (rs: regset) m labd labd0 labd' rs0 rs' rs2 v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b rs_yield bs,
        make_globalenv s (sys_yield ↦ sys_yield_function) tdispatch = ret ge ->
        (*(forall b0 o,
             rs ESP = Vptr b0 o ->
             Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->*)

        trap_into_kernel_spec sys_yield s m rs labd labd0 vargs sg b
                              v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

        (* call kernel function*)
        (* yield *)          
        find_symbol s proc_start_user = Some bs ->
        rs_yield = (Pregmap.init Vundef) #ESP <- (rs#ESP) #EDI <- (rs#EDI) #ESI <- (rs#ESI)
                                         #EBX <- Vundef #EBP <- (rs#EBP) #RA <- (Vptr bs Int.zero)->
        thread_yield_spec labd0 rs_yield = Some (labd', rs') ->
        
        (* restore registers *)          
        rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                              :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                          (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
        rs2 = (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                  #EBP <- (rs'#EBP)#PC <- (rs'#RA))  ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        high_level_invariant labd ->
        low_level_invariant (Mem.nextblock m) labd ->

        exists r_: regset,
          lasm_step (sys_yield ↦ sys_yield_function) (tdispatch (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    sys_yield s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs2)
                            (Pregmap.get l r_)).
    Proof.
      intros. destruct H0 as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
      (*rename H0 into HESP_STACK.*)
      assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.

      exploit Hexit; eauto.
      intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
      exploit Hyield; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].
      (*exploit Hstart; eauto.
        intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].*)

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      
      exploit Hsys_yield; eauto 2. intros Hfunct.

      assert (Hblock: forall b0 o,
                        rs ESP = Vptr b0 o -> Ple (Genv.genv_next ge) b0 /\ Plt b0 (Mem.nextblock m)).
      {
        intros. exploit HESP_STACK; eauto.
        inv Hstencil_matches.
        rewrite stencil_matches_genv_next.
        trivial.
      }
      clear HESP_STACK.

      rewrite (Lregset_rewrite rs).
      refine_split'; try eassumption.
      rewrite HPC.
      econstructor; eauto.

      (* call proc_exit*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hexit_symbol.

      (* call proc_exit body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_prim_call _ b_exit); eauto.  

      econstructor; eauto 1.
      instantiate (4:= proc_exit_user).
      change positive with ident in *.
      rewrite prim_exit.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      simpl. econstructor; try eassumption; try reflexivity.
      { (* genv_next s <= b1 /\ b1 < Mem.nextblock m *)
        intros b1 o rsESP.
        rewrite <- (stencil_matches_genv_next _ _ Hstencil_matches).
        apply Hblock with o.
        exact rsESP.
      }

      inv Harg.
      constructor; eauto 1;
      repeat match goal with
               | [H0: extcall_arg _ _ _ _ |- extcall_arg _ _ _ _] => inv H0; econstructor; [reflexivity| eassumption]
               | [H1: list_forall2 _ _ _  |- list_forall2 _ _ _] => inv H1; constructor
               | H1: list_forall2 _ _ _  |- _ => inv H1
             end.
      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.
      Lregset_simpl_tac.

      (* movl    proc_start_user, RA *)
      one_step_forward'.
      unfold symbol_offset. unfold fundef.
      pose proof Hstencil_matches as Hstencil_matches'.
      inv Hstencil_matches. erewrite stencil_matches_symbols.
      rewrite H1.
      Lregset_simpl_tac' 2.

      (* call svm_yield*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_yield body*)
      eapply star_one; eauto.
      eapply (LAsm.exec_step_prim_call _ b_check); eauto 1.
      econstructor; eauto 1.
      instantiate (4:= thread_yield).
      change positive with ident in *.
      rewrite prim_check.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      simpl.
      assert (HUCTX: forall v r, ZtoPreg v = Some r -> 
                                 Val.has_type (rs' r) Tint
                                 /\  val_inject (Mem.flat_inj (Mem.nextblock m))
                                                (rs' r) (rs' r)).
      {
        eapply sys_yield_generate; eauto.
      }
      econstructor; try eassumption; try reflexivity.
      eapply HUCTX.
      eapply HUCTX.
      erewrite <- stencil_matches_symbols; eassumption.

      reflexivity.

      Lregset_simpl_tac.
      simpl.
      Lregset_simpl_tac.

      intros reg.
      unfold Lregset_fold; simpl.
      repeat (rewrite Pregmap.gsspec).
      simpl_destruct_reg.     
      exploit reg_false; try eassumption.
      intros HF. inv HF.
    Qed.

    Lemma sys_yield_code_correct:
      asm_spec_le (sys_yield ↦ sys_yield_spec_low) 
                  (〚sys_yield ↦ sys_yield_function〛 tdispatch).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_yield_function)).
      {
        assert (Hmodule: get_module_function sys_yield (sys_yield ↦ sys_yield_function) = OK (Some sys_yield_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_yield_function = OK (AST.Internal sys_yield_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_yield_spec; eauto 2. intros HW. exploit HW; eauto 2.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H7. inv inv_inject_neutral.
        lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.

    (*Lemma sys_run_vm_proof:
      forall ge (s: stencil) (rs: regset) m labd labd0 labd' rs01 rs0 rs' rs2 v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,
        make_globalenv s (sys_run_vm ↦ sys_run_vm_function) tdispatch = ret ge ->

        trap_into_kernel_spec sys_run_vm s m rs labd labd0 vargs sg b
                              v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

        rs01 = (Pregmap.init Vundef) #EDI <- (rs EDI) #EBP <- (rs EBP) ->
        vm_run_spec rs01 labd0 = Some (labd', rs') ->

        rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: RA :: nil) 
                          (undef_regs (List.map preg_of destroyed_at_call) rs))  ->

        rs2 = (rs0#EAX<- (rs'#EAX)#EBX <- (rs'#EBX)#EDX <- (rs'#EDX)
                  #ESI <- (rs'#ESI)#EDI <- (rs'#EDI)#EBP <- (rs'#EBP)
                  #PC <- (rs'#RA)) ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        high_level_invariant labd ->
        low_level_invariant (Mem.nextblock m) labd ->

        exists r_: regset,
          lasm_step (sys_run_vm ↦ sys_run_vm_function) (tdispatch (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    sys_run_vm s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs2)
                            (Pregmap.get l r_)).
    Proof.
      intros. destruct H0 as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
      exploit Hexit; eauto.
      intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
      exploit Hrun_vm; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      
      exploit Hsys_run_vm; eauto 2. intros Hfunct.

      assert (Hblock: forall b0 o,
                        rs ESP = Vptr b0 o -> Ple (Genv.genv_next ge) b0 /\ Plt b0 (Mem.nextblock m)).
      {
        intros. exploit HESP_STACK; eauto.
        inv Hstencil_matches.
        rewrite stencil_matches_genv_next.
        trivial.
      }
      clear HESP_STACK.

      rewrite (Lregset_rewrite rs).
      refine_split'; try eassumption.
      rewrite HPC.
      econstructor; eauto.

      (* call proc_exit*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hexit_symbol.

      (* call proc_exit body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_prim_call _ b_exit); eauto.  

      econstructor; eauto 1.
      instantiate (4:= proc_exit_user).
      change positive with ident in *.
      rewrite prim_exit.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      simpl. econstructor; try eassumption; try reflexivity.
      { (* genv_next s <= b1 /\ b1 < Mem.nextblock m *)
        intros b1 o rsESP.
        rewrite <- (stencil_matches_genv_next _ _ Hstencil_matches).
        apply Hblock with o.
        exact rsESP.
      }

      inv Harg.
      constructor; eauto 1;
      repeat match goal with
               | [H0: extcall_arg _ _ _ _ |- extcall_arg _ _ _ _] => inv H0; econstructor; [reflexivity| eassumption]
               | [H1: list_forall2 _ _ _  |- list_forall2 _ _ _] => inv H1; constructor
               | H1: list_forall2 _ _ _  |- _ => inv H1
             end.
      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.
      Lregset_simpl_tac.

      (* call svm_vm_run*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_run_vm body*)
      eapply star_one; eauto.
      eapply (LAsm.exec_step_prim_call _ b_check); eauto 1.
      econstructor; eauto 1.
      instantiate (4:= vmx_run_vm).
      change positive with ident in *.
      rewrite prim_check.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      simpl.
      (*assert (HUCTX: forall v r, ZtoPreg v = Some r -> 
                                   Val.has_type (rs' r) Tint
                                   /\  val_inject (Mem.flat_inj (Mem.nextblock m))
                                                  (rs' r) (rs' r)).
        {
          eapply sys_yield_generate; eauto.
        }*)

      assert (HUCTX: forall r, Val.has_type (rs' r) Tint
                               /\ val_inject (Mem.flat_inj (Mem.nextblock m))
                                             (rs' r) (rs' r)).
      {
        eapply sys_run_vm_generate; eauto.
      }
      econstructor; try eassumption; try reflexivity;
      try eapply HUCTX.
      erewrite <- stencil_matches_symbols; eassumption.

      Lregset_simpl_tac.
      intros. specialize (Hblock _ _ H0).
      erewrite <- stencil_matches_genv_next; eassumption.

      reflexivity.

      Lregset_simpl_tac.
      simpl.
      Lregset_simpl_tac.
      intros reg.
      unfold Lregset_fold; simpl.
      repeat (rewrite Pregmap.gsspec).
      simpl_destruct_reg.     
      exploit reg_false; try eassumption.
      intros HF. inv HF.
    Qed.

    Lemma sys_run_vm_code_correct:
      asm_spec_le (sys_run_vm ↦ sys_run_vm_spec_low) 
                  (〚sys_run_vm ↦ sys_run_vm_function〛 tdispatch).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_run_vm_function)).
      {
        assert (Hmodule: get_module_function sys_run_vm (sys_run_vm ↦ sys_run_vm_function) = OK (Some sys_run_vm_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_run_vm_function = OK (AST.Internal sys_run_vm_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_run_vm_proof; eauto 2. intros HW. exploit HW; eauto 2.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H6. inv inv_inject_neutral.
        lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.*)

      (*Hypothesis Hrun: exists b_run, 
                                  Genv.find_symbol tge sys_run_vm1 = Some b_run
                                  /\ Genv.find_funct_ptr tge b_run = Some (External TDISPATCH.PSVMRunVM).*)

      (*Hypothesis Herr: exists b_err, 
                         Genv.find_symbol tge uctx_set_errno' = Some b_err
                         /\ Genv.find_funct_ptr tge b_err = Some (External TDISPATCH.PUCTXSetErrno).*)

      (*Lemma sys_run_vm_spec:
        forall m abd abd' rs0 (rs:regset) v0 v1 v2 v3 v4 v5 v6 v7 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 args sg b rs1 vmcb xvm rs' bs abd1,
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
          rs PC = Vptr b Int.zero ->
          Genv.find_funct_ptr tge b = Some (Im_sys_run_vm) ->
          PPROC.proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx4 = Some abd -> 
          rs ESP <> Vundef ->
          (forall b1 o, rs ESP = Vptr b1 o -> Mem.tget m b1 = Some Tag_stack) ->

          (* call kernel function*)
          (* run vm *)          
          rs0 = ((Pregmap.init Vundef)
                   #ECX<- Vundef #EDI <- (rs EDI) #ESI <- (rs ESI)
                   #EBX <- Vundef#EBP <- (rs EBP) #EDX <- Vundef 
                   #ESP <- (rs ESP)#RA <- (Vptr bs Int.zero)) ->
          TDISPATCHARG.uctx_set_errno abd Int.zero = Some abd1 ->
          VVMCBOP.svm_run_vm abd1 rs0= Some (abd', vmcb, xvm) ->
          rs' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: RA :: nil) 
                            (undef_regs (List.map preg_of temporary_regs)
                                        (undef_regs (List.map preg_of destroyed_at_call_regs) rs))) ->
          rs1 = rs' # EBX <- (ZMap.get XVMST_EBX_OFFSET xvm)
                    # ECX <- (ZMap.get XVMST_ECX_OFFSET xvm)
                    # EDX <- (ZMap.get XVMST_EDX_OFFSET xvm)
                    # ESI <- (ZMap.get XVMST_ESI_OFFSET xvm)
                    # EDI <- (ZMap.get XVMST_EDI_OFFSET xvm)
                    # EBP <- (ZMap.get XVMST_EBP_OFFSET xvm)
                    # EAX <- (ZMap.get VMCB_V_RAX_LO_OFFSET vmcb)
                    # ESP <- (ZMap.get VMCB_V_RSP_LO_OFFSET vmcb)
                    # PC <- (ZMap.get VMCB_V_RIP_LO_OFFSET vmcb) ->
          
          args = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v4 :: Vint v5 :: Vint v6
                       :: Vint v7 :: Vint v8 :: Vint v9:: Vint v10 :: Vint v11 :: Vint v12
                       :: Vint v13 :: Vint v14 :: Vint v15:: Vint v16 ::nil) ->
          (* signature *)
          sg = mksignature (Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::
                                Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::nil) None ->
          extcall_arguments rs m sg args ->
          asm_invariant tge (State rs m) ->
          TDISPATCH.low_level_invariant (Mem.nextblock m) (Mem.get_abstract_data m)  ->
          forall HPROCSTART: Genv.find_symbol tge proc_start_user = Some bs,
          exists f' m0' r_, 
            plus lstep tge (State rs m) E0 (State r_ (Mem.put_abstract_data m0' abd'))
            /\ inject_incr (Mem.flat_inj (Mem.nextblock m)) f' 
            /\ Memtype.Mem.inject f' m m0'
            /\ Mem.nextblock m <= Mem.nextblock m0'              
            /\ (forall l,
                  Val.lessdef (Pregmap.get l rs1)
                              (Pregmap.get l r_)).
      Proof. 
        intros.
        generalize H; intros HPC.
        inv H12.
        rename H2 into HESP.
        rename H3 into HESPTAG.
        assert (HOS': 0 <= 64 <= Int.max_unsigned).
        split.
        omega.
        vm_discriminate.

        destruct Hexit as [b_exit [Hexit_symbol Hexit_fun]].
        destruct Hrun as [b_check [Hcheck_symbol Hcheck_fun]].
        destruct Herr as [b_err [Herr_symbol Herr_fun]].

        destruct (SYSCALLGEN_ASM_DATA.sys_run_generate _ _ _ _ _ _ _ _ H1 H6 H13 H5) as 
            [HVM[HXV[HIK HIH]]].
 
        caseEq(Mem.alloc Tag_stack m 0 12).
        intros m1 b0 HALC.
        unfold LdataOp in *.
        specialize (Mem.valid_access_alloc_same _ _ _ _ _ HALC).
        intros.

        assert (HV1: Mem.valid_access m1 Mint32 b0 4 Freeable).
        eapply H2; auto; simpl; try omega.
        apply Z.divide_refl.
        eapply Mem.valid_access_implies with (p2:= Writable) in HV1; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (rs ESP) HV1) as [m2 HST1].

        assert (HV2: Mem.valid_access m2 Mint32 b0 8 Freeable).
        eapply Mem.store_valid_access_1; eauto.
        eapply H2; auto; simpl; try omega.
        unfold Z.divide.
        exists 2; omega.
        eapply Mem.valid_access_implies with (p2:= Writable) in HV2; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ Vundef HV2) as [m3 HST2].

        assert (HV3: Mem.valid_access m3 Mint32 b0 0 Freeable).
        eapply Mem.store_valid_access_1; eauto.
        eapply Mem.store_valid_access_1; eauto.
        eapply H2; auto; simpl; try omega.
        apply Zdivide_0.
        eapply Mem.valid_access_implies with (p2:= Writable) in HV3; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (Vint Int.zero) HV3) as [m4 HST3].

        assert (HV4: Mem.range_perm m4 b0 0 12 Cur Freeable).
        unfold Mem.range_perm.
        intros.
        do 3 (eapply Mem.perm_store_1; eauto).
        eapply Mem.perm_alloc_2; eauto.
        destruct (Mem.range_perm_free _ _ _ _ HV4) as [m5 HFree].

        clear H2.
        unfold LdataOp in *.
        esplit. esplit. esplit.
        split.
        econstructor; eauto.

        (* call proc_exit*)
        econstructor; eauto.        
        pc_add_simpl.
        simpl.
        trivial.
        rewrite H.
        simpl.
        change (Int.add Int.zero Int.one) with (Int.repr 1).
        unfold symbol_offset.
        rewrite Hexit_symbol.

        (* call proc_exit body*)
        econstructor; eauto.
        eapply (LSemantics.exec_step_prim_call _ b_exit); eauto 1; repeat simpl_Pregmap. 
        trivial.
        simpl in *.
        assert (HAG: forall av1 av2,
                       extcall_arg rs m (Locations.S (Outgoing av1 Tint)) (Vint av2) ->
                       extcall_arg (rs # RA <- (Vptr b (Int.repr 1))) # PC <-
                                   (Vptr b_exit Int.zero)
                                   m (Locations.S (Outgoing av1 Tint)) (Vint av2)).
        intros.
        inv H2; econstructor; eauto; simpl in *; repeat simpl_Pregmap.
        inv H11.
        constructor; trivial;
        repeat match goal with
          | [H0: extcall_arg _ _ _ _ |- extcall_arg _ _ _ _] => apply HAG; apply H0
          | [H0: extcall_arg _ _ _ _, H1: list_forall2 _ _ _  |- list_forall2 _ _ _] =>
            inv H1;
            constructor; trivial
        end.

        simpl.
        econstructor; eauto.
        subst uctx4 uctx3 uctx2 uctx1.
        trivial.

        repeat simpl_Pregmap.
        (* Pallocframe *)
        econstructor; eauto.
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        pc_add_simpl.
        simpl.
        repeat simpl_Pregmap.
        change (Int.unsigned (Int.add Int.zero (Int.repr 8))) with 8.
        change (Int.unsigned (Int.add Int.zero (Int.repr 4))) with 4.
        apply Mem.alloc_put_abstract_data with (a:= abd) in HALC.
        unfold TDISPATCH.abstract_data in *.
        rewrite HALC.
        apply Mem.store_put_abstract_data with (a:= abd) in HST1.
        rewrite HST1.
        apply Mem.store_put_abstract_data with (a:= abd) in HST2.
        rewrite HST2.
        reflexivity.

        (* movl 0, %eax *)
        eapply star_left; eauto.
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        change (Int.unsigned (Int.add (Int.repr 1) Int.one)) with 2.
        pc_add_simpl.
        simpl.
        trivial.

        (* movl    %eax, 0(%esp) *)
        econstructor; eauto.
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        change (Int.unsigned (Int.add (Int.add (Int.repr 1) Int.one) Int.one)) with 3.
        pc_add_simpl.

        simpl.
        unfold LSemantics.exec_storeex.
        unfold TDISPATCH.exec_storeex.
        simpl.
        rewrite Mem.get_put_abstract_data.
        rewrite HIK, HIH.
        unfold LSemantics.exec_storel.
        simpl.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero Int.zero))) with 0.
        repeat simpl_Pregmap.
        apply Mem.store_put_abstract_data with (a:= abd) in HST3.
        unfold TDISPATCH.abstract_data in *.
        rewrite HST3.
        trivial.

        (* call uctx_set_errno*)
        econstructor; eauto.        
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        change (Int.unsigned (Int.add (Int.add (Int.add (Int.repr 1) Int.one) Int.one) Int.one)) with 4.
        pc_add_simpl.
        simpl.
        trivial.
        change (Int.add (Int.add (Int.add (Int.add (Int.repr 1) Int.one) Int.one) Int.one) Int.one) with (Int.repr 5).
        unfold symbol_offset.
        rewrite Herr_symbol.

        (* call uctx_set_errno body*)
        econstructor; eauto.
        eapply (LSemantics.exec_step_external _ b_err); eauto 1.
        econstructor; eauto.
        rewrite Mem.get_put_abstract_data.
        apply H5.
        constructor; trivial.
        econstructor; eauto.
        simpl.
        apply Mem.store_put_abstract_data with (a:= abd) in HST3.
        erewrite Mem.load_store_same; eauto.
        trivial.
        constructor; trivial.

        discriminate.
        discriminate.
        intros.
        inv H2.
        erewrite Mem.tget_put_abstract_data.
        do 3 (erewrite Mem.tget_store; eauto).
        eapply Mem.tget_alloc_same; eauto.

        (*freeframe*) 
        simpl.
        repeat (simpl_Pregmap).
        econstructor; eauto.
        econstructor; eauto.
        repeat (simpl_Pregmap).
        trivial.
        pc_add_simpl.

        simpl.
        change (Int.unsigned (Int.add Int.zero (Int.repr 8))) with 8.
        change (Int.unsigned (Int.add Int.zero (Int.repr 4))) with 4.
        repeat rewrite Mem.load_put_abstract_data.
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_same; eauto.
        
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_other; eauto; simpl. 
        erewrite Mem.load_store_same; eauto.
        erewrite register_type_load_result.

        rewrite Mem.put_put_abstract_data.
        apply Mem.free_put_abstract_data with (a:= abd1) in HFree.
        unfold TDISPATCH.abstract_data in *.
        rewrite HFree.
        trivial.
        apply WT_RS.
        right. left. omega.
        right. right. omega.
        right. right. omega. 

        (* movl    proc_start_user, RA *)
        econstructor; eauto.
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        pc_add_simpl.

        simpl.
        repeat simpl_Pregmap.
        unfold symbol_offset.
        rewrite HPROCSTART.
        trivial.

        (* call svm_run_vm*)
        repeat simpl_Pregmap.
        econstructor; eauto.        
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        change (Int.unsigned (Int.add (Int.add (Int.repr 5) Int.one) Int.one)) with 7.
        pc_add_simpl.
        simpl.
        trivial.
        unfold symbol_offset.
        rewrite Hcheck_symbol.

        (* call svs_run_vm body*)
        eapply star_one; eauto.
        eapply (LSemantics.exec_step_prim_call _ b_check); eauto 1.
        trivial.
        constructor; trivial.
        unfold TDISPATCH.abstract_data in *.
        econstructor.
        rewrite Mem.get_put_abstract_data.
        eassumption.
        instantiate (1:= m5).
        rewrite Mem.put_put_abstract_data.
        trivial.
        trivial.
        trivial.
        apply HVM.
        rewrite Mem.nextblock_put_abstract_data.
        rewrite (Mem.nextblock_free _ _ _ _ _ HFree); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST3); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST2); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST1); trivial.
        erewrite Mem.nextblock_alloc; eauto.
        intros.
        apply val_inject_incr with (Mem.flat_inj (Mem.nextblock m)); trivial.
        unfold inject_incr.
        unfold Mem.flat_inj.
        intros.
        destruct (zlt b1 (Mem.nextblock m)).
        rewrite zlt_true; try omega.
        assumption.
        inv H3.
        apply HVM; trivial.

        apply HXV.
        rewrite Mem.nextblock_put_abstract_data.
        rewrite (Mem.nextblock_free _ _ _ _ _ HFree); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST3); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST2); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST1); trivial.
        erewrite Mem.nextblock_alloc; eauto.
        intros.
        apply val_inject_incr with (Mem.flat_inj (Mem.nextblock m)); trivial.
        unfold inject_incr.
        unfold Mem.flat_inj.
        intros.
        destruct (zlt b1 (Mem.nextblock m)).
        rewrite zlt_true; try omega.
        assumption.
        inv H3.
        apply HXV; trivial.

        trivial.
        trivial.
        trivial.
 
        split.
        apply inject_incr_refl.
        split.
        assert (HFB: forall b1 delta, Mem.flat_inj (Mem.nextblock m) b1 <> Some (b0, delta)).
        intros.
        unfold Mem.flat_inj.
        red; intros.
        destruct (zlt b1 (Mem.nextblock m)).
        inv H2.
        rewrite (Mem.alloc_result _ _ _ _ _ HALC) in l.
        omega.
        inv H2.

        eapply Mem.free_right_inject; eauto; [|intros; specialize (HFB b1 delta); apply HFB; trivial].
        do 3 (eapply Mem.store_outside_inject; eauto; [|intros b1 delta; intros; specialize (HFB b1 delta); apply HFB; trivial]).
        eapply Mem.alloc_right_inject; eauto.

        inv INJECT_NEUTRAL.
        apply Mem.neutral_inject; trivial.
        
        split.
        rewrite (Mem.nextblock_free _ _ _ _ _ HFree); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST3); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST2); trivial.
        rewrite (Mem.nextblock_store _  _ _ _ _ _ HST1); trivial.
        rewrite (Mem.nextblock_alloc _ _ _ _ _ HALC) ; eauto.
        omega.
       
        simpl.
        unfold nextinstr_nf.
        unfold nextinstr.
        unfold loc_external_result.
        simpl.
        intros reg.        
        repeat (rewrite Pregmap.gsspec).
        
        simpl_destruct_reg.
        
        trivial.
      Qed.
*)

      (*Hypothesis Hcreate: exists b_create, 
                                  Genv.find_symbol tge sys_proc_create1 = Some b_create
                                  /\ Genv.find_funct_ptr tge b_create = Some (External TDISPATCH.PSysProcCreate).*)

    (*Lemma sys_proc_create_spec:
        forall ge (s: stencil) (rs: regset) m rs0 n bstack busercode buserstart belf labd labd0 labd1 labd2 labd3 labd' arg1
               rs' v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 v12 v13 v14 v15 v16 vargs sg b bentry,

          make_globalenv s (sys_spawn ↦ sys_spawn_function) tdispatch = ret ge ->
          (*(forall b0 o,
             rs ESP = Vptr b0 o ->
             Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->*)

          syscall_spec sys_spawn s m rs rs' rs0 labd labd0 labd3 labd' vargs sg b
                       v0 v1 v2 v3 v4 v5 v6 arg1 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

          (* call kernel function*)
          (* read arguements*)
          uctx_arg1_spec labd0 = Some (Int.unsigned arg1) ->
          find_symbol s ELF_ENTRY_LOC = Some bentry ->
          Mem.load Mint32 m bentry (Int.unsigned arg1 * 4) = Some (Vptr busercode Int.zero) ->
          find_symbol s proc_start_user = Some buserstart ->
          find_symbol s ELF_LOC = Some belf ->
          find_symbol s STACK_LOC = Some bstack ->
          (exists fun_id, find_symbol s fun_id = Some busercode) ->
          0 <= Int.unsigned arg1 < num_proc ->

          (* proc create*)
          proc_create_spec labd0 bstack buserstart busercode Int.zero = Some (labd1, Int.unsigned n) ->
          (* rewrite return value*)
          uctx_set_retval1_spec labd1 (Int.unsigned n) = Some labd2 ->
          uctx_set_errno_spec labd2 0 = Some labd3 ->

          asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
          high_level_invariant labd ->
          low_level_invariant (Mem.nextblock m) labd ->

          exists r_: regset,
            lasm_step (sys_spawn ↦ sys_spawn_function) (tdispatch (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                      sys_spawn s rs (m, labd) r_ (m, labd')
            /\ (forall l,
                  Val.lessdef (Pregmap.get l rs0)
                              (Pregmap.get l r_)).
      Proof.
        intros. destruct H0 as [Hk[Hst [Hr _]]]. subst.
        (*rename H0 into HESP_STACK.*)
        destruct Hk as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
        assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.

        destruct H7 as [fun_id Hfind_symbol].

        exploit Hstart; eauto.
        intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].
        exploit Hexit; eauto.
        intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
        exploit Hcreate; eauto.
        intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].

        exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
        intros Hstencil_matches.
        
        exploit Hsys_spawn; eauto 2. intros Hfunct.

        assert (Hblock: forall b0 o,
                          rs ESP = Vptr b0 o -> Ple (Genv.genv_next ge) b0 /\ Plt b0 (Mem.nextblock m)).
        {
          intros. exploit HESP_STACK; eauto.
          inv Hstencil_matches.
          rewrite stencil_matches_genv_next.
          trivial.
        }
        clear HESP_STACK.

        rewrite (Lregset_rewrite rs).
        refine_split'; try eassumption.
        rewrite HPC.
        econstructor; eauto.

        (* call proc_exit*)
        one_step_forward 0.
        reflexivity.
        Lregset_simpl_tac.
        change (Int.add Int.zero Int.one) with (Int.repr 1).
        unfold symbol_offset. unfold fundef.
        rewrite Hexit_symbol.

        (* call proc_exit body*)
        econstructor; eauto 1.
        eapply (LAsm.exec_step_prim_call _ b_exit); eauto.  

        econstructor; eauto 1.
        instantiate (4:= proc_exit_user).
        change positive with ident in *.
        subrewrite'.
        refine_split'; try reflexivity.
        econstructor; eauto 1.
        refine_split'; try reflexivity; try eassumption.
        simpl. econstructor; try eassumption; try reflexivity.
        { (* genv_next s <= b1 /\ b1 < Mem.nextblock m *)
          intros b1 o rsESP.
          rewrite <- (stencil_matches_genv_next _ _ Hstencil_matches).
          apply Hblock with o.
          exact rsESP.
        }

        inv Harg.
        constructor; eauto 1;
        repeat match goal with
                 | [H0: extcall_arg _ _ _ _ |- extcall_arg _ _ _ _] => inv H0; econstructor; [reflexivity| eassumption]
                 | [H1: list_forall2 _ _ _  |- list_forall2 _ _ _] => inv H1; constructor
                 | H1: list_forall2 _ _ _  |- _ => inv H1
               end.
        inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.
        Lregset_simpl_tac.

        (* call svm_proc_create*)
        one_step_forward 1.
        reflexivity.
        Lregset_simpl_tac.
        change (Int.add (Int.repr 1) Int.one) with (Int.repr 2).
        unfold symbol_offset. unfold fundef.
        rewrite Hcheck_symbol.

        (* call svs_proc_create body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_external _ b_check); eauto 1.
        econstructor; eauto 1.
        econstructor; eauto 1.
        red. red. red. red. red. red.
        change positive with ident in *.
        subrewrite'.
        refine_split'; try reflexivity.
        econstructor; eauto 1.
        refine_split'; try reflexivity; try eassumption.
        destruct H8.
        constructor_gen_sem_intro.
        
        discriminate.
        Lregset_simpl_tac.

        (* call proc_start*)
        one_step_forward 2.
        reflexivity.
        Lregset_simpl_tac.
        change (Int.add (Int.repr 2) Int.one) with (Int.repr 3).
        unfold symbol_offset. unfold fundef.
        rewrite Hstart_symbol.

        (* call proc start body*)
        eapply star_one; eauto.
        eapply (LAsm.exec_step_prim_call _ b_start); eauto 1.
        econstructor; eauto 1.
        instantiate (4:= proc_start_user).
        change positive with ident in *.
        subrewrite'.
        refine_split'; try reflexivity.
        econstructor; eauto 1.
        refine_split'; try reflexivity; try eassumption.
        simpl.
        assert (HUCTX': forall i, 0<= i < UCTXT_SIZE -> 
                                  let v:= (ZMap.get i rs') in
                                  Val.has_type v Tint 
                                  /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
        {
          inv H12. inv inv_inject_neutral.
          eapply sys_proc_create_generate; try eassumption.
          intros. subst v.
          inv_proc; try (split; constructor).
          rewrite ZMap.gi.
          split; constructor.
        }
        econstructor; try eassumption; try reflexivity.
        eapply HUCTX'.
        eapply HUCTX'.

        inv Hstencil_matches. erewrite stencil_matches_symbols in Hstart_symbol.
        rewrite H4 in Hstart_symbol. inv Hstart_symbol.
        reflexivity.

        reflexivity.

        Lregset_simpl_tac.
        simpl.
        Lregset_simpl_tac.
        intros reg.
        unfold Lregset_fold; simpl.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.     
        constructor.
      Qed.

    Lemma sys_spawn_code_correct:
      asm_spec_le (sys_spawn ↦ sys_proccreate_spec_low) 
                  (〚sys_spawn ↦ sys_spawn_function〛 tdispatch).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_spawn_function)).
      {
        assert (Hmodule: get_module_function sys_spawn (sys_spawn ↦ sys_spawn_function) = OK (Some sys_spawn_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_spawn_function = OK (AST.Internal sys_spawn_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [Hk _]. subst.
        destruct Hk as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_proc_create_spec; eauto 2. intros HW. exploit HW; eauto 2.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H13. inv inv_inject_neutral.
        lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.*)

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

      Lemma pgf_handler_spec:
        forall ge (s: stencil) (rs: regset) m labd labd0 labd1 labd' rs0 vadr rs' v0 v1 v2 v3 v5 v6 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,

          make_globalenv s (pgf_handler ↦ pgf_handler_function) tdispatch = ret ge ->
          (*(forall b0 o,
             rs ESP = Vptr b0 o ->
             Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->*)

          syscall_spec pgf_handler s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                       v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

          (* call kernel function*)
          (* read argument *)
          vadr = fst (ti labd0) ->
          ptfault_resv_spec (Int.unsigned vadr) labd0 = Some labd1 ->

          asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
          (*high_level_invariant labd ->*)
          low_level_invariant (Mem.nextblock m) labd ->

          exists f' m0' r_, 
            lasm_step (pgf_handler ↦ pgf_handler_function) (tdispatch (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                      pgf_handler s rs 
                      (m, labd) r_ (m0', labd')
            /\ inject_incr (Mem.flat_inj (Mem.nextblock m)) f' 
            /\ Memtype.Mem.inject f' m m0'
            /\ (Mem.nextblock m <= Mem.nextblock m0')%positive
            /\ (forall l,
                  Val.lessdef (Pregmap.get l rs0)
                              (Pregmap.get l r_)).
      Proof.
        intros. 
 
        caseEq(Mem.alloc m 0 12).
        intros m1 b0 HALC.
        exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
        intros Hstencil_matches.
        
        assert (Hblock: Ple (Genv.genv_next ge) b0 /\ Plt b0 (Mem.nextblock m1)).
        {
          erewrite Mem.nextblock_alloc; eauto.
          apply Mem.alloc_result in HALC.
          rewrite HALC. 
          inv H3. inv inv_inject_neutral.
          inv Hstencil_matches.
          rewrite stencil_matches_genv_next.
          lift_unfold.
          split; xomega.
        }

        destruct H0 as [Hk[Hst [Hr _]]]. subst.
        destruct Hk as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.

        assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.

        exploit Hstart; eauto.
        intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].
        exploit Hexit; eauto.
        intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
        exploit Hget; eauto.
        intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].
        exploit Hpgfr; eauto.
        intros [[b_pgfr [Hpgfr_symbol Hpgfr_fun]] prim_pgfr].

        specialize (Mem.valid_access_alloc_same _ _ _ _ _ HALC). intros.
        assert (HV1: Mem.valid_access m1 Mint32 b0 4 Freeable).
        {
          eapply H0; auto; simpl; try omega.
          apply Z.divide_refl.
        }
        eapply Mem.valid_access_implies with (p2:= Writable) in HV1; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (rs ESP) HV1) as [m2 HST1].

        assert (HV2: Mem.valid_access m2 Mint32 b0 8 Freeable).
        {
          eapply Mem.store_valid_access_1; eauto.
          eapply H0; auto; simpl; try omega.
          unfold Z.divide.
          exists 2; omega.
        }
        eapply Mem.valid_access_implies with (p2:= Writable) in HV2; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ Vundef HV2) as [m3 HST2].

        assert (HV3: Mem.valid_access m3 Mint32 b0 0 Freeable).
        {
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply H0; auto; simpl; try omega.
          apply Zdivide_0.
        }
        eapply Mem.valid_access_implies with (p2:= Writable) in HV3; [|constructor].
        destruct (Mem.valid_access_store _ _ _ _ (Vint (fst (ti labd0))) HV3) as [m4 HST3].

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

        assert (HUCTX: ikern labd0 = true
                       /\ ihost labd0 = true 
                       /\ ikern labd1 = true
                       /\ ihost labd1 = true
                       /\(forall i, 0<= i < UCTXT_SIZE -> 
                                    let v:= (ZMap.get i rs') in
                                    Val.has_type v Tint 
                                    /\ val_inject (Mem.flat_inj (Mem.nextblock m5)) v v)).
        {
          eapply pgf_handler_generate; eauto.
          intros. subst v.
          inv_proc; try (split; constructor).
          rewrite ZMap.gi.
          split; constructor.
        }
        destruct HUCTX as [ik[ih[ik1[ih1 HUCTX]]]].

        exploit Hpgf_handler; eauto 2. intros Hfunct.

        rewrite (Lregset_rewrite rs).
        refine_split'; try eassumption.
        rewrite HPC.
        econstructor; eauto.

        (* call proc_exit*)
        one_step_forward'.
        Lregset_simpl_tac.
        unfold symbol_offset. unfold fundef.
        rewrite Hexit_symbol.

        (* call proc_exit body*)
        econstructor; eauto 1.
        eapply (LAsm.exec_step_prim_call _ b_exit); eauto.  

        econstructor; eauto 1.
        instantiate (4:= proc_exit_user).
        change positive with ident in *.
        rewrite prim_exit.
        refine_split'; try reflexivity.
        econstructor; eauto 1.
        refine_split'; try reflexivity; try eassumption.
        simpl. econstructor; try eassumption; try reflexivity.

        inv Harg.
        constructor; eauto 1;
        repeat match goal with
                 | [H0: extcall_arg _ _ _ _ |- extcall_arg _ _ _ _] => inv H0; econstructor; [reflexivity| eassumption]
                 | [H1: list_forall2 _ _ _  |- list_forall2 _ _ _] => inv H1; constructor
                 | H1: list_forall2 _ _ _  |- _ => inv H1
               end.
        inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.
        Lregset_simpl_tac.

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
        Lregset_simpl_tac.

        (* call trap_get *)
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hcheck_symbol.
        Lregset_simpl_tac.

        (* call trap_get body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_prim_call _ b_check); eauto 1.
        econstructor; eauto 1.
        instantiate (4:= trap_get).
        change positive with ident in *.
        rewrite prim_check.
        refine_split'; try reflexivity.
        econstructor; eauto. simpl.
        econstructor; eauto.
        Lregset_simpl_tac.
        unfold trap_info_get_spec.

        (* movl    %eax, 0(%esp) *)
        one_step_forward'.
        unfold exec_storeex, LoadStoreSem2.exec_storeex2.
        simpl; Lregset_simpl_tac. rewrite ik, ih.
        unfold Asm.exec_store; simpl.
        Lregset_simpl_tac. lift_trivial.
        change (Int.unsigned (Int.add Int.zero (Int.add Int.zero Int.zero))) with 0.
        rewrite HST3. reflexivity.
        unfold set; simpl.

        (* call svm_pgf_resv*)
        one_step_forward'.
        unfold symbol_offset. unfold fundef.
        rewrite Hpgfr_symbol.
        Lregset_simpl_tac.

        (* call svm_pgf_resv body*)
        econstructor; eauto.
        eapply (LAsm.exec_step_external _ b_pgfr); simpl; eauto 2.
        econstructor; eauto.
        econstructor; eauto. simpl; lift_trivial.
        erewrite Mem.load_store_same; eauto.
        constructor; trivial.

        econstructor; eauto 1.
        red. red. red. red. red. red.
        change positive with ident in *.
        rewrite prim_pgfr.
        refine_split'; try reflexivity.
        econstructor; eauto 1.
        refine_split'; try reflexivity; try eassumption.
        constructor_gen_sem_intro.

        Lregset_simpl_tac.
        lift_trivial.
        intros. inv H1.
        rewrite Hnextblock4; assumption.

        discriminate.
        discriminate.

        Lregset_simpl_tac.

        (*freeframe*) 
        one_step_forward'.
        lift_trivial.
        change (Int.unsigned (Int.add Int.zero (Int.repr 4))) with 4.
        change (Int.unsigned (Int.add Int.zero (Int.repr 8))) with 8.
        unfold set; simpl.
        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_same; eauto.

        erewrite Mem.load_store_other; eauto; simpl.
        erewrite Mem.load_store_other; eauto; simpl.  
        erewrite Mem.load_store_same; eauto.
        erewrite register_type_load_result.

        rewrite HFree. reflexivity.
        inv H3.
        apply inv_reg_wt.
        right. left. omega.
        right. right. omega.
        right. right. omega.
        Lregset_simpl_tac.

        (* call proc_start*)
        one_step_forward'.
        Lregset_simpl_tac.
        unfold symbol_offset. unfold fundef.
        rewrite Hstart_symbol.

        (* call proc start body*)
        eapply star_one; eauto.
        eapply (LAsm.exec_step_prim_call _ b_start); eauto 1.
        econstructor; eauto 1.
        instantiate (4:= proc_start_user).
        change positive with ident in *.
        rewrite prim_start.
        refine_split'; try reflexivity.
        econstructor; eauto 1.
        refine_split'; try reflexivity; try eassumption.
        simpl.
        econstructor; try eassumption; try reflexivity.
        eapply HUCTX.
        eapply HUCTX.

        inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.

        reflexivity.
        reflexivity.

        assert (HFB: forall b1 delta, Mem.flat_inj (Mem.nextblock m) b1 <> Some (b0, delta)).
        {
          intros. unfold Mem.flat_inj.
          red; intros.
          destruct (plt b1 (Mem.nextblock m)). inv H1.
          rewrite (Mem.alloc_result _ _ _ _ _ HALC) in p.
          xomega. inv H1.
        }
        eapply Mem.free_right_inject; eauto 1; [|intros; specialize (HFB b1 delta); apply HFB; trivial].
        repeat (eapply Mem.store_outside_inject; [ | | eassumption] 
                ; [|intros b1 delta; intros; specialize (HFB b1 delta); apply HFB; trivial]).
        eapply Mem.alloc_right_inject; eauto 1.
        inv H3. inv inv_inject_neutral.
        apply Mem.neutral_inject; trivial.

        rewrite (Mem.nextblock_free _ _ _ _ _ HFree); trivial.
        rewrite Hnextblock4.
        rewrite (Mem.nextblock_alloc _ _ _ _ _ HALC); eauto.
        clear. abstract xomega.

        Lregset_simpl_tac.
        simpl.
        Lregset_simpl_tac.
        intros reg.
        unfold Lregset_fold; simpl.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.     
        constructor.
      Qed.

    Lemma pgf_handler_code_correct:
      asm_spec_le (pgf_handler ↦ pagefault_handler_spec_low) 
                  (〚pgf_handler ↦ pgf_handler_function〛 tdispatch).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal pgf_handler_function)).
      {
        assert (Hmodule: get_module_function pgf_handler (pgf_handler ↦ pgf_handler_function) = OK (Some pgf_handler_function)) by
            reflexivity.
        assert (HInternal: make_internal pgf_handler_function = OK (AST.Internal pgf_handler_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [Hk _]. subst.
        destruct Hk as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit pgf_handler_spec; eauto 2. intros HW. exploit HW; eauto 2.
      intros (f' & m0' & r_ & Hstep & Hincr & Hv & Hnext & HV).
      refine_split'; try eassumption; try reflexivity.
      - lift_unfold. split; [assumption| reflexivity]. 
      - esplit; reflexivity.
    Qed.

  End WITHMEM.

End ASM_VERIFICATION.
