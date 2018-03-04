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

    Lemma sys_sendtochan_post_proof:
      forall ge (s: stencil) (rs: regset) m labd labd1 labd' rs0 rs' b,
        make_globalenv s (sys_sendtochan_post ↦ sys_sendtochan_post_function) tdispatch = ret ge ->        
        trap_sendtochan_post_spec labd = Some labd1 ->
        proc_start_user_spec labd1 = Some (labd', rs') ->
        rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                              :: IR ECX :: IR EAX :: RA :: nil) 
                          (undef_regs (List.map preg_of destroyed_at_call) rs))
                # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                # PC <- (ZMap.get U_EIP rs') ->
        (forall i, 0 <= i < UCTXT_SIZE ->
                   let v:= (ZMap.get i rs') in
                   Val.has_type v AST.Tint) ->
        (forall i, 0 <= i < UCTXT_SIZE ->
                   let v:= (ZMap.get i rs') in
                   val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
        find_symbol s sys_sendtochan_post = Some b ->
        rs PC = Vptr b Int.zero ->
        rs ESP <> Vundef ->
        (forall b0 o,
           rs ESP = Vptr b0 o ->
           Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        high_level_invariant labd ->
        low_level_invariant (Mem.nextblock m) labd ->
        exists r_: regset,
          lasm_step (sys_sendtochan_post ↦ sys_sendtochan_post_function) 
                    (tdispatch (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    sys_sendtochan_post s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs0)
                            (Pregmap.get l r_)).
    Proof.
      intros. subst.
      assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.
      exploit Hstart; eauto.
      intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].
      exploit Hsendpost; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.

      exploit Hsys_sendtochan_post; eauto 2. intros Hfunct.

      assert (Hblock: forall b0 o,
                        rs ESP = Vptr b0 o -> Ple (Genv.genv_next ge) b0 
                                              /\ Plt b0 (Mem.nextblock m)).
      {
        intros. exploit H8; eauto.
        inv Hstencil_matches.
        rewrite stencil_matches_genv_next.
        trivial.
      }
      clear H8.

      rewrite (Lregset_rewrite rs).
      refine_split'; try eassumption.
      rewrite H6.
      econstructor; eauto.

      (* call send_post *)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_is_chan_ready body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_external _ b_check); simpl; eauto 1.
      unfold trap_sendtochan_post_spec in H0; elim_none_eqn Hsend.
      unfold syncsendto_chan_post_spec in Hsend; repeat elim_none; auto.
      econstructor; eauto 1.
      econstructor; eauto 1.
      red. red. red. red. red. red.
      change positive with ident in *.
      rewrite prim_check.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      constructor_gen_sem_intro.

      Lregset_simpl_tac.
      discriminate.

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
      assert (HUCTX': forall i, 0<= i < UCTXT_SIZE -> 
                                let v:= (ZMap.get i rs') in
                                Val.has_type v Tint 
                                /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      {
        eapply sys_sendtochan_post_generate; try eassumption.
      }
      econstructor; try eassumption; try reflexivity.
      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.

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

    Lemma sys_sendtochan_post_code_correct:
      asm_spec_le (sys_sendtochan_post ↦ sys_sendtochan_post_spec_low) 
                  (〚sys_sendtochan_post ↦ sys_sendtochan_post_function〛 tdispatch).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_sendtochan_post_function)).
      {
        assert (Hmodule: get_module_function sys_sendtochan_post (sys_sendtochan_post ↦ sys_sendtochan_post_function) 
                         = OK (Some sys_sendtochan_post_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_sendtochan_post_function 
                           = OK (AST.Internal sys_sendtochan_post_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H6 in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_sendtochan_post_proof; eauto 2.
      inv H10.
      inv inv_inject_neutral.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.

    Lemma sys_dispatch_spec:
      forall ge (s: stencil) (rs: regset) m labd labd0 labd1 labd' rs0 rs' v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,
        make_globalenv s (syscall_dispatch ↦ sys_dispatch_function) tdispatch = ret ge ->
        (*(forall b0 o,
           rs ESP = Vptr b0 o ->
           Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->*)
        syscall_spec syscall_dispatch s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                     v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        
        (* call kernel function*)
        sys_dispatch_c_spec s m labd0 = Some labd1 ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        (*high_level_invariant labd ->*)
        (*low_level_invariant (Mem.nextblock m) labd ->*)
        exists r_: regset,
          lasm_step (syscall_dispatch ↦ sys_dispatch_function) 
                    (tdispatch (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    syscall_dispatch s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs0)
                            (Pregmap.get l r_)).
    Proof.
      intros. destruct H0 as [Hk[Hst [Hr _]]]. subst.
      destruct Hk as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
      assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.
      exploit Hstart; eauto.
      intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].
      exploit Hexit; eauto.
      intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
      exploit Hdispatch_c; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.

      exploit Hsys_dispatch_c; eauto 2. intros Hfunct.

      assert (Hblock: forall b0 o,
                        rs ESP = Vptr b0 o -> Ple (Genv.genv_next ge) b0 
                                              /\ Plt b0 (Mem.nextblock m)).
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

      (* call svm_is_chan_ready*)
      one_step_forward'.
      Lregset_simpl_tac.
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_is_chan_ready body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_external _ b_check); simpl; eauto 1.
      unfold sys_dispatch_c_spec in H1; elim_none_eqn Huctx.
      unfold uctx_arg1_spec in Huctx; repeat elim_none; auto 2.
      econstructor; eauto 1.
      econstructor; eauto 1.
      (* FIXME: this is super-fragile. The point is to exhibit
        [get_layer_primitive sys_is_chan_ready ttrap] so that
        prim_check can be used to rewrite. *)
      red. red. red. red. red. red.
      change positive with ident in *.
      rewrite prim_check.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      constructor_gen_sem_intro.

      Lregset_simpl_tac.
      discriminate.

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
      assert (HUCTX': forall i, 0<= i < UCTXT_SIZE -> 
                                let v:= (ZMap.get i rs') in
                                Val.has_type v Tint 
                                /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
      {
        eapply sys_dispatch_generate; try eassumption.
        - inv H2. inv inv_inject_neutral. assumption.
        - intros. subst v.
          inv_proc; try (split; constructor).
          rewrite ZMap.gi.
          split; constructor.
      }
      econstructor; try eassumption; try reflexivity.
      eapply HUCTX'.
      eapply HUCTX'.

      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.

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

    Lemma sys_dispatch_code_correct:
      asm_spec_le (syscall_dispatch ↦ sys_dispatch_c_spec_low) 
                  (〚syscall_dispatch ↦ sys_dispatch_function〛 tdispatch).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_dispatch_function)).
      {
        assert (Hmodule: get_module_function syscall_dispatch (syscall_dispatch ↦ sys_dispatch_function) 
                         = OK (Some sys_dispatch_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_dispatch_function 
                           = OK (AST.Internal sys_dispatch_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [Hk _]. subst.
        destruct Hk as [_ [_[_[Hsym _]]]].
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_dispatch_spec; eauto 2.
      inv H3.
      inv inv_inject_neutral.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.


    (*Lemma sys_is_chan_ready_spec:
      forall ge (s: stencil) (rs: regset) m labd labd0 labd1 labd' rs0 rs' v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,
        make_globalenv s (sys_ready ↦ sys_ready_function) ttrap = ret ge ->
        (*(forall b0 o,
           rs ESP = Vptr b0 o ->
           Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->*)
        syscall_spec sys_ready s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                     v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        
        (* call kernel function*)
        trap_ischanready_spec labd0 = Some labd1 ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        (*high_level_invariant labd ->*)
        (*low_level_invariant (Mem.nextblock m) labd ->*)
        exists r_: regset,
          lasm_step (sys_ready ↦ sys_ready_function) (ttrap (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    sys_ready s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs0)
                            (Pregmap.get l r_)).
    Proof.
      intros. destruct H0 as [Hk[Hst [Hr _]]]. subst.
      destruct Hk as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
      assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.

      exploit Hstart; eauto.
      intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].
      exploit Hexit; eauto.
      intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
      exploit Hchan_ready; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.

      exploit Hsys_ready; eauto 2. intros Hfunct.

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

      (* call svm_is_chan_ready*)
      one_step_forward 1.
      reflexivity.
      Lregset_simpl_tac.
      change (Int.add (Int.repr 1) Int.one) with (Int.repr 2).
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_is_chan_ready body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_external _ b_check); eauto 1.
      econstructor; eauto 1.
      econstructor; eauto 1.
      (* FIXME: this is super-fragile. The point is to exhibit
        [get_layer_primitive sys_is_chan_ready ttrap] so that
        prim_check can be used to rewrite. *)
      red. red. red. red. red. red.
      change positive with ident in *.
      subrewrite'.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      constructor_gen_sem_intro.

      Lregset_simpl_tac.
      lift_trivial. 

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
        eapply sys_ready_generate; try eassumption.
        intros. subst v.
        inv_proc; try (split; constructor).
        rewrite ZMap.gi.
        split; constructor.
      }
      econstructor; try eassumption; try reflexivity.
      eapply HUCTX'.
      eapply HUCTX'.

      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.

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

    Lemma sys_ready_code_correct:
      asm_spec_le (sys_ready ↦ sys_ischanready_spec_low) 
                  (〚sys_ready ↦ sys_ready_function〛 ttrap).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_ready_function)).
      {
        assert (Hmodule: get_module_function sys_ready (sys_ready ↦ sys_ready_function) = OK (Some sys_ready_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_ready_function = OK (AST.Internal sys_ready_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [Hk _]. subst.
        destruct Hk as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_is_chan_ready_spec; eauto 2.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H3. inv inv_inject_neutral.
        lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.

    Lemma sys_send_spec:
      forall ge (s: stencil) (rs: regset) m labd labd0 labd1 labd' rs0 rs' v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,
        make_globalenv s (sys_send ↦ sys_send_function) ttrap = ret ge ->
        (*(forall b0 o,
           rs ESP = Vptr b0 o ->
           Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->*)
        syscall_spec sys_send s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                     v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        
        (* call kernel function*)
        trap_sendtochan_spec labd0 = Some labd1 ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        (*high_level_invariant labd ->*)
        (*low_level_invariant (Mem.nextblock m) labd ->*)
        exists r_: regset,
          lasm_step (sys_send ↦ sys_send_function) (ttrap (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    sys_send s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs0)
                            (Pregmap.get l r_)).
    Proof.
      intros. destruct H0 as [Hk[Hst [Hr _]]]. subst.
      (*rename H0 into HESP_STACK.*)
      destruct Hk as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
      assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.

      exploit Hstart; eauto.
      intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].
      exploit Hexit; eauto.
      intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
      exploit Hsend; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.

      exploit Hsys_send; eauto 2. intros Hfunct.

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

      (* call svm_send*)
      one_step_forward 1.
      reflexivity.
      Lregset_simpl_tac.
      change (Int.add (Int.repr 1) Int.one) with (Int.repr 2).
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_send body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_external _ b_check); eauto 1.
      econstructor; eauto 1.
      econstructor; eauto 1.
      red. red. red. red. red. red.
      change positive with ident in *.
      subrewrite'.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      constructor_gen_sem_intro.

      Lregset_simpl_tac.
      lift_trivial. 

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
        eapply sys_send_generate; try eassumption.
        intros. subst v.
        inv_proc; try (split; constructor).
        rewrite ZMap.gi.
        split; constructor.
      }
      econstructor; try eassumption; try reflexivity.
      eapply HUCTX'.
      eapply HUCTX'.

      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.

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

    Lemma sys_send_code_correct:
      asm_spec_le (sys_send ↦ sys_sendtochan_spec_low) 
                  (〚sys_send ↦ sys_send_function〛 ttrap).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_send_function)).
      {
        assert (Hmodule: get_module_function sys_send (sys_send ↦ sys_send_function) = OK (Some sys_send_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_send_function = OK (AST.Internal sys_send_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [Hk _]. subst.
        destruct Hk as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_send_spec; eauto 2.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H3. inv inv_inject_neutral.
        lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.

    Lemma sys_recv_spec:
      forall ge (s: stencil) (rs: regset) m labd labd0 labd1 labd' rs0 rs' v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,
        make_globalenv s (sys_recv ↦ sys_recv_function) ttrap = ret ge ->
        (*(forall b0 o,
           rs ESP = Vptr b0 o ->
           Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->*)
        syscall_spec sys_recv s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                     v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        
        (* call kernel function*)
        trap_receivechan_spec labd0 = Some labd1 ->

        asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
        (*high_level_invariant labd ->*)
        (*low_level_invariant (Mem.nextblock m) labd ->*)
        exists r_: regset,
          lasm_step (sys_recv ↦ sys_recv_function) (ttrap (Hmwd:= Hmwd) (Hmem:= Hmem)) 
                    sys_recv s rs (m, labd) r_ (m, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l rs0)
                            (Pregmap.get l r_)).
    Proof.
      intros. destruct H0 as [Hk[Hst [Hr _]]]. subst.
      (*rename H0 into HESP_STACK.*)
      destruct Hk as [Hv [Hsg[Harg[Hsym[HPC[Hex [HESP HESP_STACK]]]]]]]. subst.
      assert (HOS': 0 <= 64 <= Int.max_unsigned) by rewrite_omega.

      exploit Hstart; eauto.
      intros [[b_start [Hstart_symbol Hstart_fun]] prim_start].
      exploit Hexit; eauto.
      intros [[b_exit [Hexit_symbol Hexit_fun]] prim_exit].
      exploit Hrecv; eauto.
      intros [[b_check [Hcheck_symbol Hcheck_fun]] prim_check].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.

      exploit Hsys_recv; eauto 2. intros Hfunct.

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

      (* call svm_recv*)
      one_step_forward 1.
      reflexivity.
      Lregset_simpl_tac.
      change (Int.add (Int.repr 1) Int.one) with (Int.repr 2).
      unfold symbol_offset. unfold fundef.
      rewrite Hcheck_symbol.

      (* call svs_recv body*)
      econstructor; eauto 1.
      eapply (LAsm.exec_step_external _ b_check); eauto 1.
      econstructor; eauto 1.
      econstructor; eauto 1.
      red. red. red. red. red. red.
      change positive with ident in *.
      subrewrite'.
      refine_split'; try reflexivity.
      econstructor; eauto 1.
      refine_split'; try reflexivity; try eassumption.
      constructor_gen_sem_intro.

      Lregset_simpl_tac.
      lift_trivial. 

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
        eapply sys_recv_generate; try eassumption.
        intros. subst v.
        inv_proc; try (split; constructor).
        rewrite ZMap.gi.
        split; constructor.
      }
      econstructor; try eassumption; try reflexivity.
      eapply HUCTX'.
      eapply HUCTX'.

      inv Hstencil_matches. erewrite <- stencil_matches_symbols; eassumption.

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

    Lemma sys_recv_code_correct:
      asm_spec_le (sys_recv ↦ sys_receivechan_spec_low) 
                  (〚sys_recv ↦ sys_recv_function〛 ttrap).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal sys_recv_function)).
      {
        assert (Hmodule: get_module_function sys_recv (sys_recv ↦ sys_recv_function) = OK (Some sys_recv_function)) by
            reflexivity.
        assert (HInternal: make_internal sys_recv_function = OK (AST.Internal sys_recv_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        destruct H1 as [Hk _]. subst.
        destruct Hk as [_ [_[_[Hsym _]]]]. 
        rewrite Hsym in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit sys_recv_spec; eauto 2.
      intros [r_[Hstep Hv]].
      assert (Hle: (Mem.nextblock m0 <= Mem.nextblock m0)%positive).
      {
        reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H3. inv inv_inject_neutral.
        lift_unfold. split; try reflexivity.
        eapply Mem.neutral_inject. assumption.
      - esplit; reflexivity.
    Qed.*)

  (*      Hypothesis Hreg: exists b_reg, 
                         Genv.find_symbol tge sys_set_reg1 = Some b_reg
                         /\ Genv.find_funct_ptr tge b_reg = Some (External TTRAP.PSysSetReg).

      Lemma sys_set_reg_spec:
        forall m abd abd' abd0 abd1 rs0 (rs:regset) rs' v0 v1 v2 v3 v5 v6 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 r'' args sg b v reg,
          let uctx1:= ZMap.set U_EBX (Vint v)
                               (ZMap.set U_OESP (Vint v3)
                                         (ZMap.set U_EBP (Vint v2)
                                                   (ZMap.set U_ESI (Vint v1) 
                                                             (ZMap.set U_EDI (Vint v0) (ZMap.init Vundef))))) in
          let uctx2:= ZMap.set U_ES (Vint v8)
                               (ZMap.set U_EAX (Vint reg)
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
          Genv.find_funct_ptr tge b = Some (Im_sys_set_reg) ->
            (* trapinto the kernel*)
          PPROC.proc_exit_user (Hnpc:= Hnpc) (Mem.get_abstract_data m) uctx4 = Some abd -> 
          rs ESP <> Vundef ->
          (forall b1 o, rs ESP = Vptr b1 o -> Mem.tget m b1 = Some Tag_stack) ->

          (* call kernel function*)
          (* read arguements*)          
          TTRAPARG.uctx_arg1 abd = Some reg ->
          TTRAPARG.uctx_arg2 abd = Some v ->
          (* set reg*)
          VSVM.svm_set_reg abd (Int.unsigned reg) (Vint v) = Some abd0 ->
          (* rewrite return value*)
          TTRAPARG.uctx_set_errno abd0 Int.zero = Some abd1 ->
          
          (* trapout the kernel*)
          PPROC.proc_start_user abd1 = Some (abd', rs') ->
          r'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: RA :: nil) 
                            (undef_regs (List.map preg_of temporary_regs)
                                        (undef_regs (List.map preg_of destroyed_at_call_regs) rs))) ->
          rs0 = r'' # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                    # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                    # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                    # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                    # PC <- (ZMap.get U_EIP rs') ->
          
          args = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v :: Vint v5 :: Vint v6
                       :: Vint reg :: Vint v8 :: Vint v9:: Vint v10 :: Vint v11 :: Vint v12
                       :: Vint v13 :: Vint v14 :: Vint v15:: Vint v16 ::nil) ->

          (* signature *)
          sg = mksignature (Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::
                           Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::nil) None ->
          extcall_arguments rs m sg args ->
          asm_invariant tge (State rs m) ->
          exists r_, 
            plus lstep tge (State rs m) E0 (State r_ (Mem.put_abstract_data m abd'))
            /\ (forall l,
                  Val.lessdef (Pregmap.get l rs0)
                              (Pregmap.get l r_)).
      Proof.
        intros.
        generalize H; intros HPC.
        inv H14.
        rename H2 into HESP.
        rename H3 into HESPTAG.
        (*rename H14 into HLOW.*)
        assert (HOS': 0 <= 64 <= Int.max_unsigned).
        split.
        omega.
        vm_discriminate.

        destruct Hstart as [b_start [Hstart_symbol Hstart_fun]].
        destruct Hexit as [b_exit [Hexit_symbol Hexit_fun]].
        destruct Hreg as [b_check [Hcheck_symbol Hcheck_fun]].
        
        unfold LdataOp in *.
        esplit.
        split.
        econstructor; eauto.

        (* call proc_exit*)
        econstructor; eauto.        
        econstructor; eauto.
        pc_add_simpl.
        simpl.
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
                       extcall_arg
                         ((rs # RA <- (Vptr b (Int.repr 1))) # PC <- (Vptr b_exit Int.zero))
                         m (Locations.S (Outgoing av1 Tint)) (Vint av2)).
        intros.
        inv H2; econstructor; eauto; simpl in *; repeat simpl_Pregmap.

        inv H13.
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

        (* call svm_set_reg *)
        repeat simpl_Pregmap.
        econstructor; eauto.        
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        pc_add_simpl.
        simpl.
        trivial.
        change (Int.add (Int.repr 1) Int.one) with (Int.repr 2).
        unfold symbol_offset.
        rewrite Hcheck_symbol.

        (* call svs_set_reg body*)
        econstructor; eauto.
        eapply (LSemantics.exec_step_external _ b_check); eauto 1; repeat simpl_Pregmap.
        econstructor; try rewrite Mem.get_put_abstract_data; eauto.

        constructor; trivial.
        discriminate.
        intros.
        erewrite Mem.tget_put_abstract_data; eauto.

        (* call proc_start*)
        unfold loc_external_result.
        simpl.
        repeat simpl_Pregmap.
        rewrite Mem.put_put_abstract_data.
        eapply star_left; eauto.
        econstructor; eauto.        
        repeat simpl_Pregmap.
        trivial.
        pc_add_simpl.
        simpl.
        trivial.
        change (Int.add (Int.repr 2) Int.one) with (Int.repr 3).
        unfold symbol_offset.
        rewrite Hstart_symbol.

        (* call proc start body*)
        eapply star_one; eauto.
        eapply (LSemantics.exec_step_prim_call _ b_start); eauto 1; repeat simpl_Pregmap. 
        trivial.
        constructor; trivial.
        assert (HUCTX: forall i, 0<= i < UCTXT_SIZE -> 
                                 let v:= (ZMap.get i uctx4) in
                                 Val.has_type v Tint 
                                 /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
        subst uctx4 uctx3 uctx2 uctx1.
        intros.
        subst v4.
        inv_proc; try (split; constructor).
        rewrite ZMap.gi.
        split; constructor.
        assert (HUCTX': forall i, 0<= i < UCTXT_SIZE -> 
                                 let v:= (ZMap.get i rs') in
                                 Val.has_type v Tint 
                                 /\ val_inject (Mem.flat_inj (Mem.nextblock m)) v v).
        intros.
        exploit SYSCALLGEN_ASM_DATA.sys_set_reg_generate; eauto.
        clear HUCTX.
        econstructor; eauto.
        rewrite Mem.get_put_abstract_data.
        apply H8.
        rewrite Mem.put_put_abstract_data; trivial.
        intros.
        eapply HUCTX'; eauto.
        intros.
        rewrite Mem.nextblock_put_abstract_data.
        eapply HUCTX'; eauto.
        
        trivial.
        
        simpl.
        unfold nextinstr_nf.
        unfold nextinstr.
        simpl.
        repeat simpl_Pregmap. 
        intros reg'.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.
        
        trivial.
      Qed.
   *)

  End WITHMEM.

End ASM_VERIFICATION.