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
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Refinement Proof for TrapArg                               *)
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
Require Import Asm.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import FlatMemory.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import RealParams.
Require Import AsmImplLemma.
Require Import GenSem.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import XOmega.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.

(*Require Import LAsmModuleSemAux.*)
Require Import LayerCalculusLemma.
Require Import AbstractDataType.
Require Import LAsmModuleSemAux.

Require Import LoadStoreSem2.

Require Import TSysCall.
Require Export DispatchGen.
Require Import SysCallGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := pproc_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Section PRIM_EXISTS.

      Lemma trap_into_kernel_exists:
        forall s hm lm habd habd0 labd (rs1 rs2 :regset) v0 v1 v2 v3 v5 v6 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs id sg b f,
          trap_into_kernel_spec id s hm rs1 habd habd0 vargs sg b v0 v1 v2
                                v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

          Mem.inject f hm lm ->
          relate_AbData s f habd labd ->
          high_level_invariant habd ->
          (forall reg,
             val_inject f (Pregmap.get reg rs1) (Pregmap.get reg rs2)) ->
          (forall b1 b2 delta,
             f b1 = Some (b2, delta) -> delta = 0 /\ (b1 <= b2)%positive) ->
          inject_incr (Mem.flat_inj (genv_next s)) f ->
          (asm_invariant (mem:= mwd LDATAOps) s rs2 (lm, labd)) ->
          exists labd0, trap_into_kernel_spec id s lm rs2 labd labd0 vargs sg b v0 v1 v2
                                              v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 
                        /\ relate_AbData s f habd0 labd0
                        /\ high_level_invariant habd0.
        Proof.
          unfold trap_into_kernel_spec.
          intros.
          destruct H as [Hv[Hs[Ha[Hf[Hpc[Hp [Hesp hesp']]]]]]]. subst.
          exploit proc_exit_user_exist; eauto.
          intros. inv_proc. rewrite ZMap.gi. constructor.
          intros [labd0[Hspec Hr]].
          refine_split'; try (econstructor; fail); eauto. 
          - exploit (extcall_args_inject (D1:= HDATAOps) (D2:= LDATAOps)); eauto.
            instantiate (3:= habd0).
            apply extcall_args_with_data; eauto.
            instantiate (1:= labd).
            intros [?[? Hinv]]. inv_val_inject.
            apply extcall_args_without_data in H; eauto.
          - eapply reg_symbol_inject; eassumption.
          - eapply reg_val_inject_defined; eauto 1.
          - intros.
            specialize (H3 ESP). unfold Pregmap.get in *.
            rewrite H in H3. inv H3; try congruence.
            specialize (H4 _ _ _ H10). destruct H4 as [? Hle]; subst.
            exploit hesp'; eauto.
            intros [Hle1 Hle2].
            split. revert Hle1 Hle. clear.
            intros. Coqlib.xomega. inv H6.
            inv inv_inject_neutral.
            specialize (inv_reg_inject_neutral ESP).
            rewrite H in inv_reg_inject_neutral.
            revert inv_reg_inject_neutral; clear.
            lift_unfold.
            intros inv_reg_inject_neutral.
            inv inv_reg_inject_neutral.
            unfold Mem.flat_inj in *.
            destruct (plt b0 (Mem.nextblock lm)).
            assumption. discriminate.
          - destruct proc_exit_user_inv.
            eapply exit_user_high_level_invariant; eauto.
        Qed.

    End PRIM_EXISTS.

    Lemma sys_sendtochan_post_spec_ref:
      compatsim (crel HDATA LDATA)
                primcall_sys_sendto_chan_post_compatsem
                sys_sendtochan_post_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      intros.
      inv Hmatch_ext. inv match_extcall_states.
      exploit trap_sendtochan_post_exist; eauto. 
      eapply valid_curid; eauto.      
      intros [labd'[Hpost Hr]].
      exploit proc_start_user_exist; eauto. 
      eapply valid_curid; eauto.      
      eapply trap_sendtochan_post_high_inv; eauto.
      intros (labd'' & r'0 & Hm''  & Hr'' & Hf & Heq' & Hrange).
      pose proof Hlow as Hlow'.
      eapply trap_sendtochan_post_low_inv in Hlow; eauto.      
      inv Hlow.
      unfold uctxt_inject_neutral in *.
      refine_split; econstructor; eauto 1.
      - intros; eapply uctxt_INJECT; eauto.
      - intros; eapply uctxt_INJECT; eauto.
      - eapply reg_symbol_inject; eassumption.
      - eapply reg_val_inject_defined; eauto 1.
      - intros.
        specialize (match_reg ESP). unfold Pregmap.get in *.
        rewrite H in match_reg. inv match_reg; try congruence.
        specialize (match_inject_forward _ _ _ H3). destruct match_inject_forward as [? Hle]; subst.
        exploit H14; eauto.
        intros [Hle1 Hle2].
        split. revert Hle1 Hle. clear.
        intros. Coqlib.xomega. inv ASM_INV.
        inv inv_inject_neutral.
        specialize (inv_reg_inject_neutral ESP).
        rewrite H in inv_reg_inject_neutral.
        revert inv_reg_inject_neutral; clear.
        lift_unfold.
        intros inv_reg_inject_neutral.
        inv inv_reg_inject_neutral.
        unfold Mem.flat_inj in *.
        destruct (plt b0 (Mem.nextblock m2)).
        assumption. discriminate.      
      - econstructor; eauto.
        constructor.
      - val_inject_simpl; try (eapply Hf; omega).
    Qed.

    Lemma sys_sendtochan_pre_spec_ref:
      compatsim (crel HDATA LDATA)
                primcall_sys_sendto_chan_pre_compatsem
                sys_sendtochan_pre_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      intros.
      inv Hmatch_ext. inv match_extcall_states.
      exploit trap_into_kernel_exists; eauto. intros Ht.
      exploit Ht; eauto.
      intros [labd2[Hk[Hr Hh]]].
      exploit trap_sendtochan_pre_exist; eauto. 
      eapply valid_curid; eauto.      
      intros [labd'[Hpre Hr']].
      exploit (thread_sleep_exists s labd1 d1' labd' (rs1#EBX <- Vundef
                                                         #ESP <- (Val.add (rs1 ESP) (Vint (Int.repr 28)))
                                                         #RA <- (Vptr bs Int.zero))); eauto.
      eapply trap_sendtochan_pre_high_inv; eauto.
      instantiate (1:= rs2#EBX <- Vundef
                          #ESP <- (Val.add (rs2 ESP) (Vint (Int.repr 28)))
                          #RA <- (Vptr bs Int.zero)).
      val_inject_simpl.
      eapply stencil_find_symbol_inject' in H6; eauto.
      repeat simpl_Pregmap.
      intros (labd'0 & r'0 & ofs & HM & HR & HP & HP0 & HP1).
      refine_split; econstructor; eauto.
      econstructor; eauto.
      constructor.
      val_inject_simpl; try (eapply HP; eapply PregToZ_correct; simpl; reflexivity).
    Qed.

    Lemma syscall_dispatch_spec_ref:
      compatsim (crel HDATA LDATA)
                primcall_sys_dispatch_c_compatsem
                sys_dispatch_c_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      inv Hmatch_ext. inv match_extcall_states.
      destruct H5 as [Htrapk[Hext [Hrs [He1 He2]]]]. subst.
      exploit trap_into_kernel_exists; eauto. intros Ht.
      exploit Ht; eauto.
      intros [labd1'[Hk[Hr Hh]]].
      exploit sys_dispatch_c_exist; eauto.
      eapply valid_curid; eauto.
      intros [labd'[Hm' Hr']].
      exploit proc_start_user_exist; eauto.  
      eapply valid_curid; eauto.
      clear Hm'.
      exploit (trap_proc_create_high_inv sys_dispatch_c_spec); eauto.
      intros (labd'' & r'0 & Hm''  & Hr'' & Hf & Heq' & Hrange).
      refine_split; econstructor; eauto 1.
      split; eauto 1.
      split; eauto 1.
      split; eauto 1.
      eapply trap_into_kernel_low_inv in Hlow; eauto.
      exploit (trap_proc_create_low_inv sys_dispatch_c_spec); eauto.
      inv ASM_INV. inv inv_inject_neutral. eauto.
      inversion 1; intros.
      unfold uctxt_inject_neutral in *.
      subst r'0.
      split; intros;
      eapply uctxt_INJECT; eauto.

      econstructor; eauto.
      constructor.
      val_inject_simpl; try (eapply Hf; omega).
    Qed.

    Lemma sys_yield_spec_ref:
      compatsim (crel HDATA LDATA)
                primcall_sys_yield_compatsem
                sys_yield_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      intros.
      inv Hmatch_ext. inv match_extcall_states.
      exploit trap_into_kernel_exists; eauto. intros Ht.
      exploit Ht; eauto.
      intros [labd1[Hk[Hr Hh]]].
      exploit (thread_yield_exists s labd0 d1' labd1 (rs1#EBX <- Vundef#RA <- (Vptr bs Int.zero))); eauto.
      instantiate (1:= rs2#EBX <- Vundef#RA <- (Vptr bs Int.zero)).
      val_inject_simpl.
      eapply stencil_find_symbol_inject' in H5; eauto.
      repeat simpl_Pregmap.
      intros (labd' & r'0 & ofs & HM & HR & HP1 & HP2 & HP3).
      refine_split; econstructor; eauto.
      econstructor; eauto.
      constructor.
      val_inject_simpl; try (eapply HP1; eapply PregToZ_correct; simpl; reflexivity).
    Qed.

    (*Lemma sys_run_vm_spec_ref:
      compatsim (crel HDATA LDATA)
                primcall_sys_run_vm_compatsem
                sys_run_vm_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      intros.
      inv Hmatch_ext. inv match_extcall_states.
      exploit trap_into_kernel_exists; eauto. intros Ht.
      exploit Ht; eauto.
      intros [labd1[Hk[Hr Hh]]].
      
      assert (HVAL: forall reg,
                      val_inject ι (Pregmap.get reg ((Pregmap.init Vundef) # EDI <- (rs1 EDI)) # EBP <- (rs1 EBP))
                                 (Pregmap.get reg ((Pregmap.init Vundef) # EDI <- (rs2 EDI)) # EBP <- (rs2 EBP))).
      {
        val_inject_simpl.
      }

      exploit vm_run_exist; eauto.

      intros r; destruct r as [| [] | [] | | [] |]; try constructor;
      try apply ASM_INV.

      intros r; destruct r as [| [] | [] | | [] |]; try constructor;
      try apply ASM_INV.
      
      assert (HLOW: low_level_invariant (Mem.nextblock m2) labd1).
      {
        eapply trap_into_kernel_low_inv; eauto.
      }
      eapply HLOW.

      intros (labd' & r'0 & HM & HR & HP & HP0 & HP1).
      refine_split; econstructor; eauto.
      econstructor; eauto.
      constructor.
      val_inject_simpl. 
    Qed.*)

    Lemma pagefault_handler_spec_ref:
      compatsim (crel HDATA LDATA)
                primcall_pagefault_handler_compatsem
                pagefault_handler_spec_low.
    Proof.
      compatsim_simpl (@match_AbData).
      intros.
      inv Hmatch_ext. inv match_extcall_states.
      destruct H6 as [Htrapk[Hext [Hrs [He1 He2]]]]. subst.
      exploit trap_into_kernel_exists; eauto. intros Ht.
      exploit Ht; eauto.
      intros [labd1'[Hk[Hr Hh]]].
      
      exploit ptfault_resv_exist; eauto.
      eapply valid_curid; eauto.
      intros [labd'[Hm' Hr']].
      exploit proc_start_user_exist; eauto.
      eapply valid_curid; eauto.
      eapply ptfault_resv_high_inv; eauto.
      intros (labd'' & r'0  & Hm''  & Hr'' & Hf & Heq' & Hrange).
      refine_split;
      econstructor; try eassumption; eauto 1.
      split; eauto 1. 
      split; eauto 1.
      split; eauto 1.

      eapply trap_into_kernel_low_inv in Hlow; eauto.
      exploit (ptfault_resv_low_inv); eauto.
      inversion 1; intros.
      unfold uctxt_inject_neutral in *.
      subst r'0.
      split; intros;
      eapply uctxt_INJECT; eauto.

      inv Hr. congruence.

      econstructor; eauto.
      constructor.
      val_inject_simpl; try (eapply Hf; omega).
    Qed.

    Lemma passthrough_correct:
      sim (crel HDATA LDATA) tsyscall_passthrough tdispatch.
    Proof.
      sim_oplus.
      (*- apply print_sim.*)
      - apply proc_init_sim.
      - apply proc_start_user_sim.
        destruct 1; auto.
      - layer_sim_simpl.
        + eapply load_correct2.
        + eapply store_correct2.
    Qed.

  End WITHMEM.

End Refinement.