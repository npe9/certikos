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
(*          Refinement Proof for PProc                                 *)
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
Require Import LoadStoreSem2.
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

Require Import LAsmModuleSemAux.
Require Import LayerCalculusLemma.
Require Import AbstractDataType.

Require Import PUCtxtIntro.
Require Import PProc.

Require Import ProcGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := pproc_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pipc_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    
    (** Relation between raw data at two layers*)
    Record relate_RData (f: meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
          vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
          devout_re: devout hadt = devout ladt;
          CR3_re:  CR3 hadt = CR3 ladt;
          ikern_re: ikern hadt = ikern ladt;
          pg_re: pg hadt = pg ladt;
          ihost_re: ihost hadt = ihost ladt;
          AC_re: AC hadt = AC ladt;
          ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
          ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
          LAT_re: LAT hadt = LAT ladt;
          nps_re: nps hadt = nps ladt;
          init_re: init hadt = init ladt;

          pperm_re: pperm hadt = pperm ladt;
          PT_re:  PT hadt = PT ladt;
          ptp_re: ptpool hadt = ptpool ladt;
          idpde_re: idpde hadt = idpde ladt;
          ipt_re: ipt hadt = ipt ladt;
          smspool_re: smspool hadt = smspool ladt;

          kctxt_re: kctxt_inj f num_proc (kctxt hadt) (kctxt ladt);
          abtcb_re:  abtcb hadt = abtcb ladt;
          abq_re:  abq hadt = abq ladt;
          cid_re:  cid hadt = cid ladt;
          chpool_re:  syncchpool hadt = syncchpool ladt;
          uctxt_re: uctxt_inj f (uctxt hadt) (uctxt ladt)
        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.   

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.    

    (** ** Properties of relations*)
    Section Rel_Property.

      (** Prove that after taking one step, the refinement relation still holds*)    
      Lemma relate_incr:  
        forall abd abd' f f',
          relate_RData f abd abd'
          -> inject_incr f f'
          -> relate_RData f' abd abd'.
      Proof.
        inversion 1; subst; intros; inv H; constructor; eauto.
        - eapply kctxt_inj_incr; eauto.
        - eapply uctxt_inj_incr; eauto.
      Qed.

      Lemma relate_kernel_mode:
        forall abd abd' f,
          relate_RData f abd abd' 
          -> (kernel_mode abd <-> kernel_mode abd').
      Proof.
        inversion 1; simpl; split; congruence.
      Qed.

      Lemma relate_observe:
        forall p abd abd' f,
          relate_RData f abd abd' ->
          observe p abd = observe p abd'.
      Proof.
        inversion 1; simpl; unfold ObservationImpl.observe; congruence.
      Qed.

      Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
      Proof.
        constructor; intros; simpl; trivial.
        eapply relate_incr; eauto.
        eapply relate_kernel_mode; eauto.
        eapply relate_observe; eauto.
      Qed.

    End Rel_Property.

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      Section FRESH_PRIM.

        Lemma proc_start_user_spec_ref:
          compatsim (crel HDATA LDATA)
                    (primcall_start_user_compatsem proc_start_user_spec)
                    proc_start_user_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          intros.
          inv match_extcall_states.
          exploit proc_start_user_exist; eauto 1.
          eapply valid_curid; eauto.
          intros (d2' & rs2' & HM & HR & HReg & He & Hrange'). 
          subst.
          refine_split; try econstructor; eauto. 
          eapply reg_symbol_inject; eassumption.
          econstructor; eauto. 
          constructor.
          val_inject_simpl; try (eapply HReg; omega).
        Qed.

        Lemma proc_exit_user_spec_ref:
          compatsim (crel HDATA LDATA)
                    (primcall_exit_user_compatsem proc_exit_user_spec)
                    proc_exit_user_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          intros.
          inv H4. inv match_extcall_states.
          exploit proc_exit_user_exist; eauto 1.
          - subst uctx4 uctx3 uctx2 uctx1.
            intros. inv_proc. rewrite ZMap.gi. constructor.
          - intros [d2'[HM HR]].
            refine_split; try econstructor; eauto. 
            eapply reg_symbol_inject; eassumption.
            + exploit (extcall_args_inject (D1:= HDATAOps) (D2:= LDATAOps)); eauto.
              instantiate (3:= d1').
              apply extcall_args_with_data; eauto.
              instantiate (1:= d2).
              intros [?[? Hinv]]. inv_val_inject.
              apply extcall_args_without_data in H; eauto.
            + specialize (match_reg ESP); unfold Pregmap.get in match_reg.
              inv match_reg; congruence.
            + intros.
              specialize (match_reg ESP); unfold Pregmap.get in match_reg.
              inv match_reg; try congruence.
              specialize (HESP_STACK _ _ (eq_sym H1)).
              replace b1 with b2 by congruence.
              split.
              * apply Ple_trans with b0;
                [ apply HESP_STACK | apply (match_inject_forward _ _ _ H3) ].
              * apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H3 match_inject).
            + econstructor; eauto. constructor.
            + val_inject_simpl. 
        Qed.
        
        Lemma proc_create_kernel_mode:
          forall d2 d2' b b' b2 ofs_uc q,
            proc_create_spec d2 b b' b2 ofs_uc q = Some d2'
            -> kernel_mode d2.
        Proof.
          unfold proc_create_spec; intros.
          simpl; subdestruct. auto.
        Qed.

        Lemma proc_create_spec_ref:
          compatsim (crel HDATA LDATA) (proc_create_compatsem proc_create_spec) proc_create_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit proc_create_exist; eauto 1.
          intros (labd' & HP  & HM).
          destruct H9 as [fun_id Hsymbol].
          exploit (stencil_find_symbol_inject' s ι fun_id buc); eauto.
          intros HFB.
          destruct H10 as [elf_id Hsymbol'].
          exploit (stencil_find_symbol_inject' s ι elf_id be); eauto.
          intros HFB'.
          refine_split; try econstructor; eauto. 
          - eapply proc_create_kernel_mode; eauto.
          - constructor.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_PRIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
        Qed.

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) pproc_passthrough puctxtintro.
        Proof.
          sim_oplus.
          - apply fload_sim.
          - apply fstore_sim.
          - apply vmxinfo_get_sim.          
          - apply device_output_sim.
          (*- apply pfree_sim.*)
          - apply ptRead_sim. 
          - apply ptResv_sim.
          - apply shared_mem_status_sim.
          - apply offer_shared_mem_sim.
          - apply get_curid_sim.
          - apply thread_wakeup_sim.
          (*- apply is_chan_ready_sim.
          - apply sendto_chan_sim.
          - apply receive_chan_sim.*)
          - apply syncreceive_chan_sim.
          - apply syncsendto_chan_pre_sim.
          - apply syncsendto_chan_post_sim.
          - apply proc_init_sim.
          - apply uctx_get_sim.
          - apply uctx_set_sim.
          - apply container_get_nchildren_sim.
          - apply container_get_quota_sim.
          - apply container_get_usage_sim.
          - apply container_can_consume_sim.
          - apply alloc_sim. 
          - apply hostin_sim.
          - apply hostout_sim.
          - apply trap_info_get_sim.
          - apply trap_info_ret_sim.
          - apply thread_yield_sim.
          - apply thread_sleep_sim.
          - layer_sim_simpl.
            + eapply load_correct2.
            + eapply store_correct2.
        Qed.

      End PASSTHROUGH_PRIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
