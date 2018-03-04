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

Require Import LoadStoreSem2.

Require Import TTrapArg.
Require Import TrapArgGenSpec.

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

    (** Relation between raw data at two layers*)
    Record relate_RData (f: meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
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
          uctxt_re: uctxt_inj f (uctxt hadt) (uctxt ladt);
          vmxinfo_re: vmxinfo hadt = vmxinfo ladt

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

      (** ** The low level specifications exist*)
      Section Exists.

        Lemma uctx_argn_exist':
          forall n s habd z labd f,        
            uctx_argn_spec n habd = Some z ->
            0 <= n < UCTXT_SIZE ->
            0 <= cid habd < num_proc ->
            relate_AbData s f habd labd ->
            uctx_argn_spec n labd = Some z
            /\ kernel_mode labd.
        Proof.
          intros. split.
          - eapply uctx_argn_exist; eauto.
          - unfold uctx_argn_spec in *.
            inv H2. revert H; subrewrite.
            simpl; subdestruct. eauto.
        Qed.

        Lemma uctx_set_regk_exist':
          forall k s habd habd' labd n f,
            uctx_set_regk_spec k n habd = Some habd'
            -> relate_AbData s f habd labd
            -> 0 <= cid habd < num_proc
            -> exists labd', uctx_set_regk_spec k n labd = Some labd'
                             /\ relate_AbData s f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          intros. exploit uctx_set_regk_exist; eauto.
          intros (labd' & He & HR).
          refine_split'; eauto.
          unfold uctx_set_regk_spec in He.
          simpl; subdestruct. eauto.
        Qed.
 
      End Exists.

      Section FRESH_PRIM.

        Lemma uctx_arg1_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_arg1_spec) uctx_arg1_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_argn_exist'; eauto 1.
          - omega.
          - eapply valid_curid; eauto.
          - intros [HP Hkern].
            refine_split; try econstructor; eauto.
        Qed.

        Lemma uctx_arg2_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_arg2_spec) uctx_arg2_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_argn_exist'; eauto 1.
          - omega.
          - eapply valid_curid; eauto.
          - intros [HP Hkern].
            refine_split; try econstructor; eauto.
        Qed.

        Lemma uctx_arg3_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_arg3_spec) uctx_arg3_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_argn_exist'; eauto 1.
          - omega.
          - eapply valid_curid; eauto.
          - intros [HP Hkern].
            refine_split; try econstructor; eauto.
        Qed.

        Lemma uctx_arg4_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_arg4_spec) uctx_arg4_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).        
          exploit uctx_argn_exist'; eauto 1.
          - omega.
          - eapply valid_curid; eauto.
          - intros [HP Hkern].
            refine_split; try econstructor; eauto.
        Qed.

        Lemma uctx_arg5_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_arg5_spec) uctx_arg5_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_argn_exist'; eauto 1.
          - omega.
          - eapply valid_curid; eauto.
          - intros [HP Hkern].
            refine_split; try econstructor; eauto.
        Qed.

        Lemma uctx_arg6_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_arg6_spec) uctx_arg6_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_argn_exist'; eauto 1.
          - omega.
          - eapply valid_curid; eauto.
          - intros [HP Hkern].
            refine_split; try econstructor; eauto.
        Qed.

        Lemma uctx_set_errno_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_set_errno_spec) uctx_set_errno_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_set_regk_exist'; eauto 1.
          - eapply valid_curid; eauto.
          - intros [labd' [HP [HM Hkern]]].
            refine_split; try econstructor; eauto. 
            constructor.
        Qed.

        Lemma uctx_set_retval1_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_set_retval1_spec) uctx_set_retval1_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_set_regk_exist'; eauto 1.
          - eapply valid_curid; eauto.
          - intros [labd' [HP [HM Hkern]]].
            refine_split; try econstructor; eauto. 
            constructor.
        Qed.

        Lemma uctx_set_retval2_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_set_retval2_spec) uctx_set_retval2_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_set_regk_exist'; eauto 1.
          - eapply valid_curid; eauto.
          - intros [labd' [HP [HM Hkern]]].
            refine_split; try econstructor; eauto. 
            constructor.
        Qed.

        Lemma uctx_set_retval3_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_set_retval3_spec) uctx_set_retval3_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_set_regk_exist'; eauto 1.
          - eapply valid_curid; eauto.
          - intros [labd' [HP [HM Hkern]]].
            refine_split; try econstructor; eauto. 
            constructor.
        Qed.

        Lemma uctx_set_retval4_spec_ref:
          compatsim (crel HDATA LDATA) (gensem uctx_set_retval4_spec) uctx_set_retval4_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_set_regk_exist'; eauto 1.
          - eapply valid_curid; eauto.
          - intros [labd' [HP [HM Hkern]]].
            refine_split; try econstructor; eauto. 
            constructor.
        Qed.

      End FRESH_PRIM.

      Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
      Proof.
        accessor_prop_tac.
        - eapply flatmem_store_exists; eauto.
      Qed.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) ttraparg_passthrough pproc.
      Proof.
        sim_oplus.
        - apply fload_sim.
        - apply fstore_sim.
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
        - apply uctx_get_sim.
        - apply uctx_set_sim.
        - apply proc_create_sim.
          (*
        - apply rdmsr_sim.
        - apply wrmsr_sim.
        - apply vmx_set_intercept_intwin_sim.
        - apply vmx_set_desc_sim.
        - apply vmx_inject_event_sim.
        - apply vmx_set_tsc_offset_sim.
        - apply vmx_get_tsc_offset_sim.
        - apply vmx_get_exit_reason_sim.
        - apply vmx_get_exit_fault_addr_sim.
        - apply vmx_check_pending_event_sim.
        - apply vmx_check_int_shadow_sim.
        - apply vmx_get_reg_sim.
        - apply vmx_set_reg_sim.
        - apply vmx_get_next_eip_sim.
        - apply vmx_get_io_width_sim.
        - apply vmx_get_io_write_sim.
        - apply vmx_get_exit_io_rep_sim.
        - apply vmx_get_exit_io_str_sim.
        - apply vmx_get_exit_io_port_sim.
        - apply vmx_set_mmap_sim.
        - apply vm_run_sim, VMX_INJECT.
        - apply vmx_return_from_guest_sim, VMX_INJECT.
        - apply vmx_init_sim.
        - apply vmx_init_sim.*)
        - apply proc_init_sim.
        - apply container_get_nchildren_sim.
        - apply container_get_quota_sim.
        - apply container_get_usage_sim.
        - apply container_can_consume_sim.
        - apply alloc_sim.
        - apply trap_info_get_sim.
        - apply trap_info_ret_sim.
        - apply thread_yield_sim.
        - apply thread_sleep_sim.
        - apply proc_start_user_sim.
          intros. eapply valid_curid; eauto.
        - apply proc_exit_user_sim. 
        - layer_sim_simpl.
          + eapply load_correct2.
          + eapply store_correct2.
      Qed.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
