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
(*          Refinement Proof for PThreadInit                           *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PThreadIntro layer and PThreadInit layer*)
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

Require Import LayerCalculusLemma.
Require Import AbstractDataType.

Require Import ThreadInitGenSpec.
Require Import PThreadIntro.
Require Import PThreadInit.

(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := pthreadinit_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := mshareintro_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** Relation between raw data at two layers*)
    Record relate_RData (f: meminj) (hadt: LDATA) (ladt: LDATA) :=
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
          tcb_re:  tcb hadt = tcb ladt
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

        Lemma thread_init_exist:
          forall habd habd' labd i f,
            ObjQueue.thread_init_spec i habd = ret habd'
            -> relate_RData f habd labd
            -> exists labd', thread_init_spec i labd = Some labd' 
                             /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold ObjQueue.thread_init_spec, thread_init_spec, sharedmem_init_spec, 
          thread_init_spec. 
          intros until f. exist_simpl.
        Qed.

        (*
        Lemma thread_free_exist:
          forall habd habd' labd n f,
            thread_free_spec habd n = Some habd'
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', thread_free_spec labd n = Some labd' 
                             /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold thread_free_spec, thread_free_spec,
          pt_free_spec, tcb_init_spec. 
          intros until f.
          intros HP HR; inv HR; revert HP; simpl;
          subrewrite'; intros HQ; subdestruct.
          rewrite zle_true; [|omega]. 
          inv HQ. refine_split'; eauto.
          econstructor; eauto.
        Qed.*)

      End Exists.

      Section FRESH_PRIM.

        (*Lemma thread_free_spec_ref:
          compatsim (crel HDATA LDATA) (gensem thread_free_spec) 
                    thread_free_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit thread_free_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.*)

        Lemma thread_init_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ObjQueue.thread_init_spec) thread_init_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit thread_init_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_RPIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
        Qed.          

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) pthreadinit_passthrough pthreadintro.
        Proof.
          sim_oplus.
          - apply fload_sim.
          - apply fstore_sim.
          - apply flatmem_copy_sim.
          - apply vmxinfo_get_sim.
          - apply device_output_sim.
          - apply pfree_sim.
          - apply setPT_sim.
          - apply ptRead_sim. 
          - apply ptResv_sim.
          - apply kctxt_new_sim.
          - apply shared_mem_status_sim.
          - apply offer_shared_mem_sim.
          - apply get_state_sim.
          - apply get_prev_sim.
          - apply get_next_sim.
          - apply set_state_sim.
          - apply set_prev_sim.
          - apply set_next_sim.
          - apply ptin_sim.
          - apply ptout_sim.
          - apply clearCR2_sim.
          - apply container_get_nchildren_sim.
          - apply container_get_quota_sim.
          - apply container_get_usage_sim.
          - apply container_can_consume_sim.
          - apply alloc_sim.
          - apply trapin_sim.
          - apply trapout_sim.
          - apply hostin_sim.
          - apply hostout_sim.
          - apply trap_info_get_sim.
          - apply trap_info_ret_sim.
          - apply kctxt_switch_sim.
          - layer_sim_simpl.
            + eapply load_correct2.
            + eapply store_correct2.
        Qed.

      End PASSTHROUGH_RPIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
