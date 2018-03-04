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
(*          Refinement Proof for PQueueInit                            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PQueueIntro layer and PQueueInit layer*)
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

Require Import PThreadSched.
Require Import PThread.
Require Import ThreadGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := pthread_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pthreadsched_data_ops) LDATA).

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
          cid_re:  cid hadt = cid ladt
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

        Lemma thread_yield_exist:
          forall habd habd' labd rs r' rs0 f,
            ObjThread.thread_yield_spec 
              habd (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
              #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA) = Some (habd', rs0)
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> (forall reg : PregEq.t,
                  val_inject f (Pregmap.get reg rs) (Pregmap.get reg r'))
            -> exists labd' r'0, thread_yield_spec
                                   labd (Pregmap.init Vundef)#ESP <- (r'#ESP)#EDI <- (r'#EDI)#ESI <- (r'#ESI)
                                   #EBX <- (r'#EBX)#EBP <- (r'#EBP)#RA <- (r'#RA) = Some (labd', r'0)
                                 /\ relate_RData f habd' labd'
                                 /\ (forall i r,
                                       ZtoPreg i = Some r -> val_inject f (rs0#r) (r'0#r)).
        Proof.
          Opaque remove.
          unfold ObjThread.thread_yield_spec, thread_yield_spec; intros until f.
          intros HP HR HINV HVL; pose proof HR as HR'; inv HR; revert HP.
          specialize (valid_TDQ _ HINV).                 
          specialize (correct_curid _ HINV).           
          simpl; subrewrite'; intros Hcid' Hlast HQ. 
          destruct (pg labd); contra_inv.
          destruct (Hcid' refl_equal) as [_ Hcid].
          rewrite Hcid.
          assert (HOS: 0<= num_chan <= num_chan) by omega.
          specialize (Hlast refl_equal _ HOS). 
          subdestruct; contra_inv; simpl.
          inv HQ. refine_split'; eauto 1.
          - inv HR'. econstructor; eauto 1.
            simpl; kctxt_inj_simpl.
          - unfold kctxt_inj, Pregmap.get in *.          
            intros. eapply kctxt_re0; eauto. 
            destruct Hlast as [l0[HT Hlast]]. inv HT.
            apply Hlast. apply last_correct; auto.
        Qed.

        Lemma thread_sleep_exist:
          forall habd habd' labd rs r' rs0 n f,
            ObjThread.thread_sleep_spec 
              habd (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
              #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA) n = Some (habd', rs0)
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> (forall reg : PregEq.t,
                  val_inject f (Pregmap.get reg rs) (Pregmap.get reg r'))
            -> exists labd' r'0, thread_sleep_spec 
                                   labd (Pregmap.init Vundef)#ESP <- (r'#ESP)#EDI <- (r'#EDI)#ESI <- (r'#ESI)
                                   #EBX <- (r'#EBX)#EBP <- (r'#EBP)#RA <- (r'#RA) n = Some (labd', r'0)
                                 /\ relate_RData f habd' labd'
                                 /\ (forall i r,
                                       ZtoPreg i = Some r -> val_inject f (rs0#r) (r'0#r)).
        Proof.
          Opaque remove.
          unfold ObjThread.thread_sleep_spec, thread_sleep_spec; intros until f.
          intros HP HR HINV HVL; pose proof HR as HR'; inv HR; revert HP.
          specialize (valid_TDQ _ HINV); unfold AbQCorrect.           
          specialize (correct_curid _ HINV).           
          simpl; subrewrite'; intros Hcid' Hlast HQ.
          destruct (pg labd); contra_inv.
          destruct (Hcid' refl_equal) as [_ Hcid].
          rewrite Hcid.
          assert (HOS: 0<= num_chan <= num_chan) by omega.
          specialize (Hlast refl_equal _ HOS).
          subdestruct; simpl.
          inv HQ. refine_split'; eauto 1.
          - inv HR'.  econstructor; simpl; eauto 2.
            kctxt_inj_simpl.
          - unfold kctxt_inj, Pregmap.get in *.          
            intros. eapply kctxt_re0; eauto. 
            destruct Hlast as [l0'[HT Hlast]]. inv HT.
            apply Hlast. apply last_correct; auto.
        Qed.

      End Exists.

      Section FRESH_PRIM.

        Lemma thread_yield_spec_ref:
          compatsim (crel HDATA LDATA) 
                    (primcall_thread_schedule_compatsem ObjThread.thread_yield_spec (prim_ident:= thread_yield)) 
                    thread_yield_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          inv match_extcall_states.
          exploit thread_yield_exist; eauto 1.
          intros [labd' [r'0[HP [HM HReg]]]].
          refine_split; try econstructor; eauto. 
          eapply reg_symbol_inject; eassumption.
          econstructor; eauto. constructor.
          subst rs3.
          val_inject_simpl; eapply HReg;
          apply PregToZ_correct; reflexivity.
        Qed.
        
        Lemma thread_sleep_spec_ref:
          compatsim (crel HDATA LDATA) 
                    (primcall_thread_transfer_compatsem ObjThread.thread_sleep_spec) 
                    thread_sleep_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          inv match_extcall_states.
          exploit thread_sleep_exist; eauto 1.
          intros [labd' [r'0[HP [HM HReg]]]].
          refine_split; try econstructor; eauto. 
          - eapply reg_symbol_inject; eassumption.
          - exploit (extcall_args_inject (D1:= HDATAOps) (D2:= LDATAOps)); eauto.
            instantiate (3:= d1').
            apply extcall_args_with_data; eauto.
            instantiate (1:= d2).
            intros [?[? Hinv]]. inv_val_inject.
            apply extcall_args_without_data in H; eauto.
          - econstructor; eauto. constructor.
          - subst rs3.
            val_inject_simpl; 
              eapply HReg; apply PregToZ_correct; reflexivity.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_PRIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
        Qed.          

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) pthread_passthrough pthreadsched.
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
          - apply shared_mem_status_sim.
          - apply offer_shared_mem_sim.
          - apply get_state0_sim.
          - apply get_curid_sim.
          - apply thread_spawn_sim.
          - apply thread_wakeup_sim.
          - apply sched_init_sim.
          - apply ptin_sim.
          - apply ptout_sim.
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
          - layer_sim_simpl.
            + eapply load_correct2.
            + eapply store_correct2.
        Qed.

      End PASSTHROUGH_PRIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
