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
(*          Refinement proof for MALOp layer                           *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MALInit layer and MALOp layer*)
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
Require Import LoadStoreSem1.
Require Import AsmImplLemma.
Require Import LAsm.
Require Import RefinementTactic.
Require Import PrimSemantics.


Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.
Require Import LayerCalculusLemma.

Require Import AbstractDataType.
Require Import MALOp.
Require Import MALInit.
Require Import ALOpGenSpec.

(** * Notation of the refinement relation*)
Section Refinement.  

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := malop_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := malinit_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
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
          AT_re: AT hadt = AT ladt;
          nps_re: nps hadt = nps ladt;
          init_re: init hadt = init ladt
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

        Lemma mem_init_kern_mode:
          forall i d d',
            mem_init_spec i d = Some d'
            -> kernel_mode d.
        Proof.
          unfold mem_init_spec. simpl; intros.
          subdestruct. auto.
        Qed.

        Lemma mem_init_spec_ref:
          compatsim (crel HDATA LDATA) (gensem mem_init_spec) mem_init_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit mem_init_exist; eauto 1.
          intros [labd' [HP HM]].
          refine_split; try econstructor; eauto. 
          - eapply mem_init_kern_mode; eauto.
          - constructor.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_RPIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store') (lflatmem_store:= flatmem_store')).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store'_exists; eauto.
        Qed.          

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) malop_passthrough malinit.
        Proof.
          sim_oplus.
          - apply fload'_sim.
          - apply fstore'_sim.
          - apply flatmem_copy'_sim.
          - apply vmxinfo_get_sim.
          - apply device_output_sim.
          - apply setPG0_sim.
          - apply clearCR2_sim.
          - apply setCR30_sim.
          - apply get_nps_sim.
          - apply is_at_norm_sim.
          - apply get_at_u_sim.
          - apply get_at_c_sim.
          - apply set_at_u_sim.
          - apply set_at_c_sim.
          - apply trapin_sim.
          - apply trapout0_sim.
          - apply hostin_sim.
          - apply hostout_sim.
          - apply trap_info_get_sim.
          - apply trap_info_ret_sim.
          - layer_sim_simpl.
            + eapply load_correct1.
            + eapply store_correct1.
        Qed.

      End PASSTHROUGH_RPIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
