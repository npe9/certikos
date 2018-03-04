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
(*          Refinement proof for MALInit layer                         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MBoot layer and MALInit layer*)
Require Import BootGenDef.
Require Import BootGenAccessor.
Require Import BootGenAccessor0.
Require Import BootGenAccessorDef.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** The low level specifications exist*)
    Section Exists.

      Lemma setPG_exist:
        forall (habd habd': HDATAOps) (labd: LDATAOps) f,
          setPG_spec habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', setPG_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ HP habd' = HP habd.
      Proof.
        unfold setPG_spec; intros until f; exist_simpl.
      Qed.

      Lemma setCR3_exist:
        forall (habd habd': HDATAOps) (labd: LDATAOps) id ofs f,
          setCR3_spec habd (GLOBP id ofs) = Some habd'
          -> relate_RData f habd labd
          -> exists labd', setCR3_spec labd (GLOBP id ofs) = Some labd' /\ relate_RData f habd' labd'
                           /\ HP habd' = HP habd.
      Proof.
        unfold setCR3_spec; unfold setCR3_spec; intros until f; exist_simpl.
      Qed.

      Lemma bootloader_exist:
        forall (habd habd': HDATAOps) (labd: LDATAOps) i f,
          bootloader0_spec i habd = ret habd'
          -> relate_RData f habd labd
          -> exists labd', bootloader_spec i labd = Some labd' /\ relate_RData f habd' labd'
                           /\ HP habd' = HP habd.
      Proof.
        unfold bootloader0_spec, bootloader_spec; intros until f; exist_simpl.
      Qed.

      Lemma trapout_exist:
        forall (habd habd': HDATAOps) (labd: LDATAOps) f,
          trapout'_spec habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', trapout'_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ HP habd' = HP habd.
      Proof.
        unfold trapout'_spec. intros until f; exist_simpl.
      Qed.

      Lemma hostout_exist:
        forall (habd habd': HDATAOps) (labd: LDATAOps) f,
          hostout'_spec habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', hostout'_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ HP habd' = HP habd.
      Proof.
        unfold hostout'_spec; intros until f; exist_simpl.
      Qed.

    End Exists.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Lemma passthrough_correct:
      sim (crel HDATAOps LDATAOps) mboot_passthrough preinit.
    Proof.
      unfold mboot_passthrough, preinit.
      sim_oplus_split_straight.
      - apply vmxinfo_get_sim.
      - (* set_PG *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit setPG_exist; eauto.
        eapply match_related.
        intros (labd' & HP & HM & HN).
        match_external_states_simpl. 
      - (* set_CR3 *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        inv_val_inject.
        eapply inject_forward_equal' in H3; eauto 1. inv H3.
        exploit setCR3_exist; eauto 1. eapply match_related.
        intros (labd' & HP & HM & HN).
        
        refine_split.
        + repeat (econstructor; eauto; try congruence).
          rewrite Int.add_zero; eauto.
        + constructor.
        + repeat (econstructor; eauto; try congruence).
        + apply inject_incr_refl.
      - apply get_size_sim.
      - apply is_mm_usable_sim.
      - apply get_mm_s_sim.
      - apply get_mm_l_sim. 
      - (* bootloader *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit bootloader_exist; eauto 1. eapply match_related.
        intros (labd' & HP & HM & HN).
        match_external_states_simpl. 
      - apply trapin_sim.
      - (* trapout' *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        inv match_extcall_states.
        exploit trapout_exist; eauto 1. eapply match_related.
        intros (labd' & HP & HM & HN).
        inv match_match. match_external_states_simpl.
      - apply hostin_sim.
      - (* hostout' *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        inv match_extcall_states.
        exploit hostout_exist; eauto 1. eapply match_related.
        intros (labd' & HP & HM & HN).
        inv match_match. match_external_states_simpl.
      - apply trap_info_get_sim.
      - apply trap_info_ret_sim.
      - layer_sim_simpl.
        + eapply load_correct.
        + eapply store_correct.
    Qed.

  End WITHMEM.

End Refinement.
