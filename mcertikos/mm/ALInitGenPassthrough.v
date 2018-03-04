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
Require Import ALInitGenDef.

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
        forall habd habd' labd f,
          setPG0_spec habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', setPG_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ AT habd' = AT habd /\ nps habd' = nps habd.
      Proof.
        unfold setPG0_spec, setPG_spec; intros until f; exist_simpl.
      Qed.

      Lemma setCR3_exist:
        forall habd habd' labd id ofs f,
          setCR30_spec habd (GLOBP id ofs) = Some habd'
          -> relate_RData f habd labd
          -> exists labd', setCR3_spec labd (GLOBP id ofs) = Some labd' /\ relate_RData f habd' labd'
                           /\ AT habd' = AT habd /\ nps habd' = nps habd.
      Proof.
        unfold setCR30_spec, setCR3_spec; intros until f; exist_simpl.
      Qed.

      Lemma trapout_exist:
        forall habd habd' labd f,
          trapout0_spec habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', trapout'_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ AT habd' = AT habd /\ nps habd' = nps habd.
      Proof.
        unfold trapout0_spec, trapout'_spec; intros until f; exist_simpl.
      Qed.

      Lemma hostout_exist:
        forall habd habd' labd f,
          hostout_spec habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', hostout'_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ AT habd' = AT habd /\ nps habd' = nps habd.
      Proof.
        unfold hostout_spec, hostout'_spec; intros until f; exist_simpl.
      Qed.

    End Exists.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store') (lflatmem_store:= flatmem_store')).
    Proof.
      accessor_prop_tac.
      - eapply flatmem_store'_exists; eauto.
    Qed.          

    Lemma passthrough_correct:
      sim (crel HDATA LDATA) malinit_passthrough mboot.
    Proof.
      sim_oplus.
      - apply fload'_sim.
      - apply fstore'_sim.
      - apply flatmem_copy'_sim.
      - apply vmxinfo_get_sim.
      - apply device_output_sim.
      - apply get_size_sim.
      - apply is_mm_usable_sim.
      - apply get_mm_s_sim.
      - apply get_mm_l_sim.
      - apply bootloader0_sim.
      - (* set_PG *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit setPG_exist; eauto 1; intros [labd' [HP [HM[HAT HN]]]].
        match_external_states_simpl. congruence.
      - apply clearCR2_sim.
      - (* set_CR3 *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        inv_val_inject.
        eapply inject_forward_equal' in H8; eauto 1. inv H8.
        exploit setCR3_exist; eauto 1; intros [labd' [HP [HM[HAT HN]]]].
        match_external_states_simpl. 
        rewrite Int.add_zero; eauto. congruence.
      - apply trapin_sim.
      - (* trapout *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        inv H4. inv match_extcall_states.
        exploit trapout_exist; eauto 1; intros [labd' [HP [HM[HAT HN]]]].          
        inv match_match. match_external_states_simpl. congruence.
      - apply hostin_sim.
      - (* hostout *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        inv H4. inv match_extcall_states.
        exploit hostout_exist; eauto 1; intros [labd' [HP [HM[HAT HN]]]].          
        inv match_match. match_external_states_simpl. congruence.
      - apply trap_info_get_sim.
      - apply trap_info_ret_sim.
      - layer_sim_simpl.
        + eapply load_correct1.
        + eapply store_correct1.
    Qed.

  End WITHMEM.

End Refinement.
