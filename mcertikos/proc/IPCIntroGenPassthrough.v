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
(*           Layers of PM: Refinement Proof for PThreadIntro           *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PKContextNew layer and PThreadIntro layer*)
Require Import IPCIntroGenDef.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
    Proof.
      accessor_prop_tac.
      - eapply flatmem_store_exists; eauto.
      - eapply flatmem_store_match; eauto.
    Qed.

    Lemma passthrough_correct:
      sim (crel HDATA LDATA) pipcintro_passthrough pthread.
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
      - apply thread_yield_sim.
      - apply thread_sleep_sim.
      - layer_sim_simpl.
        + eapply load_correct2.
        + eapply store_correct2.
    Qed.

  End WITHMEM.

End Refinement.
