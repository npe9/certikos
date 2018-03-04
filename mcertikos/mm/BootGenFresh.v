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
Require Import BootGenDef.
Require Import BootGenAccessorDef.
Require Import BootGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Lemma fload_spec_ref:
      compatsim (crel HDATAOps LDATAOps) (gensem fload'_spec) fload_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      functional inversion H2; subst.
      refine_split; try (econstructor; eauto).
      - simpl. lift_trivial.
        exploit flatmem_load_correct0; eauto.
        + simpl. omega.
        + simpl. apply Zdivide_mult_r. apply Zdivide_refl.
        + simpl; lift_trivial.
          intros (v' & HLoad & HVal). inv HVal.
          rewrite HLoad. 
          rewrite <- (Int.repr_unsigned z).
          rewrite <- (Int.repr_unsigned n).
          congruence.
      - inv match_related. simpl.
        split; congruence.
      - apply inject_incr_refl.
    Qed.

    Lemma fstore_spec_ref:
      compatsim (crel HDATAOps LDATAOps) (gensem fstore'_spec) fstore_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData). inv H.
      functional inversion H1; subst.
      rewrite Int.repr_unsigned in *. unfold fstore'_spec in H1.
      revert H1. subrewrite.
      exploit flatmem_store_correct0; eauto.
      - simpl. omega.
      - simpl. apply Zdivide_mult_r. apply Zdivide_refl.
      - intros (m2' & HST & Hmatch_ext').
        refine_split; eauto.
        econstructor; try eassumption.
        + simpl. lift_trivial. rewrite Int.repr_unsigned in HST.
          rewrite HST. reflexivity.
        + inv match_related. simpl.
          split; congruence.
    Qed.

  End WITHMEM.

End Refinement.