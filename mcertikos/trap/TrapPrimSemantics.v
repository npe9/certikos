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
(*              General Semantics for Primitives                       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the general semantics for primitives at all layers*)
Require Import Coqlib.
Require Import Maps.
Require Import Globalenvs.
Require Import AsmX.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import AST.
Require Import AuxStateDataType.
Require Import Constant.
Require Import FlatMemory.
Require Import GlobIdent.
Require Import Integers.
Require Import Conventions.
Require Import LAsm.
Require Import CommonTactic.
Require Import AuxLemma.

Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Export mCertiKOSType.
Require Import liblayers.compat.CompatGenSem.

Section Semantics.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context {RData} `{HD: CompatData RData}.

    Section Proc_Create.

      Variable trap_proc_create_spec : stencil -> mem -> RData -> option RData.

      Inductive extcall_trap_proccreate_sem (s: stencil) (WB: block -> Prop):
        list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
      | extcall_trap_proccreate_sem_intro:
          forall m abd abd',
            (* read arguements*)
            trap_proc_create_spec s m abd = Some abd' ->
            extcall_trap_proccreate_sem s WB nil (m, abd) Vundef (m, abd').

      Definition extcall_trap_proccreate_info: sextcall_info :=
        {|
          sextcall_step := extcall_trap_proccreate_sem;
          sextcall_csig := mkcsig (type_of_list_type (nil)) Tvoid;
          sextcall_valid s := true
        |}.

      Class TrapProcCreateINV := 
        {
          trap_proc_create_high_inv:
            forall s m d d',
              trap_proc_create_spec s m d = Some d'->
              high_level_invariant d ->
              high_level_invariant d';
          trap_proc_create_low_inv:
            forall s m d d',
              trap_proc_create_spec s m d = Some d'->
              (genv_next s <= Mem.nextblock m)%positive ->
              low_level_invariant (Mem.nextblock m) d ->
              low_level_invariant (Mem.nextblock m) d';
          trap_proc_create_kernel_mode:
            forall s m d d',
              trap_proc_create_spec s m d = Some d'->
              kernel_mode d ->
              kernel_mode d';
          trap_proc_create_extends:
            forall s m m0 d d',
              trap_proc_create_spec s m d = Some d'->
              Mem.extends m m0 ->
              trap_proc_create_spec s m0 d = Some d';
          trap_proc_create_inject:
            forall s m m0 d d' f,
              trap_proc_create_spec s m d = Some d'->
              Mem.inject f m m0 ->
              meminj_preserves_stencil s f ->
              trap_proc_create_spec s m0 d = Some d'
        }.

      Section INV.
        
        Context {inv: TrapProcCreateINV}.

        Instance extcall_trap_proccreate_invs:
          ExtcallInvariants extcall_trap_proccreate_info.
        Proof.
          constructor; intros; inv H.
          - (* low level invariant *)
            eapply trap_proc_create_low_inv; eauto.
          - (* high level invariant *)
            eapply trap_proc_create_high_inv; eauto.
          - (* kernel mode*)
            eapply trap_proc_create_kernel_mode; eauto.
          - (* nextblock *)
            reflexivity.
          - (* inject neutral *)
            split; auto.
          - (* well typed *)
            simpl; trivial.
        Qed.

        Instance extcall_trap_proccreate_props:
          ExtcallProperties extcall_trap_proccreate_info.
        Proof.
          constructor; intros.
          - (* well typed *)
            inv H. simpl. trivial.
          - (* valid_block *)
            inv H. unfold Mem.valid_block in *.
            lift_unfold. trivial.
          - (* perm *)
            inv H. lift_unfold. trivial.
          - (* unchanges *)
            inv H. simpl. apply Mem.unchanged_on_refl.
          - (* extend *)
            inv H. inv_val_inject. lift_simpl.
            destruct H0 as [HT1 HT2].
            destruct m1' as [? ?]. simpl in *. subst.
            refine_split; eauto.
            + econstructor; eauto.
              eapply trap_proc_create_extends; eauto.
            + lift_unfold. split; trivial.
            + simpl. apply Mem.unchanged_on_refl.
          - (* inject *)
            inv H0. (*pose proof H4 as Hsymbol. apply H in H4. *)
            inv_val_inject.
            lift_simpl. destruct H1 as [HT1 HT2].
            destruct m1' as [? ?]. simpl in *. subst.
            refine_split; eauto.
            + econstructor; eauto.
              eapply trap_proc_create_inject; eauto.            
            + lift_unfold. split; trivial.
            + apply Mem.unchanged_on_refl.
            + simpl. apply Mem.unchanged_on_refl.
            + constructor; congruence.

          - (* deterministic*)
            inv H. inv H0. 
            split; try congruence.
          - (* WB *)
            inv H0. econstructor; eauto.
          - (* load *)
            inv H. lift_unfold. trivial.
        Qed.

        Definition trap_proccreate_compatsem : compatsem (cdata RData) :=
          compatsem_inl {|
              sextcall_primsem_step := extcall_trap_proccreate_info;
              sextcall_props := OK _;
              sextcall_invs := OK _
            |}.

      End INV.

    End Proc_Create.

End Semantics.