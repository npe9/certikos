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
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.

Require Import compcert.cfrontend.Ctypes.
Require Import Conventions.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.

Require Import AbstractDataType.
Require Import Soundness.
Require Import TSysCall.
Require Import I64Layer.
Require Import LoadStoreSem2.

Require Import SecurityCommon.
Require Import ProofIrrelevance.
Require Import MakeProgram.

Require Import SecurityInv1.
Require Import SecurityInv2.

(* This file combines the invariants established in SecurityInv1.v and SecurityInv2.v.
   It defines two invariants secure_inv and secure_inv' which will be assumed by the
   main security lemmas. We prove that both of these invariants are preserved by each
   step of tsyscall, but only the first one holds on the initial state. See below
   for further discussion, as well as Section 3 of the paper. *)

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Local Instance : ExternalCallsOps (mwd (cdata RData)) := 
    CompatExternalCalls.compatlayer_extcall_ops tsyscall_layer.
  Local Instance : LayerConfigurationOps := compatlayer_configuration_ops tsyscall_layer.

  Section WITHIMPL.
    
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Variables (s : stencil) (M : module) (ge : genv) (b : block).
    Hypothesis (Hmake : make_globalenv s M tsyscall_layer = OK ge).
    Hypothesis (Hpsu : Genv.find_symbol ge proc_start_user = Some b).

    Section SECURE_INV.

      (* secure_inv and secure_inv', the two invariants defined in this file. Note
         that all fields of these invariants come from either SecurityInv1.v or
         SecurityInv2.v. *)

      Record secure_inv id d :=
        {
          sec_high_inv: high_level_invariant d;
          sec_ihost_inv: ihost d = true;
          sec_RA_startuser_inv: RA_startuser b d;
          sec_single_mapped_inv: single_mapped (LAT d) (nps d) id;
          sec_unshared_inv: unshared (LAT d) (nps d) id
        }.

      (* secure_inv' is the part of the invariant that does not hold on the initial
         state. Our security theorem only applies to configurations of mCertiKOS that 
         set things up to make this invariant hold. At some point, it might be nice to
         to design a particular family of configurations and prove that all members
         of this family correctly establish the invariant.

         Note that the assumption here is only that the mCertiKOS configuration
         spawns the observer process (if the observer process were never spawned, then
         it would be meaningless to reason about its security), and that the initial
         kernel process 0 eventually switches to a different user mode process 
         without placing itself on the ready queue (meaning that process 0 will never
         be scheduled again).

         Paper Reference: Section 3 *)
      Record secure_inv' id rs d :=
        {
          sec_used: cused (ZMap.get id (AC d)) = true;
          sec_usermode: usermode b rs d
        }.

      (* proof that secure_inv holds on the initial state *)

      Lemma secure_inv_init : 
        forall id, secure_inv id init_adt.
      Proof.
        intro id; constructor.
        - apply empty_data_high_level_invariant.
        - auto.
        - intros ? ? Hcon; simpl in Hcon; zmap_simpl; inv Hcon.
        - intros ? ? ? ? ? Hcon; simpl in Hcon; zmap_simpl; inv Hcon.
        - simpl; intros ? ? Hcon; inv Hcon.
          zmap_simpl; inv H0.
      Qed.

      (* proofs that the two invariants are preserved by each step *)

      Lemma secure_inv_preserved :
        forall id rs rs' (m m' : mem) (d d' : cdata RData) t,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
          secure_inv id d -> secure_inv id d'.
      Proof.
        intros id rs rs' m m' d d' t Hstep Hinv.
        destruct Hinv; constructor.
        - eapply step_inv1; eauto.
        - eapply ihost_inv; eauto.
        - eapply RA_startuser_inv; eauto.
        - eapply step_inv1; eauto. 
        - eapply step_inv1; eauto. 
      Qed.

      Lemma secure_inv'_preserved :
        forall id rs rs' (m m' : mem) (d d' : cdata RData) t,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
          secure_inv id d -> secure_inv' id rs d -> secure_inv' id rs' d'.
      Proof.
        intros id rs rs' m m' d d' t Hstep Hinv Hinv'.
        destruct Hinv; destruct Hinv'; constructor.
        - eapply step_inv1; eauto. 
        - eapply usermode_inv; eauto.
      Qed.

    End SECURE_INV.

  End WITHIMPL.

End WITHMEM.