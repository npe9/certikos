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
Require Import Globalenvs.
Require Import Smallstep.
Require Import Asm.
Require Import Conventions.
Require Import Machregs.
Require Import Observation.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.

Require Import LAsmModuleSemDef.
Require Import LAsm.

Section SINGLE_EVENT.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps LAsm.function Ctypes.type LAsm.fundef unit}.
  Context `{make_program_prf: !MakeProgram LAsm.function Ctypes.type LAsm.fundef unit}.

  Lemma LAsm_single_events `{D: compatdata} {L: compatlayer D}:
        forall (LL_ACC_DEF: LAsm.AccessorsDefined L) 
           (LL_DETERM: ExternalCallsXDefined (L))
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet)
           ph,
          single_events (LAsm.semantics (lcfg_ops := LC L) ph).
  Proof.
    red; intros. 
    assert(externalcall_prf: ExternalCalls (mwd D) 
                                           (external_calls_ops:= compatlayer_extcall_ops L)).
    {
      eapply compatlayer_extcall_strong; try assumption.
    }

    inv H; simpl.
    - omega.
    - inv H3. eapply external_call_trace_length; eauto.
    - inv H4. eapply external_call_trace_length; eauto.
    - inv H3. eapply external_call_trace_length; eauto.
    - inv H2. destruct H as [?[?[?[? Hsem]]]]; subst.
      inv Hsem. simpl. omega.
  Qed.

End SINGLE_EVENT.
