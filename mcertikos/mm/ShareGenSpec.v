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
(*          Spec between MShareOp and MShare                           *)
(*                                                                     *)
(*          Joshua Lockerman                                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provided the low spec between MShareOp and MShare layer*)
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
Require Import AuxLemma.
Require Import FlatMemory.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import RealParams.
Require Import AsmImplLemma.
Require Import GenSem.
Require Import PrimSemantics.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.

Require Import AbstractDataType.
Require Import MShareOp.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section MSAHREGEN_DEFINE.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive shared_mem_status_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | shared_mem_status_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pid1 pid2 n:
      shared_mem_status_spec (Int.unsigned pid1) (Int.unsigned pid2) labd = Some (labd', (Int.unsigned n)) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      shared_mem_status_spec_low_step s WB (Vint pid1 :: Vint pid2 :: nil)
                                     (m'0, labd) (Vint n) (m'0, labd').

  Inductive offer_shared_mem_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | offer_shared_mem_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pid1 pid2 vadr n:
      offer_shared_mem_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) labd
      = Some (labd', (Int.unsigned n)) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      offer_shared_mem_spec_low_step s WB (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                     (m'0, labd) (Vint n) (m'0, labd').


  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.


    Definition shared_mem_status_spec_low: compatsem LDATAOps :=
      csem shared_mem_status_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition offer_shared_mem_spec_low: compatsem LDATAOps :=
      csem offer_shared_mem_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tint32.

  End WITHMEM.

End MSAHREGEN_DEFINE.
