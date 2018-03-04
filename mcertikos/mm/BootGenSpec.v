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
Require Import PreInit.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive fload_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    fload_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 addr n:
      find_symbol s FlatMem_LOC = Some b0 ->
      0 <= Int.unsigned addr < adr_low ->
      Mem.load Mint32 m'0 b0 (Int.unsigned addr * 4) = Some (Vint n) ->
      kernel_mode (snd m'0) ->
      fload_spec_low_step s WB (Vint addr :: nil) m'0 (Vint n) m'0.

  Inductive fstore_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    fstore_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 addr n:
      find_symbol s FlatMem_LOC = Some b0 ->
      0 <= Int.unsigned addr < adr_low ->
      Mem.store Mint32 m'0 b0 (Int.unsigned addr * 4) (Vint n) = Some m0 ->
      kernel_mode (snd m'0) ->
      fstore_spec_low_step s WB (Vint addr :: Vint n :: nil) m'0 Vundef m0.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition fload_spec_low: compatsem LDATAOps :=
      csem fload_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition fstore_spec_low: compatsem LDATAOps :=
      csem fstore_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

  End WITHMEM.

End Refinement.  
