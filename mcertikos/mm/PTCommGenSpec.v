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

Require Import MPTOp.

Require Import AbstractDataType.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section PTCOMMGEN_DEFINE.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive pt_init_comm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | pt_init_comm_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      pt_init_comm_spec (Int.unsigned mbi_adr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      pt_init_comm_spec_low_step s WB (Vint mbi_adr :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive ptAllocPDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptAllocPDE_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr padr:
      ptAllocPDE_spec (Int.unsigned n) (Int.unsigned vadr) labd = Some (labd', Int.unsigned padr) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      ptAllocPDE_spec_low_step s WB (Vint n:: Vint vadr :: nil) (m'0, labd) (Vint padr) (m'0, labd').

  Inductive ptFreePDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptFreePDE_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr:
      ptFreePDE_spec (Int.unsigned n) (Int.unsigned vadr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      ptFreePDE_spec_low_step s WB (Vint n:: Vint vadr :: nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition pt_init_comm_spec_low: compatsem LDATAOps :=
      csem pt_init_comm_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition ptAllocPDE_spec_low: compatsem LDATAOps :=
      csem ptAllocPDE_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition ptFreePDE_spec_low: compatsem LDATAOps :=
      csem ptFreePDE_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

  End WITHMEM.

End PTCOMMGEN_DEFINE.
