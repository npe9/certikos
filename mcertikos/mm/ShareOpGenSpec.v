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
(*          Spec between MShareIntro and MShareOp                      *)
(*                                                                     *)
(*          Joshua Lockerman                                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provided the low spec between MShareIntro and MShareOp layer*)
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
Require Import MShareIntro.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section MSHAREOPGEN_DEFINE.

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive shared_mem_to_ready_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | shared_mem_to_ready_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pid1 pid2 vadr n:
      shared_mem_to_ready_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) labd
      = Some (labd', (Int.unsigned n)) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      shared_mem_to_ready_spec_low_step s WB (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                     (m'0, labd) (Vint n) (m'0, labd').

  Inductive shared_mem_to_pending_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | shared_mem_to_pending_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pid1 pid2 vadr:
      shared_mem_to_pending_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) labd
      = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      shared_mem_to_pending_spec_low_step s WB (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                     (m'0, labd) Vundef (m'0, labd').

  Inductive shared_mem_to_dead_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | shared_mem_to_dead_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' pid1 pid2 vadr:
      shared_mem_to_dead_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) labd
      = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      shared_mem_to_dead_spec_low_step s WB (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                     (m'0, labd) Vundef (m'0, labd').

  Inductive get_shared_mem_status_seen_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | get_shared_mem_status_seen_spec_low_intro s (WB: _ -> Prop) m'0 labd pid1 pid2 n:
      get_shared_mem_status_seen_spec (Int.unsigned pid1) (Int.unsigned pid2) labd
      = Some (Int.unsigned n) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      get_shared_mem_status_seen_spec_low_step s WB (Vint pid1 :: Vint pid2 :: nil)
                                     (m'0, labd) (Vint n) (m'0, labd).


  Inductive shared_mem_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | shared_mem_init_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      sharedmem_init_spec (Int.unsigned mbi_adr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      shared_mem_init_spec_low_step s WB (Vint mbi_adr :: nil)
                                     (m'0, labd) Vundef (m'0, labd').


  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.


    Definition shared_mem_to_ready_spec_low: compatsem LDATAOps :=
      csem shared_mem_to_ready_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tint32.

    Definition shared_mem_to_pending_spec_low: compatsem LDATAOps :=
      csem shared_mem_to_pending_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition shared_mem_to_dead_spec_low: compatsem LDATAOps :=
      csem shared_mem_to_dead_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition get_shared_mem_status_seen_spec_low: compatsem LDATAOps :=
      csem get_shared_mem_status_seen_spec_low_step
           (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition shared_mem_init_spec_low: compatsem LDATAOps :=
      csem shared_mem_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

  End WITHMEM.

End MSHAREOPGEN_DEFINE.
