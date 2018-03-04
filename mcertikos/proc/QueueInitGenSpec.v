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
(*          Low Level Specification                                    *)
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

Require Import PQueueIntro.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive enqueue_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | enqueue_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n i:
      PQueueIntro.enqueue_spec (Int.unsigned n) (Int.unsigned i) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      enqueue_spec_low_step s WB (Vint n :: Vint i :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive dequeue_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | dequeue_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n i:
      PQueueIntro.dequeue_spec (Int.unsigned n) labd = Some (labd', (Int.unsigned i))  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      dequeue_spec_low_step s WB (Vint n :: nil) (m'0, labd) (Vint i) (m'0, labd').

  Inductive queue_rmv_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | queue_rmv_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n i:
      queue_rmv_spec (Int.unsigned n) (Int.unsigned i) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      queue_rmv_spec_low_step s WB (Vint n :: Vint i :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive tdqueue_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | tdqueue_init_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      PQueueIntro.tdqueue_init_spec (Int.unsigned mbi_adr) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      tdqueue_init_spec_low_step s WB (Vint mbi_adr :: nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition enqueue_spec_low: compatsem LDATAOps :=
      csem enqueue_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition dequeue_spec_low: compatsem LDATAOps :=
      csem dequeue_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition queue_rmv_spec_low: compatsem LDATAOps :=
      csem queue_rmv_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition tdqueue_init_spec_low: compatsem LDATAOps :=
      csem tdqueue_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    (*Definition MSpec : compatlayer LDATAOps :=
      enqueue ↦ enqueue_spec_low
              ⊕ dequeue ↦ dequeue_spec_low
              ⊕ queue_rmv ↦ queue_rmv_spec_low
              ⊕ tdqueue_init ↦ tdqueue_init_spec_low.*)

  End WITHMEM.

End SPECIFICATION.