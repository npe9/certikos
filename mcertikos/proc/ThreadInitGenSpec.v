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
Require Import PThreadIntro.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata (cdata_ops := mshareintro_data_ops) LDATA).

  (*Inductive thread_free_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | thread_free_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n:
      PThreadIntro.thread_free_spec labd (Int.unsigned n) = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      thread_free_spec_low_step s WB (Vint n :: nil) (m'0, labd) Vundef (m'0, labd').*)

  Inductive thread_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | thread_init_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      PThreadIntro.thread_init_spec (Int.unsigned mbi_adr) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      thread_init_spec_low_step s WB (Vint mbi_adr :: nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (*Definition thread_free_spec_low: compatsem LDATAOps :=
      csem thread_free_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.*)

    Definition thread_init_spec_low: compatsem LDATAOps :=
      csem thread_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    (*Definition MSpec : compatlayer LDATAOps :=
      thread_free ↦ thread_free_spec_low
      ⊕ thread_init ↦ thread_init_spec_low.*)

  End WITHMEM.

End SPECIFICATION.