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
Require Import Conventions.
Require Import PProc.
Require Import ObjArg.
Require Import AbstractDataType.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) RData).

  Inductive uctx_arg1_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_arg1_spec_low_intro s (WB: _ -> Prop) m'0 labd arg:
      uctx_arg1_spec labd = Some (Int.unsigned arg) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_arg1_spec_low_step s WB nil (m'0, labd) (Vint arg) (m'0, labd).

  Inductive uctx_arg2_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_arg2_spec_low_intro s (WB: _ -> Prop) m'0 labd arg:
      uctx_arg2_spec labd = Some (Int.unsigned arg) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_arg2_spec_low_step s WB nil (m'0, labd) (Vint arg) (m'0, labd).

  Inductive uctx_arg3_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_arg3_spec_low_intro s (WB: _ -> Prop) m'0 labd arg:
      uctx_arg3_spec labd = Some (Int.unsigned arg) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_arg3_spec_low_step s WB nil (m'0, labd) (Vint arg) (m'0, labd).

  Inductive uctx_arg4_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_arg4_spec_low_intro s (WB: _ -> Prop) m'0 labd arg:
      uctx_arg4_spec labd = Some (Int.unsigned arg) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_arg4_spec_low_step s WB nil (m'0, labd) (Vint arg) (m'0, labd).

  Inductive uctx_arg5_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_arg5_spec_low_intro s (WB: _ -> Prop) m'0 labd arg:
      uctx_arg5_spec labd = Some (Int.unsigned arg) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_arg5_spec_low_step s WB nil (m'0, labd) (Vint arg) (m'0, labd).

  Inductive uctx_arg6_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_arg6_spec_low_intro s (WB: _ -> Prop) m'0 labd arg:
      uctx_arg6_spec labd = Some (Int.unsigned arg) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_arg6_spec_low_step s WB nil (m'0, labd) (Vint arg) (m'0, labd).

  Inductive uctx_set_errno_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_set_errno_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' arg:
      uctx_set_errno_spec (Int.unsigned arg)  labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_set_errno_spec_low_step s WB (Vint arg :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive uctx_set_retval1_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_set_retval1_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' arg:
      uctx_set_retval1_spec (Int.unsigned arg) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_set_retval1_spec_low_step s WB (Vint arg :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive uctx_set_retval2_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_set_retval2_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' arg:
      uctx_set_retval2_spec (Int.unsigned arg) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_set_retval2_spec_low_step s WB (Vint arg :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive uctx_set_retval3_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_set_retval3_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' arg:
      uctx_set_retval3_spec (Int.unsigned arg) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_set_retval3_spec_low_step s WB (Vint arg :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive uctx_set_retval4_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | uctx_set_retval4_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' arg:
      uctx_set_retval4_spec (Int.unsigned arg) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      uctx_set_retval4_spec_low_step s WB (Vint arg :: nil) (m'0, labd) Vundef (m'0, labd').

  (*Inductive la2pa_resv_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | la2pa_resv_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' arg adr:
      PProc.la2pa_resv_spec labd (Int.unsigned arg) = Some (labd', Int.unsigned adr)  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      la2pa_resv_spec_low_step s WB (Vint arg :: nil) (m'0, labd) (Vint adr) (m'0, labd').*)

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition uctx_arg1_spec_low: compatsem LDATAOps :=
      csem uctx_arg1_spec_low_step Tnil Tint32.

    Definition uctx_arg2_spec_low: compatsem LDATAOps :=
      csem uctx_arg2_spec_low_step Tnil Tint32.

    Definition uctx_arg3_spec_low: compatsem LDATAOps :=
      csem uctx_arg3_spec_low_step Tnil Tint32.

    Definition uctx_arg4_spec_low: compatsem LDATAOps :=
      csem uctx_arg4_spec_low_step Tnil Tint32.

    Definition uctx_arg5_spec_low: compatsem LDATAOps :=
      csem uctx_arg5_spec_low_step Tnil Tint32.

    Definition uctx_arg6_spec_low: compatsem LDATAOps :=
      csem uctx_arg6_spec_low_step Tnil Tint32.

    Definition uctx_set_errno_spec_low: compatsem LDATAOps :=
      csem uctx_set_errno_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition uctx_set_retval1_spec_low: compatsem LDATAOps :=
      csem uctx_set_retval1_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition uctx_set_retval2_spec_low: compatsem LDATAOps :=
      csem uctx_set_retval2_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition uctx_set_retval3_spec_low: compatsem LDATAOps :=
      csem uctx_set_retval3_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition uctx_set_retval4_spec_low: compatsem LDATAOps :=
      csem uctx_set_retval4_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    (*Definition la2pa_resv_spec_low: compatsem LDATAOps :=
      csem la2pa_resv_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.*)

  End WITHMEM.

End SPECIFICATION.