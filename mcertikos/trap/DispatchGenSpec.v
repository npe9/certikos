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
Require Import TTrap.
Require Import AbstractDataType.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) RData).

  Inductive sys_dispatch_c_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | sys_dispatch_c_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      sys_dispatch_c_spec s m'0 labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      sys_dispatch_c_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_sendtochan_pre_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_sendtochan_pre_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0 val:
      trap_sendtochan_pre_spec labd = Some (labd0, Int.unsigned val) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_sendtochan_pre_spec_low_step s WB nil (m'0, labd) (Vint val) (m'0, labd0).

  Inductive trap_sendtochan_post_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_sendtochan_post_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_sendtochan_post_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_sendtochan_post_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition sys_dispatch_c_spec_low: compatsem LDATAOps :=
      csem sys_dispatch_c_spec_low_step Tnil Tvoid.

    Definition trap_sendtochan_pre_spec_low: compatsem LDATAOps :=
      csem trap_sendtochan_pre_spec_low_step Tnil Tint32.

    Definition trap_sendtochan_post_spec_low: compatsem LDATAOps :=
      csem trap_sendtochan_post_spec_low_step Tnil Tvoid.

  End WITHMEM.

End SPECIFICATION.