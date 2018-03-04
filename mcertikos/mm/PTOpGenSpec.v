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

Require Import MPTIntro.
Require Import AbstractDataType.
Require Import CalRealIDPDE.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section PTOPGEN_DEFINE.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive ptRead_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptRead_spec_low_intro s (WB: _ -> Prop) m'0 labd n vadr padr:
      ptRead_spec (Int.unsigned n) (Int.unsigned vadr) labd = Some (Int.unsigned padr) ->
      kernel_mode labd ->
      high_level_invariant  labd ->
      ptRead_spec_low_step s WB (Vint n:: Vint vadr :: nil) (m'0, labd) (Vint padr) (m'0, labd).

  Inductive ptReadPDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptReadPDE_spec_low_intro s (WB: _ -> Prop) m'0 labd n vadr padr:
      ptReadPDE_spec (Int.unsigned n) (Int.unsigned vadr) labd = Some (Int.unsigned padr) ->
      kernel_mode labd ->
      high_level_invariant  labd ->
      ptReadPDE_spec_low_step s WB (Vint n:: Vint vadr :: nil) (m'0, labd) (Vint padr) (m'0, labd).

  Inductive ptRmvAux_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptRmvAux_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr:
      ptRmvAux_spec (Int.unsigned n) (Int.unsigned vadr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant  labd ->
      ptRmvAux_spec_low_step s WB (Vint n:: Vint vadr :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive ptRmvPDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptRmvPDE_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr:
      ptRmvPDE_spec (Int.unsigned n) (Int.unsigned vadr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant  labd ->
      ptRmvPDE_spec_low_step s WB (Vint n:: Vint vadr :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive ptInsertAux_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptInsertAux_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr padr p:
      ptInsertAux_spec (Int.unsigned n) (Int.unsigned vadr)
      (Int.unsigned padr) (Int.unsigned p) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant  labd ->
      ptInsertAux_spec_low_step s WB (Vint n:: Vint vadr :: Vint padr :: Vint p :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive ptInsertPDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptInsertPDE_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr padr:
      ptInsertPDE_spec (Int.unsigned n) (Int.unsigned vadr)
      (Int.unsigned padr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant  labd ->
      ptInsertPDE_spec_low_step s WB (Vint n:: Vint vadr :: Vint padr :: nil) (m'0, labd) Vundef (m'0, labd').


  Function idpde_init_low_spec (mbi_adr:Z) (adt: RData)  : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo}  {AT: real_AT (AT adt)} {nps: real_nps} 
             {AC: real_AC} {init: true} {idpde: real_idpde (idpde adt)}
      | _ => None
    end.

  Inductive idpde_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | idpdeinit_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      idpde_init_low_spec (Int.unsigned mbi_adr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      idpde_init_spec_low_step s WB (Vint mbi_adr :: nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition ptRead_spec_low: compatsem LDATAOps :=
      csem ptRead_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition ptReadPDE_spec_low: compatsem LDATAOps :=
      csem ptReadPDE_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition ptRmvAux_spec_low: compatsem LDATAOps :=
      csem ptRmvAux_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition ptRmvPDE_spec_low: compatsem LDATAOps :=
      csem ptRmvPDE_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition ptInsertAux_spec_low: compatsem LDATAOps :=
      csem ptInsertAux_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition ptInsertPDE_spec_low: compatsem LDATAOps :=
      csem ptInsertPDE_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition idpde_init_spec_low: compatsem LDATAOps :=
      csem idpde_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

  End WITHMEM.

End PTOPGEN_DEFINE.  
