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
Require Import PAbQueue.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive get_curid_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_curid_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 v:
      find_symbol s CURID_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 0 = Some (Vint v) ->
      kernel_mode (snd m'0) ->
      get_curid_spec_low_step s WB nil m'0 (Vint v) m'0.

  Inductive set_curid_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_curid_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 v:
      find_symbol s CURID_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 0 (Vint v) = Some m0 ->
      kernel_mode (snd m'0) ->
      set_curid_spec_low_step s WB (Vint v :: nil) m'0 Vundef m0.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_curid_spec_low: compatsem LDATAOps :=
      csem get_curid_spec_low_step Tnil Tint32.

    Definition set_curid_spec_low: compatsem LDATAOps :=
      csem set_curid_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.
    
    (*Definition MSpec : compatlayer LDATAOps :=
      get_curid ↦ get_curid_spec_low
                ⊕ set_curid ↦ set_curid_spec_low.
     
    Definition MVar : compatlayer LDATAOps :=
      CURID_LOC ↦ mkglobvar Tint32 (Init_int32 Int.zero :: nil) false false.*)

  End WITHMEM.

End Refinement.