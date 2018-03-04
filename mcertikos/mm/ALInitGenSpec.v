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
Require Import MBoot.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section ALINITGEN_DEFINE.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive getnps_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    getnps_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n:
      find_symbol s NPS_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 0 = Some (Vint n) ->
      kernel_mode (snd m'0) ->
      getnps_spec_low_step s WB nil m'0 (Vint n) m'0.

  Inductive setnps_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setnps_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n:
      find_symbol s NPS_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 0 (Vint n) = Some m0 ->
      kernel_mode (snd m'0) ->
      setnps_spec_low_step s WB (Vint n :: nil) m'0 Vundef m0.

  Inductive getatu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps) :=
    getatu_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n v v':
      find_symbol s AT_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * 12 + 4) = Some (Vint v') ->
      Int.unsigned v = IntToBoolZ v' ->
      0 <= (Int.unsigned n) < maxpage ->
      kernel_mode (snd m'0) ->
      getatu_spec_low_step s WB (Vint n :: nil) m'0 (Vint v) m'0.

  Inductive setatu_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setatu_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n v:
      find_symbol s AT_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 12 + 4) (Vint v) = Some m0 ->
      0 <= (Int.unsigned n) < maxpage ->
      kernel_mode (snd m'0) ->
      setatu_spec_low_step s WB (Vint n :: Vint v :: nil) m'0 Vundef m0.

  Inductive getatc_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps) :=
    getatc_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n v:
      find_symbol s AT_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * 12 + 8) = Some (Vint v) ->
      0 <= (Int.unsigned n) < maxpage ->
      kernel_mode (snd m'0) ->
      getatc_spec_low_step s WB (Vint n :: nil) m'0 (Vint v) m'0.

  Inductive setatc_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setatc_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n v:
      find_symbol s AT_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 12 + 8) (Vint v) = Some m0 ->
      0 <= (Int.unsigned n) < maxpage ->
      kernel_mode (snd m'0) ->
      setatc_spec_low_step s WB (Vint n :: Vint v :: nil) m'0 Vundef m0.

  Inductive getatnorm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    getatnorm_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n v v':
      find_symbol s AT_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * 12) = Some (Vint v') ->
      Int.unsigned v = ZToATTypeZ (Int.unsigned v') ->
      0 <= (Int.unsigned n) < maxpage ->
      kernel_mode (snd m'0) ->
      getatnorm_spec_low_step s WB (Vint n :: nil) m'0 (Vint v) m'0.

  Inductive setatnorm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setatnorm_spec_low_intro s (WB: _ -> Prop) (m'0 m0 m1 m2: mwd LDATAOps) b0 n v:
      find_symbol s AT_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 12) (Vint v) = Some m0 ->
      Mem.store Mint32 m0 b0 (Int.unsigned n * 12 + 4) Vzero = Some m1 ->
      Mem.store Mint32 m1 b0 (Int.unsigned n * 12 + 8) Vzero = Some m2 ->
      0 <= (Int.unsigned n) < maxpage ->
      kernel_mode (snd m'0) ->
      setatnorm_spec_low_step s WB (Vint n :: Vint v :: nil) m'0 Vundef m2.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_nps_spec_low: compatsem LDATAOps :=
      csem getnps_spec_low_step Tnil Tint32.

    Definition set_nps_spec_low: compatsem LDATAOps :=
      csem setnps_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition at_get_spec_low: compatsem LDATAOps :=
      csem getatu_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition at_set_spec_low: compatsem LDATAOps :=
      csem setatu_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition is_norm_spec_low: compatsem LDATAOps :=
      csem getatnorm_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition set_norm_spec_low: compatsem LDATAOps :=
      csem setatnorm_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.
 
    Definition at_get_c_spec_low: compatsem LDATAOps :=
      csem getatc_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition at_set_c_spec_low: compatsem LDATAOps :=
      csem setatc_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.
   
  End WITHMEM.

End ALINITGEN_DEFINE.  
