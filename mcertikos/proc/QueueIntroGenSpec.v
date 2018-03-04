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

Require Import PThreadInit.
Require Import AbstractDataType.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.


(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive get_head_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_head_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n v:
      find_symbol s TDQPool_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned n) * 8) = Some (Vint v) ->
      0 <= (Int.unsigned n) <= num_chan ->
      kernel_mode (snd m'0) ->
      get_head_spec_low_step s WB (Vint n :: nil) m'0 (Vint v) m'0.

  Inductive get_tail_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_tail_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n v:
      find_symbol s TDQPool_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned n) * 8 + 4) = Some (Vint v) ->
      0 <= (Int.unsigned n) <= num_chan ->
      kernel_mode (snd m'0) ->
      get_tail_spec_low_step s WB (Vint n :: nil) m'0 (Vint v) m'0.

  Inductive set_head_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_head_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n v:
      find_symbol s TDQPool_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 8) (Vint v) = Some m0 ->
      0 <= (Int.unsigned n) <= num_chan ->
      kernel_mode (snd m'0) ->
      set_head_spec_low_step s WB (Vint n :: Vint v :: nil) m'0 Vundef m0.

  Inductive set_tail_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_tail_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n v:
      find_symbol s TDQPool_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 8 + 4) (Vint v) = Some m0 ->
      0 <= (Int.unsigned n) <= num_chan ->
      kernel_mode (snd m'0) ->
      set_tail_spec_low_step s WB (Vint n :: Vint v :: nil) m'0 Vundef m0.

  Inductive tdq_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    tdq_init_spec_low_intro s (WB: _ -> Prop) (m0 m1 m2: mwd LDATAOps) b0 n:
      find_symbol s TDQPool_LOC = Some b0 ->
      Mem.store Mint32 m0 b0 (Int.unsigned n * 8) (Vint (Int.repr num_chan)) = Some m1 ->
      Mem.store Mint32 m1 b0 (Int.unsigned n * 8 + 4) (Vint (Int.repr num_chan)) = Some m2 ->
      0 <= (Int.unsigned n) <= num_chan ->
      kernel_mode (snd m0) ->
      tdq_init_spec_low_step s WB (Vint n :: nil) m0 Vundef m2.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_head_spec_low: compatsem LDATAOps :=
      csem get_head_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition set_head_spec_low: compatsem LDATAOps :=
      csem set_head_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition get_tail_spec_low: compatsem LDATAOps :=
      csem get_tail_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition set_tail_spec_low: compatsem LDATAOps :=
      csem set_tail_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition tdq_init_spec_low: compatsem LDATAOps :=
      csem tdq_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.
    
    (*Definition MSpec : compatlayer LDATAOps :=
      get_head ↦ get_head_spec_low
                ⊕ get_tail ↦ get_tail_spec_low
                ⊕ set_head ↦ set_head_spec_low
                ⊕ set_tail ↦ set_tail_spec_low
                ⊕ tdq_init ↦ tdq_init_spec_low.
    
    Definition MVar : compatlayer LDATAOps :=
      TDQPool_LOC ↦ mkglobvar (Tarray Tint32 ((num_chan + 1) * 8) (mk_attr false None))
              (Init_space ((num_chan + 1) * 8) :: nil) false false.*)

  End WITHMEM.

End Refinement.
