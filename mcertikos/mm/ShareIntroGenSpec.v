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
(*          Spec between MPTNew and MShareIntro                        *)
(*                                                                     *)
(*          Joshua Lockerman                                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provided the low spec between MPTNew and MShareIntro layers **)
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
Require Import MPTNew.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section MSHAREOPGEN_DEFINE.

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive get_shared_mem_loc_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
      sextcall_sem (mem := mwd LDATAOps) :=
      get_shared_mem_loc_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 pid1 pid2 n:
        find_symbol s SHRDMEMPOOL_LOC = Some b0 ->
        Mem.load Mint32 m'0 b0
                 (768 * Int.unsigned pid1 +
                  12 * Int.unsigned pid2 + 0)
        = Some (Vint n) ->
        0 <= Int.unsigned pid1 < num_proc ->
        0 <= Int.unsigned pid2 < num_proc ->
        kernel_mode (snd m'0) ->
        get_shared_mem_loc_spec_low_step s WB (Vint pid1 :: Vint pid2 :: nil) m'0 (Vint n) m'0.
    
  Inductive set_shared_mem_loc_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
      sextcall_sem (mem := mwd LDATAOps) :=
      set_shared_mem_loc_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 pid1 pid2 loc:
        find_symbol s SHRDMEMPOOL_LOC = Some b0 ->
        Mem.store Mint32 m'0 b0
                  (768 * Int.unsigned pid1 +
                   12 * Int.unsigned pid2 + 0)
                  (Vint loc)
        = Some m0 ->
        0 <= Int.unsigned pid1 < num_proc ->
        0 <= Int.unsigned pid2 < num_proc ->
        kernel_mode (snd m'0) ->
        set_shared_mem_loc_spec_low_step s WB (Vint pid1 :: Vint pid2 :: Vint loc :: nil) m'0 Vundef m0.

  Inductive get_shared_mem_state_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
      sextcall_sem (mem := mwd LDATAOps) :=
      get_shared_mem_state_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 pid1 pid2 n:
        find_symbol s SHRDMEMPOOL_LOC = Some b0 ->
        Mem.load Mint32 m'0 b0
                 (768 * Int.unsigned pid1 +
                  12 * Int.unsigned pid2 + 4)
        = Some (Vint n) ->
        0 <= Int.unsigned pid1 < num_proc ->
        0 <= Int.unsigned pid2 < num_proc ->
        kernel_mode (snd m'0) ->
        get_shared_mem_state_spec_low_step s WB (Vint pid1 :: Vint pid2 :: nil) m'0 (Vint n) m'0.

  Inductive set_shared_mem_state_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
      sextcall_sem (mem := mwd LDATAOps) :=
      set_shared_mem_state_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 pid1 pid2 loc:
        find_symbol s SHRDMEMPOOL_LOC = Some b0 ->
        Mem.store Mint32 m'0 b0
                  (768 * Int.unsigned pid1 +
                   12 * Int.unsigned pid2 + 4)
                  (Vint loc)
        = Some m0 ->
        0 <= Int.unsigned pid1 < num_proc ->
        0 <= Int.unsigned pid2 < num_proc ->
        kernel_mode (snd m'0) ->
        set_shared_mem_state_spec_low_step s WB (Vint pid1 :: Vint pid2 :: Vint loc :: nil) m'0 Vundef m0.

  Inductive get_shared_mem_seen_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
      sextcall_sem (mem := mwd LDATAOps) :=
      get_shared_mem_seen_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 pid1 pid2 n:
        find_symbol s SHRDMEMPOOL_LOC = Some b0 ->
        Mem.load Mint32 m'0 b0
                 (768 * Int.unsigned pid1 +
                  12 * Int.unsigned pid2 + 8)
        = Some (Vint n) ->
        0 <= Int.unsigned pid1 < num_proc ->
        0 <= Int.unsigned pid2 < num_proc ->
        kernel_mode (snd m'0) ->
        get_shared_mem_seen_spec_low_step s WB (Vint pid1 :: Vint pid2 :: nil) m'0 (Vint n) m'0.

  Inductive set_shared_mem_seen_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
      sextcall_sem (mem := mwd LDATAOps) :=
      set_shared_mem_seen_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 pid1 pid2 loc:
        find_symbol s SHRDMEMPOOL_LOC = Some b0 ->
        Mem.store Mint32 m'0 b0
                  (768 * Int.unsigned pid1 +
                   12 * Int.unsigned pid2 + 8)
                  (Vint loc)
        = Some m0 ->
        0 <= Int.unsigned pid1 < num_proc ->
        0 <= Int.unsigned pid2 < num_proc ->
        kernel_mode (snd m'0) ->
        set_shared_mem_seen_spec_low_step s WB (Vint pid1 :: Vint pid2 :: Vint loc :: nil) m'0 Vundef m0.

  Inductive clear_shared_mem_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    clear_shared_mem_spec_low_intro s (WB: _ -> Prop) (m'0 m1 m2 m0: mwd LDATAOps) b0 pid1 pid2:
      find_symbol s SHRDMEMPOOL_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0
                (Int.unsigned
                   (Int.repr
                      (768 * Int.unsigned pid1 +
                       12 * Int.unsigned pid2 + 0)))
                (Vint Int.zero)
      = Some m1 ->
      Mem.store Mint32 m1 b0
                (Int.unsigned
                   (Int.repr
                      (768 * Int.unsigned pid1 +
                       12 * Int.unsigned pid2 + 4)))
                (Vint (Int.repr (SHARED_MEM_DEAD)))
      = Some m2 ->
      Mem.store Mint32 m2 b0
                (Int.unsigned
                   (Int.repr
                      (768 * Int.unsigned pid1+
                       12 * Int.unsigned pid2 + 8)))
                (Vint Int.one)
      = Some m0 ->
      0 <= Int.unsigned pid1 < num_proc ->
      0 <= Int.unsigned pid2 < num_proc ->
      kernel_mode (snd m'0) ->
      clear_shared_mem_spec_low_step s WB (Vint pid1 :: Vint pid2 :: nil) m'0 Vundef m0.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition get_shared_mem_state_spec_low: compatsem LDATAOps := 
      csem get_shared_mem_state_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition set_shared_mem_state_spec_low: compatsem LDATAOps := 
      csem set_shared_mem_state_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.


    Definition get_shared_mem_loc_spec_low: compatsem LDATAOps := 
      csem get_shared_mem_loc_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition set_shared_mem_loc_spec_low: compatsem LDATAOps := 
      csem set_shared_mem_loc_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.


    Definition get_shared_mem_seen_spec_low: compatsem LDATAOps := 
      csem get_shared_mem_seen_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition set_shared_mem_seen_spec_low: compatsem LDATAOps := 
      csem set_shared_mem_seen_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition clear_shared_mem_spec_low: compatsem LDATAOps := 
      csem clear_shared_mem_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

  End WITHMEM.

End MSHAREOPGEN_DEFINE.