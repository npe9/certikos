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
Require Import PThread.
Require Import ObjSyncIPC.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  (*Inductive get_chan_info_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_chan_info_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n v:
      find_symbol s CHPOOL_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned n) * 8) = Some (Vint v) ->
      0 <= (Int.unsigned n) < num_chan ->
      kernel_mode (snd m'0) ->
      get_chan_info_spec_low_step s WB (Vint n :: nil) m'0 (Vint v) m'0.

  Inductive get_chan_content_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_chan_content_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n v:
      find_symbol s CHPOOL_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned n) * 8 + 4) = Some (Vint v) ->
      0 <= (Int.unsigned n) < num_chan ->
      kernel_mode (snd m'0) ->
      get_chan_content_spec_low_step s WB (Vint n :: nil) m'0 (Vint v) m'0.

  Inductive set_chan_info_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_chan_info_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n v:
      find_symbol s CHPOOL_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 8) (Vint v) = Some m0 ->
      0 <= (Int.unsigned n) < num_chan ->
      kernel_mode (snd m'0) ->
      set_chan_info_spec_low_step s WB (Vint n :: Vint v :: nil) m'0 Vundef m0.

  Inductive set_chan_content_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_chan_content_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n v:
      find_symbol s CHPOOL_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 8 + 4) (Vint v) = Some m0 ->
      0 <= (Int.unsigned n) < num_chan ->
      kernel_mode (snd m'0) ->
      set_chan_content_spec_low_step s WB (Vint n :: Vint v :: nil) m'0 Vundef m0.

  Inductive init_chan_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    init_chan_spec_low_intro s (WB: _ -> Prop) (m0 m1 m2: mwd LDATAOps) b0 n v1 v2:
      find_symbol s CHPOOL_LOC = Some b0 ->
      Mem.store Mint32 m0 b0 (Int.unsigned n * 8) (Vint v1) = Some m1 ->
      Mem.store Mint32 m1 b0 (Int.unsigned n * 8 + 4) (Vint v2) = Some m2 ->
      0 <= (Int.unsigned n) < num_chan ->
      kernel_mode (snd m0) ->
      init_chan_spec_low_step s WB (Vint n :: Vint v1 :: Vint v2 :: nil) m0 Vundef m2.*)

  Inductive get_sync_chan_to_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_sync_chan_to_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 chanid to:
      find_symbol s SYNCCHPOOL_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned chanid) * 12) = Some (Vint to) ->
      0 <= (Int.unsigned chanid) < num_chan ->
      kernel_mode (snd m'0) ->
      get_sync_chan_to_spec_low_step s WB (Vint chanid :: nil) m'0 (Vint to) m'0.

  Inductive get_sync_chan_paddr_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_sync_chan_paddr_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 chanid paddr:
      find_symbol s SYNCCHPOOL_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned chanid) * 12 + 4) = Some (Vint paddr) ->
      0 <= (Int.unsigned chanid) < num_chan ->
      kernel_mode (snd m'0) ->
      get_sync_chan_paddr_spec_low_step s WB (Vint chanid :: nil) m'0 (Vint paddr) m'0.

  Inductive get_sync_chan_count_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_sync_chan_count_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 chanid count:
      find_symbol s SYNCCHPOOL_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned chanid) * 12 + 8) = Some (Vint count) ->
      0 <= (Int.unsigned chanid) < num_chan ->
      kernel_mode (snd m'0) ->
      get_sync_chan_count_spec_low_step s WB (Vint chanid :: nil) m'0 (Vint count) m'0.

  Inductive set_sync_chan_to_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_sync_chan_to_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 chanid to:
      find_symbol s SYNCCHPOOL_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned chanid * 12) (Vint to) = Some m0 ->
      0 <= (Int.unsigned chanid) < num_chan ->
      kernel_mode (snd m'0) ->
      set_sync_chan_to_spec_low_step s WB (Vint chanid :: Vint to :: nil) m'0 Vundef m0.

  Inductive set_sync_chan_paddr_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_sync_chan_paddr_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 chanid paddr:
      find_symbol s SYNCCHPOOL_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned chanid * 12 + 4) (Vint paddr) = Some m0 ->
      0 <= (Int.unsigned chanid) < num_chan ->
      kernel_mode (snd m'0) ->
      set_sync_chan_paddr_spec_low_step s WB (Vint chanid :: Vint paddr :: nil) m'0 Vundef m0.

  Inductive set_sync_chan_count_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    set_sync_chan_count_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 chanid count:
      find_symbol s SYNCCHPOOL_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned chanid * 12 + 8) (Vint count) = Some m0 ->
      0 <= (Int.unsigned chanid) < num_chan ->
      kernel_mode (snd m'0) ->
      set_sync_chan_count_spec_low_step s WB (Vint chanid :: Vint count :: nil) m'0 Vundef m0.

  Inductive init_sync_chan_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    init_sync_chan_spec_low_intro s (WB: _ -> Prop) (m0 m1 m2 m3: mwd LDATAOps) b0 chanid:
      find_symbol s SYNCCHPOOL_LOC = Some b0 ->
      Mem.store Mint32 m0 b0 (Int.unsigned chanid * 12) (Vint (Int.repr num_chan)) = Some m1 ->
      Mem.store Mint32 m1 b0 (Int.unsigned chanid * 12 + 4) (Vint Int.zero) = Some m2 ->
      Mem.store Mint32 m2 b0 (Int.unsigned chanid * 12 + 8) (Vint Int.zero) = Some m3 ->
      0 <= (Int.unsigned chanid) < num_chan ->
      kernel_mode (snd m0) ->
      init_sync_chan_spec_low_step s WB (Vint chanid :: nil) m0 Vundef m3.
  
  Inductive get_kernel_pa_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    get_kernel_pa_spec_low_intro s (WB: _ -> Prop) m'0 labd pid vaddr pa:
      get_kernel_pa_spec (Int.unsigned pid) (Int.unsigned vaddr) labd = Some (Int.unsigned pa) ->
      0 <= (Int.unsigned pid) < num_proc ->
      kernel_mode labd ->
      get_kernel_pa_spec_low_step s WB (Vint pid :: Vint vaddr :: nil) (m'0, labd) (Vint pa) (m'0, labd).

(*
  Inductive flatmem_copy_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | flatmem_copy_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' count from to:
      flatmem_copy_spec (Int.unsigned count) (Int.unsigned from) (Int.unsigned to) labd = Some labd'   ->
      kernel_mode labd ->
      high_level_invariant labd ->
      flatmem_copy_spec_low_step s WB (Vint count :: Vint from :: Vint to :: nil) (m'0, labd) Vundef (m'0, labd').
*)


  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (*Definition get_chan_info_spec_low: compatsem LDATAOps :=
      csem get_chan_info_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition set_chan_info_spec_low: compatsem LDATAOps :=
      csem set_chan_info_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition get_chan_content_spec_low: compatsem LDATAOps :=
      csem get_chan_content_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition set_chan_content_spec_low: compatsem LDATAOps :=
      csem set_chan_content_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition init_chan_spec_low: compatsem LDATAOps :=
      csem init_chan_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.*)

    Definition get_sync_chan_to_spec_low: compatsem LDATAOps :=
      csem get_sync_chan_to_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition get_sync_chan_paddr_spec_low: compatsem LDATAOps :=
      csem get_sync_chan_paddr_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.
    
    Definition get_sync_chan_count_spec_low: compatsem LDATAOps :=
      csem get_sync_chan_count_spec_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition set_sync_chan_to_spec_low: compatsem LDATAOps :=
      csem set_sync_chan_to_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition set_sync_chan_paddr_spec_low: compatsem LDATAOps :=
      csem set_sync_chan_paddr_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.
    
    Definition set_sync_chan_count_spec_low: compatsem LDATAOps :=
      csem set_sync_chan_count_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.

    Definition init_sync_chan_spec_low: compatsem LDATAOps :=
      csem init_sync_chan_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition get_kernel_pa_spec_low: compatsem LDATAOps :=
      csem get_kernel_pa_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.
    
(*
    Definition flatmem_copy_spec_low: compatsem LDATAOps :=
      csem flatmem_copy_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.
*)

    (*Definition MSpec : compatlayer LDATAOps :=
      get_chan_info ↦ get_chan_info_spec_low
                ⊕ get_chan_content ↦ get_chan_content_spec_low
                ⊕ set_chan_info ↦ set_chan_info_spec_low
                ⊕ set_chan_content ↦ set_chan_content_spec_low
                ⊕ init_chan ↦ init_chan_spec_low.
    
    Definition MVar : compatlayer LDATAOps :=
      CHPOOL_LOC ↦ mkglobvar (Tarray Tint32 (num_proc * 8) (mk_attr false None))
              (Init_space (num_proc * 8) :: nil) false false.*)

  End WITHMEM.

End Refinement.
