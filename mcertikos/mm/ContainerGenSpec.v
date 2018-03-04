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
(*          Refinement proof for MContainer layer                      *)
(*                                                                     *)
(*          David Costanzo <david.costanzo@yale.edu>                   *)
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
Require Import MALT.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section CONTAINERGEN_DEFINE.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Definition QUOTA := 0.
  Definition USAGE := 4.
  Definition PARENT := 8.
  Definition NCHILDREN := 12.
  Definition USED := 16.
  Definition CSIZE := 20.

  Inductive container_init_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_init_low_intro s (WB: _ -> Prop) (m m' m1 m2 m3 m4: mem) labd labd' b0 mbi:
      mem_init_spec (Int.unsigned mbi) labd = Some labd' ->
      find_symbol s AC_LOC = Some b0 ->
      Mem.store Mint32 m b0 QUOTA (Vint (Int.repr real_quota)) = Some m1 ->
      Mem.store Mint32 m1 b0 USAGE (Vint Int.zero) = Some m2 ->
      Mem.store Mint32 m2 b0 PARENT (Vint Int.zero) = Some m3 ->
      Mem.store Mint32 m3 b0 NCHILDREN (Vint Int.zero) = Some m4 ->
      Mem.store Mint32 m4 b0 USED (Vint Int.one) = Some m' ->
      kernel_mode labd ->
      container_init_low_step s WB (Vint mbi :: nil) (m,labd) Vundef (m',labd').

  Inductive container_get_parent_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_get_parent_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 i v:
      find_symbol s AC_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + PARENT) = Some (Vint v) ->
      0 <= Int.unsigned i < num_id ->
      kernel_mode (snd m'0) ->
      container_get_parent_low_step s WB (Vint i :: nil) m'0 (Vint v) m'0.

  Inductive container_get_nchildren_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_get_nchildren_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 i v:
      find_symbol s AC_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + NCHILDREN) = Some (Vint v) ->
      0 <= Int.unsigned i < num_id ->
      kernel_mode (snd m'0) ->
      container_get_nchildren_low_step s WB (Vint i :: nil) m'0 (Vint v) m'0.

  Inductive container_get_quota_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_get_quota_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 i v:
      find_symbol s AC_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + QUOTA) = Some (Vint v) ->
      0 <= Int.unsigned i < num_id ->
      kernel_mode (snd m'0) ->
      container_get_quota_low_step s WB (Vint i :: nil) m'0 (Vint v) m'0.

  Inductive container_get_usage_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_get_usage_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 i v:
      find_symbol s AC_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + USAGE) = Some (Vint v) ->
      0 <= Int.unsigned i < num_id ->
      kernel_mode (snd m'0) ->
      container_get_usage_low_step s WB (Vint i :: nil) m'0 (Vint v) m'0.

  Inductive container_can_consume_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_can_consume_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 i n q u:
      find_symbol s AC_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + QUOTA) = Some (Vint q) ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
      0 <= Int.unsigned i < num_id ->
      kernel_mode (snd m'0) ->
      container_can_consume_low_step s WB (Vint i :: Vint n :: nil) m'0 
        (Vint (match (Int.unsigned n <=? Int.unsigned q, 
                      Int.unsigned u <=? Int.unsigned q - Int.unsigned n) with
               | (true, true) => Int.one 
               | _ => Int.zero end)) m'0.

  Inductive container_split_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_split_low_step_intro s (WB: _ -> Prop) (m m' m1 m2 m3 m4 m5 m6: mwd LDATAOps) 
                                   b0 i n j u nc:
      find_symbol s AC_LOC = Some b0 -> 
      0 <= Int.unsigned i < num_id -> 0 <= Int.unsigned j < num_id ->
      Int.unsigned j = Int.unsigned i * max_children + 1 + Int.unsigned nc ->      
      Mem.load Mint32 m b0 (Int.unsigned i * CSIZE + USED) = Some (Vint Int.one) ->
      Mem.load Mint32 m b0 (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
      Mem.load Mint32 m b0 (Int.unsigned i * CSIZE + NCHILDREN) = Some (Vint nc) ->
      Mem.store Mint32 m b0 (Int.unsigned j * CSIZE + USED) (Vint Int.one) = Some m1 ->
      Mem.store Mint32 m1 b0 (Int.unsigned j * CSIZE + QUOTA) (Vint n) = Some m2 ->
      Mem.store Mint32 m2 b0 (Int.unsigned j * CSIZE + USAGE) (Vint Int.zero) = Some m3 ->
      Mem.store Mint32 m3 b0 (Int.unsigned j * CSIZE + PARENT) (Vint i) = Some m4 ->
      Mem.store Mint32 m4 b0 (Int.unsigned j * CSIZE + NCHILDREN) (Vint Int.zero) = Some m5 ->
      Mem.store Mint32 m5 b0 (Int.unsigned i * CSIZE + USAGE) (Vint (Int.add u n)) = Some m6 ->
      Mem.store Mint32 m6 b0 (Int.unsigned i * CSIZE + NCHILDREN) (Vint (Int.add nc Int.one)) = Some m' ->
      kernel_mode (snd m) ->
      container_split_low_step s WB (Vint i :: Vint n :: nil) m (Vint j) m'.

  (*Inductive container_revoke_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_revoke_low_step_intro s (WB: _ -> Prop) (m'0 m0 m1 m2: mwd LDATAOps) b0 i p q u nc:
      find_symbol s AC_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + QUOTA) = Some (Vint q) ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + PARENT) = Some (Vint p) ->
      Mem.load Mint32 m'0 b0 (Int.unsigned p * CSIZE + USAGE) = Some (Vint u) ->
      Mem.load Mint32 m'0 b0 (Int.unsigned p * CSIZE + NCHILDREN) = Some (Vint nc) ->
      Mem.store Mint32 m'0 b0 (Int.unsigned p * CSIZE + USAGE) (Vint (Int.sub u q)) = Some m1 ->
      Mem.store Mint32 m1 b0 (Int.unsigned p * CSIZE + NCHILDREN) (Vint (Int.sub nc Int.one)) = Some m2 ->
      Mem.store Mint32 m2 b0 (Int.unsigned i * CSIZE + USED) (Vint Int.zero) = Some m0 ->
      kernel_mode (snd m'0) ->
      container_revoke_low_step s WB (Vint i :: nil) m'0 Vundef m0.*)

  Inductive container_alloc_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_alloc_low_step_intro0 s (WB: _ -> Prop) (m: mwd LDATAOps) b0 i u:
      find_symbol s AC_LOC = Some b0 ->
      0 <= Int.unsigned i < num_id -> 
      Mem.load Mint32 m b0 (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
      Mem.load Mint32 m b0 (Int.unsigned i * CSIZE + QUOTA) = Some (Vint u) ->    
      kernel_mode (snd m) ->
      container_alloc_low_step s WB (Vint i :: nil) m Vzero m
  | container_alloc_low_step_intro1 s (WB: _ -> Prop) (m m': mem) d d' b0 i u q pi:
      palloc'_spec d = Some (d', pi) ->
      find_symbol s AC_LOC = Some b0 ->
      0 <= Int.unsigned i < num_id -> Int.unsigned u < Int.unsigned q ->
      0 <= pi <= Int.max_unsigned ->
      Mem.load Mint32 m b0 (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
      Mem.load Mint32 m b0 (Int.unsigned i * CSIZE + QUOTA) = Some (Vint q) ->       
      Mem.store Mint32 m b0 (Int.unsigned i * CSIZE + USAGE) (Vint (Int.add u Int.one)) = Some m' ->
      kernel_mode d ->
      container_alloc_low_step s WB (Vint i :: nil) (m,d) (Vint (Int.repr pi)) (m',d').

  (*Inductive container_free_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
  | container_free_low_step_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 i u:
      find_symbol s AC_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
      Mem.store Mint32 m'0 b0 (Int.unsigned i * CSIZE + USAGE) (Vint (Int.sub u Int.one)) = Some m0 ->
      kernel_mode (snd m'0) ->
      container_free_low_step s WB (Vint i :: nil) m'0 Vundef m0.*)

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition container_init_spec_low: compatsem LDATAOps :=
      csem container_init_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition container_get_parent_spec_low: compatsem LDATAOps :=
      csem container_get_parent_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition container_get_nchildren_spec_low: compatsem LDATAOps :=
      csem container_get_nchildren_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition container_get_quota_spec_low: compatsem LDATAOps :=
      csem container_get_quota_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition container_get_usage_spec_low: compatsem LDATAOps :=
      csem container_get_usage_low_step (type_of_list_type (Tint32::nil)) Tint32.

    Definition container_can_consume_spec_low: compatsem LDATAOps :=
      csem container_can_consume_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition container_split_spec_low: compatsem LDATAOps :=
      csem container_split_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    (*Definition container_revoke_spec_low: compatsem LDATAOps :=
      csem container_revoke_low_step (type_of_list_type (Tint32::nil)) Tvoid.*)

    Definition container_alloc_spec_low: compatsem LDATAOps :=
      csem container_alloc_low_step (type_of_list_type (Tint32::nil)) Tint32.

    (*Definition container_free_spec_low: compatsem LDATAOps :=
      csem container_free_low_step (type_of_list_type (Tint32::nil)) Tvoid.*)
    
  End WITHMEM.

End CONTAINERGEN_DEFINE.
