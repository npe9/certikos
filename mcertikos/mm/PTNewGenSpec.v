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

Require Import MPTInit.
Require Import AbstractDataType.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section PTBITGEN_DEFINE.  

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive pmap_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | pmap_init_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      pmap_init_spec (Int.unsigned mbi_adr) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      pmap_init_spec_low_step s WB (Vint mbi_adr :: nil) (m'0, labd) Vundef (m'0, labd').

  (*Inductive pt_free_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | pt_free_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n:
      MPTBit.pt_free_spec (Int.unsigned n) labd = Some labd' ->
      kernel_mode labd ->
      high_level_invariant labd ->
      pt_free_spec_low_step s WB (Vint n :: nil) (m'0, labd) Vundef (m'0, labd').*)

  Inductive ptResv_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptResv_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr p r:
      ptResv_spec (Int.unsigned n) (Int.unsigned vadr) (Int.unsigned p) labd = 
      Some (labd', Int.unsigned r) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      ptResv_spec_low_step s WB (Vint n :: Vint vadr :: Vint p :: nil) (m'0, labd) (Vint r) (m'0, labd').

  Inductive ptResv2_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptResv2_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n vadr p n' vadr' p' r:
      ptResv2_spec (Int.unsigned n) (Int.unsigned vadr) (Int.unsigned p)
                          (Int.unsigned n') (Int.unsigned vadr') (Int.unsigned p') labd = 
      Some (labd', Int.unsigned r) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      ptResv2_spec_low_step s WB (Vint n :: Vint vadr :: Vint p :: Vint n' :: Vint vadr' :: Vint p' :: nil)
                            (m'0, labd) (Vint r) (m'0, labd').

  Inductive pt_new_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | pt_new_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' id q n:
      pt_new_spec (Int.unsigned id) (Int.unsigned q) labd = Some (labd', Int.unsigned n) ->
      kernel_mode labd ->
      high_level_invariant labd ->      
      pt_new_spec_low_step s WB (Vint id :: Vint q :: nil) (m'0, labd) (Vint n) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition pmap_init_spec_low: compatsem LDATAOps :=
      csem pmap_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    (*Definition pt_free_spec_low: compatsem LDATAOps :=
      csem pt_free_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.*)

    Definition ptResv_spec_low: compatsem LDATAOps :=
      csem ptResv_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tint32.

    Definition ptResv2_spec_low: compatsem LDATAOps :=
      csem ptResv2_spec_low_step 
           (type_of_list_type (Tint32::Tint32::Tint32::Tint32::Tint32::Tint32::nil))
           Tint32.

    Definition pt_new_spec_low: compatsem LDATAOps :=
      csem pt_new_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    (*Definition MSpec : compatlayer LDATAOps :=
      pt_resv ↦ ptResv_spec_low
              ⊕ pt_new ↦ pt_new_spec_low
              ⊕ pt_free ↦ pt_free_spec_low
              ⊕ pmap_init ↦ pmap_init_spec_low.*)

  End WITHMEM.

End PTBITGEN_DEFINE.