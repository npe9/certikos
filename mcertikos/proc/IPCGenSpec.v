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
Require Import Conventions.

Require Import AbstractDataType.

Require Import PIPCIntro.
Require Import ObjProc.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive syncreceive_chan_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | syncreceive_chan_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' fromid vaddr rcount acount:
      syncreceive_chan_spec (Int.unsigned fromid) (Int.unsigned vaddr) (Int.unsigned rcount) labd  = Some (labd', Int.unsigned acount) ->
      0 <= Int.unsigned fromid < num_proc ->
      kernel_mode labd ->
      high_level_invariant labd ->
      syncreceive_chan_spec_low_step s WB (Vint fromid :: Vint vaddr :: Vint rcount :: nil) (m'0, labd) (Vint acount) (m'0, labd').

  Inductive syncsendto_chan_pre_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | syncsendto_chan_pre_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' chid vaddr scount acount:
      syncsendto_chan_pre_spec (Int.unsigned chid) (Int.unsigned vaddr) (Int.unsigned scount) labd = Some (labd', Int.unsigned acount) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      syncsendto_chan_pre_spec_low_step s WB (Vint chid :: Vint vaddr :: Vint scount :: nil) (m'0, labd) (Vint acount) (m'0, labd').

  Inductive syncsendto_chan_post_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | syncsendto_chan_post_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' r:
      syncsendto_chan_post_spec labd = Some (labd', Int.unsigned r)   ->
      kernel_mode labd ->
      high_level_invariant labd ->
      syncsendto_chan_post_spec_low_step s WB nil (m'0, labd) (Vint r) (m'0, labd').

  Inductive proc_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | proc_init_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      proc_init_spec (Int.unsigned mbi_adr) labd = Some labd'   ->
      kernel_mode labd ->
      high_level_invariant labd ->
      proc_init_spec_low_step s WB (Vint mbi_adr :: nil) (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition syncreceive_chan_spec_low: compatsem LDATAOps :=
      csem syncreceive_chan_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tint32.

    Definition syncsendto_chan_pre_spec_low: compatsem LDATAOps :=
      csem syncsendto_chan_pre_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tint32.

    Definition syncsendto_chan_post_spec_low: compatsem LDATAOps :=
      csem syncsendto_chan_post_spec_low_step Tnil Tint32.

    Definition proc_init_spec_low: compatsem LDATAOps :=
      csem proc_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    (*Definition MSpec : compatlayer LDATAOps :=
      syncreceive_chan ↦ syncreceive_chan_spec_low
                   ⊕ syncsendto_chan_pre ↦ syncsendto_chan_pre_spec_low
                   ⊕ syncsendto_chan_post ↦ syncsendto_chan_post_spec_low
                   ⊕ proc_init ↦ proc_init_spec_low.*)

  End WITHMEM.

End SPECIFICATION.
