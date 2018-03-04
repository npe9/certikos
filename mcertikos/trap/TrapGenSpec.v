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
Require Import TTrapArg.
Require Import AbstractDataType.
Require Import ObjTrap.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) RData).

  (*Inductive trap_ischanready_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_ischanready_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_ischanready_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_ischanready_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_sendtochan_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_sendtochan_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_sendtochan_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_sendtochan_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).*)

  Inductive trap_receivechan_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_receivechan_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_receivechan_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_receivechan_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  (*Inductive trap_inject_event_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_inject_event_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_inject_event_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_inject_event_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_check_int_shadow_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_check_int_shadow_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_check_int_shadow_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_check_int_shadow_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_check_pending_event_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_check_pending_event_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_check_pending_event_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_check_pending_event_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_intercept_int_window_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_intercept_int_window_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_intercept_int_window_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_intercept_int_window_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_get_next_eip_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_get_next_eip_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_get_next_eip_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_get_next_eip_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_get_reg_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_get_reg_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_get_reg_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_get_reg_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_set_reg_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_set_reg_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_set_reg_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_set_reg_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_set_seg_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_set_seg_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_set_seg_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_set_seg_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_get_tsc_offset_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_get_tsc_offset_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_get_tsc_offset_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_get_tsc_offset_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_set_tsc_offset_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_set_tsc_offset_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_set_tsc_offset_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_set_tsc_offset_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_get_exitinfo_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_get_exitinfo_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_get_exitinfo_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_get_exitinfo_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_handle_rdmsr_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_handle_rdmsr_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_handle_rdmsr_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_handle_rdmsr_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_handle_wrmsr_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_handle_wrmsr_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_handle_wrmsr_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_handle_wrmsr_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_mmap_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_mmap_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_mmap_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_mmap_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).*)

  Inductive ptf_resv_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | ptf_resv_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0 i:
      ptfault_resv_spec (Int.unsigned i) labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      ptf_resv_spec_low_step s WB (Vint i::nil) (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_proc_create_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_proc_create_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_proc_create_spec s m'0 labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_proc_create_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_get_quota_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_get_quota_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_get_quota_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_get_quota_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).

  Inductive trap_offer_shared_mem_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | trap_offer_shared_mem_spec_low_intro s (WB: _ -> Prop) m'0 labd labd0:
      trap_offer_shared_mem_spec labd = Some labd0 ->
      kernel_mode labd ->
      high_level_invariant labd ->
      trap_offer_shared_mem_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd0).


  Inductive print_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | print_spec_low_intro s (WB: _ -> Prop) m'0 labd labd':
      print_spec labd = Some labd'->
      kernel_mode labd ->
      high_level_invariant labd ->
      print_spec_low_step s WB nil (m'0, labd) Vundef (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition trap_offer_shared_mem_spec_low: compatsem LDATAOps :=
      csem trap_offer_shared_mem_spec_low_step Tnil Tvoid.

    Definition trap_proc_create_spec_low: compatsem LDATAOps :=
      csem trap_proc_create_spec_low_step Tnil Tvoid.

    Definition trap_get_quota_spec_low: compatsem LDATAOps :=
      csem trap_get_quota_spec_low_step Tnil Tvoid.

    Definition ptf_resv_spec_low: compatsem LDATAOps :=
      csem ptf_resv_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    (*Definition trap_mmap_spec_low: compatsem LDATAOps :=
      csem trap_mmap_spec_low_step Tnil Tvoid.*)

    (*Definition trap_sendtochan_spec_low: compatsem LDATAOps :=
      csem trap_sendtochan_spec_low_step Tnil Tvoid.

    Definition trap_ischanready_spec_low: compatsem LDATAOps :=
      csem trap_ischanready_spec_low_step Tnil Tvoid.*)

    Definition trap_receivechan_spec_low: compatsem LDATAOps :=
      csem trap_receivechan_spec_low_step Tnil Tvoid.

    Definition print_spec_low: compatsem LDATAOps :=
      csem print_spec_low_step Tnil Tvoid.

    (*Definition trap_intercept_int_window_spec_low: compatsem LDATAOps :=
      csem trap_intercept_int_window_spec_low_step Tnil Tvoid.

    Definition trap_inject_event_spec_low: compatsem LDATAOps :=
      csem trap_inject_event_spec_low_step Tnil Tvoid.

    Definition trap_check_int_shadow_spec_low: compatsem LDATAOps :=
      csem trap_check_int_shadow_spec_low_step Tnil Tvoid.

    Definition trap_check_pending_event_spec_low: compatsem LDATAOps :=
      csem trap_check_pending_event_spec_low_step Tnil Tvoid.

    Definition trap_get_next_eip_spec_low: compatsem LDATAOps :=
      csem trap_get_next_eip_spec_low_step Tnil Tvoid.

    Definition trap_get_reg_spec_low: compatsem LDATAOps :=
      csem trap_get_reg_spec_low_step Tnil Tvoid.

    Definition trap_set_reg_spec_low: compatsem LDATAOps :=
      csem trap_set_reg_spec_low_step Tnil Tvoid.

    Definition trap_set_seg_spec_low: compatsem LDATAOps :=
      csem trap_set_seg_spec_low_step Tnil Tvoid.

    Definition trap_get_tsc_offset_spec_low: compatsem LDATAOps :=
      csem trap_get_tsc_offset_spec_low_step Tnil Tvoid.

    Definition trap_set_tsc_offset_spec_low: compatsem LDATAOps :=
      csem trap_set_tsc_offset_spec_low_step Tnil Tvoid.

    Definition trap_get_exitinfo_spec_low: compatsem LDATAOps :=
      csem trap_get_exitinfo_spec_low_step Tnil Tvoid.

    Definition trap_handle_rdmsr_spec_low: compatsem LDATAOps :=
      csem trap_handle_rdmsr_spec_low_step Tnil Tvoid.

    Definition trap_handle_wrmsr_spec_low: compatsem LDATAOps :=
      csem trap_handle_wrmsr_spec_low_step Tnil Tvoid.*)

  End WITHMEM.

End SPECIFICATION.
