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
Require Import PCurID.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  (*Inductive thread_kill_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | thread_kill_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n i:
      PCurID.thread_kill_spec labd (Int.unsigned n) (Int.unsigned i) = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      thread_kill_spec_low_step s WB (Vint n :: Vint i :: nil) (m'0, labd) Vundef (m'0, labd').*)

  Inductive thread_spawn_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | thread_spawn_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n b' b0 ofs' id q:
      thread_spawn_spec labd b0 b' ofs' (Int.unsigned id) (Int.unsigned q)  = Some (labd', Int.unsigned n)  ->
      find_symbol s STACK_LOC = Some b0 ->
      (exists fun_id, find_symbol s fun_id = Some b') ->
      kernel_mode labd ->
      high_level_invariant labd ->
      thread_spawn_spec_low_step s WB (Vptr b' ofs' :: Vint id :: Vint q :: nil) (m'0, labd) (Vint n) (m'0, labd').

  Inductive thread_wakeup_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | thread_wakeup_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n:
      thread_wakeup_spec (Int.unsigned n) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      thread_wakeup_spec_low_step s WB (Vint n :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive sched_init_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | sched_init_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' mbi_adr:
      sched_init_spec (Int.unsigned mbi_adr) labd = Some labd'  ->
      kernel_mode labd ->
      high_level_invariant labd ->
      sched_init_spec_low_step s WB (Vint mbi_adr :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive thread_sched_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | thread_sched_spec_low_intro s m0 labd labd' rs r b:
      find_symbol s thread_sched = Some b ->
      rs PC = Vptr b Int.zero ->
      thread_sched_spec labd 
                        ((Pregmap.init Vundef) # ESP <- (rs ESP) # EDI <- (rs EDI)
                                               # ESI <- (rs ESI) # EBX <- (rs EBX) # EBP <- 
                                               (rs EBP) # RA <- (rs RA)) = Some (labd', r) ->
      asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m0) labd ->
      let rs' := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                 :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                             (undef_regs (List.map preg_of destroyed_at_call) rs)) in
      thread_sched_spec_low_step s rs (m0, labd) 
                                 (rs'#ESP<- (r#ESP)#EDI <- (r#EDI)#ESI <- (r#ESI)#EBX <- (r#EBX)
                                     #EBP <- (r#EBP)#PC <- (r#RA)) (m0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (*Definition thread_kill_spec_low: compatsem LDATAOps :=
      csem thread_kill_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tvoid.*)

    Definition thread_spawn_spec_low: compatsem LDATAOps :=
      csem thread_spawn_spec_low_step (type_of_list_type (Tpointer Tvoid noattr::Tint32::Tint32::nil)) Tint32.

    Definition thread_wakeup_spec_low: compatsem LDATAOps :=
      csem thread_wakeup_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition sched_init_spec_low: compatsem LDATAOps :=
      csem sched_init_spec_low_step (type_of_list_type (Tint32::nil)) Tvoid.

    Definition thread_sched_spec_low: compatsem LDATAOps :=
      asmsem thread_sched thread_sched_spec_low_step.

    (*Definition MSpec : compatlayer LDATAOps :=
      thread_kill ↦ thread_kill_spec_low
                  ⊕ thread_spawn ↦ thread_spawn_spec_low
                  ⊕ thread_wakeup ↦ thread_wakeup_spec_low
                  ⊕ sched_init ↦ sched_init_spec_low
                  ⊕ thread_sched ↦ thread_sched_spec_low.*)

  End WITHMEM.

End SPECIFICATION.