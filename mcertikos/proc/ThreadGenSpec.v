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

Require Import PThreadSched.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive thread_yield_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | thread_yield_spec_low_intro s m0 labd labd' rs r b:
      find_symbol s thread_yield = Some b ->
      rs PC = Vptr b Int.zero ->
      PThreadSched.thread_yield_spec labd 
                                     ((Pregmap.init Vundef) # ESP <- (rs ESP) # EDI <- (rs EDI)
                                                            # ESI <- (rs ESI) # EBX <- (rs EBX) # EBP <- 
                                                            (rs EBP) # RA <- (rs RA)) = Some (labd', r) ->
      asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m0) labd ->
      let rs' := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                            (undef_regs (List.map preg_of destroyed_at_call) rs)) in
      thread_yield_spec_low_step s rs (m0, labd) 
                                 (rs'#ESP<- (r#ESP)#EDI <- (r#EDI)#ESI <- (r#ESI)#EBX <- (r#EBX)
                                     #EBP <- (r#EBP)#PC <- (r#RA)) (m0, labd').

  Inductive thread_sleep_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | thread_sleep_spec_low_intro s m0 labd labd' rs r n sig b:
      find_symbol s thread_sleep = Some b ->
      rs PC = Vptr b Int.zero ->
      PThreadSched.thread_sleep_spec labd 
                                     ((Pregmap.init Vundef) # ESP <- (rs ESP) # EDI <- (rs EDI)
                                                            # ESI <- (rs ESI) # EBX <- (rs EBX) # EBP <- 
                                                            (rs EBP) # RA <- (rs RA))
      (Int.unsigned n) = Some (labd', r) ->
      asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m0) labd ->
      sig = mksignature (AST.Tint::nil) None cc_default ->
      extcall_arguments rs m0 sig (Vint n ::nil) ->
      let rs' := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                 :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                             (undef_regs (List.map preg_of destroyed_at_call) rs)) in
      thread_sleep_spec_low_step s rs (m0, labd) 
                                 (rs'#ESP<- (r#ESP)#EDI <- (r#EDI)#ESI <- (r#ESI)#EBX <- (r#EBX)
                                     #EBP <- (r#EBP)#PC <- (r#RA)) (m0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition thread_yield_spec_low: compatsem LDATAOps :=
      asmsem thread_yield thread_yield_spec_low_step.

    Definition thread_sleep_spec_low: compatsem LDATAOps :=
      asmsem_withsig thread_sleep thread_sleep_spec_low_step (mksignature (AST.Tint::nil) None cc_default).

    (*Definition MSpec : compatlayer LDATAOps :=
      thread_yield ↦ thread_yield_spec_low
                   ⊕ thread_sleep ↦ thread_sleep_spec_low.*)

  End WITHMEM.

End SPECIFICATION.