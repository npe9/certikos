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

Require Import PUCtxtIntro.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive proc_create_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sextcall_sem (mem := mwd LDATAOps):=
  | proc_create_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' bst bstc buc ofs_uc be ofse q n:
      proc_create_spec labd bst bstc buc ofs_uc (Int.unsigned q) = Some (labd', Int.unsigned n)  ->
      find_symbol s STACK_LOC = Some bst ->
      find_symbol s proc_start_user = Some bstc ->
      (exists fun_id, find_symbol s fun_id = Some buc) ->
      (exists elf_id, find_symbol s elf_id = Some be) ->
      kernel_mode labd ->
      high_level_invariant labd ->
      proc_create_spec_low_step s WB (Vptr be ofse :: Vptr buc ofs_uc :: Vint q :: nil) 
                                (m'0, labd) (Vint n) (m'0, labd').

  Inductive proc_exit_user_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | proc_exit_user_spec_low_intro s m0 labd labd' rs rs' sig vargs
                                v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 b:
      let uctx1:= ZMap.set U_EBX (Vint v4)
                           (ZMap.set U_OESP (Vint v3)
                                     (ZMap.set U_EBP (Vint v2)
                                               (ZMap.set U_ESI (Vint v1) 
                                                         (ZMap.set U_EDI (Vint v0) (ZMap.init Vundef))))) in
      let uctx2:= ZMap.set U_ES (Vint v8)
                           (ZMap.set U_EAX (Vint v7)
                                     (ZMap.set U_ECX (Vint v6) 
                                               (ZMap.set U_EDX (Vint v5) uctx1))) in
      let uctx3:= ZMap.set U_EIP (Vint v12)
                           (ZMap.set U_ERR (Vint v11) 
                                     (ZMap.set U_TRAPNO (Vint v10) 
                                               (ZMap.set U_DS (Vint v9) uctx2))) in
      let uctx4:= ZMap.set U_SS (Vint v16) 
                           (ZMap.set U_ESP (Vint v15) 
                                     (ZMap.set U_EFLAGS (Vint v14)
                                               (ZMap.set U_CS (Vint v13) uctx3))) in            
      find_symbol s proc_exit_user = Some b ->
      rs PC = Vptr b Int.zero ->
      proc_exit_user_spec labd uctx4 = Some labd' ->
      rs' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: IR EBX :: RA :: nil)
                        (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
      sig = mksignature (AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                AST.Tint::nil) None cc_default ->
      vargs = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v4 :: Vint v5 :: Vint v6
                    :: Vint v7 :: Vint v8 :: Vint v9:: Vint v10 :: Vint v11 :: Vint v12
                    :: Vint v13 :: Vint v14 :: Vint v15:: Vint v16 ::nil) ->
      extcall_arguments rs m0 sig vargs ->
      rs ESP <> Vundef ->
      (forall b1 o,
         rs ESP = Vptr b1 o ->
         Ple (genv_next s) b1 /\ Plt b1 (Mem.nextblock m0)) ->
      asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m0) labd ->
      proc_exit_user_spec_low_step s rs (m0, labd) 
                                   (rs'# PC <- (rs RA)) (m0, labd').

  Inductive proc_start_user_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | proc_start_user_spec_low_intro s m0 labd labd' rs rs' rs'' b:
      find_symbol s proc_start_user = Some b ->
      rs PC = Vptr b Int.zero ->
      proc_start_user_spec labd = Some (labd', rs') ->
      rs'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: IR ECX :: IR EAX :: RA :: nil)
                         (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
      asm_invariant (mem := mwd LDATAOps) s rs (m0, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m0) labd ->
      proc_start_user_spec_low_step s rs (m0, labd) 
                                    (rs''# EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                                         # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                                         # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                                         # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                                         # PC <- (ZMap.get U_EIP rs')) (m0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Import AST.

    Definition exit_sig :=
      mksignature (Tint::Tint::Tint::Tint::Tint::Tint::
                       Tint::Tint::Tint::Tint::Tint::
                       Tint::Tint::Tint::Tint::Tint::
                       Tint::nil) None cc_default.

    Definition proc_create_spec_low: compatsem LDATAOps :=
      csem proc_create_spec_low_step (type_of_list_type (Tpointer Tvoid noattr::Tpointer Tvoid noattr::Tint32::nil)) Tint32.

    Definition proc_start_user_spec_low: compatsem LDATAOps :=
      asmsem proc_start_user proc_start_user_spec_low_step.

    Definition proc_exit_user_spec_low: compatsem LDATAOps :=
      asmsem_withsig proc_exit_user proc_exit_user_spec_low_step exit_sig.

    (*Definition MSpec : compatlayer LDATAOps :=
      proc_create ↦ proc_create_spec_low
                   ⊕ proc_start_user ↦ proc_start_user_spec_low
                   ⊕ proc_exit_user ↦ proc_exit_user_spec_low.*)

  End WITHMEM.

End SPECIFICATION.