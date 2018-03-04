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
Require Import TSysCall.
Require Import AbstractDataType.

Require Import Conventions.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) RData).

  (*Inductive sys_run_vm_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | sys_run_vm_spec_low_intro s m (rs:regset) v7 labd labd0 labd' rs01 rs0 rs' rs2 v0 v1 v2 v3 v5 v6 
                                v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 vargs sg b:

      trap_into_kernel_spec sys_run_vm s m rs labd labd0 vargs sg b
                            v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

      rs01 = (Pregmap.init Vundef) #EDI <- (rs EDI) #EBP <- (rs EBP) ->
      vm_run_spec rs01 labd0 = Some (labd', rs') ->

      rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: RA :: nil) 
                        (undef_regs (List.map preg_of destroyed_at_call) rs))  ->

      rs2 = (rs0#EAX<- (rs'#EAX)#EBX <- (rs'#EBX)#EDX <- (rs'#EDX)
                #ESI <- (rs'#ESI)#EDI <- (rs'#EDI)#EBP <- (rs'#EBP)
                #PC <- (rs'#RA)) ->

      asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m) labd ->

      sys_run_vm_spec_low_step s rs (m, labd) rs2 (m, labd').*)

  Inductive pagefault_handler_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | pagefault_handler_spec_low_intro s m labd labd0 labd1 labd' rs0 vadr (rs:regset) rs' v0 v1 v2 v3 v5 v6 
                                     v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b:

      syscall_spec pgf_handler s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                   v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

      (* call kernel function*)
      (* read argument *)
      vadr = fst (ti labd0) ->
      ptfault_resv_spec (Int.unsigned vadr) labd0 = Some labd1 ->

      asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m) labd ->

      pagefault_handler_spec_low_step s rs (m, labd) rs0 (m, labd').

  Inductive sys_sendtochan_pre_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | sys_sendtochan_pre_spec_low_intro s m (rs:regset) chanid labd labd0 labd1 labd' rs0 rs' rs2 v0 v1 v2 v3 v5 v6 
                                      v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 vargs rs_yield bs sg b:
      
      trap_into_kernel_spec sys_sendtochan_pre s m rs labd labd0 vargs sg b
                            v0 v1 v2 v3 v4 v5 v6 chanid v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

      (* call kernel function*)
      trap_sendtochan_pre_spec labd0 = Some (labd1, Int.unsigned chanid) ->
      (* yield *)          
      find_symbol s sys_sendtochan_post = Some bs ->
      rs_yield = (Pregmap.init Vundef)#ESP <- (Val.add (rs ESP) (Vint (Int.repr 28)))
                                      #EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                      #EBX <- Vundef#EBP <- (rs#EBP)#RA <- (Vptr bs Int.zero) ->
      thread_sleep_spec labd1 rs_yield (Int.unsigned chanid) = Some (labd', rs') ->

      rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                            :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                        (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
      rs2 = (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                #EBP <- (rs'#EBP)#PC <- (rs'#RA))  ->

      asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m) labd ->

      sys_sendtochan_pre_spec_low_step s rs (m, labd) rs2 (m, labd').

  Inductive sys_sendtochan_post_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | sys_sendtochan_post_spec_low_intro s m (rs:regset) labd labd1 labd' rs0 rs' b:
      trap_sendtochan_post_spec labd = Some labd1 ->
      proc_start_user_spec labd1 = Some (labd', rs') ->
      rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                            :: IR ECX :: IR EAX :: RA :: nil) 
                        (undef_regs (List.map preg_of destroyed_at_call) rs))
              # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
              # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
              # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
              # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
              # PC <- (ZMap.get U_EIP rs') ->
      (forall i, 0 <= i < UCTXT_SIZE ->
                 let v:= (ZMap.get i rs') in
                 Val.has_type v AST.Tint) ->
      (forall i, 0 <= i < UCTXT_SIZE ->
                 let v:= (ZMap.get i rs') in
                 val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
      find_symbol s sys_sendtochan_post = Some b ->
      rs PC = Vptr b Int.zero ->
      rs ESP <> Vundef ->
      (forall b0 o,
         rs ESP = Vptr b0 o ->
         Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->

      asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m) labd ->

      sys_sendtochan_post_spec_low_step s rs (m, labd) rs0 (m, labd').

  Inductive sys_dispatch_c_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | sys_dispatch_c_spec_low_intro s  m labd labd' labd0 labd1 rs0  (rs:regset) rs' v0 v1 v2 v3 v5 v6 
                                   v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b:

      syscall_spec syscall_dispatch s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                   v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      
      (* call kernel function*)
      sys_dispatch_c_spec s m labd0 = Some labd1 ->

      asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m) labd ->

      sys_dispatch_c_spec_low_step s rs (m, labd) rs0 (m, labd').

  Inductive sys_yield_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | sys_yield_spec_low_intro s m labd labd0 labd' rs0 rs' rs2  (rs:regset) v0 v1 v2 v3 v5 v6 
                             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs rs_yield bs sg b:

      trap_into_kernel_spec sys_yield s m rs labd labd0 vargs sg b
                            v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

      (* call kernel function*)
      (* yield *)          
      find_symbol s proc_start_user = Some bs ->
      rs_yield = (Pregmap.init Vundef) #ESP <- (rs#ESP) #EDI <- (rs#EDI) #ESI <- (rs#ESI)
                                       #EBX <- Vundef #EBP <- (rs#EBP) #RA <- (Vptr bs Int.zero)->
      thread_yield_spec labd0 rs_yield = Some (labd', rs') ->
      
      (* restore registers *)          
      rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                            :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                        (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
      rs2 = (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                #EBP <- (rs'#EBP)#PC <- (rs'#RA))  ->

      asm_invariant (mem := mwd LDATAOps) s rs (m, labd) ->
      high_level_invariant labd ->
      low_level_invariant (Mem.nextblock m) labd ->

      sys_yield_spec_low_step s rs (m, labd) rs2 (m, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition pagefault_handler_spec_low: compatsem LDATAOps :=
      asmsem pgf_handler pagefault_handler_spec_low_step.

    Definition sys_dispatch_c_spec_low: compatsem LDATAOps :=
      asmsem syscall_dispatch sys_dispatch_c_spec_low_step.

    Definition sys_yield_spec_low: compatsem LDATAOps :=
      asmsem sys_yield sys_yield_spec_low_step.

    Definition sys_sendtochan_pre_spec_low: compatsem LDATAOps :=
      asmsem sys_sendtochan_pre sys_sendtochan_pre_spec_low_step.

    Definition sys_sendtochan_post_spec_low: compatsem LDATAOps :=
      asmsem sys_sendtochan_post sys_sendtochan_post_spec_low_step.

    (*Definition sys_run_vm_spec_low: compatsem LDATAOps :=
      asmsem sys_run_vm sys_run_vm_spec_low_step.*)

  End WITHMEM.

End SPECIFICATION.