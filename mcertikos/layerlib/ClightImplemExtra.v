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
Require Import List.
Require Import Errors.
Require Import Values.
Require Import AST.
Require Import Memtype.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import StackOrHeap.
Require Import Implementation.
Require Import SeparateCompiler.
Require Import ClightBigstep.
Require Import MemWithData.
Require Import AsmExtra.
Require Import LAsm.
Require Export ClightImplem.

Section SOURCE_IMPLEM.

  Context (high: Type)
          `{Hsc_high: SyntaxConfiguration high}.

  Context {ldata} {low} `{Hlayer: LayerConfiguration ldata low}.
  
  (** * Auxiliaries for memory accesses. *)
  Context `{exec_load: Asm.genv -> memory_chunk-> mem 
                       -> addrmode-> regset-> preg-> (outcome)}.
  Context `{exec_store: Asm.genv -> memory_chunk-> mem 
                        -> addrmode-> regset-> preg-> (outcome)}.
  
  Context `{ primitive_call: low -> primcall_sem}.
  Context `{ is_primitive_call: low -> bool}.

  Context {kernel_mode: ldata -> Prop}.

  Hypothesis exec_load_exec_loadex:
             forall m,
               kernel_mode (Mem.get_abstract_data m) ->
               forall ge chunk a rd,
               forall (r rs' : regset) m',
                 Asm.exec_load ge chunk m a r rd = Asm.Next rs' m' ->
                 exec_load ge chunk m a r rd = Asm.Next rs' m'.

  Hypothesis exec_store_exec_storeex:
    forall m,
      kernel_mode (Mem.get_abstract_data m) ->
      forall ge chunk a rd,
      forall (r rs' : regset) m',
        Asm.exec_store ge chunk m a r rd = Asm.Next rs' m' ->
        exec_store ge chunk m a r rd = Asm.Next rs' m'.

  Hypothesis extcall_sem_not_primitive:
    forall p: low,
    forall (ge: genv) args m t res m',
      external_call p ge args m t res m' ->
      is_primitive_call p = false.

  Hypothesis prim_kernel_mode:
    forall p: low,
    forall (ge: genv) args m t res m',
      external_call p ge args m t res m' ->
      kernel_mode (Mem.get_abstract_data m) ->
      kernel_mode (Mem.get_abstract_data m').

  Variable si: source_implem Asm.code unit high (low := low) Clight.fundef Ctypes.type.

  Hypothesis symbols_norepet: list_norepet (map fst (source_implem_new_globs (high := high) si)).

  Variable (hp: Asm.program (external_function := high)).
  
  Let hge := Genv.globalenv hp.

  Hypothesis symbols_fresh:
    forall s' : ident,
      Genv.find_symbol hge s' <> None ->
      ~ In s' (map fst (source_implem_new_globs si)).

  Let im := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar si.
  
  Let lp := transf_program im hp.
  Let lge := Genv.globalenv lp.

  Let p := source_program_only si hp.
  Let ge := Genv.globalenv p.

  Variable (tp: Asm.program (external_function := low)).

  Hypothesis (TRANS: transf_clight_program p = OK tp).

  Variables
    (b:    block)       (** the block to which the function pointer points to  *)
    (m:    mem)         (** the memory before *)
    (args: list val)    (** the list of arguments *)    

    (** Clight behavior *)
    (targs: Ctypes.typelist)
    (tres:  Ctypes.type)
    (t: Events.trace)
    (res: val)
    (m_clight: mem)
    (f: Clight.fundef)
    (CLIGHT: Genv.find_funct_ptr ge b = Some f ->
             bigstep_terminates ge b args m targs tres t (res, m_clight))

    (** assembly properties about memory state and registers *)
    (rs:   regset)      (** the register set before *)
    (sg:   signature)   (** the intended signature of the callee *)
    (ARGS: extcall_arguments rs m sg args)
    (SP_NOT_VUNDEF: rs ESP <> Vundef)
    (RA_NOT_VUNDEF: rs RA <> Vundef)
    (SP_STACK: forall b o, rs Asm.ESP = Vptr b o -> Mem.tget m b = Some Tag_stack)
    (PC_VALUE: rs PC = Vptr b Integers.Int.zero)
    (INVAR: asm_invariant lge (State rs m))
    
    (** Linking (to do manually) *)
    (SIG: sg = Ctypes.signature_of_type targs tres)
    (ef: high) (fallback: Asm.fundef (external_function := low))
    (SOURCE_FUN_IMPL: source_implem_extfuns si ef = SourceFun f fallback)
    (KERNEL_MODE: kernel_mode (Mem.get_abstract_data m))

    (** Linking (provided by the layer refinement proof) *)
    (SOURCE: Genv.find_funct_ptr hge b = Some (External ef))


  .
 
  Theorem bigstep_clight_to_lsem:

    exists j rs' m_asm,
      inject_incr (Mem.flat_inj (Mem.nextblock m)) j
      /\ Memtype.Mem.inject j m_clight m_asm
      /\ Mem.nextblock m <= Mem.nextblock m_asm
      /\ plus (LSemantics.stepl
              (is_primitive_call := is_primitive_call)
              (primitive_call := primitive_call)
              (exec_store := exec_store)
              (exec_load := exec_load)
           ) lge (State rs m) t (State rs' m_asm)
      /\ val_inject j res (rs' # (preg_of (Conventions1.loc_result sg)))
      /\ rs' # PC  = rs # RA
      /\ rs' # ESP = rs # ESP
      /\ (forall l,
         ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call -> Val.lessdef (rs (preg_of l)) (rs' (preg_of l)))
.

  Proof.
    intros.
    exploit (@bigstep_clight_to_asm high low); eauto.
    intro J. exploit J; clear J; eauto. (* just because "exploit" is not written for functions with that many arguments... *)
    intros [j [rs' [m_asm [Hplus [Hincr [Hinj_mem [Hinj_res [H_ESP [H_PC [H_CALLEESAVE _]]]]]]]]]].
    refine (_ (plus_nextblock _ _ _ _ _ _ _)); eauto.
    intro.
    exploit (LSemantics.asm_subset_lsem_plus (kernel_mode := kernel_mode) (primitive_call := primitive_call) (is_primitive_call := is_primitive_call) (exec_load := exec_load) (exec_store := exec_store)); eauto; eauto 11.
  Qed.

End SOURCE_IMPLEM.

