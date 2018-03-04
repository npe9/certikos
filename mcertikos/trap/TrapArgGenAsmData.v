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
(*Require Import Errors.*)
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import MemoryExtra.
Require Import EventsExtra.
Require Import GlobalenvsExtra.
Require Import Locations.
Require Import DataType.
Require Import LAsm.
Require Import CDataTypes.
Require Import AsmExtra.
Require Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import ZArith.Zwf.
Require Import EventsExtra.
Require Import GlobalenvsExtra.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import MemoryExtra.
Require Import Maps.
Require Import Heap.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import Implementation.
(*Require Import SeparateCompiler.*)
Require Import ClightImplemExtra.
Require Import LayerDefinition.
Require Import RealParams.
Require Import CInitSpecsMPTOp.
Require Import CInitSpecsMPTCommon.
Require Import CInitSpecsMPTBit.
Require Import CInitSpecsproc.
Require Import AsmImplLemma.
Require Import ProcDataType.
(*Require Import VirtDataType.*)
(*Require Import TrapDataType.*)
Require Import Conventions.
Require Import PProc.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module TRAPARGGEN_ASM_DATA.

  Section ASM_VERIFY.

    Context `{real_params: RealParams}.

    Notation Lfundef := (Asm.fundef (external_function:= PPROC.primOp)).

    (*Definition Im_vm_exit : Lfundef := 
      AST.Internal (
                    Pcall_s host_in ::
                    Pcall_s svm_state_save ::
                    Pcall_s restore_hctx ::
                    nil).

    Notation Lprogram := (Asm.program (external_function:= PPROC.primOp)).
    Variable tprog: Lprogram.
    Notation tge := (Genv.globalenv tprog).

    Notation LDATA :=(VSVMINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).

    Context `{PageFaultHandler_LOC: ident}.
    Context `{START_USER_FUN_LOC: ident}.

    Section WITHMEM.

      Local Instance LdataOp:AbstractDataOps LDATA:= (PPROC.abstract_data (Hnpc:= Hnpc)).

      Context {mem__L}
              `{HLmem: !LayerMemoryModel LDATA mem__L}.

      Lemma vm_exit_generate:
          forall m0 labd' v0 v1 v2 v3 v4 v5 v6 v7 v8 rs',
            let labd := (Mem.get_abstract_data m0) in
            PPROC.svm_exit_vm labd (Vint v0) (Vint v1) (Vint v2) (Vint v3)
                                 (Vint v4) (Vint v5) (Vint v6) (Vint v7) (Vint v8) = Some (labd', rs')
            -> PPROC.low_level_invariant (Mem.nextblock m0) labd
            -> exists labd0,
                 VSVMINTRO.hostin labd = Some labd0
                 /\ PPROC.svm_state_save labd0 (Vint v0) (Vint v1) (Vint v2) (Vint v3)
                                            (Vint v4) (Vint v5) (Vint v6) (Vint v7) (Vint v8) = Some labd'
                 /\ VSVMINTRO.restore_hctx labd' = Some rs'
                 /\ (forall v r, ZtoPreg_Host v = Some r -> Val.has_type (rs'#r) Tint)
                 /\ (forall v r, ZtoPreg_Host v = Some r 
                                 -> val_inject (Mem.flat_inj (Mem.nextblock m0)) (rs'#r) (rs'#r)).            
      Proof.
        intros.
        apply PPROC.svm_exit_vm_eq in H.
        functional inversion H; unfold xvmst'', xvmst', vmcbv, adt in *.
        inv H0.
        destruct H7.
        destruct H2.
        destruct H7.
        destruct H8.
        destruct H9.

        assert (exists adt, VSVMINTRO.hostin_aux labd = Some adt).
          esplit.
          unfold VSVMINTRO.hostin_aux.
          rewrite H4, H5.
          reflexivity.
        destruct H11 as [adt' HEX'].
        specialize (VSVMINTRO.hostin_aux_correct _ _ HEX').
        intro INV'.
        assert (exists abd, VSVMINTRO.hostin labd = Some abd).
        exists (VSVMINTRO.mkAbData (PgSize:= PgSize) (num_proc:= num_proc) (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) adt' INV').
          apply VSVMINTRO.hostin_eq_r.
          assumption.
        destruct H11 as [abd' hostin].
        generalize hostin; intro hostin_aux.
        apply VSVMINTRO.hostin_eq in hostin_aux.
        functional inversion hostin_aux; clear hostin_aux.
        unfold adt0 in *.

        exists abd'.
        repeat (split; auto).
        apply PPROC.svm_state_save_eq_r.
        unfold PPROC.svm_state_save_aux.
        rewrite <- H11; simpl.
        rewrite H3, H5.
        rewrite <- H1.
        rewrite H3, H5.
        reflexivity.
        unfold VSVMINTRO.restore_hctx.
        rewrite <- H1; simpl.
        rewrite H3, H5.
        reflexivity.
        intros; destruct (H8 _ _ H14); assumption.
        intros; destruct (H8 _ _ H14); assumption.
      Qed.


    End WITHMEM.

  End ASM_VERIFY.

End TRAPARGGEN_ASM_DATA.
