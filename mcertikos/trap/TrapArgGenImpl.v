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
Require Import TTrapArg.
Require Import PProc.
(*Require Import VSVMSave.
Require Import VSVMIntro.*)
Require Export TrapArgGen.
(*Require Export TrapArgGenAsm.*)
Require Import PProcCode.
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
Require Import LayerTemplate2.
Require Import Implementation.
Require Import SeparateCompiler.
Require Import ClightImplemExtra.
Require Import LayerDefinition.
Require Import RealParams.
Require Import CInitSpecsMPTOp.
Require Import CInitSpecsMPTCommon.
Require Import CInitSpecsMPTBit.
Require Import CInitSpecsproc.
(*Require Import CInitSpecsvirt.*)

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module TRAPARGGENIMPL.
  Export TrapArgGen.TRAPARGGEN.

  Lemma hprim_finite_type:
    forall
      (Q: TTRAPARG.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec TTRAPARG.PAlloc)...
    destruct (Q_dec TTRAPARG.PFree)...
    destruct (Q_dec TTRAPARG.PPTRead)...
    destruct (Q_dec TTRAPARG.PPTResv)...
    destruct (Q_dec TTRAPARG.PProcCreate)...
    destruct (Q_dec TTRAPARG.PThreadKill)...
    destruct (Q_dec TTRAPARG.PThreadWakeup)...
    destruct (Q_dec TTRAPARG.PThreadYield)...
    destruct (Q_dec TTRAPARG.PThreadSleep)...
    destruct (Q_dec TTRAPARG.PGetCurID)...
    destruct (Q_dec TTRAPARG.PProcStartUser)...
    destruct (Q_dec TTRAPARG.PProcExitUser)...
    destruct (Q_dec TTRAPARG.PUCTXGet)...
    destruct (Q_dec TTRAPARG.PUCTXSet)...
    destruct (Q_dec TTRAPARG.PTrapGet)...
    destruct (Q_dec TTRAPARG.PTrapRet)...
    destruct (Q_dec TTRAPARG.PIsChanReady)...
    destruct (Q_dec TTRAPARG.PSendToChan)...
    destruct (Q_dec TTRAPARG.PReceiveChan)...
    destruct (Q_dec TTRAPARG.PUCTXArg1)...
    destruct (Q_dec TTRAPARG.PUCTXArg2)...
    destruct (Q_dec TTRAPARG.PUCTXArg3)...
    destruct (Q_dec TTRAPARG.PUCTXArg4)...
    destruct (Q_dec TTRAPARG.PUCTXArg5)...
    destruct (Q_dec TTRAPARG.PUCTXSetErrno)...
    destruct (Q_dec TTRAPARG.PUCTXSetRetVal1)...
    destruct (Q_dec TTRAPARG.PLa2PaResv)...
    destruct (Q_dec TTRAPARG.PProcInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation LDATA :=(PPROC.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).
    Notation HDATA := LDATA.
  
    Notation Hfundef := (Asm.fundef (external_function:= TTRAPARG.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PPROC.primOp)).

    Notation funkind := (funkind (low:= PPROC.primOp) Asm.code (Clight.fundef (external_function := PPROC.primOp))).

    Notation dummy := (AST.Internal nil).        

    Definition source_implem_extfuns (p: TTRAPARG.primOp): funkind :=
      match p with
        | TTRAPARG.PAlloc => Code _ (AST.External PPROC.PAlloc)
        | TTRAPARG.PFree => Code _ (AST.External PPROC.PFree)
        | TTRAPARG.PPTRead => Code _ (AST.External PPROC.PPTRead)
        | TTRAPARG.PPTResv => Code _ (AST.External PPROC.PPTResv)
        | TTRAPARG.PProcCreate => Code _ (AST.External PPROC.PProcCreate)
        | TTRAPARG.PThreadKill => Code _ (AST.External PPROC.PThreadKill)
        | TTRAPARG.PThreadWakeup => Code _ (AST.External PPROC.PThreadWakeup)
        | TTRAPARG.PThreadYield => Code _ (AST.External PPROC.PThreadYield)
        | TTRAPARG.PThreadSleep => Code _ (AST.External PPROC.PThreadSleep)
        | TTRAPARG.PGetCurID => Code _ (AST.External PPROC.PGetCurID)
        | TTRAPARG.PProcStartUser => Code _ (AST.External PPROC.PProcStartUser)
        | TTRAPARG.PProcExitUser => Code _ (AST.External PPROC.PProcExitUser)
        | TTRAPARG.PUCTXGet => Code _ (AST.External PPROC.PUCTXGet)
        | TTRAPARG.PUCTXSet => Code _ (AST.External PPROC.PUCTXSet)
        | TTRAPARG.PTrapGet => Code _ (AST.External PPROC.PTrapGet)
        | TTRAPARG.PTrapRet => Code _ (AST.External PPROC.PTrapRet)
        | TTRAPARG.PIsChanReady => Code _ (AST.External PPROC.PIsChanReady)
        | TTRAPARG.PSendToChan => Code _ (AST.External PPROC.PSendToChan)
        | TTRAPARG.PReceiveChan => Code _ (AST.External PPROC.PReceiveChan)
        | TTRAPARG.PUCTXArg1 => SourceFun (Clight.Internal (PPROCCODE.f_uctx_arg1)) (AST.Internal nil)
        | TTRAPARG.PUCTXArg2 => SourceFun (Clight.Internal (PPROCCODE.f_uctx_arg2)) (AST.Internal nil)
        | TTRAPARG.PUCTXArg3 => SourceFun (Clight.Internal (PPROCCODE.f_uctx_arg3)) (AST.Internal nil)
        | TTRAPARG.PUCTXArg4 => SourceFun (Clight.Internal (PPROCCODE.f_uctx_arg4)) (AST.Internal nil)
        | TTRAPARG.PUCTXArg5 => SourceFun (Clight.Internal (PPROCCODE.f_uctx_arg5)) (AST.Internal nil)
        | TTRAPARG.PUCTXSetErrno => SourceFun (Clight.Internal (PPROCCODE.f_uctx_set_errno)) (AST.Internal nil)
        | TTRAPARG.PUCTXSetRetVal1 => SourceFun (Clight.Internal (PPROCCODE.f_uctx_set_retval1)) (AST.Internal nil)
        | TTRAPARG.PLa2PaResv => SourceFun (Clight.Internal (PPROCCODE.f_la2pa_resv)) (AST.Internal nil)
        | TTRAPARG.PProcInit => Code _ (AST.External PPROC.PProcInit)
      end.
 
    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (uctx_get, Some (Gfun (SourceFun (Clight.External (PPROC.PUCTXGet) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tint) dummy)))
        :: (uctx_set1, Some (Gfun (SourceFun (Clight.External (PPROC.PUCTXSet) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid) dummy)))
        :: (get_curid1, Some (Gfun (SourceFun (Clight.External (PPROC.PGetCurID) (Ctypes.Tnil) tint) dummy)))
        :: (pt_resv2, Some (Gfun (SourceFun (Clight.External (PPROC.PPTResv) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid) dummy)))
        :: (pt_read, Some (Gfun (SourceFun (Clight.External (PPROC.PPTRead) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tint) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit TTRAPARG.primOp (low := PPROC.primOp) (Clight.fundef (external_function := PPROC.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit TTRAPARG.primOp (low := PPROC.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= TTRAPARG.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PPROC.primOp)).
                
    Let Im_uctx_arg1: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PUCTXArg1).
    Let Im_uctx_arg2: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PUCTXArg2).
    Let Im_uctx_arg3: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PUCTXArg3).
    Let Im_uctx_arg4: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PUCTXArg4).
    Let Im_uctx_arg5: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PUCTXArg5).
    Let Im_uctx_set_errno: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PUCTXSetErrno).
    Let Im_uctx_set_retval1: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PUCTXSetRetVal1).
    Let Im_la2pa_resv: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns TTRAPARG.PLa2PaResv).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because TTRAPARG.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
    Lemma extfun_compilation_succeeds_dec:
      {forall p clight asmfallback, 
        source_implem_extfuns p = SourceFun clight asmfallback ->
        exists asm, transf_clight_fundef clight = OK asm} +
      {~ forall p clight asmfallback, 
        source_implem_extfuns p = SourceFun clight asmfallback ->
        exists asm, transf_clight_fundef clight = OK asm}.
    Proof.
      apply hprim_finite_type.
      intro.
      destruct (source_implem_extfuns p); try (left; discriminate).
      case_eq (transf_clight_fundef sf).
       left. intros. inv H0. eauto.
      intros. right. intro. exploit H0; eauto. destruct 1. congruence.
    Defined.

    Hypothesis extfun_compilation_succeeds:
      forall p clight asmfallback, 
        source_implem_extfuns p = SourceFun clight asmfallback ->
        exists asm, transf_clight_fundef clight = OK asm.

    Section WithProg.

    Variable prog: Hprogram.

    Definition tprog: Lprogram := Implementation.transf_program im prog.

    Let TRANSF: TRAPARGGEN.transf_program Im_uctx_arg1 Im_uctx_arg2 Im_uctx_arg3 Im_uctx_arg4 Im_uctx_arg5 Im_uctx_set_errno Im_uctx_set_retval1 Im_la2pa_resv impl_glbl prog = OK tprog.
    Proof.
      unfold tprog.
      unfold Asm.program, Asm.fundef.
      generalize (transf_program_eq im prog).
      intros.
      rewrite <- H.
      unfold transf_program.
      simpl.
      f_equal.
      apply FunctionalExtensionality.functional_extensionality.
      destruct x; simpl.
       reflexivity.
      destruct p; reflexivity.
    Qed.

    Notation ge := (Genv.globalenv prog).
    Notation tge := (Genv.globalenv tprog).

    Hypothesis prog_main_valid:
      ~ Plt' (prog_main prog) (prog_first_symbol prog).

    Hypothesis prog_first_valid:
      ~ Plt' (prog_first_symbol prog) (get_next_symbol (map fst impl_glbl)).

    Hypothesis prog_nonempty:
      prog_defs_names prog <> nil.
        
    Lemma tprog_first_next:
      prog_first_symbol tprog = get_first_symbol (map fst impl_glbl) /\
      prog_next_symbol  tprog = prog_next_symbol prog.
    Proof.
      replace (get_first_symbol (map fst impl_glbl)) with (implem_first_symbol im) by reflexivity.
      unfold tprog.
      apply transf_program_first_next_symbol.
      assumption.
      assumption.
      discriminate.
    Qed.

    Lemma tprog_main_valid:
      ~ Plt' (prog_main tprog) (prog_first_symbol tprog).
    Proof.
      Opaque Plt'.
      simpl.
      destruct tprog_first_next.
      rewrite H.
      apply Ple'_not_Plt'.
      eapply Ple'_trans.
      apply first_le_next.
      discriminate.
      eapply Ple'_trans.
      apply not_Plt'_Ple'.
      eassumption.
      apply not_Plt'_Ple'.
      assumption.
    Qed.

    Lemma tprog_nonempty:
      prog_defs_names tprog <> nil.
    Proof.
      apply transf_program_nonempty.
      assumption.
    Qed.

    Let NEW_INJ:  (forall s', Genv.find_symbol ge s' <> None -> 
                                     ~ In s' (map fst impl_glbl)).
    Proof.
      change impl_glbl with (implem_new_globs im).
      apply new_ids_fresh.
      assumption.
    Qed.

    Let sprog : Clight.program (external_function := PPROC.primOp) := source_program_only source_implem prog.
    Let sge := Genv.globalenv sprog.

    Ltac elim_or H t :=
      match type of H with
        | False => contradiction
        | _ \/ _ =>
          let K := fresh "K" in
          destruct H as [H | K]; [ elim_or H t | elim_or K t ]
        | _ => t H
      end.

    Let tsprog_strong : {tsprog | transf_clight_program sprog = OK tsprog}.
    Proof.
      case_eq (transf_clight_program sprog); eauto.
      intros. exfalso.
      refine (_ (Implementation.compilation_succeeds
                    transf_clight_fundef
                    Cshmgen.transl_globvar
                    source_implem _ _ _
                    prog)).
      destruct 1.
      generalize (transf_clight_fundef_to_program _ _ H0).
      unfold sprog in H.
      congruence.
      assumption.
      simpl. 
      intros until fallback.
      intro K.
      let t J := (inv J; rewrite transf_clight_fundef_external; eauto) in elim_or K t.
      unfold Cshmgen.transl_globvar. eauto.
    Qed.

    Let tsprog := let (p, _) := tsprog_strong in p.

    Let tsprog_prop : transf_clight_program sprog = OK tsprog.
    Proof.
      unfold tsprog.
      destruct tsprog_strong.
      assumption.
    Qed.

    Let tsge := Genv.globalenv tsprog.

    (** uctx_get *)

    Let buctx_get: block := Genv.genv_next ge + Z.of_nat 0.

    Let huctx_get1 : Genv.find_symbol sge uctx_get = Some buctx_get. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_get).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let huctx_get2 : Genv.find_funct sge (Vptr buctx_get Int.zero) = Some (Clight.External (PPROC.PUCTXGet) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_get _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let huctx_get3 : Clight.type_of_global sge buctx_get = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_get).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_get. unfold Asm.fundef. omega.
      intros.
      simpl in huctx_get2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_get2. reflexivity.
    Qed.     

    (** uctx_set1 *)

    Let buctx_set1: block := Genv.genv_next ge + Z.of_nat 1.

    Let huctx_set11 : Genv.find_symbol sge uctx_set1 = Some buctx_set1. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_set1).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let huctx_set12 : Genv.find_funct sge (Vptr buctx_set1 Int.zero) = Some (Clight.External (PPROC.PUCTXSet) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_set1 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let huctx_set13 : Clight.type_of_global sge buctx_set1 = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_set1).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_set1. unfold Asm.fundef. omega.
      intros.
      simpl in huctx_set12. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_set12. reflexivity.
    Qed.   

    (** get_curid1 *)

    Let bget_curid1: block := Genv.genv_next ge + Z.of_nat 2.

    Let hget_curid11 : Genv.find_symbol sge get_curid1 = Some bget_curid1. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_curid1).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hget_curid12 : Genv.find_funct sge (Vptr bget_curid1 Int.zero) = Some (Clight.External (PPROC.PGetCurID) (Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_curid1 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hget_curid13 : Clight.type_of_global sge bget_curid1 = Some (Ctypes.Tfunction (Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_curid1).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_curid1. unfold Asm.fundef. omega.
      intros.
      simpl in hget_curid12. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_curid12. reflexivity.
    Qed.     

    (** pt_resv2 *)

    Let bpt_resv2: block := Genv.genv_next ge + Z.of_nat 3.

    Let hpt_resv21 : Genv.find_symbol sge pt_resv2 = Some bpt_resv2. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_resv2).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_resv22 : Genv.find_funct sge (Vptr bpt_resv2 Int.zero) = Some (Clight.External (PPROC.PPTResv) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_resv2 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 9.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hpt_resv23 : Clight.type_of_global sge bpt_resv2 = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_resv2).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_resv2. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_resv22. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_resv22. reflexivity.
    Qed.   

    (** pt_read *)

    Let bpt_read: block := Genv.genv_next ge + Z.of_nat 4.

    Let hpt_read1 : Genv.find_symbol sge pt_read = Some bpt_read. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_read).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_read2 : Genv.find_funct sge (Vptr bpt_read Int.zero) = Some (Clight.External (PPROC.PPTRead) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_read _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 9.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hpt_read3 : Clight.type_of_global sge bpt_read = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_read).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_read. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_read2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_read2. reflexivity.
    Qed.  
 

    Context `{PageFaultHandler_LOC: ident}.
    Context `{START_USER_FUN_LOC: ident}.

    Section WITHMEM.

      Local Instance LdataOp:AbstractDataOps LDATA:= (PPROC.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel LDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections LDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) LDATA TTRAPARG.primOp mem__H :=
        TTRAPARG.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                           (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc)
                           (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                           (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                           (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) 
                           (real_chpool := real_chpool)
                           (STACK_LOC:= STACK_LOC)(STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC := START_USER_FUN_LOC).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PPROC.primOp mem__L :=
        PPROC.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                       (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                       (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                       (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                       (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool := real_chpool)
                       (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC := START_USER_FUN_LOC).        

      Notation HLoad := (TTRAPARG.exec_loadex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation HStore := (TTRAPARG.exec_storeex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation LLoad := (PPROC.exec_loadex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation LStore := (PPROC.exec_storeex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).

      Notation lstep := (PPROC.step 
                           (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4) (real_chpool:= real_chpool)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)
                           (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC:= START_USER_FUN_LOC) (NPT_LOC:=NPT_LOC)).

      Notation LADT := PPROC.ADT.

      Let uctx_arg1_spec :
        forall m0 rs b arg1 sig,
          rs PC = Vptr b Int.zero ->
          PPROC.uctx_arg1 (Mem.get_abstract_data m0) = Some arg1 ->
          Genv.find_funct_ptr tge b = Some (Im_uctx_arg1) ->
          sig = mksignature nil (Some Tint) ->
          extcall_arguments rs m0 sig nil -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PUCTXArg1)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint arg1)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.uctx_arg1_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          functional inversion H0; unfold adt in *; auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_get_abstract_data.
          intro.
          inv H10.
          eauto 11.
        Qed.

      Let uctx_arg2_spec :
        forall m0 rs b arg2 sig,
          rs PC = Vptr b Int.zero ->
          PPROC.uctx_arg2 (Mem.get_abstract_data m0) = Some arg2 ->
          Genv.find_funct_ptr tge b = Some (Im_uctx_arg2) ->
          sig = mksignature nil (Some Tint) ->
          extcall_arguments rs m0 sig nil -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PUCTXArg2)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint arg2)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.uctx_arg2_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          functional inversion H0; unfold adt in *; auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_get_abstract_data.
          intro.
          inv H10.
          eauto 11.
        Qed.

      Let uctx_arg3_spec :
        forall m0 rs b arg3 sig,
          rs PC = Vptr b Int.zero ->
          PPROC.uctx_arg3 (Mem.get_abstract_data m0) = Some arg3 ->
          Genv.find_funct_ptr tge b = Some (Im_uctx_arg3) ->
          sig = mksignature nil (Some Tint) ->
          extcall_arguments rs m0 sig nil -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PUCTXArg3)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint arg3)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.uctx_arg3_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          functional inversion H0; unfold adt in *; auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_get_abstract_data.
          intro.
          inv H10.
          eauto 11.
        Qed.

      Let uctx_arg4_spec :
        forall m0 rs b arg4 sig,
          rs PC = Vptr b Int.zero ->
          PPROC.uctx_arg4 (Mem.get_abstract_data m0) = Some arg4 ->
          Genv.find_funct_ptr tge b = Some (Im_uctx_arg4) ->
          sig = mksignature nil (Some Tint) ->
          extcall_arguments rs m0 sig nil -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PUCTXArg4)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint arg4)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.uctx_arg4_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          functional inversion H0; unfold adt in *; auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_get_abstract_data.
          intro.
          inv H10.
          eauto 11.
        Qed.

      Let uctx_arg5_spec :
        forall m0 rs b arg5 sig,
          rs PC = Vptr b Int.zero ->
          PPROC.uctx_arg5 (Mem.get_abstract_data m0) = Some arg5 ->
          Genv.find_funct_ptr tge b = Some (Im_uctx_arg5) ->
          sig = mksignature nil (Some Tint) ->
          extcall_arguments rs m0 sig nil -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PUCTXArg5)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint arg5)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.uctx_arg5_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          functional inversion H0; unfold adt in *; auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_get_abstract_data.
          intro.
          inv H10.
          eauto 11.
        Qed.

      Let uctx_set_errno_spec :
        forall m0 rs b errno adt sig,
          rs PC = Vptr b Int.zero ->
          PPROC.uctx_set_errno (Mem.get_abstract_data m0) errno = Some adt ->
          Genv.find_funct_ptr tge b = Some (Im_uctx_set_errno) ->
          sig = mksignature (Tint :: nil) None ->
          extcall_arguments rs m0 sig (Vint errno :: nil) -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PUCTXSetErrno)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' adt))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.uctx_set_errno_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          apply PPROC.uctx_set_errno_eq in H0.
          destruct (PPROC.INV (Mem.get_abstract_data m0)).
          functional inversion H0; unfold adt0 in *; auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) adt) in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace adt with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

      Let uctx_set_retval1_spec :
        forall m0 rs b retval1 adt sig,
          rs PC = Vptr b Int.zero ->
          PPROC.uctx_set_retval1 (Mem.get_abstract_data m0) retval1 = Some adt ->
          Genv.find_funct_ptr tge b = Some (Im_uctx_set_retval1) ->
          sig = mksignature (Tint :: nil) None ->
          extcall_arguments rs m0 sig (Vint retval1 :: nil) -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PUCTXSetRetVal1)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' adt))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.uctx_set_retval1_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          apply PPROC.uctx_set_retval1_eq in H0.
          destruct (PPROC.INV (Mem.get_abstract_data m0)).
          functional inversion H0; unfold adt0 in *; auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) adt) in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace adt with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

      Let la2pa_resv_spec :
        forall m0 rs b vadr padr adt sig,
          rs PC = Vptr b Int.zero ->
          PPROC.la2pa_resv (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh)
                              (Mem.get_abstract_data m0) (Int.unsigned vadr) = Some (adt, Int.unsigned padr) ->
          Genv.find_funct_ptr tge b = Some (Im_la2pa_resv) ->
          sig = mksignature (Tint :: nil) (Some Tint) ->
          extcall_arguments rs m0 sig (Vint vadr :: nil) -> (* how to match arguement with the state*)
          Genv.find_funct_ptr ge b = Some (External TTRAPARG.PLa2PaResv)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' adt))
               /\ r_ # (loc_external_result sig) = (Vint padr)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     TTRAPARG.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PPROC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PPROC.is_primitive_call)
                     (kernel_mode := PPROC.kernel_mode)
                  ).
          apply PPROC.exec_load_exec_loadex.
          apply PPROC.exec_store_exec_storeex.
          apply PPROC.extcall_not_primitive.
          apply PPROC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PPROCCODE.la2pa_resv_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PPROC.kernel_mode.
          functional inversion H0;
          unfold PPROC.ptRead in H11;
          case_eq (PPROC.ikern (LADT (Mem.get_abstract_data m0))); intro ikern; rewrite ikern in H11; try discriminate H11;
          case_eq (PPROC.ihost (LADT (Mem.get_abstract_data m0))); intro ihost; rewrite ihost in H11; try discriminate H11;
          auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) adt) in PLUS.
          inv H10.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace adt with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

(*
      Let AndImplies: forall A B: Prop, (A /\ (A -> B)) -> (A /\ B).
      Proof.
        intros.
        destruct H.
        split.
        assumption.
        apply H0; assumption.
      Qed.

      Let bhost_in: block := Genv.genv_next ge + Z.of_nat 5.
      Let Hhostin: exists b_hostin, Genv.find_symbol tge host_in = Some b_hostin
                                             /\ Genv.find_funct_ptr tge b_hostin = Some (External PPROC.PHostIn).
      Proof.
        exists bhost_in.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ host_in).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ host_in _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 9.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bsvm_state_save: block := Genv.genv_next ge + Z.of_nat 6.
      Let Hsave_svm: exists b_save, 
                                  Genv.find_symbol tge svm_state_save = Some b_save
                                  /\ Genv.find_funct_ptr tge b_save = Some (External PPROC.PSVMStateSave).
      Proof.
        exists bsvm_state_save.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ svm_state_save).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ svm_state_save _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 9.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let brestore_hctx: block := Genv.genv_next ge + Z.of_nat 7.
      Let Hrestore_hctx: exists b_restore, 
                                  Genv.find_symbol tge restore_hctx = Some b_restore
                                  /\ Genv.find_funct_ptr tge b_restore = Some (External PPROC.PRestoreHctx).
      Proof.
        exists brestore_hctx.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ restore_hctx).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ restore_hctx _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 9.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.
*)

    Theorem transf_program_correct:
       Smallstep.backward_simulation 
          (TTRAPARG.semantics (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                              (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                              (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                              (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool:= real_chpool) (STACK_TOP:= STACK_TOP) 
                              (START_USER_FUN_LOC:= START_USER_FUN_LOC) (NPT_LOC:=NPT_LOC) prog) 
          (PPROC.semantics (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (STACK_TOP:= STACK_TOP)
                          (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                          (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                          (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                          (Hnchan:= Hnchan) (real_abq:= real_abq) (real_chpool:= real_chpool)
                          (START_USER_FUN_LOC:= START_USER_FUN_LOC) (NPT_LOC:=NPT_LOC) tprog).
    Proof.
      (*pose TRAPARGGEN_ASM.svm_exit_vm_spec.*)
      eapply TRAPARGGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End TRAPARGGENIMPL.
