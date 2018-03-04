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
Require Import TTrap.
Require Import TTrapArg.
(*Require Import TrapDataType.*)
(*Require Import VSVM.
Require Import VSVMIntro.*)
Require Import PProc.
Require Export TrapGen.
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
Require Import TTrapArgCode.
Require Import Ctypes.
(*Require Import VVMCBOp.*)

Open Local Scope string_scope.

Module TRAPGENIMPL.
  Export TrapGen.TRAPGEN.

  Lemma hprim_finite_type:
    forall
      (Q: TTRAP.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec TTRAP.PAlloc)...
    destruct (Q_dec TTRAP.PFree)...
    destruct (Q_dec TTRAP.PPTRead)...
    destruct (Q_dec TTRAP.PPTFaultResv)...
    destruct (Q_dec TTRAP.PThreadKill)...
    destruct (Q_dec TTRAP.PThreadWakeup)...
    destruct (Q_dec TTRAP.PThreadYield)...
    destruct (Q_dec TTRAP.PThreadSleep)...
    destruct (Q_dec TTRAP.PGetCurID)...
    destruct (Q_dec TTRAP.PUCTXGet)...
    destruct (Q_dec TTRAP.PUCTXSet)...
    destruct (Q_dec TTRAP.PProcStartUser)...
    destruct (Q_dec TTRAP.PProcExitUser)...
    destruct (Q_dec TTRAP.PTrapGet)...
    destruct (Q_dec TTRAP.PTrapRet)...
    destruct (Q_dec TTRAP.PUCTXArg1)...
    destruct (Q_dec TTRAP.PUCTXArg2)...
    destruct (Q_dec TTRAP.PUCTXArg3)...
    destruct (Q_dec TTRAP.PUCTXArg4)...
    destruct (Q_dec TTRAP.PUCTXArg5)...
    destruct (Q_dec TTRAP.PUCTXSetErrno)...
    destruct (Q_dec TTRAP.PUCTXSetRetVal1)...
    destruct (Q_dec TTRAP.PSysProcCreate)...
    destruct (Q_dec TTRAP.PSysIsChanReady)...
    destruct (Q_dec TTRAP.PSysSendToChan)...
    destruct (Q_dec TTRAP.PSysReceiveChan)...
    destruct (Q_dec TTRAP.PProcInit)...
    left; destruct p; assumption.
  Defined.

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation LDATA :=(PPROC.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).
    Notation HDATA := LDATA.

    Notation Hfundef := (Asm.fundef (external_function:= TTRAP.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= TTRAPARG.primOp)).

    Notation funkind := (funkind (low:= TTRAPARG.primOp) Asm.code (Clight.fundef (external_function := TTRAPARG.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (prim : TTRAP.primOp): funkind :=
      match prim with
        | TTRAP.PAlloc => Code _ (AST.External TTRAPARG.PAlloc)
        | TTRAP.PFree => Code _ (AST.External TTRAPARG.PFree)
        | TTRAP.PPTRead => Code _ (AST.External TTRAPARG.PPTRead)
        | TTRAP.PPTFaultResv => SourceFun (Clight.Internal (TTRAPARGCODE.f_ptf_resv)) (AST.Internal nil)
        | TTRAP.PThreadKill => Code _ (AST.External TTRAPARG.PThreadKill)
        | TTRAP.PThreadWakeup => Code _ (AST.External TTRAPARG.PThreadWakeup)
        | TTRAP.PThreadYield => Code _ (AST.External TTRAPARG.PThreadYield)
        | TTRAP.PThreadSleep => Code _ (AST.External TTRAPARG.PThreadSleep)
        | TTRAP.PGetCurID => Code _ (AST.External TTRAPARG.PGetCurID)
        | TTRAP.PUCTXGet => Code _ (AST.External TTRAPARG.PUCTXGet)
        | TTRAP.PUCTXSet => Code _ (AST.External TTRAPARG.PUCTXSet)
        | TTRAP.PProcStartUser => Code _ (AST.External TTRAPARG.PProcStartUser)
        | TTRAP.PProcExitUser => Code _ (AST.External TTRAPARG.PProcExitUser)
        | TTRAP.PTrapGet => Code _ (AST.External TTRAPARG.PTrapGet)
        | TTRAP.PTrapRet => Code _ (AST.External TTRAPARG.PTrapRet)
        | TTRAP.PUCTXArg1 => Code _ (AST.External TTRAPARG.PUCTXArg1)
        | TTRAP.PUCTXArg2 => Code _ (AST.External TTRAPARG.PUCTXArg2)
        | TTRAP.PUCTXArg3 => Code _ (AST.External TTRAPARG.PUCTXArg3)
        | TTRAP.PUCTXArg4 => Code _ (AST.External TTRAPARG.PUCTXArg4)
        | TTRAP.PUCTXArg5 => Code _ (AST.External TTRAPARG.PUCTXArg5)
        | TTRAP.PUCTXSetErrno => Code _ (AST.External TTRAPARG.PUCTXSetErrno)
        | TTRAP.PUCTXSetRetVal1 => Code _ (AST.External TTRAPARG.PUCTXSetRetVal1)

        | TTRAP.PSysProcCreate => SourceFun (Clight.Internal (TTRAPARGCODE.f_sys_proc_create)) (AST.Internal nil)
        | TTRAP.PSysIsChanReady => SourceFun (Clight.Internal (TTRAPARGCODE.f_sys_is_chan_ready)) (AST.Internal nil)
        | TTRAP.PSysSendToChan => SourceFun (Clight.Internal (TTRAPARGCODE.f_sys_sendto_chan)) (AST.Internal nil)
        | TTRAP.PSysReceiveChan => SourceFun (Clight.Internal (TTRAPARGCODE.f_sys_receive_chan)) (AST.Internal nil)
        | TTRAP.PProcInit => Code _ (AST.External TTRAPARG.PProcInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Record implem_dep := {
      dep_ident: ident;
      dep_lname: TTRAPARG.primOp;
      dep_args: typelist;
      dep_ret: type
    }.

    Definition implem_deps: list implem_dep :=
      {|
         dep_ident := uctx_arg1;
         dep_lname := TTRAPARG.PUCTXArg1;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := uctx_arg2;
         dep_lname := TTRAPARG.PUCTXArg2;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := uctx_arg3;
         dep_lname := TTRAPARG.PUCTXArg3;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := uctx_arg4;
         dep_lname := TTRAPARG.PUCTXArg4;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := uctx_arg5;
         dep_lname := TTRAPARG.PUCTXArg5;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := uctx_set_errno;
         dep_lname := TTRAPARG.PUCTXSetErrno;
         dep_args := (Tcons tint Tnil);
         dep_ret := Tvoid
      |} ::
      {|
         dep_ident := uctx_set_retval1;
         dep_lname := TTRAPARG.PUCTXSetRetVal1;
         dep_args := (Tcons tint Tnil);
         dep_ret := Tvoid
      |} ::
      {|
         dep_ident := is_chan_ready;
         dep_lname := TTRAPARG.PIsChanReady;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := sendto_chan;
         dep_lname := TTRAPARG.PSendToChan;
         dep_args := (Tcons tint (Tcons tint Tnil));
         dep_ret := tint
      |} ::
      {|
         dep_ident := receive_chan;
         dep_lname := TTRAPARG.PReceiveChan;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := proc_create;
         dep_lname := TTRAPARG.PProcCreate;
         dep_args := (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil));
         dep_ret := tint
      |} ::
      {|
         dep_ident := get_curid5;
         dep_lname := TTRAPARG.PGetCurID;
         dep_args := Tnil;
         dep_ret := tint
      |} ::
      {|
         dep_ident := pt_resv1;
         dep_lname := TTRAPARG.PPTResv;
         dep_args := (Tcons tint (Tcons tint (Tcons tint Tnil)));
         dep_ret := tvoid
      |} ::
      {|
         dep_ident := la2pa_resv;
         dep_lname := TTRAPARG.PLa2PaResv;
         dep_args := (Tcons tint Tnil);
         dep_ret := tint
      |} ::
      nil.

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      map (fun d => (dep_ident d,
                     Some (Gfun (SourceFun (Clight.External (dep_lname d) (dep_args d) (dep_ret d)) dummy))))
          implem_deps.

    Lemma NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit TTRAP.primOp (low := TTRAPARG.primOp) (Clight.fundef (external_function := TTRAPARG.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Definition im : implem Asm.code unit TTRAP.primOp (low := TTRAPARG.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= TTRAP.primOp)).
    Notation Lprogram := (Asm.program (external_function:= TTRAPARG.primOp)).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Lemma well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.

    (* This is basically an axiom that can be easily checked because TTRAP.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

    Lemma extfun_compilation_succeeds_dec:
      {forall p clight asmfallback,
        source_implem_extfuns p = SourceFun clight asmfallback ->
        exists asm, transf_clight_fundef clight = Errors.OK asm} +
      {~ forall p clight asmfallback,
        source_implem_extfuns p = SourceFun clight asmfallback ->
        exists asm, transf_clight_fundef clight = Errors.OK asm}.
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
        exists asm, transf_clight_fundef clight = Errors.OK asm.

    Section WithProg.

    Variable prog: Hprogram.

    Definition tprog: Lprogram := Implementation.transf_program im prog.

    Definition Im (p: TTRAP.primOp): Lfundef :=
      transf_source_fun' transf_clight_fundef (source_implem_extfuns p).

    Lemma TRANSF: TRAPGEN.transf_program
                  (Im TTRAP.PSysProcCreate)
                  (Im TTRAP.PSysIsChanReady)
                  (Im TTRAP.PSysSendToChan)
                  (Im TTRAP.PSysReceiveChan)
                  (Im TTRAP.PPTFaultResv)
                  impl_glbl prog = Errors.OK tprog.
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

    Lemma NEW_INJ:  (forall s', Genv.find_symbol ge s' <> None ->
                                     ~ In s' (map fst impl_glbl)).
    Proof.
      change impl_glbl with (implem_new_globs im).
      apply new_ids_fresh.
      assumption.
    Qed.

    Definition sprog : Clight.program (external_function := TTRAPARG.primOp) := source_program_only source_implem prog.
    Definition sge := Genv.globalenv sprog.

    Ltac elim_or H t :=
      match type of H with
        | False => contradiction
        | _ \/ _ =>
          let K := fresh "K" in
          destruct H as [H | K]; [ elim_or H t | elim_or K t ]
        | _ => t H
      end.

    Lemma tsprog_strong : {tsprog | transf_clight_program sprog = Errors.OK tsprog}.
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

    Definition tsprog := let (p, _) := tsprog_strong in p.

    Lemma tsprog_prop : transf_clight_program sprog = Errors.OK tsprog.
    Proof.
      unfold tsprog.
      destruct tsprog_strong.
      assumption.
    Qed.

    Definition tsge := Genv.globalenv tsprog.


    (** uctx_arg1 *)

    Definition buctx_arg1: block := Genv.genv_next ge + Z.of_nat 0.

    Lemma huctx_arg11 : Genv.find_symbol sge uctx_arg1 = Some buctx_arg1.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_arg1).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma huctx_arg12 : Genv.find_funct sge (Vptr buctx_arg1 Int.zero) = Some (Clight.External (TTRAPARG.PUCTXArg1) Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_arg1 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof huctx_arg11 as huctx_arg11.
      pose proof huctx_arg11 as foo.
      congruence.
    Qed.

    Lemma huctx_arg13 : Clight.type_of_global sge buctx_arg1 = Some (Ctypes.Tfunction Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_arg1).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_arg1. unfold Asm.fundef. omega.
      intros.
      pose proof huctx_arg12 as huctx_arg12.
      simpl in huctx_arg12. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_arg12. reflexivity.
    Qed.

    (** uctx_arg2 *)

    Definition buctx_arg2: block := Genv.genv_next ge + Z.of_nat 1.

    Lemma huctx_arg21 : Genv.find_symbol sge uctx_arg2 = Some buctx_arg2.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_arg2).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma huctx_arg22 : Genv.find_funct sge (Vptr buctx_arg2 Int.zero) = Some (Clight.External (TTRAPARG.PUCTXArg2) Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_arg2 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof huctx_arg21 as huctx_arg21.
      pose proof huctx_arg21.
      congruence.
    Qed.

    Lemma huctx_arg23 : Clight.type_of_global sge buctx_arg2 = Some (Ctypes.Tfunction Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_arg2).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_arg2. unfold Asm.fundef. omega.
      intros.
      pose proof huctx_arg22 as huctx_arg22.
      simpl in huctx_arg22. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_arg22. reflexivity.
    Qed.

    (** uctx_arg3 *)

    Definition buctx_arg3: block := Genv.genv_next ge + Z.of_nat 2.

    Lemma huctx_arg31 : Genv.find_symbol sge uctx_arg3 = Some buctx_arg3.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_arg3).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma huctx_arg32 : Genv.find_funct sge (Vptr buctx_arg3 Int.zero) = Some (Clight.External (TTRAPARG.PUCTXArg3) Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_arg3 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof huctx_arg31 as huctx_arg31.
      pose proof huctx_arg31.
      congruence.
    Qed.

    Lemma huctx_arg33 : Clight.type_of_global sge buctx_arg3 = Some (Ctypes.Tfunction Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_arg3).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_arg3. unfold Asm.fundef. omega.
      intros.
      pose proof huctx_arg32 as huctx_arg32.
      simpl in huctx_arg32. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_arg32. reflexivity.
    Qed.

    (** uctx_arg4 *)

    Definition buctx_arg4: block := Genv.genv_next ge + Z.of_nat 3.

    Lemma huctx_arg41 : Genv.find_symbol sge uctx_arg4 = Some buctx_arg4.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_arg4).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma huctx_arg42 : Genv.find_funct sge (Vptr buctx_arg4 Int.zero) = Some (Clight.External (TTRAPARG.PUCTXArg4) Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_arg4 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof huctx_arg41 as huctx_arg41.
      pose proof huctx_arg41.
      congruence.
    Qed.

    Lemma huctx_arg43 : Clight.type_of_global sge buctx_arg4 = Some (Ctypes.Tfunction Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_arg4).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_arg4. unfold Asm.fundef. omega.
      intros.
      pose proof huctx_arg42 as huctx_arg42.
      simpl in huctx_arg42. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_arg42. reflexivity.
    Qed.

    (** uctx_arg5 *)

    Definition buctx_arg5: block := Genv.genv_next ge + Z.of_nat 4.

    Lemma huctx_arg51 : Genv.find_symbol sge uctx_arg5 = Some buctx_arg5.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_arg5).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma huctx_arg52 : Genv.find_funct sge (Vptr buctx_arg5 Int.zero) = Some (Clight.External (TTRAPARG.PUCTXArg5) Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_arg5 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof huctx_arg51 as huctx_arg51.
      pose proof huctx_arg51.
      congruence.
    Qed.

    Lemma huctx_arg53 : Clight.type_of_global sge buctx_arg5 = Some (Ctypes.Tfunction Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_arg5).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_arg5. unfold Asm.fundef. omega.
      intros.
      pose proof huctx_arg52 as huctx_arg52.
      simpl in huctx_arg52. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_arg52. reflexivity.
    Qed.

    (** uctx_set_errno *)

    Definition buctx_set_errno: block := Genv.genv_next ge + Z.of_nat 5.

    Lemma huctx_set_errno1 : Genv.find_symbol sge uctx_set_errno = Some buctx_set_errno.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_set_errno).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma huctx_set_errno2 : Genv.find_funct sge (Vptr buctx_set_errno Int.zero) = Some (Clight.External (TTRAPARG.PUCTXSetErrno) (Tcons tint Tnil) Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_set_errno _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof huctx_set_errno1 as huctx_set_errno1.
      congruence.
    Qed.

    Lemma huctx_set_errno3 : Clight.type_of_global sge buctx_set_errno = Some (Ctypes.Tfunction (Tcons tint Tnil) Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_set_errno).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_set_errno. unfold Asm.fundef. omega.
      intros.
      pose proof huctx_set_errno2 as huctx_set_errno2.
      simpl in huctx_set_errno2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_set_errno2. reflexivity.
    Qed.

    (** uctx_set_retval1 *)

    Definition buctx_set_retval1: block := Genv.genv_next ge + Z.of_nat 6.

    Lemma huctx_set_retval11 : Genv.find_symbol sge uctx_set_retval1 = Some buctx_set_retval1.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_set_retval1).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma huctx_set_retval12 : Genv.find_funct sge (Vptr buctx_set_retval1 Int.zero) = Some (Clight.External (TTRAPARG.PUCTXSetRetVal1) (Tcons tint Tnil) Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_set_retval1 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof huctx_set_retval11 as huctx_set_retval11.
      congruence.
    Qed.

    Lemma huctx_set_retval13 : Clight.type_of_global sge buctx_set_retval1 = Some (Ctypes.Tfunction (Tcons tint Tnil) Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_set_retval1).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_set_retval1. unfold Asm.fundef. omega.
      intros.
      pose proof huctx_set_retval12 as huctx_set_retval12.
      simpl in huctx_set_retval12. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_set_retval12. reflexivity.
    Qed.

    (** is_chan_ready *)

    Definition bis_chan_ready: block := Genv.genv_next ge + Z.of_nat 7.

    Lemma his_chan_ready1 : Genv.find_symbol sge is_chan_ready = Some bis_chan_ready.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ is_chan_ready).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma his_chan_ready2 : Genv.find_funct sge (Vptr bis_chan_ready Int.zero) = Some (Clight.External (TTRAPARG.PIsChanReady) Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ is_chan_ready _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof his_chan_ready1 as his_chan_ready1.
      pose proof his_chan_ready1 as foo.
      rewrite H in foo;
      inversion foo.
      subst.
      apply H0.
      tauto.
    Qed.

    Lemma his_chan_ready3 : Clight.type_of_global sge bis_chan_ready = Some (Ctypes.Tfunction Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bis_chan_ready).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bis_chan_ready. unfold Asm.fundef. omega.
      intros.
      pose proof his_chan_ready2 as his_chan_ready2.
      simpl in his_chan_ready2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite his_chan_ready2. reflexivity.
    Qed.

    (** sendto_chan *)

    Definition bsendto_chan: block := Genv.genv_next ge + Z.of_nat 8.

    Lemma hsendto_chan1 : Genv.find_symbol sge sendto_chan = Some bsendto_chan.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ sendto_chan).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma hsendto_chan2 : Genv.find_funct sge (Vptr bsendto_chan Int.zero) = Some (Clight.External (TTRAPARG.PSendToChan) (Tcons tint (Tcons tint Tnil)) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ sendto_chan _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof hsendto_chan1 as hsendto_chan1.
      pose proof hsendto_chan1 as foo.
      rewrite H in foo;
      inversion foo.
      subst.
      apply H0.
      tauto.
    Qed.

    Lemma hsendto_chan3 : Clight.type_of_global sge bsendto_chan = Some (Ctypes.Tfunction (Tcons tint (Tcons tint Tnil)) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bsendto_chan).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bsendto_chan. unfold Asm.fundef. omega.
      intros.
      pose proof hsendto_chan2 as hsendto_chan2.
      simpl in hsendto_chan2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hsendto_chan2. reflexivity.
    Qed.

    (** receive_chan *)

    Definition breceive_chan: block := Genv.genv_next ge + Z.of_nat 9.

    Lemma hreceive_chan1 : Genv.find_symbol sge receive_chan = Some breceive_chan.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ receive_chan).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma hreceive_chan2 : Genv.find_funct sge (Vptr breceive_chan Int.zero) = Some (Clight.External (TTRAPARG.PReceiveChan) Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ receive_chan _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof hreceive_chan1 as hreceive_chan1.
      pose proof hreceive_chan1 as foo.
      rewrite H in foo;
      inversion foo.
      subst.
      apply H0.
      tauto.
    Qed.

    Lemma hreceive_chan3 : Clight.type_of_global sge breceive_chan = Some (Ctypes.Tfunction Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge breceive_chan).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold breceive_chan. unfold Asm.fundef. omega.
      intros.
      pose proof hreceive_chan2 as hreceive_chan2.
      simpl in hreceive_chan2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hreceive_chan2. reflexivity.
    Qed.

    (** proc_create *)

    Definition bproc_create: block := Genv.genv_next ge + Z.of_nat 10.

    Lemma hproc_create1 : Genv.find_symbol sge proc_create = Some bproc_create.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ proc_create).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma hproc_create2 : Genv.find_funct sge (Vptr bproc_create Int.zero) = Some (Clight.External (TTRAPARG.PProcCreate) (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ proc_create _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof hproc_create1 as hproc_create1.
      pose proof hproc_create1 as foo.
      rewrite H in foo;
      inversion foo.
      subst.
      apply H0.
      tauto.
    Qed.

    Lemma hproc_create3 : Clight.type_of_global sge bproc_create = Some (Ctypes.Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bproc_create).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bproc_create. unfold Asm.fundef. omega.
      intros.
      pose proof hproc_create2 as hproc_create2.
      simpl in hproc_create2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hproc_create2. reflexivity.
    Qed.


    (** get_curid5 *)
    Definition bget_curid5: block := Genv.genv_next ge + Z.of_nat 11.

    Lemma hget_curid1 : Genv.find_symbol sge get_curid5 = Some bget_curid5.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_curid5).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma hget_curid2 : Genv.find_funct sge (Vptr bget_curid5 Int.zero) = Some (Clight.External (TTRAPARG.PGetCurID) (Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_curid5 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof hget_curid1 as hget_curid51.
      pose proof hget_curid51 as foo.
      rewrite H in foo;
      inversion foo.
      subst.
      apply H0.
      tauto.
    Qed.

    Lemma hget_curid3 : Clight.type_of_global sge bget_curid5 = Some (Ctypes.Tfunction (Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_curid5).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_curid5. unfold Asm.fundef. omega.
      intros.
      pose proof hget_curid2 as hget_curid2.
      simpl in hget_curid2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_curid2. reflexivity.
    Qed.

    (** pt_resv1 *)

    Definition bpt_resv1: block := Genv.genv_next ge + Z.of_nat 12.

    Lemma hpt_resv1 : Genv.find_symbol sge pt_resv1 = Some bpt_resv1.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_resv1).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma hpt_resv2 : Genv.find_funct sge (Vptr bpt_resv1 Int.zero) = Some (Clight.External (TTRAPARG.PPTResv) (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_resv1 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof hpt_resv1 as hpt_resv11.
      pose proof hpt_resv11 as foo.
      rewrite H in foo;
      inversion foo.
      subst.
      apply H0.
      tauto.
    Qed.

    Lemma hpt_resv3 : Clight.type_of_global sge bpt_resv1 = Some (Ctypes.Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_resv1).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_resv1. unfold Asm.fundef. omega.
      intros.
      pose proof hpt_resv2 as hpt_resv2.
      simpl in hpt_resv2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_resv2. reflexivity.
    Qed.

    (** la2pa_resv *)

    Definition bla2pa_resv: block := Genv.genv_next ge + Z.of_nat 13.

    Lemma hla2pa_resv1 : Genv.find_symbol sge la2pa_resv = Some bla2pa_resv.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      apply NOREPET_IMPL.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ la2pa_resv).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Lemma hla2pa_resv2 : Genv.find_funct sge (Vptr bla2pa_resv Int.zero) = Some (Clight.External (TTRAPARG.PLa2PaResv) (Tcons tint Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ la2pa_resv _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: apply NOREPET_IMPL.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      pose proof hla2pa_resv1 as hla2pa_resv1.
      pose proof hla2pa_resv1 as foo.
      rewrite H in foo;
      inversion foo.
      subst.
      apply H0.
      tauto.
    Qed.

    Lemma hla2pa_resv3 : Clight.type_of_global sge bla2pa_resv = Some (Ctypes.Tfunction (Tcons tint Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bla2pa_resv).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bla2pa_resv. unfold Asm.fundef. omega.
      intros.
      pose proof hla2pa_resv2 as hla2pa_resv2.
      simpl in hla2pa_resv2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hla2pa_resv2. reflexivity.
    Qed.

    Hint Resolve
      huctx_arg11
      huctx_arg12
      huctx_arg13
      huctx_arg21
      huctx_arg22
      huctx_arg23
      huctx_arg31
      huctx_arg32
      huctx_arg33
      huctx_arg41
      huctx_arg42
      huctx_arg43
      huctx_arg51
      huctx_arg52
      huctx_arg53
      huctx_set_errno1
      huctx_set_errno2
      huctx_set_errno3
      huctx_set_retval11
      huctx_set_retval12
      huctx_set_retval13
      his_chan_ready1
      his_chan_ready2
      his_chan_ready3
      hsendto_chan1
      hsendto_chan2
      hsendto_chan3
      hreceive_chan1
      hreceive_chan2
      hreceive_chan3
      hproc_create1
      hproc_create2
      hproc_create3
      hget_curid1
      hget_curid2
      hget_curid3
      hpt_resv1
      hpt_resv2
      hpt_resv3
      hla2pa_resv1
      hla2pa_resv2
      hla2pa_resv3.

    Context `{PageFaultHandler_LOC: ident}.
    Context `{START_USER_FUN_LOC: ident}.

    Section WITHMEM.

      Local Instance LdataOp:AbstractDataOps LDATA:= (PPROC.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel LDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections LDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) LDATA TTRAP.primOp mem__H :=
        TTRAP.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                        (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (ELF_LOC:= ELF_LOC)
                        (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                        (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                        (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan)
                        (real_chpool := real_chpool)
                        (STACK_LOC:= STACK_LOC)(STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC := START_USER_FUN_LOC) (ELF_ENTRY_LOC:= ELF_ENTRY_LOC).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA TTRAPARG.primOp mem__L :=
        TTRAPARG.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                           (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                           (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                           (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                           (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool := real_chpool)
                           (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC := START_USER_FUN_LOC).

      Notation HLoad := (TTRAP.exec_loadex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation HStore := (TTRAP.exec_storeex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation LLoad := (TTRAPARG.exec_loadex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation LStore := (TTRAPARG.exec_storeex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).

      Notation lstep := (TTRAPARG.step
                           (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4) (real_chpool:= real_chpool)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)
                           (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC:= START_USER_FUN_LOC)(NPT_LOC:=NPT_LOC)).

      Notation LADT := PPROC.ADT.

      Hint Resolve
        TTRAPARG.exec_load_exec_loadex
        TTRAPARG.exec_store_exec_storeex
        TTRAPARG.extcall_not_primitive
        TTRAPARG.primitive_kernel_mode
        NEW_INJ
        NOREPET_IMPL.

      Ltac discharge_or:= match goal with
        | [|- ?a = ?a] => reflexivity
        | [|- (?a = ?a) \/ _] => left; reflexivity
        | [|- _ \/ _] => right
        | _ => fail
      end.

      Lemma sys_proc_create_spec :
        forall m0 rs b sig elf_id buserstart belf busercode bstack bentry
               ofs pid abd' abd'' abd0,
          rs PC = Vptr b Int.zero ->
          Genv.find_funct_ptr tge b = Some (Im TTRAP.PSysProcCreate) ->
          TTRAPARG.uctx_arg1 (Mem.get_abstract_data m0) = Some elf_id ->
          Genv.find_symbol tge START_USER_FUN_LOC = Some buserstart ->
          Genv.find_symbol tge ELF_LOC = Some belf ->
          Genv.find_symbol tge ELF_ENTRY_LOC = Some bentry ->
          Genv.find_symbol tge STACK_LOC = Some bstack ->
          (exists fun_id, Genv.find_symbol tge fun_id = Some busercode) ->
          Genv.find_symbol ge START_USER_FUN_LOC = Some buserstart ->
          Genv.find_symbol ge ELF_LOC = Some belf ->
          Genv.find_symbol ge ELF_ENTRY_LOC = Some bentry ->
          Genv.find_symbol ge STACK_LOC = Some bstack ->
          (exists fun_id, Genv.find_symbol ge fun_id = Some busercode) ->
          Int.unsigned ofs = (Int.unsigned pid + 1) * PgSize - 4 ->
          0<= (Int.unsigned elf_id) < num_proc ->
          Mem.load Mint32 m0 bentry ((Int.unsigned elf_id) * 4) = Some (Vptr busercode Int.zero) ->
          PPROC.proc_create (Hnchan := Hnchan) (STACK_TOP := STACK_TOP)
                                (Mem.get_abstract_data m0)
                                bstack buserstart busercode ofs Int.zero= Some (abd', Int.unsigned pid) ->
          TTRAPARG.uctx_set_retval1 abd' pid = Some abd'' ->
          TTRAPARG.uctx_set_errno abd'' Int.zero = Some abd0 ->
          sig = mksignature nil None ->
          extcall_arguments rs m0 sig nil ->
          Genv.find_funct_ptr ge b = Some (External TTRAP.PSysProcCreate)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' abd0))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
      Proof.
        intros.
        exploit (ClightImplemExtra.bigstep_clight_to_lsem
                   TTRAP.primOp
                   (exec_load := LLoad)
                   (exec_store := LStore)
                   (primitive_call := TTRAPARG.primitive_call (Hnchan:= Hnchan))
                   (is_primitive_call := TTRAPARG.is_primitive_call)
                   (kernel_mode := PPROC.kernel_mode)
                );
          eauto.
        * apply NOREPET_IMPL.
        * apply NEW_INJ.
        * apply tsprog_prop.
        * intros; eapply TTRAPARGCODE.sys_proc_create_correct; eauto.

          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          repeat (destruct H18; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ]).
          contradiction.
          eassumption.

          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          repeat (destruct H18; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ]).
          contradiction.
          eassumption.

          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          repeat (destruct H18; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ]).
          contradiction.
          eassumption.

          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          repeat (destruct H18; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ]).
          contradiction.
          eassumption.

          destruct H11.
          esplit.
          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          destruct H27; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ].
          repeat (destruct H18; subst;
          [apply NEW_INJ in H26;
          simpl in H26;
          destruct H26;
          repeat discharge_or | ]).
          contradiction.
          eassumption.

        * subst.
          reflexivity.
        * reflexivity.
        * unfold PPROC.kernel_mode.
          apply PPROC.proc_create_eq in H15.
          unfold PPROC.proc_create_aux in H15.
          case_eq (PPROC.pe (LADT (Mem.get_abstract_data m0))); intro rw; rewrite rw in H15; try discriminate H15; clear rw.
          case_eq (PPROC.ikern (LADT (Mem.get_abstract_data m0))); intro rw; rewrite rw in H15; try discriminate H15; clear rw.
          case_eq (PPROC.ihost (LADT (Mem.get_abstract_data m0))); intro rw; rewrite rw in H15; try discriminate H15; clear rw.
          auto.
        * destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) abd0) in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace abd0 with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
      Qed.

      Lemma sys_is_chan_ready_spec :
        forall m0 rs b sig ready abd' abd'',
          rs PC = Vptr b Int.zero ->
          Genv.find_funct_ptr tge b = Some (Im TTRAP.PSysIsChanReady) ->
          PPROC.is_chan_ready (Mem.get_abstract_data m0) = Some ready ->
          TTRAPARG.uctx_set_retval1 (Mem.get_abstract_data m0) ready = Some abd' ->
          TTRAPARG.uctx_set_errno abd' Int.zero = Some abd'' ->
          sig = mksignature nil None ->
          extcall_arguments rs m0 sig nil ->
          Genv.find_funct_ptr ge b = Some (External TTRAP.PSysIsChanReady)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_,
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f'
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' abd''))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
      Proof.
        intros.
        exploit (ClightImplemExtra.bigstep_clight_to_lsem
                   TTRAP.primOp
                   (exec_load := LLoad)
                   (exec_store := LStore)
                   (primitive_call := TTRAPARG.primitive_call (Hnchan:= Hnchan))
                   (is_primitive_call := TTRAPARG.is_primitive_call)
                   (kernel_mode := PPROC.kernel_mode)
                );
          eauto.
        * apply NOREPET_IMPL.
        * apply NEW_INJ.
        * apply tsprog_prop.
        * intros; eapply TTRAPARGCODE.sys_is_chan_ready_correct; eauto.
        * subst.
          reflexivity.
        * reflexivity.
        * unfold PPROC.kernel_mode.
          functional inversion H1; unfold adt in *; auto.
        * destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) abd'') in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace abd'' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
      Qed.

      Lemma sys_send_spec :
        forall m0 rs b sig chid content ret abd' abd'' abd''',
          rs PC = Vptr b Int.zero ->
          Genv.find_funct_ptr tge b = Some (Im TTRAP.PSysSendToChan) ->
          TTRAPARG.uctx_arg1 (Mem.get_abstract_data m0) = Some chid ->
          TTRAPARG.uctx_arg2 (Mem.get_abstract_data m0) = Some content ->
          PPROC.sendto_chan (Mem.get_abstract_data m0)
                                (Int.unsigned chid) content = Some (abd', ret) ->
          TTRAPARG.uctx_set_retval1 abd' ret = Some abd'' ->
          TTRAPARG.uctx_set_errno abd'' Int.zero = Some abd''' ->
          sig = mksignature nil None ->
          extcall_arguments rs m0 sig nil ->
          Genv.find_funct_ptr ge b = Some (External TTRAP.PSysSendToChan)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_,
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f'
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' abd'''))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
      Proof.
        intros.
        exploit (ClightImplemExtra.bigstep_clight_to_lsem
                   TTRAP.primOp
                   (exec_load := LLoad)
                   (exec_store := LStore)
                   (primitive_call := TTRAPARG.primitive_call (Hnchan:= Hnchan))
                   (is_primitive_call := TTRAPARG.is_primitive_call)
                   (kernel_mode := PPROC.kernel_mode)
                );
          eauto.
        * apply NOREPET_IMPL.
        * apply NEW_INJ.
        * apply tsprog_prop.
        * intros; eapply TTRAPARGCODE.sys_sendto_chan_correct; eauto.
        * subst.
          reflexivity.
        * reflexivity.
        * unfold PPROC.kernel_mode.
          apply PPROC.sendto_chan_eq in H3.
          functional inversion H3; unfold adt in *; auto.
        * destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) abd''') in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace abd''' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
      Qed.

      Lemma sys_recv_spec :
        forall m0 rs b sig content abd' abd'' abd''',
          rs PC = Vptr b Int.zero ->
          Genv.find_funct_ptr tge b = Some (Im TTRAP.PSysReceiveChan) ->
          PPROC.receive_chan (Hnchan := Hnchan)
                                 (Mem.get_abstract_data m0) = Some (abd', content) ->
          TTRAPARG.uctx_set_retval1 abd' content = Some abd'' ->
          TTRAPARG.uctx_set_errno abd'' Int.zero = Some abd''' ->
          sig = mksignature nil None ->
          extcall_arguments rs m0 sig nil ->
          Genv.find_funct_ptr ge b = Some (External TTRAP.PSysReceiveChan)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_,
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f'
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' abd'''))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
      Proof.
        intros.
        exploit (ClightImplemExtra.bigstep_clight_to_lsem
                   TTRAP.primOp
                   (exec_load := LLoad)
                   (exec_store := LStore)
                   (primitive_call := TTRAPARG.primitive_call (Hnchan:= Hnchan))
                   (is_primitive_call := TTRAPARG.is_primitive_call)
                   (kernel_mode := PPROC.kernel_mode)
                );
          eauto.
        * apply NOREPET_IMPL.
        * apply NEW_INJ.
        * apply tsprog_prop.
        * intros; eapply TTRAPARGCODE.sys_receive_chan_correct; eauto.
        * subst.
          reflexivity.
        * reflexivity.
        * unfold PPROC.kernel_mode.
          apply PPROC.receive_chan_eq in H1.
          functional inversion H1; unfold adt in *; auto.
        * destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) abd''') in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace abd''' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
      Qed.

      Lemma ptf_resv_spec :
        forall m0 rs b sig abd' abd'' vadr,
          rs PC = Vptr b Int.zero ->
          Genv.find_funct_ptr tge b = Some (Im TTRAP.PPTFaultResv) ->
          PPROC.ptResv (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (Mem.get_abstract_data m0) 
                           (PPROC.cid(LADT(Mem.get_abstract_data m0)))
                           (Int.unsigned vadr) PT_PERM_PTU = Some abd' ->
          TTRAPARG.uctx_set_errno abd' Int.zero = Some abd'' ->
          sig = mksignature (AST.Tint::nil) None ->
          extcall_arguments rs m0 sig (Vint vadr::nil) ->
          Genv.find_funct_ptr ge b = Some (External TTRAP.PPTFaultResv)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> asm_invariant tge (State rs m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' abd''))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
      Proof.
        intros.
        exploit (ClightImplemExtra.bigstep_clight_to_lsem
                   TTRAP.primOp
                   (exec_load := LLoad)
                   (exec_store := LStore)
                   (primitive_call := TTRAPARG.primitive_call (Hnchan:= Hnchan))
                   (is_primitive_call := TTRAPARG.is_primitive_call)
                   (kernel_mode := PPROC.kernel_mode)
                );
          eauto.
        * apply NOREPET_IMPL.
        * apply NEW_INJ.
        * apply tsprog_prop.
        * intros; eapply TTRAPARGCODE.ptf_resv_correct; eauto.
        * subst.
          reflexivity.
        * reflexivity.
        * unfold PPROC.kernel_mode.
          apply PPROC.ptResv_eq in H1.
          functional inversion H1.
          functional inversion H11; unfold adt in *; auto.
        * destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) abd'') in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace abd'' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
      Qed.

      Theorem transf_program_correct:
        Smallstep.backward_simulation
          (TTRAP.semantics (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (ELF_ENTRY_LOC:= ELF_ENTRY_LOC)
                           (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                           (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                           (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                           (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool:= real_chpool) (STACK_TOP:= STACK_TOP)
                           (START_USER_FUN_LOC:= START_USER_FUN_LOC) (ELF_LOC:= ELF_LOC) (NPT_LOC:=NPT_LOC)prog)
          (TTRAPARG.semantics (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (STACK_TOP:= STACK_TOP)
                              (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                              (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                              (Hnchan:= Hnchan) (real_abq:= real_abq) (real_chpool:= real_chpool)
                              (START_USER_FUN_LOC:= START_USER_FUN_LOC) (NPT_LOC:=NPT_LOC) tprog).
      Proof.
        eapply (TRAPGEN.transf_program_correct
                  (Im TTRAP.PSysProcCreate)
                  (Im TTRAP.PSysIsChanReady)
                  (Im TTRAP.PSysSendToChan)
                  (Im TTRAP.PSysReceiveChan)
                  (Im TTRAP.PPTFaultResv)
                  impl_glbl); eauto.

        * apply TRANSF.
        * apply sys_proc_create_spec.
        * apply sys_is_chan_ready_spec.
        * apply sys_send_spec.
        * apply sys_recv_spec.
        * apply ptf_resv_spec.

          Grab Existential Variables.
          omega.
      Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End TRAPGENIMPL.
