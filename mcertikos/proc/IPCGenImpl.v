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
Require Import PIPC.
Require Import PIPCIntro.
Require Export IPCGen.
Require Import PIPCIntroCode.
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

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module IPCGENIMPL.
  Export IPCGen.IPCGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PIPC.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PIPC.PAlloc)...
    destruct (Q_dec PIPC.PFree)...
    destruct (Q_dec PIPC.PSetPT)...
    destruct (Q_dec PIPC.PPTRead)...
    destruct (Q_dec PIPC.PPTResv)...
    destruct (Q_dec PIPC.PThreadSpawn)...
    destruct (Q_dec PIPC.PThreadKill)...
    destruct (Q_dec PIPC.PThreadWakeup)...
    destruct (Q_dec PIPC.PThreadYield)...
    destruct (Q_dec PIPC.PThreadSleep)...
    destruct (Q_dec PIPC.PGetCurID)...
    destruct (Q_dec PIPC.PPTIn)...
    destruct (Q_dec PIPC.PPTOut)...
    destruct (Q_dec PIPC.PTrapIn)...
    destruct (Q_dec PIPC.PTrapOut)...
    destruct (Q_dec PIPC.PHostIn)...
    destruct (Q_dec PIPC.PHostOut)...
    destruct (Q_dec PIPC.PTrapGet)...
    destruct (Q_dec PIPC.PTrapRet)...
    destruct (Q_dec PIPC.PIsChanReady)...
    destruct (Q_dec PIPC.PSendToChan)...
    destruct (Q_dec PIPC.PReceiveChan)...
    destruct (Q_dec PIPC.PProcInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PIPC.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                   (num_chan:= num_chan) (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA :=(PIPCINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (Asm.fundef (external_function:= PIPC.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PIPCINTRO.primOp)).

    Notation funkind := (funkind (low:= PIPCINTRO.primOp) Asm.code (Clight.fundef (external_function := PIPCINTRO.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: PIPC.primOp): funkind :=
      match p with
        | PIPC.PAlloc => Code _ (AST.External PIPCINTRO.PAlloc)
        | PIPC.PFree => Code _ (AST.External PIPCINTRO.PFree)
        | PIPC.PSetPT => Code _ (AST.External PIPCINTRO.PSetPT)
        | PIPC.PPTRead => Code _ (AST.External PIPCINTRO.PPTRead)
        | PIPC.PPTResv => Code _ (AST.External PIPCINTRO.PPTResv)
        | PIPC.PThreadSpawn => Code _ (AST.External PIPCINTRO.PThreadSpawn)
        | PIPC.PThreadKill => Code _ (AST.External PIPCINTRO.PThreadKill)
        | PIPC.PThreadWakeup => Code _ (AST.External PIPCINTRO.PThreadWakeup)
        | PIPC.PThreadYield => Code _ (AST.External PIPCINTRO.PThreadYield)
        | PIPC.PThreadSleep => Code _ (AST.External PIPCINTRO.PThreadSleep)
        | PIPC.PGetCurID => SourceFun (Clight.External (PIPCINTRO.PGetCurID) (Ctypes.Tnil) tint) dummy
        | PIPC.PPTIn => Code _ (AST.External PIPCINTRO.PPTIn)
        | PIPC.PPTOut => Code _ (AST.External PIPCINTRO.PPTOut)
        | PIPC.PTrapIn => Code _ (AST.External PIPCINTRO.PTrapIn)
        | PIPC.PTrapOut => Code _ (AST.External PIPCINTRO.PTrapOut)
        | PIPC.PHostIn => Code _ (AST.External PIPCINTRO.PHostIn)
        | PIPC.PHostOut => Code _ (AST.External PIPCINTRO.PHostOut)
        | PIPC.PTrapGet => Code _ (AST.External PIPCINTRO.PTrapGet)
        | PIPC.PTrapRet => Code _ (AST.External PIPCINTRO.PTrapRet)
        | PIPC.PIsChanReady => SourceFun (Clight.Internal PIPCINTROCODE.f_is_chan_ready) (AST.Internal nil)
        | PIPC.PSendToChan => SourceFun (Clight.Internal PIPCINTROCODE.f_sendto_chan) (AST.Internal nil)
        | PIPC.PReceiveChan => SourceFun (Clight.Internal PIPCINTROCODE.f_receive_chan) (AST.Internal nil)
        | PIPC.PProcInit => SourceFun (Clight.Internal PIPCINTROCODE.f_proc_init) (AST.Internal nil)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (get_chan_info, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PGetChanInfo) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (get_chan_content, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PGetChanContent) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (set_chan_info, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PSetChanInfo) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (set_chan_content, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PSetChanContent) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (thread_wakeup, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PThreadWakeup) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (init_chan, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PInitChan) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid) dummy)))
        :: (sched_init, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PSchedInit) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (get_curid, Some (Gfun (SourceFun (Clight.External (PIPCINTRO.PGetCurID) (Ctypes.Tnil) tint) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PIPC.primOp (low := PIPCINTRO.primOp) (Clight.fundef (external_function := PIPCINTRO.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PIPC.primOp (low := PIPCINTRO.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PIPC.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PIPCINTRO.primOp)).

    Let Im_is_chan_ready: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPC.PIsChanReady).
    Let Im_sendto_chan: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPC.PSendToChan).
    Let Im_receive_chan: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPC.PReceiveChan).
    Let Im_proc_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPC.PProcInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PIPC.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: IPCGEN.transf_program Im_proc_init Im_is_chan_ready Im_sendto_chan Im_receive_chan impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PIPCINTRO.primOp) := source_program_only source_implem prog.
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

    (** get_chan_info *)

    Let bget_chan_info: block := Genv.genv_next ge + Z.of_nat 0.

    Let hget_chan_info1 : Genv.find_symbol sge get_chan_info = Some bget_chan_info. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_chan_info).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hget_chan_info2 : Genv.find_funct sge (Vptr bget_chan_info Int.zero) = Some (Clight.External (PIPCINTRO.PGetChanInfo) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_chan_info _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hget_chan_info3 : Clight.type_of_global sge bget_chan_info = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_chan_info).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_chan_info. unfold Asm.fundef. omega.
      intros.
      simpl in hget_chan_info2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_chan_info2. reflexivity.
    Qed.   

    (** get_chan_content *)

    Let bget_chan_content: block := Genv.genv_next ge + Z.of_nat 1.

    Let hget_chan_content1 : Genv.find_symbol sge get_chan_content = Some bget_chan_content. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_chan_content).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hget_chan_content2 : Genv.find_funct sge (Vptr bget_chan_content Int.zero) = Some (Clight.External (PIPCINTRO.PGetChanContent) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_chan_content _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hget_chan_content3 : Clight.type_of_global sge bget_chan_content = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_chan_content).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_chan_content. unfold Asm.fundef. omega.
      intros.
      simpl in hget_chan_content2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_chan_content2. reflexivity.
    Qed.   

    (** set_chan_info *)

    Let bset_chan_info: block := Genv.genv_next ge + Z.of_nat 2.

    Let hset_chan_info1 : Genv.find_symbol sge set_chan_info = Some bset_chan_info. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_chan_info).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_chan_info2 : Genv.find_funct sge (Vptr bset_chan_info Int.zero) = Some (Clight.External (PIPCINTRO.PSetChanInfo) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_chan_info _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_chan_info3 : Clight.type_of_global sge bset_chan_info = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_chan_info).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_chan_info. unfold Asm.fundef. omega.
      intros.
      simpl in hset_chan_info2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_chan_info2. reflexivity.
    Qed.   

    (** set_chan_content *)

    Let bset_chan_content: block := Genv.genv_next ge + Z.of_nat 3.

    Let hset_chan_content1 : Genv.find_symbol sge set_chan_content = Some bset_chan_content. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_chan_content).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_chan_content2 : Genv.find_funct sge (Vptr bset_chan_content Int.zero) = Some (Clight.External (PIPCINTRO.PSetChanContent) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_chan_content _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_chan_content3 : Clight.type_of_global sge bset_chan_content = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_chan_content).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_chan_content. unfold Asm.fundef. omega.
      intros.
      simpl in hset_chan_content2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_chan_content2. reflexivity.
    Qed.   

    (** thread_wakeup *)

    Let bthread_wakeup: block := Genv.genv_next ge + Z.of_nat 4.

    Let hthread_wakeup1 : Genv.find_symbol sge thread_wakeup = Some bthread_wakeup. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ thread_wakeup).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hthread_wakeup2 : Genv.find_funct sge (Vptr bthread_wakeup Int.zero) = Some (Clight.External (PIPCINTRO.PThreadWakeup) (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ thread_wakeup _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hthread_wakeup3 : Clight.type_of_global sge bthread_wakeup = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bthread_wakeup).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bthread_wakeup. unfold Asm.fundef. omega.
      intros.
      simpl in hthread_wakeup2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hthread_wakeup2. reflexivity.
    Qed.   

    (** init_chan *)

    Let binit_chan: block := Genv.genv_next ge + Z.of_nat 5.

    Let hinit_chan1 : Genv.find_symbol sge init_chan = Some binit_chan. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ init_chan).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hinit_chan2 : Genv.find_funct sge (Vptr binit_chan Int.zero) = Some (Clight.External (PIPCINTRO.PInitChan) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ init_chan _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hinit_chan3 : Clight.type_of_global sge binit_chan = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge binit_chan).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold binit_chan. unfold Asm.fundef. omega.
      intros.
      simpl in hinit_chan2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hinit_chan2. reflexivity.
    Qed.   

    (** sched_init *)

    Let bsched_init: block := Genv.genv_next ge + Z.of_nat 6.

    Let hsched_init1 : Genv.find_symbol sge sched_init = Some bsched_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ sched_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hsched_init2 : Genv.find_funct sge (Vptr bsched_init Int.zero) = Some (Clight.External (PIPCINTRO.PSchedInit) (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ sched_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hsched_init3 : Clight.type_of_global sge bsched_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bsched_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bsched_init. unfold Asm.fundef. omega.
      intros.
      simpl in hsched_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hsched_init2. reflexivity.
    Qed. 

    (** get_curid *)

    Let bget_curid: block := Genv.genv_next ge + Z.of_nat 7.

    Let hget_curid1 : Genv.find_symbol sge get_curid = Some bget_curid. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_curid).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hget_curid2 : Genv.find_funct sge (Vptr bget_curid Int.zero) = Some (Clight.External (PIPCINTRO.PGetCurID) (Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_curid _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 9.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hget_curid3 : Clight.type_of_global sge bget_curid = Some (Ctypes.Tfunction (Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_curid).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_curid. unfold Asm.fundef. omega.
      intros.
      simpl in hget_curid2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_curid2. reflexivity.
    Qed. 

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Local Instance HdataOp:AbstractDataOps HDATA:= (PIPC.abstract_data (Hnpc:= Hnpc)).
      Local Instance LdataOp:AbstractDataOps LDATA:= (PIPCINTRO.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PIPC.primOp mem__H :=
        PIPC.layer_def(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                      (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                      (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                      (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                      (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool:= real_chpool).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PIPCINTRO.primOp mem__L :=
        PIPCINTRO.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                            (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                            (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                            (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).        

      Notation HLoad := (PIPC.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PIPC.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PIPCINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PIPCINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PIPCINTRO.step 
                           (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)).

      Notation LADT := PIPCINTRO.ADT.

      Let is_chan_ready_spec:
        forall r' b m0 sig r,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_is_chan_ready)
          -> Genv.find_funct_ptr ge b = Some (External PIPC.PIsChanReady)
          -> sig = mksignature nil (Some Tint)
          -> PIPCINTRO.is_chan_ready (Mem.get_abstract_data m0) = Some r
          -> extcall_arguments r' m0 sig nil
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint r)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPC.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPCINTRO.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPCINTRO.is_primitive_call)
                     (kernel_mode := PIPCINTRO.kernel_mode)
                  ).
          apply PIPCINTRO.exec_load_exec_loadex.
          apply PIPCINTRO.exec_store_exec_storeex.
          apply PIPCINTRO.extcall_not_primitive.
          apply PIPCINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PIPCINTROCODE.is_chan_ready_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPCINTRO.kernel_mode.
          functional inversion H3; unfold adt in *; destruct (PIPCINTRO.INV (Mem.get_abstract_data m0)); auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          inv H10.
          rewrite Mem.nextblock_put_abstract_data in NB.
          eauto 11.
        Qed.

      Let sendto_chan_spec:
        forall r' n b m0 labd' sig i r,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_sendto_chan)
          -> Genv.find_funct_ptr ge b = Some (External PIPC.PSendToChan)
          -> sig = mksignature (Tint :: Tint :: nil) (Some Tint)
          -> extcall_arguments r' m0 sig (Vint n:: Vint i::nil)
          -> PIPCINTRO.sendto_chan (Mem.get_abstract_data m0) (Int.unsigned n) i = Some (labd', r)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ r_ # (loc_external_result sig) = (Vint r)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPC.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPCINTRO.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPCINTRO.is_primitive_call)
                     (kernel_mode := PIPCINTRO.kernel_mode)
                  ).
          apply PIPCINTRO.exec_load_exec_loadex.
          apply PIPCINTRO.exec_store_exec_storeex.
          apply PIPCINTRO.extcall_not_primitive.
          apply PIPCINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PIPCINTROCODE.sendto_chan_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPCINTRO.kernel_mode.
          apply PIPCINTRO.sendto_chan_eq in H4.
          functional inversion H4; unfold adt in *; destruct (PIPCINTRO.INV (Mem.get_abstract_data m0)); auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
          inv H10.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace labd' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

      Let receive_chan_spec:
        forall r' b m0 labd' sig r,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_receive_chan)
          -> Genv.find_funct_ptr ge b = Some (External PIPC.PReceiveChan)
          -> sig = mksignature nil (Some Tint)
          -> PIPCINTRO.receive_chan (Hnchan:= Hnchan) (Mem.get_abstract_data m0) = Some (labd', r)
          -> extcall_arguments r' m0 sig nil
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ r_ # (loc_external_result sig) = (Vint r)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPC.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPCINTRO.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPCINTRO.is_primitive_call)
                     (kernel_mode := PIPCINTRO.kernel_mode)
                  ).
          apply PIPCINTRO.exec_load_exec_loadex.
          apply PIPCINTRO.exec_store_exec_storeex.
          apply PIPCINTRO.extcall_not_primitive.
          apply PIPCINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PIPCINTROCODE.receive_chan_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPCINTRO.kernel_mode.
          apply PIPCINTRO.receive_chan_eq in H3.
          functional inversion H3; unfold adt in *; destruct (PIPCINTRO.INV (Mem.get_abstract_data m0)); auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
          inversion H10.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace labd' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

      Let proc_init_spec:
        forall r' b m0 labd' sig mbi_adr,
          let labd := (Mem.get_abstract_data m0) in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_proc_init)
          -> Genv.find_funct_ptr ge b = Some (External PIPC.PProcInit)
          -> sig = mksignature (Tint :: nil) None
          -> extcall_arguments r' m0 sig (Vint mbi_adr:: nil)
          -> PIPCINTRO.proc_init (Hnpc:= Hnpc) (Mem.get_abstract_data m0) real_nps 
                                 (real_AT (PIPCINTRO.AT (LADT labd)))
                                 (real_ptp (PIPCINTRO.ptpool (LADT labd)))
                                 (real_pt (PIPCINTRO.ptpool (LADT labd)))
                                 (real_ptb (PIPCINTRO.pb (LADT labd)))
                                 (real_abtcb (PIPCINTRO.abtcb (LADT labd)))
                                 (real_abq (PIPCINTRO.abq (LADT labd)))
                                 (real_chpool (PIPCINTRO.chpool (LADT labd)))
                                 (Int.unsigned mbi_adr) = Some labd'
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPC.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPCINTRO.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPCINTRO.is_primitive_call)
                     (kernel_mode := PIPCINTRO.kernel_mode)
                  ).
          apply PIPCINTRO.exec_load_exec_loadex.
          apply PIPCINTRO.exec_store_exec_storeex.
          apply PIPCINTRO.extcall_not_primitive.
          apply PIPCINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PIPCINTROCODE.proc_init_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPCINTRO.kernel_mode.
          apply PIPCINTRO.proc_init_eq in H4.
          functional inversion H4; unfold adt in *; destruct (PIPCINTRO.INV (Mem.get_abstract_data m0)); auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace labd' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

    Theorem transf_program_correct:
       Smallstep.backward_simulation 
          (PIPC.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                          (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                          (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                          (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                          (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool:= real_chpool) prog) 
          (PIPCINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                               (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                               (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                               (Hnchan:= Hnchan) (real_abq:= real_abq) tprog).
    Proof.
      eapply IPCGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End IPCGENIMPL.
