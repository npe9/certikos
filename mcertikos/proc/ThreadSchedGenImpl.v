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
Require Import PThreadSched.
Require Import PCurID.
Require Export ThreadSchedGen.
Require Import PCurIDCode.
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
Require Import ThreadSchedGenAsm.
Require Import Conventions.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module THREADSCHEDGENIMPL.
  Export ThreadSchedGen.THREADSCHEDGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PTHREADSCHED.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PTHREADSCHED.PAlloc)...
    destruct (Q_dec PTHREADSCHED.PFree)...
    destruct (Q_dec PTHREADSCHED.PSetPT)...
    destruct (Q_dec PTHREADSCHED.PPTRead)...
    destruct (Q_dec PTHREADSCHED.PPTResv)...
    destruct (Q_dec PTHREADSCHED.PThreadSpawn)...
    destruct (Q_dec PTHREADSCHED.PThreadKill)...
    destruct (Q_dec PTHREADSCHED.PThreadWakeup)...
    destruct (Q_dec PTHREADSCHED.PThreadSched)...
    destruct (Q_dec PTHREADSCHED.PSetState)...
    destruct (Q_dec PTHREADSCHED.PEnQueue)...
    destruct (Q_dec PTHREADSCHED.PGetCurID)...
    destruct (Q_dec PTHREADSCHED.PPTIn)...
    destruct (Q_dec PTHREADSCHED.PPTOut)...
    destruct (Q_dec PTHREADSCHED.PTrapIn)...
    destruct (Q_dec PTHREADSCHED.PTrapOut)...
    destruct (Q_dec PTHREADSCHED.PHostIn)...
    destruct (Q_dec PTHREADSCHED.PHostOut)...
    destruct (Q_dec PTHREADSCHED.PTrapGet)...
    destruct (Q_dec PTHREADSCHED.PTrapRet)...
    destruct (Q_dec PTHREADSCHED.PSchedInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PTHREADSCHED.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                           (num_chan:= num_chan) (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA :=(PCURID.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                    (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (Asm.fundef (external_function:= PTHREADSCHED.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PCURID.primOp)).

    Notation funkind := (funkind (low:= PCURID.primOp) Asm.code (Clight.fundef (external_function := PCURID.primOp))).

    Notation dummy := (AST.Internal nil).

    Let Im_thread_sched: Lfundef := THREADSCHEDGEN_ASM.Im_thread_sched.

    Definition source_implem_extfuns (p: PTHREADSCHED.primOp): funkind :=
      match p with
        | PTHREADSCHED.PAlloc => Code _ (AST.External PCURID.PAlloc)
        | PTHREADSCHED.PFree => Code _ (AST.External PCURID.PFree)
        | PTHREADSCHED.PSetPT => Code _ (AST.External PCURID.PSetPT)
        | PTHREADSCHED.PPTRead => Code _ (AST.External PCURID.PPTRead)
        | PTHREADSCHED.PPTResv => Code _ (AST.External PCURID.PPTResv)
        | PTHREADSCHED.PThreadSpawn => SourceFun (Clight.Internal PCURIDCODE.f_thread_spawn) (AST.Internal nil)
        | PTHREADSCHED.PThreadKill => SourceFun (Clight.Internal PCURIDCODE.f_thread_kill) (AST.Internal nil)
        | PTHREADSCHED.PThreadWakeup => SourceFun (Clight.Internal PCURIDCODE.f_thread_wakeup) (AST.Internal nil)
        | PTHREADSCHED.PThreadSched => Code _ Im_thread_sched
        | PTHREADSCHED.PSetState => Code _ (AST.External PCURID.PSetState)
        | PTHREADSCHED.PEnQueue => Code _ (AST.External PCURID.PEnQueue)
        | PTHREADSCHED.PGetCurID => Code _ (AST.External PCURID.PGetCurID)
        | PTHREADSCHED.PPTIn => Code _ (AST.External PCURID.PPTIn)
        | PTHREADSCHED.PPTOut => Code _ (AST.External PCURID.PPTOut)
        | PTHREADSCHED.PTrapIn => Code _ (AST.External PCURID.PTrapIn)
        | PTHREADSCHED.PTrapOut => Code _ (AST.External PCURID.PTrapOut)
        | PTHREADSCHED.PHostIn => Code _ (AST.External PCURID.PHostIn)
        | PTHREADSCHED.PHostOut => Code _ (AST.External PCURID.PHostOut)
        | PTHREADSCHED.PTrapGet => Code _ (AST.External PCURID.PTrapGet)
        | PTHREADSCHED.PTrapRet => Code _ (AST.External PCURID.PTrapRet)
        | PTHREADSCHED.PSchedInit => SourceFun (Clight.Internal PCURIDCODE.f_sched_init) (AST.Internal nil)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (kctxt_new, Some (Gfun (SourceFun (Clight.External (PCURID.PKCtxtNew) (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tint) dummy)))
        :: (set_state, Some (Gfun (SourceFun (Clight.External (PCURID.PSetState) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (enqueue, Some (Gfun (SourceFun (Clight.External (PCURID.PEnQueue) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (dequeue, Some (Gfun (SourceFun (Clight.External (PCURID.PDeQueue) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (queue_rmv, Some (Gfun (SourceFun (Clight.External (PCURID.PQueueRmv) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (tdqueue_init, Some (Gfun (SourceFun (Clight.External (PCURID.PTDQueueInit) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (set_curid, Some (Gfun (SourceFun (Clight.External (PCURID.PSetCurID) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (thread_free, Some (Gfun (SourceFun (Clight.External (PCURID.PThreadFree) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (get_curid_1, Some (Gfun (SourceFun (Clight.External (PCURID.PGetCurID) (Ctypes.Tnil) tint) dummy)))
        :: (kctxt_switch, Some (Gfun (SourceFun (Clight.External (PCURID.PKCtxtSwitch) (Ctypes.Tnil) tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PTHREADSCHED.primOp (low := PCURID.primOp) (Clight.fundef (external_function := PCURID.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PTHREADSCHED.primOp (low := PCURID.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PTHREADSCHED.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PCURID.primOp)).

    Let Im_thread_wakeup: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADSCHED.PThreadWakeup).
    Let Im_thread_spawn: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADSCHED.PThreadSpawn).
    Let Im_thread_kill: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADSCHED.PThreadKill).
    Let Im_sched_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADSCHED.PSchedInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PTHREADSCHED.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: THREADSCHEDGEN.transf_program Im_thread_wakeup Im_thread_spawn Im_thread_kill Im_thread_sched Im_sched_init impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PCURID.primOp) := source_program_only source_implem prog.
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

    (** kctxt_new *)

    Let bkctxt_new: block := Genv.genv_next ge + Z.of_nat 0.

    Let hkctxt_new1 : Genv.find_symbol sge kctxt_new = Some bkctxt_new. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ kctxt_new).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hkctxt_new2 : Genv.find_funct sge (Vptr bkctxt_new Int.zero) = Some (Clight.External (PCURID.PKCtxtNew) (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ kctxt_new _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hkctxt_new3 : Clight.type_of_global sge bkctxt_new = Some (Ctypes.Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bkctxt_new).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bkctxt_new. unfold Asm.fundef. omega.
      intros.
      simpl in hkctxt_new2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hkctxt_new2. reflexivity.
    Qed.   

    (** set_state *)

    Let bset_state: block := Genv.genv_next ge + Z.of_nat 1.

    Let hset_state1 : Genv.find_symbol sge set_state = Some bset_state. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_state).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_state2 : Genv.find_funct sge (Vptr bset_state Int.zero) = Some (Clight.External (PCURID.PSetState) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_state _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_state3 : Clight.type_of_global sge bset_state = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_state).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_state. unfold Asm.fundef. omega.
      intros.
      simpl in hset_state2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_state2. reflexivity.
    Qed.   

    (** enqueue *)

    Let benqueue: block := Genv.genv_next ge + Z.of_nat 2.

    Let henqueue1 : Genv.find_symbol sge enqueue = Some benqueue. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ enqueue).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let henqueue2 : Genv.find_funct sge (Vptr benqueue Int.zero) = Some (Clight.External (PCURID.PEnQueue) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ enqueue _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let henqueue3 : Clight.type_of_global sge benqueue = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge benqueue).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold benqueue. unfold Asm.fundef. omega.
      intros.
      simpl in henqueue2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite henqueue2. reflexivity.
    Qed.   

    (** dequeue *)

    Let bdequeue: block := Genv.genv_next ge + Z.of_nat 3.

    Let hdequeue1 : Genv.find_symbol sge dequeue = Some bdequeue. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ dequeue).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hdequeue2 : Genv.find_funct sge (Vptr bdequeue Int.zero) = Some (Clight.External (PCURID.PDeQueue) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ dequeue _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hdequeue3 : Clight.type_of_global sge bdequeue = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bdequeue).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bdequeue. unfold Asm.fundef. omega.
      intros.
      simpl in hdequeue2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hdequeue2. reflexivity.
    Qed. 

    (** queue_rmv *)

    Let bqueue_rmv: block := Genv.genv_next ge + Z.of_nat 4.

    Let hqueue_rmv1 : Genv.find_symbol sge queue_rmv = Some bqueue_rmv. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ queue_rmv).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hqueue_rmv2 : Genv.find_funct sge (Vptr bqueue_rmv Int.zero) = Some (Clight.External (PCURID.PQueueRmv) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ queue_rmv _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hqueue_rmv3 : Clight.type_of_global sge bqueue_rmv = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bqueue_rmv).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bqueue_rmv. unfold Asm.fundef. omega.
      intros.
      simpl in hqueue_rmv2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hqueue_rmv2. reflexivity.
    Qed.   

    (** tdqueue_init *)

    Let btdqueue_init: block := Genv.genv_next ge + Z.of_nat 5.

    Let htdqueue_init1 : Genv.find_symbol sge tdqueue_init = Some btdqueue_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ tdqueue_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let htdqueue_init2 : Genv.find_funct sge (Vptr btdqueue_init Int.zero) = Some (Clight.External (PCURID.PTDQueueInit) (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ tdqueue_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let htdqueue_init3 : Clight.type_of_global sge btdqueue_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge btdqueue_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold btdqueue_init. unfold Asm.fundef. omega.
      intros.
      simpl in htdqueue_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite htdqueue_init2. reflexivity.
    Qed. 

    (** set_curid *)

    Let bset_curid: block := Genv.genv_next ge + Z.of_nat 6.

    Let hset_curid1 : Genv.find_symbol sge set_curid = Some bset_curid. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_curid).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hset_curid2 : Genv.find_funct sge (Vptr bset_curid Int.zero) = Some (Clight.External (PCURID.PSetCurID) (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_curid _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hset_curid3 : Clight.type_of_global sge bset_curid = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_curid).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_curid. unfold Asm.fundef. omega.
      intros.
      simpl in hset_curid2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_curid2. reflexivity.
    Qed. 

    (** thread_free *)

    Let bthread_free: block := Genv.genv_next ge + Z.of_nat 7.

    Let hthread_free1 : Genv.find_symbol sge thread_free = Some bthread_free. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ thread_free).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hthread_free2 : Genv.find_funct sge (Vptr bthread_free Int.zero) = Some (Clight.External (PCURID.PThreadFree) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ thread_free _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 10.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hthread_free3 : Clight.type_of_global sge bthread_free = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bthread_free).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bthread_free. unfold Asm.fundef. omega.
      intros.
      simpl in hthread_free2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hthread_free2. reflexivity.
    Qed. 

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Local Instance HdataOp:AbstractDataOps HDATA:= (PTHREADSCHED.abstract_data (Hnpc:= Hnpc)).
      Local Instance LdataOp:AbstractDataOps LDATA:= (PCURID.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PTHREADSCHED.primOp mem__H :=
        PTHREADSCHED.layer_def(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                              (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                              (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                              (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PCURID.primOp mem__L :=
        PCURID.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                         (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                         (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                         (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                         (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).    

      Notation HLoad := (PTHREADSCHED.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PTHREADSCHED.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PCURID.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PCURID.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PCURID.step 
                           (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)).

      Notation LADT := PCURID.ADT.

      Let thread_kill_spec:
        forall r' n b m0 labd' sig i,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_thread_kill)
          -> Genv.find_funct_ptr ge b = Some (External PTHREADSCHED.PThreadKill)
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> extcall_arguments r' m0 sig (Vint n:: Vint i::nil)
          -> PCURID.thread_kill (Hnchan:= Hnchan)
                                (Mem.get_abstract_data m0) (Int.unsigned n) (Int.unsigned i) 
                                (real_free_pt (PCURID.ptpool (LADT (Mem.get_abstract_data m0))) n) = Some labd'
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
                     PTHREADSCHED.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PCURID.primitive_call)
                     (is_primitive_call := PCURID.is_primitive_call)
                     (kernel_mode := PCURID.kernel_mode)
                  ).
          apply PCURID.exec_load_exec_loadex.
          apply PCURID.exec_store_exec_storeex.
          apply PCURID.extcall_not_primitive.
          apply PCURID.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PCURIDCODE.thread_kill_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PCURID.kernel_mode.
          apply PCURID.thread_kill_eq in H4.
          functional inversion H4; unfold adt in *; destruct (PCURID.INV (Mem.get_abstract_data m0)); auto.

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

      Let thread_spawn_spec:
        forall r' n b m0 labd' sig b' ofs b0 ofs',
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_thread_spawn)
          -> Genv.find_funct_ptr ge b = Some (External PTHREADSCHED.PThreadSpawn)
          -> PCURID.thread_spawn 
               (Hnchan:= Hnchan) (Mem.get_abstract_data m0) b0 ofs b' ofs' = Some (labd', Int.unsigned n)
          -> Genv.find_symbol tge STACK_LOC = Some b0 
          -> Genv.find_symbol ge STACK_LOC = Some b0 
          -> Int.unsigned ofs = (Int.unsigned n + 1) * PgSize - 4 
          -> (exists fun_id, Genv.find_symbol tge fun_id = Some b') 
          -> (exists fun_id, Genv.find_symbol ge fun_id = Some b') 
          -> sig = mksignature (Tint::nil) (Some Tint)
          -> extcall_arguments r' m0 sig (Vptr b' ofs'::nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ r_ # (loc_external_result sig) = (Vint n)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PTHREADSCHED.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PCURID.primitive_call)
                     (is_primitive_call := PCURID.is_primitive_call)
                     (kernel_mode := PCURID.kernel_mode)
                  ).
          apply PCURID.exec_load_exec_loadex.
          apply PCURID.exec_store_exec_storeex.
          apply PCURID.extcall_not_primitive.
          apply PCURID.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PCURIDCODE.thread_spawn_correct; eauto.

          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          apply NEW_INJ in H15.
          simpl in H15.
          destruct H16; subst.
          destruct H15.
          left; reflexivity.
          destruct H16; subst.
          destruct H15.
          right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; right; right; right; left; reflexivity.
          contradiction.
          eassumption.
          destruct H7.
          esplit.
          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          apply NEW_INJ in H15.
          simpl in H15.
          destruct H16; subst.
          destruct H15.
          left; reflexivity.
          destruct H16; subst.
          destruct H15.
          right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; right; right; left; reflexivity.
          destruct H8; subst.
          destruct H15.
          right; right; right; right; right; right; right; right; right; left; reflexivity.
          contradiction.
          eassumption.

          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PCURID.kernel_mode.
          apply PCURID.thread_spawn_eq in H2.
          unfold PCURID.thread_spawn_aux in H2.
          destruct (PCURID.INV (Mem.get_abstract_data m0)).
          destruct (PCURID.pe (LADT (Mem.get_abstract_data m0))); try discriminate H2.
          destruct (PCURID.ipt (LADT (Mem.get_abstract_data m0))); try discriminate H2.
          destruct (PCURID.ihost (LADT (Mem.get_abstract_data m0))); try discriminate H2.
          auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
          inversion H15.
          rewrite Int.repr_unsigned in *.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace labd' with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

      Let thread_wakeup_spec:
        forall r' n b m0 labd' sig,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_thread_wakeup)
          -> Genv.find_funct_ptr ge b = Some (External PTHREADSCHED.PThreadWakeup)
          -> PCURID.thread_wakeup 
               (Hnchan:= Hnchan) (Mem.get_abstract_data m0) (Int.unsigned n) = Some labd'
          -> sig = mksignature (Tint::nil) None
          -> extcall_arguments r' m0 sig (Vint n :: nil)
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
                     PTHREADSCHED.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PCURID.primitive_call)
                     (is_primitive_call := PCURID.is_primitive_call)
                     (kernel_mode := PCURID.kernel_mode)
                  ).
          apply PCURID.exec_load_exec_loadex.
          apply PCURID.exec_store_exec_storeex.
          apply PCURID.extcall_not_primitive.
          apply PCURID.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PCURIDCODE.thread_wakeup_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PCURID.kernel_mode.
          apply PCURID.thread_wakeup_eq in H2.
          unfold PCURID.thread_wakeup_aux in H2.
          destruct (PCURID.INV (Mem.get_abstract_data m0)).
          destruct (PCURID.pe (LADT (Mem.get_abstract_data m0))); try discriminate H2.
          destruct (PCURID.ipt (LADT (Mem.get_abstract_data m0))); try discriminate H2.
          destruct (PCURID.ihost (LADT (Mem.get_abstract_data m0))); try discriminate H2.
          auto.
          destruct (PCURID.ipt (LADT (Mem.get_abstract_data m0))); discriminate H2.

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

      Let sched_init_spec:
        forall r' b m0 labd' sig mbi_adr,
          let labd := (Mem.get_abstract_data m0) in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_sched_init)
          -> Genv.find_funct_ptr ge b = Some (External PTHREADSCHED.PSchedInit)
          -> sig = mksignature (Tint :: nil) None
          -> extcall_arguments r' m0 sig (Vint mbi_adr:: nil)
          -> PCURID.sched_init (Hnchan:= Hnchan)(Hnpc:= Hnpc) (Mem.get_abstract_data m0) real_nps 
                               (real_AT (PCURID.AT (LADT labd)))
                               (real_ptp (PCURID.ptpool (LADT labd)))
                               (real_pt (PCURID.ptpool (LADT labd)))
                               (real_ptb (PCURID.pb (LADT labd)))
                               (real_abtcb (PCURID.abtcb (LADT labd)))
                               (real_abq (PCURID.abq (LADT labd)))
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
                     PTHREADSCHED.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PCURID.primitive_call)
                     (is_primitive_call := PCURID.is_primitive_call)
                     (kernel_mode := PCURID.kernel_mode)
                  ).
          apply PCURID.exec_load_exec_loadex.
          apply PCURID.exec_store_exec_storeex.
          apply PCURID.extcall_not_primitive.
          apply PCURID.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PCURIDCODE.sched_init_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PCURID.kernel_mode.
          apply PCURID.sched_init_eq in H4.
          functional inversion H4.
          unfold adt in *.
          destruct (PCURID.INV (Mem.get_abstract_data m0)).
          auto.

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

      Let AndImplies: forall A B: Prop, (A /\ (A -> B)) -> (A /\ B).
      Proof.
        intros.
        destruct H.
        split.
        assumption.
        apply H0; assumption.
      Qed.

      Let hdequeue_tge: exists b_dequeue, Genv.find_symbol tge dequeue = Some b_dequeue
                                             /\ Genv.find_funct_ptr tge b_dequeue = Some (External PCURID.PDeQueue).
      Proof.
        exists bdequeue.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ dequeue).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ dequeue _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 9.
        2: assumption.
        fold tprog tge.
        rewrite transf_clight_fundef_external.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        congruence.
        reflexivity.
        reflexivity.
      Qed.

      Let bget_curid_1: block := Genv.genv_next ge + Z.of_nat 8.
      Let hget_curid_1_tge: exists b_get_cid, Genv.find_symbol tge get_curid_1 = Some b_get_cid
                                             /\ Genv.find_funct_ptr tge b_get_cid = Some (External PCURID.PGetCurID).
      Proof.
        exists bget_curid_1.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ get_curid_1).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_curid_1 _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 10.
        2: assumption.
        fold tprog tge.
        rewrite transf_clight_fundef_external.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        congruence.
        reflexivity.
        reflexivity.
      Qed.

      Let bkctxt_switch: block := Genv.genv_next ge + Z.of_nat 9.
      Let hkctxt_switch_tge: exists b_kctxt_switch, 
                                  Genv.find_symbol tge kctxt_switch = Some b_kctxt_switch
                                  /\ Genv.find_funct_ptr tge b_kctxt_switch = Some (External PCURID.PKCtxtSwitch).
      Proof.
        exists bkctxt_switch.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ kctxt_switch).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ kctxt_switch _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 11.
        2: assumption.
        fold tprog tge.
        rewrite transf_clight_fundef_external.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        congruence.
        reflexivity.
        reflexivity.
      Qed.

      Let hset_curid_tge: exists b_set_cid, Genv.find_symbol tge set_curid = Some b_set_cid
                                             /\ Genv.find_funct_ptr tge b_set_cid = Some (External PCURID.PSetCurID).
      Proof.
        exists bset_curid.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ set_curid).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_curid _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 11.
        2: assumption.
        fold tprog tge.
        rewrite transf_clight_fundef_external.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        congruence.
        reflexivity.
        reflexivity.
      Qed.

      Let Hset_state: exists b_set_state, Genv.find_symbol tge set_state = Some b_set_state
                                                 /\ Genv.find_funct_ptr tge b_set_state = Some (External PCURID.PSetState).
      Proof.
        exists bset_state.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ set_state).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_state _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 11.
        2: assumption.
        fold tprog tge.
        rewrite transf_clight_fundef_external.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        congruence.
        reflexivity.
        reflexivity.
      Qed.

      Let threadsched_spec:
        forall r' b m0 labd' r'0 r'',
          let labd := (Mem.get_abstract_data m0) in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_thread_sched)
          -> PCURID.thread_sched (Hnchan:= Hnchan) labd 
                                 ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                        # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                        (r' EBP) # RA <- (r' RA)) = Some (labd', r'0)
          -> asm_invariant tge (State r' m0)
          -> PCURID.low_level_invariant (Mem.nextblock m0) labd
          -> r'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: IR EDX :: IR ECX :: IR EAX :: RA :: nil) 
                               (undef_regs (List.map preg_of temporary_regs)
                                           (undef_regs (List.map preg_of destroyed_at_call_regs) r')))
          -> exists f' m0' r_, 
               plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'              
               /\ (forall l,
                     Val.lessdef (Pregmap.get l (r''#ESP<- (r'0#ESP)#EDI <- (r'0#EDI)#ESI <- (r'0#ESI)#EBX <- (r'0#EBX)
                                                    #EBP <- (r'0#EBP)#PC <- (r'0#RA)))
                                 (Pregmap.get l r_)).
      Proof.
        apply THREADSCHEDGEN_ASM.threadsched_spec; trivial.
      Qed.

    Theorem transf_program_correct:
       Smallstep.backward_simulation 
          (PTHREADSCHED.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                                  (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                                  (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                                  (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                                  (real_abq:= real_abq) (Hnchan:= Hnchan) prog) 
          (PCURID.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                            (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                            (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                            (Hnchan:= Hnchan) (real_abq:= real_abq) tprog). 
    Proof.
      eapply THREADSCHEDGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End THREADSCHEDGENIMPL.
