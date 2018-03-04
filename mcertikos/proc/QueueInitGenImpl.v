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
Require Import PQueueInit.
Require Import PQueueIntro.
Require Export QueueInitGen.
Require Import PQueueIntroCode.
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

Module QUEUEINITGENIMPL.
  Export QueueInitGen.QUEUEINITGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PQUEUEINIT.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PQUEUEINIT.PAlloc)...
    destruct (Q_dec PQUEUEINIT.PFree)...
    destruct (Q_dec PQUEUEINIT.PSetPT)...
    destruct (Q_dec PQUEUEINIT.PPTRead)...
    destruct (Q_dec PQUEUEINIT.PPTResv)...
    destruct (Q_dec PQUEUEINIT.PKCtxtNew)...
    destruct (Q_dec PQUEUEINIT.PThreadFree)...
    destruct (Q_dec PQUEUEINIT.PKCtxtSwitch)...
    destruct (Q_dec PQUEUEINIT.PGetState)...
    destruct (Q_dec PQUEUEINIT.PSetState)...
    destruct (Q_dec PQUEUEINIT.PDeQueue)...
    destruct (Q_dec PQUEUEINIT.PEnQueue)...
    destruct (Q_dec PQUEUEINIT.PQueueRmv)...
    destruct (Q_dec PQUEUEINIT.PPTIn)...
    destruct (Q_dec PQUEUEINIT.PPTOut)...
    destruct (Q_dec PQUEUEINIT.PTrapIn)...
    destruct (Q_dec PQUEUEINIT.PTrapOut)...
    destruct (Q_dec PQUEUEINIT.PHostIn)...
    destruct (Q_dec PQUEUEINIT.PHostOut)...
    destruct (Q_dec PQUEUEINIT.PTrapGet)...
    destruct (Q_dec PQUEUEINIT.PTrapRet)...
    destruct (Q_dec PQUEUEINIT.PTDQueueInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PQUEUEINIT.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low)
                                         (num_chan:= num_chan) (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA :=(PQUEUEINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                         (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (Asm.fundef (external_function:= PQUEUEINIT.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PQUEUEINTRO.primOp)).

    Notation funkind := (funkind (low:= PQUEUEINTRO.primOp) Asm.code (Clight.fundef (external_function := PQUEUEINTRO.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: PQUEUEINIT.primOp): funkind :=
      match p with
        | PQUEUEINIT.PAlloc => Code _ (AST.External PQUEUEINTRO.PAlloc)
        | PQUEUEINIT.PFree => Code _ (AST.External PQUEUEINTRO.PFree)
        | PQUEUEINIT.PSetPT => Code _ (AST.External PQUEUEINTRO.PSetPT)
        | PQUEUEINIT.PPTRead => Code _ (AST.External PQUEUEINTRO.PPTRead)
        | PQUEUEINIT.PPTResv => Code _ (AST.External PQUEUEINTRO.PPTResv)
        | PQUEUEINIT.PKCtxtNew => Code _ (AST.External PQUEUEINTRO.PKCtxtNew)
        | PQUEUEINIT.PThreadFree => Code _ (AST.External PQUEUEINTRO.PThreadFree)
        | PQUEUEINIT.PKCtxtSwitch => Code _ (AST.External PQUEUEINTRO.PKCtxtSwitch)
        | PQUEUEINIT.PGetState => Code _ (AST.External PQUEUEINTRO.PGetState)
        | PQUEUEINIT.PSetState => Code _ (AST.External PQUEUEINTRO.PSetState)
        | PQUEUEINIT.PEnQueue => SourceFun (Clight.Internal PQUEUEINTROCODE.f_enqueue) (AST.Internal nil)
        | PQUEUEINIT.PDeQueue => SourceFun (Clight.Internal PQUEUEINTROCODE.f_dequeue) (AST.Internal nil)
        | PQUEUEINIT.PQueueRmv => SourceFun (Clight.Internal PQUEUEINTROCODE.f_queue_rmv) (AST.Internal nil)
        | PQUEUEINIT.PPTIn => Code _ (AST.External PQUEUEINTRO.PPTIn)
        | PQUEUEINIT.PPTOut => Code _ (AST.External PQUEUEINTRO.PPTOut)
        | PQUEUEINIT.PTrapIn => Code _ (AST.External PQUEUEINTRO.PTrapIn)
        | PQUEUEINIT.PTrapOut => Code _ (AST.External PQUEUEINTRO.PTrapOut)
        | PQUEUEINIT.PHostIn => Code _ (AST.External PQUEUEINTRO.PHostIn)
        | PQUEUEINIT.PHostOut => Code _ (AST.External PQUEUEINTRO.PHostOut)
        | PQUEUEINIT.PTrapGet => Code _ (AST.External PQUEUEINTRO.PTrapGet)
        | PQUEUEINIT.PTrapRet => Code _ (AST.External PQUEUEINTRO.PTrapRet)
        | PQUEUEINIT.PTDQueueInit => SourceFun (Clight.Internal PQUEUEINTROCODE.f_tdqueue_init) (AST.Internal nil)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (set_prev, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PSetPrev) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (set_next, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PSetNext) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (get_head, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PGetHead) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (get_tail, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PGetTail) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (get_prev, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PGetPrev) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (get_next, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PGetNext) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (set_head, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PSetHead) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (set_tail, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PSetTail) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (tdq_init, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PTDQInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: (thread_init, Some (Gfun (SourceFun (Clight.External (PQUEUEINTRO.PThreadInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PQUEUEINIT.primOp (low := PQUEUEINTRO.primOp) (Clight.fundef (external_function := PQUEUEINTRO.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PQUEUEINIT.primOp (low := PQUEUEINTRO.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PQUEUEINIT.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PQUEUEINTRO.primOp)).

    Let Im_enqueue: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINIT.PEnQueue).
    Let Im_dequeue: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINIT.PDeQueue).
    Let Im_queue_rmv: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINIT.PQueueRmv).
    Let Im_tdqueue_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINIT.PTDQueueInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PQUEUEINIT.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: QUEUEINITGEN.transf_program Im_enqueue Im_dequeue Im_queue_rmv Im_tdqueue_init impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PQUEUEINTRO.primOp) := source_program_only source_implem prog.
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

    (** set_prev *)

    Let bset_prev: block := Genv.genv_next ge + Z.of_nat 0.

    Let hset_prev1 : Genv.find_symbol sge set_prev = Some bset_prev. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_prev).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_prev2 : Genv.find_funct sge (Vptr bset_prev Int.zero) = Some (Clight.External (PQUEUEINTRO.PSetPrev) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_prev _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_prev3 : Clight.type_of_global sge bset_prev = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_prev).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_prev. unfold Asm.fundef. omega.
      intros.
      simpl in hset_prev2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_prev2. reflexivity.
    Qed.   

    (** set_next *)

    Let bset_next: block := Genv.genv_next ge + Z.of_nat 1.

    Let hset_next1 : Genv.find_symbol sge set_next = Some bset_next. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_next).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_next2 : Genv.find_funct sge (Vptr bset_next Int.zero) = Some (Clight.External (PQUEUEINTRO.PSetNext) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_next _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_next3 : Clight.type_of_global sge bset_next = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_next).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_next. unfold Asm.fundef. omega.
      intros.
      simpl in hset_next2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_next2. reflexivity.
    Qed.   

    (** get_head *)

    Let bget_head: block := Genv.genv_next ge + Z.of_nat 2.

    Let hget_head1 : Genv.find_symbol sge get_head = Some bget_head. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_head).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hget_head2 : Genv.find_funct sge (Vptr bget_head Int.zero) = Some (Clight.External (PQUEUEINTRO.PGetHead) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_head _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hget_head3 : Clight.type_of_global sge bget_head = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_head).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_head. unfold Asm.fundef. omega.
      intros.
      simpl in hget_head2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_head2. reflexivity.
    Qed. 

    (** get_tail *)

    Let bget_tail: block := Genv.genv_next ge + Z.of_nat 3.

    Let hget_tail1 : Genv.find_symbol sge get_tail = Some bget_tail. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_tail).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hget_tail2 : Genv.find_funct sge (Vptr bget_tail Int.zero) = Some (Clight.External (PQUEUEINTRO.PGetTail) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_tail _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hget_tail3 : Clight.type_of_global sge bget_tail = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_tail).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_tail. unfold Asm.fundef. omega.
      intros.
      simpl in hget_tail2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_tail2. reflexivity.
    Qed. 

    (** get_prev *)

    Let bget_prev: block := Genv.genv_next ge + Z.of_nat 4.

    Let hget_prev1 : Genv.find_symbol sge get_prev = Some bget_prev. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_prev).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hget_prev2 : Genv.find_funct sge (Vptr bget_prev Int.zero) = Some (Clight.External (PQUEUEINTRO.PGetPrev) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_prev _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hget_prev3 : Clight.type_of_global sge bget_prev = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_prev).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_prev. unfold Asm.fundef. omega.
      intros.
      simpl in hget_prev2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_prev2. reflexivity.
    Qed. 

    (** get_next *)

    Let bget_next: block := Genv.genv_next ge + Z.of_nat 5.

    Let hget_next1 : Genv.find_symbol sge get_next = Some bget_next. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_next).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hget_next2 : Genv.find_funct sge (Vptr bget_next Int.zero) = Some (Clight.External (PQUEUEINTRO.PGetNext) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_next _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hget_next3 : Clight.type_of_global sge bget_next = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_next).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_next. unfold Asm.fundef. omega.
      intros.
      simpl in hget_next2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_next2. reflexivity.
    Qed. 

    (** set_head *)

    Let bset_head: block := Genv.genv_next ge + Z.of_nat 6.

    Let hset_head1 : Genv.find_symbol sge set_head = Some bset_head. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_head).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_head2 : Genv.find_funct sge (Vptr bset_head Int.zero) = Some (Clight.External (PQUEUEINTRO.PSetHead) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_head _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_head3 : Clight.type_of_global sge bset_head = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_head).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_head. unfold Asm.fundef. omega.
      intros.
      simpl in hset_head2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_head2. reflexivity.
    Qed.

    (** set_tail *)

    Let bset_tail: block := Genv.genv_next ge + Z.of_nat 7.

    Let hset_tail1 : Genv.find_symbol sge set_tail = Some bset_tail. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_tail).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_tail2 : Genv.find_funct sge (Vptr bset_tail Int.zero) = Some (Clight.External (PQUEUEINTRO.PSetTail) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_tail _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 9.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_tail3 : Clight.type_of_global sge bset_tail = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_tail).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_tail. unfold Asm.fundef. omega.
      intros.
      simpl in hset_tail2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_tail2. reflexivity.
    Qed.      

    (** tdq_init *)

    Let btdq_init: block := Genv.genv_next ge + Z.of_nat 8.

    Let htdq_init1 : Genv.find_symbol sge tdq_init = Some btdq_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ tdq_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let htdq_init2 : Genv.find_funct sge (Vptr btdq_init Int.zero) = Some (Clight.External (PQUEUEINTRO.PTDQInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ tdq_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 10.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let htdq_init3 : Clight.type_of_global sge btdq_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge btdq_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold btdq_init. unfold Asm.fundef. omega.
      intros.
      simpl in htdq_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite htdq_init2. reflexivity.
    Qed. 

    (** thread_init *)

    Let bthread_init: block := Genv.genv_next ge + Z.of_nat 9.

    Let hthread_init1 : Genv.find_symbol sge thread_init = Some bthread_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ thread_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hthread_init2 : Genv.find_funct sge (Vptr bthread_init Int.zero) = Some (Clight.External (PQUEUEINTRO.PThreadInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ thread_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 12.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hthread_init3 : Clight.type_of_global sge bthread_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bthread_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bthread_init. unfold Asm.fundef. omega.
      intros.
      simpl in hthread_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hthread_init2. reflexivity.
    Qed. 

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PQUEUEINIT.primOp mem__H :=
        PQUEUEINIT.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_tcb:= real_tcb)
                             (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                             (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                             (num_chan := num_chan) (real_tdq:= real_tdq).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PQUEUEINTRO.primOp mem__L :=
        PQUEUEINTRO.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (num_chan := num_chan) (real_tcb:= real_tcb)
                              (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                              (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb).    

      Notation HLoad := (PQUEUEINIT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PQUEUEINIT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PQUEUEINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PQUEUEINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PQUEUEINTRO.step 
                           (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_tcb:= real_tcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan)).

      Notation LADT := PQUEUEINTRO.ADT.

      Let enqueue_spec:
        forall r' n b m0 labd' sig i,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_enqueue)
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> PQUEUEINTRO.enqueue (num_chan:= num_chan) (Hnpc:= Hnpc)
                                 (Mem.get_abstract_data m0) (Int.unsigned n) (Int.unsigned i) = Some labd'
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINIT.PEnQueue)
          -> asm_invariant tge (State r' m0)
          -> extcall_arguments r' m0 sig (Vint n :: Vint i :: nil)
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
                     PQUEUEINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PQUEUEINTRO.primitive_call)
                     (is_primitive_call := PQUEUEINTRO.is_primitive_call)
                     (kernel_mode := PQUEUEINTRO.kernel_mode)
                  ).
          apply PQUEUEINTRO.exec_load_exec_loadex.
          apply PQUEUEINTRO.exec_store_exec_storeex.
          apply PQUEUEINTRO.extcall_not_primitive.
          apply PQUEUEINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PQUEUEINTROCODE.enqueue_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PQUEUEINTRO.kernel_mode.
          apply PQUEUEINTRO.enqueue_eq in H2.
          functional inversion H2; unfold adt in *; destruct (PQUEUEINTRO.INV (Mem.get_abstract_data m0)); auto.

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

      Let dequeue_spec:
        forall r' n b m0 labd' sig i,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_dequeue)
          -> sig = mksignature (Tint :: nil) (Some Tint)
          -> PQUEUEINTRO.dequeue (num_chan:= num_chan) (Hnpc:= Hnpc)
                                 (Mem.get_abstract_data m0) (Int.unsigned n) = Some (labd', (Int.unsigned i))
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINIT.PDeQueue)
          -> asm_invariant tge (State r' m0)
          -> extcall_arguments r' m0 sig (Vint n :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ r_ # (loc_external_result sig) = (Vint i)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PQUEUEINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PQUEUEINTRO.primitive_call)
                     (is_primitive_call := PQUEUEINTRO.is_primitive_call)
                     (kernel_mode := PQUEUEINTRO.kernel_mode)
                  ).
          apply PQUEUEINTRO.exec_load_exec_loadex.
          apply PQUEUEINTRO.exec_store_exec_storeex.
          apply PQUEUEINTRO.extcall_not_primitive.
          apply PQUEUEINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PQUEUEINTROCODE.dequeue_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PQUEUEINTRO.kernel_mode.
          apply PQUEUEINTRO.dequeue_eq in H2.
          functional inversion H2; unfold adt in *; destruct (PQUEUEINTRO.INV (Mem.get_abstract_data m0)); auto.

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

      Let queue_rmv_spec:
        forall r' n b m0 labd' sig i,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_queue_rmv)
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> PQUEUEINTRO.queue_rmv (num_chan:= num_chan) (Hnpc:= Hnpc)
                                   (Mem.get_abstract_data m0) (Int.unsigned n) (Int.unsigned i) = Some labd'
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINIT.PQueueRmv)
          -> asm_invariant tge (State r' m0)
          -> extcall_arguments r' m0 sig (Vint n :: Vint i ::nil)
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
                     PQUEUEINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PQUEUEINTRO.primitive_call)
                     (is_primitive_call := PQUEUEINTRO.is_primitive_call)
                     (kernel_mode := PQUEUEINTRO.kernel_mode)
                  ).
          apply PQUEUEINTRO.exec_load_exec_loadex.
          apply PQUEUEINTRO.exec_store_exec_storeex.
          apply PQUEUEINTRO.extcall_not_primitive.
          apply PQUEUEINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PQUEUEINTROCODE.queue_rmv_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PQUEUEINTRO.kernel_mode.
          apply PQUEUEINTRO.queue_rmv_eq in H2.
          functional inversion H2; unfold adt in *; destruct (PQUEUEINTRO.INV (Mem.get_abstract_data m0)); auto.

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

      Let tdqueue_init_spec:
        forall r' b m0 labd' sig mbi_adr,
          let labd := (Mem.get_abstract_data m0) in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_tdqueue_init)
          -> sig = mksignature (Tint :: nil) None
          -> PQUEUEINTRO.tdqueue_init (num_chan:= num_chan) (Hnpc:= Hnpc) (Mem.get_abstract_data m0) real_nps 
                                      (real_AT (PQUEUEINTRO.AT (LADT labd)))
                                      (real_ptp (PQUEUEINTRO.ptpool (LADT labd)))
                                      (real_pt (PQUEUEINTRO.ptpool (LADT labd)))
                                      (real_ptb (PQUEUEINTRO.pb (LADT labd)))
                                      (real_tcb (PQUEUEINTRO.tcb (LADT labd)))
                                      (real_tdq (PQUEUEINTRO.tdq (LADT labd)))
                                      (Int.unsigned mbi_adr) = Some labd'
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINIT.PTDQueueInit)
          -> asm_invariant tge (State r' m0)
          -> extcall_arguments r' m0 sig (Vint mbi_adr :: nil)
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
                     PQUEUEINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PQUEUEINTRO.primitive_call)
                     (is_primitive_call := PQUEUEINTRO.is_primitive_call)
                     (kernel_mode := PQUEUEINTRO.kernel_mode)
                  ).
          apply PQUEUEINTRO.exec_load_exec_loadex.
          apply PQUEUEINTRO.exec_store_exec_storeex.
          apply PQUEUEINTRO.extcall_not_primitive.
          apply PQUEUEINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PQUEUEINTROCODE.tdqueue_init_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PQUEUEINTRO.kernel_mode.
          apply PQUEUEINTRO.tdqueue_init_eq in H2.
          functional inversion H2.
          functional inversion H10.
          unfold adt0 in *.
          destruct (PQUEUEINTRO.INV (Mem.get_abstract_data m0)).
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

    Theorem transf_program_correct:
       Smallstep.backward_simulation 
          (PQUEUEINIT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                                (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                                (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_tcb:= real_tcb)
                                (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                                (real_tdq:= real_tdq) prog) 
          (PQUEUEINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                                 (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                                 (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_tcb:= real_tcb)
                                 (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) tprog). 
    Proof.
      eapply QUEUEINITGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End QUEUEINITGENIMPL.
