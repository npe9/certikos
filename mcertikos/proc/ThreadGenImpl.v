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
Require Import PThread.
Require Import PThreadSched.
Require Export ThreadGen.
Require Import ThreadGenAsm.
Require Import ThreadGenAsm1.
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
Require Import Conventions1.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module THREADGENIMPL.
  Export ThreadGen.THREADGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PTHREAD.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PTHREAD.PAlloc)...
    destruct (Q_dec PTHREAD.PFree)...
    destruct (Q_dec PTHREAD.PSetPT)...
    destruct (Q_dec PTHREAD.PPTRead)...
    destruct (Q_dec PTHREAD.PPTResv)...
    destruct (Q_dec PTHREAD.PThreadSpawn)...
    destruct (Q_dec PTHREAD.PThreadKill)...
    destruct (Q_dec PTHREAD.PThreadWakeup)...
    destruct (Q_dec PTHREAD.PThreadYield)...
    destruct (Q_dec PTHREAD.PThreadSleep)...
    destruct (Q_dec PTHREAD.PGetCurID)...
    destruct (Q_dec PTHREAD.PPTIn)...
    destruct (Q_dec PTHREAD.PPTOut)...
    destruct (Q_dec PTHREAD.PTrapIn)...
    destruct (Q_dec PTHREAD.PTrapOut)...
    destruct (Q_dec PTHREAD.PHostIn)...
    destruct (Q_dec PTHREAD.PHostOut)...
    destruct (Q_dec PTHREAD.PTrapGet)...
    destruct (Q_dec PTHREAD.PTrapRet)...
    destruct (Q_dec PTHREAD.PSchedInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PTHREAD.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                      (num_chan:= num_chan) (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA :=(PTHREADSCHED.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                          (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (Asm.fundef (external_function:= PTHREAD.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PTHREADSCHED.primOp)).

    Notation funkind := (funkind (low:= PTHREADSCHED.primOp) Asm.code (Clight.fundef (external_function := PTHREADSCHED.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: PTHREAD.primOp): funkind :=
      match p with
        | PTHREAD.PAlloc => Code _ (AST.External PTHREADSCHED.PAlloc)
        | PTHREAD.PFree => Code _ (AST.External PTHREADSCHED.PFree)
        | PTHREAD.PSetPT => Code _ (AST.External PTHREADSCHED.PSetPT)
        | PTHREAD.PPTRead => Code _ (AST.External PTHREADSCHED.PPTRead)
        | PTHREAD.PPTResv => Code _ (AST.External PTHREADSCHED.PPTResv)
        | PTHREAD.PThreadSpawn => Code _ (AST.External PTHREADSCHED.PThreadSpawn)
        | PTHREAD.PThreadKill => Code _ (AST.External PTHREADSCHED.PThreadKill)
        | PTHREAD.PThreadWakeup => Code _ (AST.External PTHREADSCHED.PThreadWakeup)
        | PTHREAD.PThreadYield => Code _ THREADGEN_ASM.Im_thread_yield
        | PTHREAD.PThreadSleep => Code _ THREADGEN1_ASM.Im_thread_sleep
        | PTHREAD.PGetCurID => Code _ (AST.External PTHREADSCHED.PGetCurID)
        | PTHREAD.PPTIn => Code _ (AST.External PTHREADSCHED.PPTIn)
        | PTHREAD.PPTOut => Code _ (AST.External PTHREADSCHED.PPTOut)
        | PTHREAD.PTrapIn => Code _ (AST.External PTHREADSCHED.PTrapIn)
        | PTHREAD.PTrapOut => Code _ (AST.External PTHREADSCHED.PTrapOut)
        | PTHREAD.PHostIn => Code _ (AST.External PTHREADSCHED.PHostIn)
        | PTHREAD.PHostOut => Code _ (AST.External PTHREADSCHED.PHostOut)
        | PTHREAD.PTrapGet => Code _ (AST.External PTHREADSCHED.PTrapGet)
        | PTHREAD.PTrapRet => Code _ (AST.External PTHREADSCHED.PTrapRet)
        | PTHREAD.PSchedInit => Code _ (AST.External PTHREADSCHED.PSchedInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (thread_sched, Some (Gfun (SourceFun (Clight.External (PTHREADSCHED.PThreadSched) (Ctypes.Tnil) tvoid) dummy)))
        :: (get_curid3, Some (Gfun (SourceFun (Clight.External (PTHREADSCHED.PGetCurID) (Ctypes.Tnil) tint) dummy)))
        :: (enqueue1, Some (Gfun (SourceFun (Clight.External (PTHREADSCHED.PEnQueue) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (set_state1, Some (Gfun (SourceFun (Clight.External (PTHREADSCHED.PSetState) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PTHREAD.primOp (low := PTHREADSCHED.primOp) (Clight.fundef (external_function := PTHREADSCHED.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PTHREAD.primOp (low := PTHREADSCHED.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PTHREAD.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PTHREADSCHED.primOp)).

    Let Im_thread_wakeup: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREAD.PThreadWakeup).
    Let Im_thread_spawn: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREAD.PThreadSpawn).
    Let Im_thread_kill: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREAD.PThreadKill).
    Let Im_sched_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREAD.PSchedInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PTHREAD.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: THREADGEN.transf_program THREADGEN1_ASM.Im_thread_sleep THREADGEN_ASM.Im_thread_yield impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PTHREADSCHED.primOp) := source_program_only source_implem prog.
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

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Local Instance HdataOp:AbstractDataOps HDATA:= (PTHREAD.abstract_data (Hnpc:= Hnpc)).
      Local Instance LdataOp:AbstractDataOps LDATA:= (PTHREADSCHED.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PTHREAD.primOp mem__H :=
        PTHREAD.layer_def(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                         (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                         (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                         (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                         (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PTHREADSCHED.primOp mem__L :=
        PTHREADSCHED.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                               (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                               (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                               (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).        

      Notation HLoad := (PTHREAD.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PTHREAD.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PTHREADSCHED.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PTHREADSCHED.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC)(PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PTHREADSCHED.step 
                           (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)).

      Notation LADT := PTHREADSCHED.ADT.

      Let AndImplies: forall A B: Prop, (A /\ (A -> B)) -> (A /\ B).
      Proof.
        intros.
        destruct H.
        split.
        assumption.
        apply H0; assumption.
      Qed.

      Let bthread_sched: block := Genv.genv_next ge + Z.of_nat 0.
      Let hthread_sched_tge: exists b_thread_sched, Genv.find_symbol tge thread_sched = Some b_thread_sched
                                             /\ Genv.find_funct_ptr tge b_thread_sched = Some (External PTHREADSCHED.PThreadSched).
      Proof.
        exists bthread_sched.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ thread_sched).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ thread_sched _ _)).
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

      Let bget_curid3: block := Genv.genv_next ge + Z.of_nat 1.
      Let hget_curid3_tge: exists b_get_curid3, Genv.find_symbol tge get_curid3 = Some b_get_curid3
                                             /\ Genv.find_funct_ptr tge b_get_curid3 = Some (External PTHREADSCHED.PGetCurID).
      Proof.
        exists bget_curid3.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ get_curid3).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_curid3 _ _)).
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

      Let benqueue1: block := Genv.genv_next ge + Z.of_nat 2.
      Let henqueue1_tge: exists b_enqueue1, Genv.find_symbol tge enqueue1 = Some b_enqueue1
                                             /\ Genv.find_funct_ptr tge b_enqueue1 = Some (External PTHREADSCHED.PEnQueue).
      Proof.
        exists benqueue1.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ enqueue1).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ enqueue1 _ _)).
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

      Let bset_state1: block := Genv.genv_next ge + Z.of_nat 3.
      Let hset_state1_tge: exists b_set_state1, Genv.find_symbol tge set_state1 = Some b_set_state1
                                             /\ Genv.find_funct_ptr tge b_set_state1 = Some (External PTHREADSCHED.PSetState).
      Proof.
        exists bset_state1.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ set_state1).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_state1 _ _)).
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

      Let threadyield_spec:
        forall r' b m0 labd' r'0 r'',
          let labd := (Mem.get_abstract_data m0) in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (THREADGEN_ASM.Im_thread_yield)
          -> PTHREADSCHED.thread_yield (Hnchan:= Hnchan) labd 
                                       ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                              # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                              (r' EBP) # RA <- (r' RA)) = Some (labd', r'0)
          -> asm_invariant tge (State r' m0)
          -> PTHREADSCHED.low_level_invariant (Mem.nextblock m0) labd
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
        eapply THREADGEN_ASM.threadyield_spec; eauto.
      Qed.

      Let threadsleep_spec:
        forall r' b m0 labd' r'0 r'' n sig,
          let labd := (Mem.get_abstract_data m0) in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (THREADGEN1_ASM.Im_thread_sleep)
          -> PTHREADSCHED.thread_sleep (Hnchan:= Hnchan) labd 
                                       ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                              # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                              (r' EBP) # RA <- (r' RA)) (Int.unsigned n) = Some (labd', r'0)
          -> asm_invariant tge (State r' m0)
          -> PTHREADSCHED.low_level_invariant (Mem.nextblock m0) labd
          -> r'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: IR EDX :: IR ECX :: IR EAX :: RA :: nil) 
                               (undef_regs (List.map preg_of temporary_regs)
                                           (undef_regs (List.map preg_of destroyed_at_call_regs) r')))
          -> sig = mksignature (Tint::nil) None
          -> extcall_arguments r' m0 sig (Vint n ::nil)
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
        eapply THREADGEN1_ASM.threadsleep_spec; eauto.
      Qed.

    Theorem transf_program_correct:
       Smallstep.backward_simulation 
          (PTHREAD.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                             (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                             (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                             (real_abq:= real_abq) (Hnchan:= Hnchan) prog) 
          (PTHREADSCHED.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                                  (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                                  (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                                  (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                                  (Hnchan:= Hnchan) (real_abq:= real_abq) tprog). 
    Proof.
      eapply THREADGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End THREADGENIMPL.
