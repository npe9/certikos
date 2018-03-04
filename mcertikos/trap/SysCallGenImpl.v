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
Require Import TSysCall.
Require Import TTrap.
Require Import PProc.
Require Export SysCallGen.
Require Import SysCallGenAsm.
Require Import SysCallGenAsm2.
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

Module SYSCALLGENIMPL.
  Export SysCallGen.SYSCALLGEN.

  Lemma hprim_finite_type:
    forall
      (Q: TSYSCALL.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec TSYSCALL.PAlloc)...
    destruct (Q_dec TSYSCALL.PFree)...
    destruct (Q_dec TSYSCALL.PPTRead)...
    destruct (Q_dec TSYSCALL.PThreadKill)...
    destruct (Q_dec TSYSCALL.PThreadWakeup)...
    destruct (Q_dec TSYSCALL.PGetCurID)...
    destruct (Q_dec TSYSCALL.PUCTXGet)...
    destruct (Q_dec TSYSCALL.PUCTXSet)...

    destruct (Q_dec TSYSCALL.PThreadYield)...
    destruct (Q_dec TSYSCALL.PThreadSleep)...
    destruct (Q_dec TSYSCALL.PPageFaultHandler)...

    destruct (Q_dec TSYSCALL.PSysProcCreate)...
    destruct (Q_dec TSYSCALL.PSysYield)...

    destruct (Q_dec TSYSCALL.PSysIsChanReady)...
    destruct (Q_dec TSYSCALL.PSysSendToChan)...
    destruct (Q_dec TSYSCALL.PSysReceiveChan)...
    destruct (Q_dec TSYSCALL.PSysWaitChan)...

    destruct (Q_dec TSYSCALL.PProcInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation LDATA :=(PPROC.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).
    Notation HDATA := LDATA.
  
    Notation Hfundef := (Asm.fundef (external_function:= TSYSCALL.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= TTRAP.primOp)).

    Notation funkind := (funkind (low:= TTRAP.primOp) Asm.code (Clight.fundef (external_function := TTRAP.primOp))).

    Notation dummy := (AST.Internal nil).   

    Definition source_implem_extfuns (p: TSYSCALL.primOp): funkind :=
      match p with
        | TSYSCALL.PAlloc => Code _ (AST.External TTRAP.PAlloc)
        | TSYSCALL.PFree => Code _ (AST.External TTRAP.PFree)
        | TSYSCALL.PPTRead => Code _ (AST.External TTRAP.PPTRead)
        | TSYSCALL.PThreadKill => Code _ (AST.External TTRAP.PThreadKill)
        | TSYSCALL.PThreadWakeup => Code _ (AST.External TTRAP.PThreadWakeup)
        | TSYSCALL.PGetCurID => Code _ (AST.External TTRAP.PGetCurID)
        | TSYSCALL.PUCTXGet => Code _ (AST.External TTRAP.PUCTXGet)
        | TSYSCALL.PUCTXSet => Code _ (AST.External TTRAP.PUCTXSet)
                                    
        | TSYSCALL.PThreadYield => Code _ (AST.External TTRAP.PThreadYield)
        | TSYSCALL.PThreadSleep => Code _ (AST.External TTRAP.PThreadSleep)
        | TSYSCALL.PPageFaultHandler => Code _ SYSCALLGEN_ASM4.Im_pgf_handler
                                             
        | TSYSCALL.PSysProcCreate => Code _ SYSCALLGEN_ASM4.Im_sys_proc_create
        | TSYSCALL.PSysYield => Code _ SYSCALLGEN_ASM4.Im_sys_yield
                                     
        | TSYSCALL.PSysIsChanReady => Code _ SYSCALLGEN_ASM3.Im_sys_is_chan_ready
        | TSYSCALL.PSysSendToChan => Code _ SYSCALLGEN_ASM3.Im_sys_send
        | TSYSCALL.PSysReceiveChan => Code _ SYSCALLGEN_ASM3.Im_sys_recv
        | TSYSCALL.PSysWaitChan => Code _ SYSCALLGEN_ASM4.Im_sys_wait
                                        
        | TSYSCALL.PProcInit => Code _ (AST.External TTRAP.PProcInit)
      end.
 
    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (proc_start_user, Some (Gfun (Code _ (AST.External TTRAP.PProcStartUser)))) 
        :: (proc_exit_user, Some (Gfun (Code _ (AST.External TTRAP.PProcExitUser)))) 
        :: (sys_is_chan_ready1, Some (Gfun (Code _ (AST.External TTRAP.PSysIsChanReady)))) 
        :: (sys_send1, Some (Gfun (Code _ (AST.External TTRAP.PSysSendToChan)))) 
        :: (sys_recv1, Some (Gfun (Code _ (AST.External TTRAP.PSysReceiveChan)))) 
        :: (thread_yield, Some (Gfun (Code _ (AST.External TTRAP.PThreadYield)))) 
        :: (thread_sleep, Some (Gfun (Code _ (AST.External TTRAP.PThreadSleep)))) 
        :: (trap_get, Some (Gfun (Code _ (AST.External TTRAP.PTrapGet)))) 
        :: (ptfault_resv, Some (Gfun (Code _ (AST.External TTRAP.PPTFaultResv)))) 
        :: (sys_proc_create1, Some (Gfun (Code _ (AST.External TTRAP.PSysProcCreate)))) 
        :: (uctx_set_errno', Some (Gfun (Code _ (AST.External TTRAP.PUCTXSetErrno)))) 
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit TSYSCALL.primOp (low := TTRAP.primOp) (Clight.fundef (external_function := TTRAP.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit TSYSCALL.primOp (low := TTRAP.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= TSYSCALL.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= TTRAP.primOp)).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because TSYSCALL.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: SYSCALLGEN.transf_program SYSCALLGEN_ASM4.Im_sys_proc_create
              SYSCALLGEN_ASM3.Im_sys_is_chan_ready
              SYSCALLGEN_ASM3.Im_sys_send
              SYSCALLGEN_ASM3.Im_sys_recv
              SYSCALLGEN_ASM4.Im_pgf_handler
              SYSCALLGEN_ASM4.Im_sys_yield
              SYSCALLGEN_ASM4.Im_sys_wait impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := TTRAP.primOp) := source_program_only source_implem prog.
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

    (*Require Import TrapDataType.*)

    Context `{PageFaultHandler_LOC: ident}.
    Context `{START_USER_FUN_LOC: ident}.

    Section WITHMEM.

      Local Instance LdataOp:AbstractDataOps LDATA:= (TTRAP.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel LDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections LDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) LDATA TSYSCALL.primOp mem__H :=
        TSYSCALL.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                           (kern_high:=kern_high) (maxpage:=maxpage) (Hnpc := Hnpc)
                           (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                           (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                           (num_chan := num_chan) (real_abq:= real_abq) (real_chpool := real_chpool) (Hnchan:= Hnchan).        

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA TTRAP.primOp mem__L :=
        TTRAP.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                        (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                        (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                        (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                        (num_chan := num_chan) (real_abq:= real_abq) (real_chpool := real_chpool)
                        (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC := START_USER_FUN_LOC)
                        (ELF_LOC:= ELF_LOC) (ELF_ENTRY_LOC:= ELF_ENTRY_LOC) (Hnchan:= Hnchan).        

      Notation HLoad := (TSYSCALL.exec_loadex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation HStore := (TSYSCALL.exec_storeex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation LLoad := (TTRAP.exec_loadex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).
      Notation LStore := (TTRAP.exec_storeex (PgSize:=PgSize)(PageFaultHandler_LOC:= PageFaultHandler_LOC) (NPT_LOC:=NPT_LOC)).

      Notation Hprimitive := (TSYSCALL.primitive_call
                                (HPS4:= HPS4) (Hnchan:= Hnchan) (STACK_LOC:=STACK_LOC)
                                (ELF_ENTRY_LOC:= ELF_ENTRY_LOC) (STACK_TOP:= STACK_TOP) (Hlow := Hlow) (Hhigh:= Hhigh)
                                (START_USER_FUN_LOC := START_USER_FUN_LOC) (ELF_LOC:= ELF_LOC)).

      Notation lstep := (TTRAP.step 
                           (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4) (real_chpool:= real_chpool)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)
                           (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC:= START_USER_FUN_LOC)
                            (ELF_ENTRY_LOC:= ELF_ENTRY_LOC) (ELF_LOC:= ELF_LOC) (NPT_LOC:=NPT_LOC)).

      Notation LADT := PPROC.ADT.

      Let AndImplies: forall A B: Prop, (A /\ (A -> B)) -> (A /\ B).
      Proof.
        intros.
        destruct H.
        split.
        assumption.
        apply H0; assumption.
      Qed.

      Let bproc_start_user: block := Genv.genv_next ge + Z.of_nat 0.
      Let Hstart: exists b_start, Genv.find_symbol tge proc_start_user = Some b_start
                                             /\ Genv.find_funct_ptr tge b_start = Some (External TTRAP.PProcStartUser).
      Proof.
        exists bproc_start_user.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ proc_start_user).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ proc_start_user _ _)).
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

      Let bproc_exit_user: block := Genv.genv_next ge + Z.of_nat 1.
      Let Hexit: exists b_exit, 
                                  Genv.find_symbol tge proc_exit_user = Some b_exit
                                  /\ Genv.find_funct_ptr tge b_exit = Some (External TTRAP.PProcExitUser).
      Proof.
        exists bproc_exit_user.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ proc_exit_user).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ proc_exit_user _ _)).
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

      Let bsys_is_chan_ready1: block := Genv.genv_next ge + Z.of_nat 2.
      Let Hchan_ready: exists b_ready, 
                                  Genv.find_symbol tge sys_is_chan_ready1 = Some b_ready
                                  /\ Genv.find_funct_ptr tge b_ready = Some (External TTRAP.PSysIsChanReady).
      Proof.
        exists bsys_is_chan_ready1.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ sys_is_chan_ready1).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ sys_is_chan_ready1 _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 16.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bsys_send1: block := Genv.genv_next ge + Z.of_nat 3.
      Let Hsend: exists b_send, 
                                  Genv.find_symbol tge sys_send1 = Some b_send
                                  /\ Genv.find_funct_ptr tge b_send = Some (External TTRAP.PSysSendToChan).
      Proof.
        exists bsys_send1.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ sys_send1).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ sys_send1 _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 22.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bsys_recv1: block := Genv.genv_next ge + Z.of_nat 4.
      Let Hrecv: exists b_recv, 
                                  Genv.find_symbol tge sys_recv1 = Some b_recv
                                  /\ Genv.find_funct_ptr tge b_recv = Some (External TTRAP.PSysReceiveChan).
      Proof.
        exists bsys_recv1.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ sys_recv1).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ sys_recv1 _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 23.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bthread_yield: block := Genv.genv_next ge + Z.of_nat 5.
      Let Hyield: exists b_yield, 
                                  Genv.find_symbol tge thread_yield = Some b_yield
                                  /\ Genv.find_funct_ptr tge b_yield = Some (External TTRAP.PThreadYield).
      Proof.
        exists bthread_yield.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ thread_yield).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ thread_yield _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 25.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bthread_sleep: block := Genv.genv_next ge + Z.of_nat 6.
      Let Hsleep: exists b_sleep, 
                           Genv.find_symbol tge thread_sleep = Some b_sleep
                           /\ Genv.find_funct_ptr tge b_sleep = Some (External TTRAP.PThreadSleep).
      Proof.
        exists bthread_sleep.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ thread_sleep).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ thread_sleep _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 26.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let btrap_get: block := Genv.genv_next ge + Z.of_nat 7.
      Let Hget: exists b_get, 
                                  Genv.find_symbol tge trap_get = Some b_get
                                  /\ Genv.find_funct_ptr tge b_get = Some (External TTRAP.PTrapGet).
      Proof.
        exists btrap_get.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ trap_get).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ trap_get _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 28.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bptfault_resv: block := Genv.genv_next ge + Z.of_nat 8.
      Let Hpgfr: exists b_pgfr, 
                         Genv.find_symbol tge ptfault_resv = Some b_pgfr
                         /\ Genv.find_funct_ptr tge b_pgfr = Some (External TTRAP.PPTFaultResv).
      Proof.
        exists bptfault_resv.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ ptfault_resv).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ ptfault_resv _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 29.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bsys_proc_create1: block := Genv.genv_next ge + Z.of_nat 9.
      Let Hcreate: exists b_create, 
                                  Genv.find_symbol tge sys_proc_create1 = Some b_create
                                  /\ Genv.find_funct_ptr tge b_create = Some (External TTRAP.PSysProcCreate).
      Proof.
        exists bsys_proc_create1.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ sys_proc_create1).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ sys_proc_create1 _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 30.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let buctx_set_errno': block := Genv.genv_next ge + Z.of_nat 10.
      Let Herr: exists b_err, 
                  Genv.find_symbol tge uctx_set_errno' = Some b_err
                  /\ Genv.find_funct_ptr tge b_err = Some (External TTRAP.PUCTXSetErrno).
      Proof.
        exists buctx_set_errno'.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ uctx_set_errno').
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_set_errno' _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 31.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

    Theorem transf_program_correct:
       Smallstep.backward_simulation 
          (TSYSCALL.semantics (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (ELF_ENTRY_LOC:= ELF_ENTRY_LOC)
                              (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                              (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                              (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool:= real_chpool) (STACK_TOP:= STACK_TOP) 
                              (START_USER_FUN_LOC:= START_USER_FUN_LOC) (ELF_LOC:= ELF_LOC) 
                              (PROC_START_USER_LOC := proc_start_user) (NPT_LOC:=NPT_LOC) prog) 
          (TTRAP.semantics (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (STACK_TOP:= STACK_TOP) 
                           (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                           (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                           (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                           (Hnchan:= Hnchan) (real_abq:= real_abq) (real_chpool:= real_chpool)
                           (START_USER_FUN_LOC:= START_USER_FUN_LOC) (ELF_LOC:= ELF_LOC) 
                           (ELF_ENTRY_LOC:= ELF_ENTRY_LOC) (NPT_LOC:=NPT_LOC) tprog).
    Proof.
      eapply SYSCALLGEN.transf_program_correct; simpl; eauto 1.
      eapply SYSCALLGEN_ASM4.pgf_handler_spec; eauto.
      eapply SYSCALLGEN_ASM4.sys_proc_create_spec; eauto.
      eapply SYSCALLGEN_ASM4.sys_yield_spec; eauto.
      eapply SYSCALLGEN_ASM3.sys_is_chan_ready_spec; eauto.
      eapply SYSCALLGEN_ASM3.sys_send_spec; eauto.
      eapply SYSCALLGEN_ASM3.sys_recv_spec; eauto.
      eapply SYSCALLGEN_ASM4.sys_wait_spec; eauto.
      Grab Existential Variables.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End SYSCALLGENIMPL.
