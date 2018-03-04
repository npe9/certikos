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
Require Import PProc.
Require Import PUCtxtIntro.
Require Export ProcGen.
Require Export ProcGenAsm.
Require Import PUCtxtIntroCode.
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

Module PROCGENIMPL.
  Export ProcGen.PROCGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PPROC.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PPROC.PAlloc)...
    destruct (Q_dec PPROC.PFree)...
    destruct (Q_dec PPROC.PPTRead)...
    destruct (Q_dec PPROC.PPTResv)...
    destruct (Q_dec PPROC.PProcCreate)...
    destruct (Q_dec PPROC.PThreadKill)...
    destruct (Q_dec PPROC.PThreadWakeup)...
    destruct (Q_dec PPROC.PThreadYield)...
    destruct (Q_dec PPROC.PThreadSleep)...
    destruct (Q_dec PPROC.PGetCurID)...
    destruct (Q_dec PPROC.PProcStartUser)...
    destruct (Q_dec PPROC.PProcExitUser)...
    destruct (Q_dec PPROC.PUCTXGet)...
    destruct (Q_dec PPROC.PUCTXSet)...
    destruct (Q_dec PPROC.PHostIn)...
    destruct (Q_dec PPROC.PHostOut)...
    destruct (Q_dec PPROC.PTrapGet)...
    destruct (Q_dec PPROC.PTrapRet)...
    destruct (Q_dec PPROC.PIsChanReady)...
    destruct (Q_dec PPROC.PSendToChan)...
    destruct (Q_dec PPROC.PReceiveChan)...
    destruct (Q_dec PPROC.PProcInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PPROC.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                    (num_chan:= num_chan) (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA :=(PUCTXTINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                         (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (Asm.fundef (external_function:= PPROC.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PUCTXTINTRO.primOp)).

    Notation funkind := (funkind (low:= PUCTXTINTRO.primOp) Asm.code (Clight.fundef (external_function := PUCTXTINTRO.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: PPROC.primOp): funkind :=
      match p with
        | PPROC.PAlloc => Code _ (AST.External PUCTXTINTRO.PAlloc)
        | PPROC.PFree => Code _ (AST.External PUCTXTINTRO.PFree)
        | PPROC.PPTRead => Code _ (AST.External PUCTXTINTRO.PPTRead)
        | PPROC.PPTResv => Code _ (AST.External PUCTXTINTRO.PPTResv)
        | PPROC.PProcCreate => SourceFun (Clight.Internal (PUCTXTINTROCODE.f_proc_create (START_USER_FUN_LOC:=proc_start_user))) 
                                         (AST.Internal nil)
        | PPROC.PThreadKill => Code _ (AST.External PUCTXTINTRO.PThreadKill)
        | PPROC.PThreadWakeup => Code _ (AST.External PUCTXTINTRO.PThreadWakeup)
        | PPROC.PThreadYield => Code _ (AST.External PUCTXTINTRO.PThreadYield)
        | PPROC.PThreadSleep => Code _ (AST.External PUCTXTINTRO.PThreadSleep)
        | PPROC.PGetCurID => Code _ (AST.External PUCTXTINTRO.PGetCurID)
        | PPROC.PProcStartUser => Code _ PROCGEN_ASM.Im_proc_start_user
        | PPROC.PProcExitUser => Code _ PROCGEN_ASM.Im_proc_exit_user
        | PPROC.PUCTXGet => Code _ (AST.External PUCTXTINTRO.PUCTXGet)
        | PPROC.PUCTXSet => Code _ (AST.External PUCTXTINTRO.PUCTXSet)
        | PPROC.PHostIn => Code _ (AST.External PUCTXTINTRO.PHostIn)
        | PPROC.PHostOut => Code _ (AST.External PUCTXTINTRO.PHostOut)
        | PPROC.PTrapGet => Code _ (AST.External PUCTXTINTRO.PTrapGet)
        | PPROC.PTrapRet => Code _ (AST.External PUCTXTINTRO.PTrapRet)
        | PPROC.PIsChanReady => Code _ (AST.External PUCTXTINTRO.PIsChanReady)
        | PPROC.PSendToChan => Code _ (AST.External PUCTXTINTRO.PSendToChan)
        | PPROC.PReceiveChan => Code _ (AST.External PUCTXTINTRO.PReceiveChan)
        | PPROC.PProcInit => Code _ (AST.External PUCTXTINTRO.PProcInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (thread_spawn, Some (Gfun (SourceFun (Clight.External (PUCTXTINTRO.PThreadSpawn) (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tint) dummy)))
        :: (uctx_set, Some (Gfun (SourceFun (Clight.External (PUCTXTINTRO.PUCTXSet) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid) dummy)))
        :: (uctx_set_eip, Some (Gfun (SourceFun (Clight.External (PUCTXTINTRO.PUCTXSetEIP) (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) tvoid) dummy)))
        :: (elf_load, Some (Gfun (SourceFun (Clight.External (PUCTXTINTRO.PELFLoad) (Ctypes.Tcons (tptr tvoid) (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy)))
        :: (pt_in, Some (Gfun (Code _ (AST.External PUCTXTINTRO.PPTIn))))
        :: (trap_in, Some (Gfun (Code _ (AST.External PUCTXTINTRO.PTrapIn))))
        :: (save_uctx, Some (Gfun (Code _ (AST.External PUCTXTINTRO.PSaveUCTX))))
        :: (pt_out, Some (Gfun (Code _ (AST.External PUCTXTINTRO.PPTOut))))
        :: (get_curid4, Some (Gfun (Code _ (AST.External PUCTXTINTRO.PGetCurID))))
        :: (restore_uctx, Some (Gfun (Code _ (AST.External PUCTXTINTRO.PRestoreUCTX))))
        :: (set_cr31, Some (Gfun (Code _ (AST.External PUCTXTINTRO.PSetPT))))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PPROC.primOp (low := PUCTXTINTRO.primOp) (Clight.fundef (external_function := PUCTXTINTRO.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PPROC.primOp (low := PUCTXTINTRO.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PPROC.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PUCTXTINTRO.primOp)).

    Let Im_proc_create: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PPROC.PProcCreate).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PPROC.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: PROCGEN.transf_program Im_proc_create PROCGEN_ASM.Im_proc_start_user PROCGEN_ASM.Im_proc_exit_user impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PUCTXTINTRO.primOp) := source_program_only source_implem prog.
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

    (** thread_spawn *)

    Let bthread_spawn: block := Genv.genv_next ge + Z.of_nat 0.

    Let hthread_spawn1 : Genv.find_symbol sge thread_spawn = Some bthread_spawn. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ thread_spawn).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hthread_spawn2 : Genv.find_funct sge (Vptr bthread_spawn Int.zero) = Some (Clight.External (PUCTXTINTRO.PThreadSpawn) (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ thread_spawn _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hthread_spawn3 : Clight.type_of_global sge bthread_spawn = Some (Ctypes.Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bthread_spawn).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bthread_spawn. unfold Asm.fundef. omega.
      intros.
      simpl in hthread_spawn2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hthread_spawn2. reflexivity.
    Qed.   

    (** uctx_set *)

    Let buctx_set: block := Genv.genv_next ge + Z.of_nat 1.

    Let huctx_set1 : Genv.find_symbol sge uctx_set = Some buctx_set. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_set).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let huctx_set2 : Genv.find_funct sge (Vptr buctx_set Int.zero) = Some (Clight.External (PUCTXTINTRO.PUCTXSet) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_set _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let huctx_set3 : Clight.type_of_global sge buctx_set = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_set).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_set. unfold Asm.fundef. omega.
      intros.
      simpl in huctx_set2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_set2. reflexivity.
    Qed.   

    (** uctx_set_eip *)

    Let buctx_set_eip: block := Genv.genv_next ge + Z.of_nat 2.

    Let huctx_set_eip1 : Genv.find_symbol sge uctx_set_eip = Some buctx_set_eip. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ uctx_set_eip).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let huctx_set_eip2 : Genv.find_funct sge (Vptr buctx_set_eip Int.zero) = Some (Clight.External (PUCTXTINTRO.PUCTXSetEIP) (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ uctx_set_eip _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let huctx_set_eip3 : Clight.type_of_global sge buctx_set_eip = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge buctx_set_eip).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold buctx_set_eip. unfold Asm.fundef. omega.
      intros.
      simpl in huctx_set_eip2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite huctx_set_eip2. reflexivity.
    Qed.   

    (** elf_load *)

    Let belf_load: block := Genv.genv_next ge + Z.of_nat 3.

    Let helf_load1 : Genv.find_symbol sge elf_load = Some belf_load. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ elf_load).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let helf_load2 : Genv.find_funct sge (Vptr belf_load Int.zero) = Some (Clight.External (PUCTXTINTRO.PELFLoad) (Ctypes.Tcons (tptr tvoid) (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ elf_load _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let helf_load3 : Clight.type_of_global sge belf_load = Some (Ctypes.Tfunction (Ctypes.Tcons (tptr tvoid) (Ctypes.Tcons tint Ctypes.Tnil)) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge belf_load).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold belf_load. unfold Asm.fundef. omega.
      intros.
      simpl in helf_load2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite helf_load2. reflexivity.
    Qed.  

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Local Instance HdataOp:AbstractDataOps HDATA:= (PPROC.abstract_data (Hnpc:= Hnpc)).
      Local Instance LdataOp:AbstractDataOps LDATA:= (PUCTXTINTRO.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PPROC.primOp mem__H :=
        PPROC.layer_def    (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                           (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc)
                           (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                           (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                           (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) 
                           (real_chpool := real_chpool)
                           (STACK_LOC:= STACK_LOC)(STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC := proc_start_user).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PUCTXTINTRO.primOp mem__L :=
        PUCTXTINTRO.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                              (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                              (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                              (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool := real_chpool).        

      Notation HLoad := (PPROC.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PPROC.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PUCTXTINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PUCTXTINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PUCTXTINTRO.step 
                           (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4) (real_chpool:= real_chpool)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)).

      Notation LADT := PUCTXTINTRO.ADT.

      Ltac discharge_or:= match goal with
        | [|- ?a = ?a] => reflexivity
        | [|- (?a = ?a) \/ _] => left; reflexivity
        | [|- _ \/ _] => right
        | _ => fail
      end.

      Let proc_create_spec:
        forall m'0 labd' n b buc ofs  ofs_uc be ofse r' sig bst bstc,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_proc_create)
          -> Genv.find_funct_ptr ge b = Some (External PPROC.PProcCreate)
          -> Genv.find_symbol tge STACK_LOC = Some bst 
          -> Genv.find_symbol ge STACK_LOC = Some bst 
          -> Int.unsigned ofs = (Int.unsigned n + 1) * PgSize - 4 
          -> Genv.find_symbol tge proc_start_user = Some bstc
          -> Genv.find_symbol ge proc_start_user = Some bstc
          -> (exists fun_id, Genv.find_symbol tge fun_id = Some buc) 
          -> (exists fun_id, Genv.find_symbol ge fun_id = Some buc) 
          -> (exists elf_id, Genv.find_symbol tge elf_id = Some be) 
          -> (exists elf_id, Genv.find_symbol ge elf_id = Some be) 
          -> PUCTXTINTRO.proc_create 
               (Hnchan:= Hnchan) (STACK_TOP:= STACK_TOP)
               (Mem.get_abstract_data m'0) bst bstc buc ofs ofs_uc = Some (labd', Int.unsigned n)
          -> sig = mksignature (Tint::Tint::nil) (Some Tint)
          -> extcall_arguments  r' m'0 sig (Vptr be ofse :: Vptr buc ofs_uc :: nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
               /\ Memtype.Mem.inject f' m'0 m0'
               /\ Mem.nextblock m'0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m'0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ r_ # (loc_external_result sig) = (Vint n)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PPROC.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PUCTXTINTRO.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PUCTXTINTRO.is_primitive_call)
                     (kernel_mode := PUCTXTINTRO.kernel_mode)
                  ).
          apply PUCTXTINTRO.exec_load_exec_loadex.
          apply PUCTXTINTRO.exec_store_exec_storeex.
          apply PUCTXTINTRO.extcall_not_primitive.
          apply PUCTXTINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PUCTXTINTROCODE.proc_create_correct; eauto.

          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          repeat (destruct H12; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ]).
          contradiction.
          eassumption.
          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          repeat (destruct H12; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ]).
          contradiction.
          eassumption.
          destruct H8.
          esplit.
          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          repeat (destruct H12; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ]).
          contradiction.
          eassumption.
          destruct H10.
          esplit.
          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          destruct H20; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ].
          repeat (destruct H12; subst;
          [apply NEW_INJ in H19;
          simpl in H19;
          destruct H19;
          repeat discharge_or | ]).
          contradiction.
          eassumption.

          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PUCTXTINTRO.kernel_mode.
          apply PUCTXTINTRO.proc_create_eq in H11.
          unfold PUCTXTINTRO.proc_create_aux in H11.
          destruct (PUCTXTINTRO.INV (Mem.get_abstract_data m'0)).
          destruct (PUCTXTINTRO.pe (LADT (Mem.get_abstract_data m'0))); try discriminate H11.
          destruct (PUCTXTINTRO.ipt (LADT (Mem.get_abstract_data m'0))); try discriminate H11.
          destruct (PUCTXTINTRO.ihost (LADT (Mem.get_abstract_data m'0))); try discriminate H11.
          auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m'0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m'0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m'0)) labd') in PLUS.
          inv H19.
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

      Let bpt_in: block := Genv.genv_next ge + Z.of_nat 4.
      Let Hptin: exists b_ptin, Genv.find_symbol tge pt_in = Some b_ptin
                                             /\ Genv.find_funct_ptr tge b_ptin = Some (External PUCTXTINTRO.PPTIn).
      Proof.
        exists bpt_in.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ pt_in).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_in _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 6.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let btrap_in: block := Genv.genv_next ge + Z.of_nat 5.
      Let Htrapin: exists b_trapin, Genv.find_symbol tge trap_in = Some b_trapin
                                             /\ Genv.find_funct_ptr tge b_trapin = Some (External PUCTXTINTRO.PTrapIn).
      Proof.
        exists btrap_in.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ trap_in).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ trap_in _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 7.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bsave_uctx: block := Genv.genv_next ge + Z.of_nat 6.
      Let Hsave_uctx: exists b_save, 
                                  Genv.find_symbol tge save_uctx = Some b_save
                                  /\ Genv.find_funct_ptr tge b_save = Some (External PUCTXTINTRO.PSaveUCTX).
      Proof.
        exists bsave_uctx.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ save_uctx).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ save_uctx _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 8.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bpt_out: block := Genv.genv_next ge + Z.of_nat 7.
      Let Hptout: exists b_ptout, Genv.find_symbol tge pt_out = Some b_ptout
                                             /\ Genv.find_funct_ptr tge b_ptout = Some (External PUCTXTINTRO.PPTOut).
      Proof.
        exists bpt_out.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ pt_out).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_out _ _)).
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

      Let bget_curid4: block := Genv.genv_next ge + Z.of_nat 8.
      Let Hget_curid: exists b_get_cid, Genv.find_symbol tge get_curid4 = Some b_get_cid
                                             /\ Genv.find_funct_ptr tge b_get_cid = Some (External PUCTXTINTRO.PGetCurID).
      Proof.
        exists bget_curid4.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ get_curid4).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_curid4 _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 10.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let brestore_uctx: block := Genv.genv_next ge + Z.of_nat 9.
      Let Hrestore_uctx: exists b_restore, 
                                  Genv.find_symbol tge restore_uctx = Some b_restore
                                  /\ Genv.find_funct_ptr tge b_restore = Some (External PUCTXTINTRO.PRestoreUCTX).
      Proof.
        exists brestore_uctx.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ restore_uctx).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ restore_uctx _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 11.
        2: assumption.
        fold tprog tge.
        destruct 1 as [? [? ?]].
        unfold Asm.fundef in *.
        rewrite H in H0; injection H0; intros; subst.
        rewrite H2.
        assumption.
      Qed.

      Let bset_cr31: block := Genv.genv_next ge + Z.of_nat 10.
      Let Hset_cr3: exists b_set_cr3, Genv.find_symbol tge set_cr31 = Some b_set_cr3
                                                 /\ Genv.find_funct_ptr tge b_set_cr3 = Some (External PUCTXTINTRO.PSetPT).
      Proof.
        exists bset_cr31.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ set_cr31).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_cr31 _ _)).
        2: exact (transf_program_eq im prog).
        3: simpl; eauto 12.
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
          (PPROC.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                           (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                           (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                           (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                           (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool:= real_chpool) (STACK_TOP:= STACK_TOP) 
                           (START_USER_FUN_LOC:= proc_start_user) prog) 
          (PUCTXTINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                                 (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                                 (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                                 (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                                 (Hnchan:= Hnchan) (real_abq:= real_abq) (real_chpool:= real_chpool) tprog).
    Proof.
      pose PROCGEN_ASM.procstartuser_spec.
      pose PROCGEN_ASM.procexituser_spec.
      eapply PROCGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End PROCGENIMPL.
