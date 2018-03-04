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
Require Import PThreadInit.
Require Import PThreadIntro.
Require Export ThreadInitGen.
Require Import PThreadIntroCode.
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

Module THREADINITGENIMPL.
  Export ThreadInitGen.THREADINITGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PTHREADINIT.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PTHREADINIT.PAlloc)...
    destruct (Q_dec PTHREADINIT.PFree)...
    destruct (Q_dec PTHREADINIT.PSetPT)...
    destruct (Q_dec PTHREADINIT.PPTRead)...
    destruct (Q_dec PTHREADINIT.PPTResv)...
    destruct (Q_dec PTHREADINIT.PKCtxtNew)...
    destruct (Q_dec PTHREADINIT.PThreadFree)...
    destruct (Q_dec PTHREADINIT.PKCtxtSwitch)...
    destruct (Q_dec PTHREADINIT.PGetState)...
    destruct (Q_dec PTHREADINIT.PGetPrev)...
    destruct (Q_dec PTHREADINIT.PGetNext)...
    destruct (Q_dec PTHREADINIT.PSetState)...
    destruct (Q_dec PTHREADINIT.PSetPrev)...
    destruct (Q_dec PTHREADINIT.PSetNext)...
    destruct (Q_dec PTHREADINIT.PPTIn)...
    destruct (Q_dec PTHREADINIT.PPTOut)...
    destruct (Q_dec PTHREADINIT.PTrapIn)...
    destruct (Q_dec PTHREADINIT.PTrapOut)...
    destruct (Q_dec PTHREADINIT.PHostIn)...
    destruct (Q_dec PTHREADINIT.PHostOut)...
    destruct (Q_dec PTHREADINIT.PTrapGet)...
    destruct (Q_dec PTHREADINIT.PTrapRet)...
    destruct (Q_dec PTHREADINIT.PThreadInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PTHREADINIT.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low)
                                          (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA := (PTHREADINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                           (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (Asm.fundef (external_function:= PTHREADINIT.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PTHREADINTRO.primOp)).

    Notation funkind := (funkind (low:= PTHREADINTRO.primOp) Asm.code (Clight.fundef (external_function := PTHREADINTRO.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: PTHREADINIT.primOp): funkind :=
      match p with
        | PTHREADINIT.PAlloc => Code _ (AST.External PTHREADINTRO.PAlloc)
        | PTHREADINIT.PFree => Code _ (AST.External PTHREADINTRO.PFree)
        | PTHREADINIT.PSetPT => Code _ (AST.External PTHREADINTRO.PSetPT)
        | PTHREADINIT.PPTRead => Code _ (AST.External PTHREADINTRO.PPTRead)
        | PTHREADINIT.PPTResv => Code _ (AST.External PTHREADINTRO.PPTResv)
        | PTHREADINIT.PKCtxtNew => Code _ (AST.External PTHREADINTRO.PKCtxtNew)
        | PTHREADINIT.PThreadFree => SourceFun (Clight.Internal PTHREADINTROCODE.f_thread_free) (AST.Internal nil)
        | PTHREADINIT.PKCtxtSwitch => Code _ (AST.External PTHREADINTRO.PKCtxtSwitch)
        | PTHREADINIT.PGetState => Code _ (AST.External PTHREADINTRO.PGetState)
        | PTHREADINIT.PGetPrev => Code _ (AST.External PTHREADINTRO.PGetPrev)
        | PTHREADINIT.PGetNext => Code _ (AST.External PTHREADINTRO.PGetNext)
        | PTHREADINIT.PSetState => Code _ (AST.External PTHREADINTRO.PSetState)
        | PTHREADINIT.PSetPrev => Code _ (AST.External PTHREADINTRO.PSetPrev)
        | PTHREADINIT.PSetNext => Code _ (AST.External PTHREADINTRO.PSetNext)
        | PTHREADINIT.PPTIn => Code _ (AST.External PTHREADINTRO.PPTIn)
        | PTHREADINIT.PPTOut => Code _ (AST.External PTHREADINTRO.PPTOut)
        | PTHREADINIT.PTrapIn => Code _ (AST.External PTHREADINTRO.PTrapIn)
        | PTHREADINIT.PTrapOut => Code _ (AST.External PTHREADINTRO.PTrapOut)
        | PTHREADINIT.PHostIn => Code _ (AST.External PTHREADINTRO.PHostIn)
        | PTHREADINIT.PHostOut => Code _ (AST.External PTHREADINTRO.PHostOut)
        | PTHREADINIT.PTrapGet => Code _ (AST.External PTHREADINTRO.PTrapGet)
        | PTHREADINIT.PTrapRet => Code _ (AST.External PTHREADINTRO.PTrapRet)
        | PTHREADINIT.PThreadInit => SourceFun (Clight.Internal PTHREADINTROCODE.f_thread_init) (AST.Internal nil)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (pt_free, Some (Gfun (SourceFun (Clight.External (PTHREADINTRO.PPTFree) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (tcb_init, Some (Gfun (SourceFun (Clight.External (PTHREADINTRO.PTCBInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: (pmap_init, Some (Gfun (SourceFun (Clight.External (PTHREADINTRO.PPMapInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PTHREADINIT.primOp (low := PTHREADINTRO.primOp) (Clight.fundef (external_function := PTHREADINTRO.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PTHREADINIT.primOp (low := PTHREADINTRO.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PTHREADINIT.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PTHREADINTRO.primOp)).

    Let Im_thread_free: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINIT.PThreadFree).
    Let Im_thread_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINIT.PThreadInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PTHREADINIT.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: THREADINITGEN.transf_program Im_thread_free Im_thread_init impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PTHREADINTRO.primOp) := source_program_only source_implem prog.
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

    (** pt_free *)

    Let bpt_free: block := Genv.genv_next ge + Z.of_nat 0.

    Let hpt_free1 : Genv.find_symbol sge pt_free = Some bpt_free. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_free).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_free2 : Genv.find_funct sge (Vptr bpt_free Int.zero) = Some (Clight.External (PTHREADINTRO.PPTFree) (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_free _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hpt_free3 : Clight.type_of_global sge bpt_free = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_free).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_free. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_free2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_free2. reflexivity.
    Qed.   

    (** tcb_init *)

    Let btcb_init: block := Genv.genv_next ge + Z.of_nat 1.

    Let htcb_init1 : Genv.find_symbol sge tcb_init = Some btcb_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ tcb_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let htcb_init2 : Genv.find_funct sge (Vptr btcb_init Int.zero) = Some (Clight.External (PTHREADINTRO.PTCBInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ tcb_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let htcb_init3 : Clight.type_of_global sge btcb_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge btcb_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold btcb_init. unfold Asm.fundef. omega.
      intros.
      simpl in htcb_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite htcb_init2. reflexivity.
    Qed. 

    (** pmap_init *)

    Let bpmap_init: block := Genv.genv_next ge + Z.of_nat 2.

    Let hpmap_init1 : Genv.find_symbol sge pmap_init = Some bpmap_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pmap_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hpmap_init2 : Genv.find_funct sge (Vptr bpmap_init Int.zero) = Some (Clight.External (PTHREADINTRO.PPMapInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pmap_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hpmap_init3 : Clight.type_of_global sge bpmap_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpmap_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpmap_init. unfold Asm.fundef. omega.
      intros.
      simpl in hpmap_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpmap_init2. reflexivity.
    Qed. 

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PTHREADINIT.primOp mem__H :=
        PTHREADINIT.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_tcb:= real_tcb)
                              (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                              (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PTHREADINTRO.primOp mem__L :=
        PTHREADINTRO.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                               (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                               (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb).    

      Notation HLoad := (PTHREADINIT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PTHREADINIT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PTHREADINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PTHREADINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC)(PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PTHREADINTRO.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)).

      Notation LADT := PTHREADINTRO.ADT.

      Let thread_free_spec:
        forall r' n b m0 labd' sig,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_thread_free)
          -> sig = mksignature (Tint :: nil) None
          -> PTHREADINTRO.thread_free (Mem.get_abstract_data m0) (Int.unsigned n)
                                      (real_free_pt (PTHREADINTRO.ptpool (LADT (Mem.get_abstract_data m0))) n) = Some labd'
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINIT.PThreadFree)
          -> asm_invariant tge (State r' m0)
          -> extcall_arguments r' m0 sig (Vint n ::  nil)
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
                     PTHREADINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREADINTRO.primitive_call)
                     (is_primitive_call := PTHREADINTRO.is_primitive_call)
                     (kernel_mode := PTHREADINTRO.kernel_mode)
                  ).
          apply PTHREADINTRO.exec_load_exec_loadex.
          apply PTHREADINTRO.exec_store_exec_storeex.
          apply PTHREADINTRO.extcall_not_primitive.
          apply PTHREADINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADINTROCODE.thread_free_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREADINTRO.kernel_mode.
          unfold PTHREADINTRO.thread_free in H2.
          case_eq (PTHREADINTRO.pt_free (Mem.get_abstract_data m0) 
           (Int.unsigned n)
           (real_free_pt
              (PTHREADINTRO.ptpool (LADT (Mem.get_abstract_data m0))) n)); [intros ? ptfree | intro ptfree]; rewrite ptfree in H2; try discriminate H2.
          apply PTHREADINTRO.pt_free_eq in ptfree.
          functional inversion ptfree.
          unfold adt in *.
          destruct (PTHREADINTRO.INV (Mem.get_abstract_data m0)).
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

      Let thread_init_spec:
        forall r' b m0 labd' sig mbi_adr,
          let labd := (Mem.get_abstract_data m0) in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_thread_init)
          -> sig = mksignature (Tint :: nil) None
          -> PTHREADINTRO.thread_init (Hnpc:= Hnpc) (Mem.get_abstract_data m0) real_nps 
                                      (real_AT (PTHREADINTRO.AT (LADT labd)))
                                      (real_ptp (PTHREADINTRO.ptpool (LADT labd)))
                                      (real_pt (PTHREADINTRO.ptpool (LADT labd)))
                                      (real_ptb (PTHREADINTRO.pb (LADT labd)))
                                      (real_tcb (PTHREADINTRO.tcb (LADT labd))) (Int.unsigned mbi_adr) = Some labd'
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINIT.PThreadInit)
          -> asm_invariant tge (State r' m0)
          -> extcall_arguments r' m0 sig (Vint mbi_adr ::  nil)
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
                     PTHREADINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREADINTRO.primitive_call)
                     (is_primitive_call := PTHREADINTRO.is_primitive_call)
                     (kernel_mode := PTHREADINTRO.kernel_mode)
                  ).
          apply PTHREADINTRO.exec_load_exec_loadex.
          apply PTHREADINTRO.exec_store_exec_storeex.
          apply PTHREADINTRO.extcall_not_primitive.
          apply PTHREADINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADINTROCODE.thread_init_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREADINTRO.kernel_mode.
          apply PTHREADINTRO.thread_init_eq in H2.
          unfold PTHREADINTRO.thread_init_aux in H2.
          case_eq (PTHREADINTRO.pmap_init_aux (Mem.get_abstract_data m0) real_nps
           (real_AT (PTHREADINTRO.AT (LADT labd)))
           (real_ptp (PTHREADINTRO.ptpool (LADT labd)))
           (real_pt (PTHREADINTRO.ptpool (LADT labd)))
           (real_ptb (PTHREADINTRO.pb (LADT labd))) 
           (Int.unsigned mbi_adr)); [intros ? tmp | intro tmp]; rewrite tmp in H2; try discriminate H2.
          functional inversion tmp.
          unfold adt in *.
          destruct (PTHREADINTRO.INV (Mem.get_abstract_data m0)).
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
          (PTHREADINIT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                                 (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                                 (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_tcb:= real_tcb)
                                 (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) prog) 
          (PTHREADINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                                  (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) 
                                  (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                                  (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) tprog). 
    Proof.
      eapply THREADINITGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End THREADINITGENIMPL.
