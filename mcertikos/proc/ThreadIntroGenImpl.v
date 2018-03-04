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
Require Import PThreadIntro.
Require Import PKContextNew.
Require Import PKContext.
Require Export ThreadIntroGen.
Require Import PKContextNewCode.
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

Module THREADINTROGENIMPL.
  Export ThreadIntroGen.THREADINTROGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PTHREADINTRO.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PTHREADINTRO.PAlloc)...
    destruct (Q_dec PTHREADINTRO.PFree)...
    destruct (Q_dec PTHREADINTRO.PSetPT)...
    destruct (Q_dec PTHREADINTRO.PPTRead)...
    destruct (Q_dec PTHREADINTRO.PPTResv)...
    destruct (Q_dec PTHREADINTRO.PKCtxtNew)...
    destruct (Q_dec PTHREADINTRO.PPTFree)...
    destruct (Q_dec PTHREADINTRO.PKCtxtSwitch)...
    destruct (Q_dec PTHREADINTRO.PGetState)...
    destruct (Q_dec PTHREADINTRO.PGetPrev)...
    destruct (Q_dec PTHREADINTRO.PGetNext)...
    destruct (Q_dec PTHREADINTRO.PSetState)...
    destruct (Q_dec PTHREADINTRO.PSetPrev)...
    destruct (Q_dec PTHREADINTRO.PSetNext)...
    destruct (Q_dec PTHREADINTRO.PTCBInit)...
    destruct (Q_dec PTHREADINTRO.PPTIn)...
    destruct (Q_dec PTHREADINTRO.PPTOut)...
    destruct (Q_dec PTHREADINTRO.PTrapIn)...
    destruct (Q_dec PTHREADINTRO.PTrapOut)...
    destruct (Q_dec PTHREADINTRO.PHostIn)...
    destruct (Q_dec PTHREADINTRO.PHostOut)...
    destruct (Q_dec PTHREADINTRO.PTrapGet)...
    destruct (Q_dec PTHREADINTRO.PTrapRet)...
    destruct (Q_dec PTHREADINTRO.PPMapInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PTHREADINTRO.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                                          (kern_high:=kern_high) (maxpage:=maxpage)).   
    Notation LDATA := (PKCONTEXT.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).  
  
    Notation Hfundef := (Asm.fundef (external_function:= PTHREADINTRO.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PKCTXTNEW.primOp)).

    Notation funkind := (funkind (low:= PKCTXTNEW.primOp) Asm.code (Clight.fundef (external_function := PKCTXTNEW.primOp))).

    Definition source_implem_extfuns (p: PTHREADINTRO.primOp): funkind :=
      match p with
        | PTHREADINTRO.PAlloc => Code _ (AST.External PKCTXTNEW.PAlloc)
        | PTHREADINTRO.PFree => Code _ (AST.External PKCTXTNEW.PFree)
        | PTHREADINTRO.PSetPT => Code _ (AST.External PKCTXTNEW.PSetPT)
        | PTHREADINTRO.PPTRead => Code _ (AST.External PKCTXTNEW.PPTRead)
        | PTHREADINTRO.PPTResv => Code _ (AST.External PKCTXTNEW.PPTResv)
        | PTHREADINTRO.PKCtxtNew => Code _ (AST.External PKCTXTNEW.PKCtxtNew)
        | PTHREADINTRO.PPTFree => Code _ (AST.External PKCTXTNEW.PPTFree)
        | PTHREADINTRO.PKCtxtSwitch => Code _ (AST.External PKCTXTNEW.PKCtxtSwitch)
        | PTHREADINTRO.PGetState => SourceFun (Clight.Internal PKCONTEXTNEWCODE.f_get_state) (AST.Internal nil)
        | PTHREADINTRO.PGetPrev => SourceFun (Clight.Internal PKCONTEXTNEWCODE.f_get_prev) (AST.Internal nil)
        | PTHREADINTRO.PGetNext => SourceFun (Clight.Internal PKCONTEXTNEWCODE.f_get_next) (AST.Internal nil)
        | PTHREADINTRO.PSetState => SourceFun (Clight.Internal PKCONTEXTNEWCODE.f_set_state) (AST.Internal nil)
        | PTHREADINTRO.PSetPrev => SourceFun (Clight.Internal PKCONTEXTNEWCODE.f_set_prev) (AST.Internal nil)
        | PTHREADINTRO.PSetNext => SourceFun (Clight.Internal PKCONTEXTNEWCODE.f_set_next) (AST.Internal nil)
        | PTHREADINTRO.PTCBInit => SourceFun (Clight.Internal PKCONTEXTNEWCODE.f_tcb_init) (AST.Internal nil)
        | PTHREADINTRO.PPTIn => Code _ (AST.External PKCTXTNEW.PPTIn)
        | PTHREADINTRO.PPTOut => Code _ (AST.External PKCTXTNEW.PPTOut)
        | PTHREADINTRO.PTrapIn => Code _ (AST.External PKCTXTNEW.PTrapIn)
        | PTHREADINTRO.PTrapOut => Code _ (AST.External PKCTXTNEW.PTrapOut)
        | PTHREADINTRO.PHostIn => Code _ (AST.External PKCTXTNEW.PHostIn)
        | PTHREADINTRO.PHostOut => Code _ (AST.External PKCTXTNEW.PHostOut)
        | PTHREADINTRO.PTrapGet => Code _ (AST.External PKCTXTNEW.PTrapGet)
        | PTHREADINTRO.PTrapRet => Code _ (AST.External PKCTXTNEW.PTrapRet)
        | PTHREADINTRO.PPMapInit => Code _ (AST.External PKCTXTNEW.PPMapInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
        (TCBPool_LOC, Some (Gvar (mkglobvar (SourceVar (tarray t_struct_TCB num_proc) tt) ((Init_space (num_proc*12))::nil) false)))
        :: nil.

    Let NOREPET: list_norepet (TCBPool_LOC :: nil).
    Proof.
      case_eq (list_norepet_dec peq (TCBPool_LOC :: nil)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PTHREADINTRO.primOp (low := PKCTXTNEW.primOp) (Clight.fundef (external_function := PKCTXTNEW.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let im : implem Asm.code unit PTHREADINTRO.primOp (low := PKCTXTNEW.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PTHREADINTRO.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PKCTXTNEW.primOp)).

    Let Im_get_state: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINTRO.PGetState).
    Let Im_get_prev: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINTRO.PGetPrev).
    Let Im_get_next: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINTRO.PGetNext).
    Let Im_set_state: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINTRO.PSetState).
    Let Im_set_prev: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINTRO.PSetPrev).
    Let Im_set_next: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINTRO.PSetNext).
    Let Im_tcb_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PTHREADINTRO.PTCBInit).

    Notation new_glbl := (new_glbl (num_proc:= num_proc) TCBPool_LOC).

    Let impl_glbl :  list (ident * option (globdef Lfundef unit)) := nil.

    (* This is basically an axiom that can be easily checked because PTHREADINTRO.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: THREADINTROGEN.transf_program (num_proc:= num_proc)  Im_get_state Im_get_prev Im_get_next Im_set_state Im_set_prev Im_set_next Im_tcb_init TCBPool_LOC impl_glbl prog = OK tprog.
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

    Hypothesis prog_nonempty:
      prog_defs_names prog <> nil.

    Hypothesis prog_main_valid:
      ~ Plt' (prog_main prog) (prog_first_symbol prog).

    Hypothesis prog_first_valid:
      ~ Plt' (prog_first_symbol prog) (get_next_symbol (map fst source_implem_new_globs)).

    Let VALID_LOC: (TCBPool_LOC <> (prog_main prog)).
    Proof.
      intro.
      exploit (get_next_symbol_prop TCBPool_LOC (map fst (source_implem_new_globs))).
      simpl; tauto. 
      eapply Ple_not_Plt.
      apply Ple_Ple'.
      eapply Ple'_trans.
      apply not_Plt'_Ple'.
      eassumption.
      apply not_Plt'_Ple'.
      congruence.
    Qed.       

    Notation ge := (Genv.globalenv prog).
    Notation tge := (Genv.globalenv tprog).
        
    Let NEW_INJ:  (forall s', Genv.find_symbol ge s' <> None -> 
                                     ~ In s' (map fst new_glbl)).
    Proof.
      change new_glbl with (implem_new_globs im).
      eapply new_ids_fresh.
      assumption.
    Qed.

    Let sprog : Clight.program (external_function := PKCTXTNEW.primOp) := source_program_only source_implem prog.
    Let sge := Genv.globalenv sprog.

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
      exploit (transf_clight_fundef_to_program (external_function := PKCTXTNEW.primOp)); eauto.
      unfold sprog in H.
      congruence.
      assumption.
      simpl. destruct 1; try discriminate. destruct H0; try discriminate. 
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
    
    Lemma tcbpool_loc_prop:
      forall b0,
        Genv.find_symbol tge TCBPool_LOC = Some b0 ->
        Genv.find_symbol sge TCBPool_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some (tarray t_struct_TCB num_proc).
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   TCBPool_LOC
                                   (mkglobvar (SourceVar (tarray t_struct_TCB num_proc) tt) ((Init_space (num_proc*12))::nil) false)
                                   _ (refl_equal _) H)).
      destruct 1.
      split; auto.
      unfold Clight.type_of_global.
      unfold sge, sprog.
      rewrite H1.
      reflexivity.
      simpl; tauto.
    Qed.

    Let well_idglob_impl_glbl: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.

    Let TCBPool_LOC_not_in: ~ In TCBPool_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge TCBPool_LOC <> None) by congruence.
      eapply NEW_INJ; eauto.
      simpl; tauto.
    Qed.

    Lemma tprog_first_next:
      prog_first_symbol tprog = get_first_symbol (map fst source_implem_new_globs) /\
      prog_next_symbol  tprog = prog_next_symbol prog.
    Proof.
      change (get_first_symbol (map fst source_implem_new_globs)) with (implem_first_symbol im).
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

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.
      
      Context {mem__H} {mem__L}
              `{Hlmmh: !LayerMemoryModel HDATA mem__H}
              `{Hlmml: !LayerMemoryModel LDATA mem__L}
              `{Hlmi: !LayerMemoryInjections HDATA LDATA _ _}.

      Instance HLayer: LayerDefinition (layer_mem:= Hlmmh) HDATA PTHREADINTRO.primOp mem__H :=
        PTHREADINTRO.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                               (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage)
                               (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                               (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC).
      
      Instance LLayer: LayerDefinition (layer_mem:= Hlmml) LDATA PKCTXTNEW.primOp mem__L :=
        PKCTXTNEW.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                            (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage)
                            (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                            (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC).

      Notation LLoad := (PKCTXTNEW.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PKCTXTNEW.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (PTHREADINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PTHREADINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PKCTXTNEW.step (NPT_LOC:=NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                        (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                        (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                        (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)).

      Notation LADT := PKCONTEXT.ADT.

      Let get_state_spec:
        forall r' b m'0 n b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_state) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TCBPool_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * 12) = Some (Vint r)
          -> 0 <= (Int.unsigned n) < num_proc
          -> PKCONTEXT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint :: nil) (Some Tint)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINTRO.PGetState)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n ::  nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
               /\ Memtype.Mem.inject f' m'0 m0'
               /\ Mem.nextblock m'0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint r)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.          
          exploit tcbpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PTHREADINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PKCTXTNEW.primitive_call)
                     (is_primitive_call := PKCTXTNEW.is_primitive_call)
                     (kernel_mode := PKCONTEXT.kernel_mode)
                  ).
          apply PKCTXTNEW.exec_load_exec_loadex.
          apply PKCTXTNEW.exec_store_exec_storeex.
          apply PKCTXTNEW.extcall_not_primitive.
          apply PKCTXTNEW.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PKCONTEXTNEWCODE.get_state_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PKCONTEXT.kernel_mode.
          destruct (PKCONTEXT.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H21.
          eauto 11.
        Qed.

      Let get_prev_spec:
        forall r' b m'0 n b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_prev) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TCBPool_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * 12 + 4) = Some (Vint r)
          -> 0 <= (Int.unsigned n) < num_proc
          -> PKCONTEXT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint :: nil) (Some Tint)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINTRO.PGetPrev)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n ::  nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
               /\ Memtype.Mem.inject f' m'0 m0'
               /\ Mem.nextblock m'0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint r)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.          
          exploit tcbpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PTHREADINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PKCTXTNEW.primitive_call)
                     (is_primitive_call := PKCTXTNEW.is_primitive_call)
                     (kernel_mode := PKCONTEXT.kernel_mode)
                  ).
          apply PKCTXTNEW.exec_load_exec_loadex.
          apply PKCTXTNEW.exec_store_exec_storeex.
          apply PKCTXTNEW.extcall_not_primitive.
          apply PKCTXTNEW.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PKCONTEXTNEWCODE.get_prev_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PKCONTEXT.kernel_mode.
          destruct (PKCONTEXT.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H21.
          eauto 11.
        Qed.

      Let get_next_spec:
        forall r' b m'0 n b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_next) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TCBPool_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * 12 + 8) = Some (Vint r)
          -> 0 <= (Int.unsigned n) < num_proc
          -> PKCONTEXT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint :: nil) (Some Tint)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINTRO.PGetNext)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n ::  nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
               /\ Memtype.Mem.inject f' m'0 m0'
               /\ Mem.nextblock m'0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sig) = (Vint r)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.          
          exploit tcbpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PTHREADINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PKCTXTNEW.primitive_call)
                     (is_primitive_call := PKCTXTNEW.is_primitive_call)
                     (kernel_mode := PKCONTEXT.kernel_mode)
                  ).
          apply PKCTXTNEW.exec_load_exec_loadex.
          apply PKCTXTNEW.exec_store_exec_storeex.
          apply PKCTXTNEW.extcall_not_primitive.
          apply PKCTXTNEW.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PKCONTEXTNEWCODE.get_next_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PKCONTEXT.kernel_mode.
          destruct (PKCONTEXT.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H21.
          eauto 11.
        Qed.

    Let set_state_spec:
      forall r' b m'0 n b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_state) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TCBPool_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 12) (Vint i) = Some m0
          -> 0 <= Int.unsigned n < num_proc
          -> PKCONTEXT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINTRO.PSetState)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n :: Vint i:: nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'                    
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit tcbpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PTHREADINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PKCTXTNEW.primitive_call)
                 (is_primitive_call := PKCTXTNEW.is_primitive_call)
                 (kernel_mode := PKCONTEXT.kernel_mode)
              ).
      apply PKCTXTNEW.exec_load_exec_loadex.
      apply PKCTXTNEW.exec_store_exec_storeex.
      apply PKCTXTNEW.extcall_not_primitive.
      apply PKCTXTNEW.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PKCONTEXTNEWCODE.set_state_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PKCONTEXT.kernel_mode.
      destruct (PKCONTEXT.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
      eauto 11.
    Qed.

    Let set_prev_spec:
      forall r' b m'0 n b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_prev) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TCBPool_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 12 + 4) (Vint i) = Some m0
          -> 0 <= Int.unsigned n < num_proc
          -> PKCONTEXT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINTRO.PSetPrev)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n :: Vint i:: nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'                    
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit tcbpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PTHREADINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PKCTXTNEW.primitive_call)
                 (is_primitive_call := PKCTXTNEW.is_primitive_call)
                 (kernel_mode := PKCONTEXT.kernel_mode)
              ).
      apply PKCTXTNEW.exec_load_exec_loadex.
      apply PKCTXTNEW.exec_store_exec_storeex.
      apply PKCTXTNEW.extcall_not_primitive.
      apply PKCTXTNEW.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PKCONTEXTNEWCODE.set_prev_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PKCONTEXT.kernel_mode.
      destruct (PKCONTEXT.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
      eauto 11.
    Qed.

    Let set_next_spec:
      forall r' b m'0 n b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_next) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TCBPool_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 12 + 8) (Vint i) = Some m0
          -> 0 <= Int.unsigned n < num_proc
          -> PKCONTEXT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINTRO.PSetNext)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n :: Vint i:: nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'                    
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit tcbpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PTHREADINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PKCTXTNEW.primitive_call)
                 (is_primitive_call := PKCTXTNEW.is_primitive_call)
                 (kernel_mode := PKCONTEXT.kernel_mode)
              ).
      apply PKCTXTNEW.exec_load_exec_loadex.
      apply PKCTXTNEW.exec_store_exec_storeex.
      apply PKCTXTNEW.extcall_not_primitive.
      apply PKCTXTNEW.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PKCONTEXTNEWCODE.set_next_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PKCONTEXT.kernel_mode.
      destruct (PKCONTEXT.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
      eauto 11.
    Qed.

    Let tcb_init_spec:
      forall r' b m'0 n b0 m1 m2 m3 sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_tcb_init) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TCBPool_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 12) (Vint (Int.repr 3)) = Some m1
          -> Mem.store Mint32 m1 b0 (Int.unsigned n * 12 + 4) (Vint (Int.repr num_proc)) = Some m2
          -> Mem.store Mint32 m2 b0 (Int.unsigned n * 12 + 8) (Vint (Int.repr num_proc)) = Some m3
          -> 0 <= Int.unsigned n < num_proc
          -> PKCONTEXT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PKCONTEXT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint :: nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PTHREADINTRO.PTCBInit)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n :: nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m3)) f' 
               /\ Memtype.Mem.inject f' m3 m0'
               /\ Mem.nextblock m3 <= Mem.nextblock m0'                    
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit tcbpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PTHREADINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PKCTXTNEW.primitive_call)
                 (is_primitive_call := PKCTXTNEW.is_primitive_call)
                 (kernel_mode := PKCONTEXT.kernel_mode)
              ).
      apply PKCTXTNEW.exec_load_exec_loadex.
      apply PKCTXTNEW.exec_store_exec_storeex.
      apply PKCTXTNEW.extcall_not_primitive.
      apply PKCTXTNEW.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PKCONTEXTNEWCODE.tcb_init_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PKCONTEXT.kernel_mode.
      destruct (PKCONTEXT.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
      eauto 11.
    Qed.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (PTHREADINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                                  (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmmh) (HPS4:= HPS4) (Hnpc:= Hnpc)
                                  (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                                  (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) prog) 
          (PKCTXTNEW.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                               (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmml) (HPS4:= HPS4) 
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                               (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) tprog).  
    Proof.
      eapply THREADINTROGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
      vm_compute; reflexivity.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End THREADINTROGENIMPL.
