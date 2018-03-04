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
Require Import PQueueIntro.
Require Import PThreadInit.
Require Export QueueIntroGen.
Require Import PThreadInitCode.
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

Module QUEUEINTROGENIMPL.
  Export QueueIntroGen.QUEUEINTROGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PQUEUEINTRO.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PQUEUEINTRO.PAlloc)...
    destruct (Q_dec PQUEUEINTRO.PFree)...
    destruct (Q_dec PQUEUEINTRO.PSetPT)...
    destruct (Q_dec PQUEUEINTRO.PPTRead)...
    destruct (Q_dec PQUEUEINTRO.PPTResv)...
    destruct (Q_dec PQUEUEINTRO.PKCtxtNew)...
    destruct (Q_dec PQUEUEINTRO.PThreadFree)...
    destruct (Q_dec PQUEUEINTRO.PKCtxtSwitch)...
    destruct (Q_dec PQUEUEINTRO.PGetState)...
    destruct (Q_dec PQUEUEINTRO.PGetPrev)...
    destruct (Q_dec PQUEUEINTRO.PGetNext)...
    destruct (Q_dec PQUEUEINTRO.PSetState)...
    destruct (Q_dec PQUEUEINTRO.PSetPrev)...
    destruct (Q_dec PQUEUEINTRO.PSetNext)...
    destruct (Q_dec PQUEUEINTRO.PGetHead)...
    destruct (Q_dec PQUEUEINTRO.PGetTail)...
    destruct (Q_dec PQUEUEINTRO.PSetHead)...
    destruct (Q_dec PQUEUEINTRO.PSetTail)...
    destruct (Q_dec PQUEUEINTRO.PTDQInit)...
    destruct (Q_dec PQUEUEINTRO.PPTIn)...
    destruct (Q_dec PQUEUEINTRO.PPTOut)...
    destruct (Q_dec PQUEUEINTRO.PTrapIn)...
    destruct (Q_dec PQUEUEINTRO.PTrapOut)...
    destruct (Q_dec PQUEUEINTRO.PHostIn)...
    destruct (Q_dec PQUEUEINTRO.PHostOut)...
    destruct (Q_dec PQUEUEINTRO.PTrapGet)...
    destruct (Q_dec PQUEUEINTRO.PTrapRet)...
    destruct (Q_dec PQUEUEINTRO.PThreadInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PQUEUEINTRO.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                                         (kern_high:=kern_high) (maxpage:=maxpage)).   
    Notation LDATA := (PTHREADINIT.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                         (kern_high:=kern_high) (maxpage:=maxpage)).                             
  
    Notation Hfundef := (Asm.fundef (external_function:= PQUEUEINTRO.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PTHREADINIT.primOp)).

    Notation funkind := (funkind (low:= PTHREADINIT.primOp) Asm.code (Clight.fundef (external_function := PTHREADINIT.primOp))).

    Definition source_implem_extfuns (p: PQUEUEINTRO.primOp): funkind :=
      match p with
        | PQUEUEINTRO.PAlloc => Code _ (AST.External PTHREADINIT.PAlloc)
        | PQUEUEINTRO.PFree => Code _ (AST.External PTHREADINIT.PFree)
        | PQUEUEINTRO.PSetPT => Code _ (AST.External PTHREADINIT.PSetPT)
        | PQUEUEINTRO.PPTRead => Code _ (AST.External PTHREADINIT.PPTRead)
        | PQUEUEINTRO.PPTResv => Code _ (AST.External PTHREADINIT.PPTResv)
        | PQUEUEINTRO.PKCtxtNew => Code _ (AST.External PTHREADINIT.PKCtxtNew)
        | PQUEUEINTRO.PThreadFree => Code _ (AST.External PTHREADINIT.PThreadFree)
        | PQUEUEINTRO.PKCtxtSwitch => Code _ (AST.External PTHREADINIT.PKCtxtSwitch)
        | PQUEUEINTRO.PGetState => Code _ (AST.External PTHREADINIT.PGetState)
        | PQUEUEINTRO.PGetPrev => Code _ (AST.External PTHREADINIT.PGetPrev)
        | PQUEUEINTRO.PGetNext => Code _ (AST.External PTHREADINIT.PGetNext)
        | PQUEUEINTRO.PSetState => Code _ (AST.External PTHREADINIT.PSetState)
        | PQUEUEINTRO.PSetPrev => Code _ (AST.External PTHREADINIT.PSetPrev)
        | PQUEUEINTRO.PSetNext => Code _ (AST.External PTHREADINIT.PSetNext)
        | PQUEUEINTRO.PGetHead => SourceFun (Clight.Internal PTHREADINITCODE.f_get_head) (AST.Internal nil)
        | PQUEUEINTRO.PGetTail => SourceFun (Clight.Internal PTHREADINITCODE.f_get_tail) (AST.Internal nil)
        | PQUEUEINTRO.PSetHead => SourceFun (Clight.Internal PTHREADINITCODE.f_set_head) (AST.Internal nil)
        | PQUEUEINTRO.PSetTail => SourceFun (Clight.Internal PTHREADINITCODE.f_set_tail) (AST.Internal nil)
        | PQUEUEINTRO.PTDQInit => SourceFun (Clight.Internal PTHREADINITCODE.f_tdq_init) (AST.Internal nil)
        | PQUEUEINTRO.PPTIn => Code _ (AST.External PTHREADINIT.PPTIn)
        | PQUEUEINTRO.PPTOut => Code _ (AST.External PTHREADINIT.PPTOut)
        | PQUEUEINTRO.PTrapIn => Code _ (AST.External PTHREADINIT.PTrapIn)
        | PQUEUEINTRO.PTrapOut => Code _ (AST.External PTHREADINIT.PTrapOut)
        | PQUEUEINTRO.PHostIn => Code _ (AST.External PTHREADINIT.PHostIn)
        | PQUEUEINTRO.PHostOut => Code _ (AST.External PTHREADINIT.PHostOut)
        | PQUEUEINTRO.PTrapGet => Code _ (AST.External PTHREADINIT.PTrapGet)
        | PQUEUEINTRO.PTrapRet => Code _ (AST.External PTHREADINIT.PTrapRet)
        | PQUEUEINTRO.PThreadInit => Code _ (AST.External PTHREADINIT.PThreadInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
        (TDQPool_LOC, Some (Gvar (mkglobvar (SourceVar (tarray t_struct_TDQ (num_chan+1)) tt) ((Init_space ((num_chan+1)*8))::nil) false)))
        :: nil.

    Let NOREPET: list_norepet (TDQPool_LOC :: nil).
    Proof.
      case_eq (list_norepet_dec peq (TDQPool_LOC :: nil)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PQUEUEINTRO.primOp (low := PTHREADINIT.primOp) (Clight.fundef (external_function := PTHREADINIT.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let im : implem Asm.code unit PQUEUEINTRO.primOp (low := PTHREADINIT.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PQUEUEINTRO.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PTHREADINIT.primOp)).

    Let Im_get_head: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINTRO.PGetHead).
    Let Im_get_tail: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINTRO.PGetTail).
    Let Im_set_head: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINTRO.PSetHead).
    Let Im_set_tail: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINTRO.PSetTail).
    Let Im_tdq_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PQUEUEINTRO.PTDQInit).

    Notation new_glbl := (new_glbl (num_chan:= num_chan) TDQPool_LOC).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) := nil.

    (* This is basically an axiom that can be easily checked because PQUEUEINTRO.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: QUEUEINTROGEN.transf_program (num_chan:= num_chan) Im_get_head Im_get_tail Im_set_head Im_set_tail Im_tdq_init TDQPool_LOC impl_glbl prog = OK tprog.
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

    Let VALID_LOC: (TDQPool_LOC <> (prog_main prog)).
    Proof.
      intro.
      exploit (get_next_symbol_prop TDQPool_LOC (map fst (source_implem_new_globs))).
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

    Let sprog : Clight.program (external_function := PTHREADINIT.primOp) := source_program_only source_implem prog.
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
      exploit (transf_clight_fundef_to_program (external_function := PTHREADINIT.primOp)); eauto.
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
    
    Lemma tdqpool_loc_prop:
      forall b0,
        Genv.find_symbol tge TDQPool_LOC = Some b0 ->
        Genv.find_symbol sge TDQPool_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some (tarray t_struct_TDQ (num_chan+1)).
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   TDQPool_LOC
                                   (mkglobvar (SourceVar (tarray t_struct_TDQ (num_chan+1)) tt) ((Init_space ((num_chan+1)*8))::nil) false)
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

    Let TDQPool_LOC_not_in: ~ In TDQPool_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge TDQPool_LOC <> None) by congruence.
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

      Instance HLayer: LayerDefinition (layer_mem:= Hlmmh) HDATA PQUEUEINTRO.primOp mem__H :=
        PQUEUEINTRO.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                              (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_tcb := real_tcb)
                              (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                              (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                              (num_chan:= num_chan).
      
      Instance LLayer: LayerDefinition (layer_mem:= Hlmml) LDATA PTHREADINIT.primOp mem__L :=
        PTHREADINIT.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                              (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_tcb := real_tcb)
                              (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                              (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC). 

      Notation LLoad := (PTHREADINIT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PTHREADINIT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (PQUEUEINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PQUEUEINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PTHREADINIT.step (NPT_LOC:=NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                          (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                          (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                          (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(real_tcb:=real_tcb)).

      Notation LADT := PTHREADINIT.ADT.

      Let get_head_spec:
        forall r' b m'0 n b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_head)
          -> Genv.find_symbol tge TDQPool_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * 8) = Some (Vint r)
          -> 0 <= (Int.unsigned n) <= num_chan
          -> PTHREADINIT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint :: nil) (Some Tint)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINTRO.PGetHead)
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
          exploit tdqpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PQUEUEINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREADINIT.primitive_call)
                     (is_primitive_call := PTHREADINIT.is_primitive_call)
                     (kernel_mode := PTHREADINIT.kernel_mode)
                  ).
          apply PTHREADINIT.exec_load_exec_loadex.
          apply PTHREADINIT.exec_store_exec_storeex.
          apply PTHREADINIT.extcall_not_primitive.
          apply PTHREADINIT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADINITCODE.get_head_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREADINIT.kernel_mode.
          destruct (PTHREADINIT.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H21.
          eauto 11.
        Qed.

      Let get_tail_spec:
        forall r' b m'0 n b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_tail)
          -> Genv.find_symbol tge TDQPool_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * 8 + 4) = Some (Vint r)
          -> 0 <= (Int.unsigned n) <= num_chan
          -> PTHREADINIT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint :: nil) (Some Tint)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINTRO.PGetTail)
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
          exploit tdqpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PQUEUEINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREADINIT.primitive_call)
                     (is_primitive_call := PTHREADINIT.is_primitive_call)
                     (kernel_mode := PTHREADINIT.kernel_mode)
                  ).
          apply PTHREADINIT.exec_load_exec_loadex.
          apply PTHREADINIT.exec_store_exec_storeex.
          apply PTHREADINIT.extcall_not_primitive.
          apply PTHREADINIT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADINITCODE.get_tail_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREADINIT.kernel_mode.
          destruct (PTHREADINIT.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H21.
          eauto 11.
        Qed.

    Let set_head_spec:
      forall r' b m'0 n b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_head) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TDQPool_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 8) (Vint i) = Some m0
          -> 0 <= Int.unsigned n <= num_chan
          -> PTHREADINIT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINTRO.PSetHead)
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
      exploit tdqpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PQUEUEINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PTHREADINIT.primitive_call)
                 (is_primitive_call := PTHREADINIT.is_primitive_call)
                 (kernel_mode := PTHREADINIT.kernel_mode)
              ).
      apply PTHREADINIT.exec_load_exec_loadex.
      apply PTHREADINIT.exec_store_exec_storeex.
      apply PTHREADINIT.extcall_not_primitive.
      apply PTHREADINIT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PTHREADINITCODE.set_head_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PTHREADINIT.kernel_mode.
      destruct (PTHREADINIT.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
      eauto 11.
    Qed.

    Let set_tail_spec:
      forall r' b m'0 n b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_tail) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge TDQPool_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 8 + 4) (Vint i) = Some m0
          -> 0 <= Int.unsigned n <= num_chan
          -> PTHREADINIT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint :: Tint :: nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINTRO.PSetTail)
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
      exploit tdqpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PQUEUEINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PTHREADINIT.primitive_call)
                 (is_primitive_call := PTHREADINIT.is_primitive_call)
                 (kernel_mode := PTHREADINIT.kernel_mode)
              ).
      apply PTHREADINIT.exec_load_exec_loadex.
      apply PTHREADINIT.exec_store_exec_storeex.
      apply PTHREADINIT.extcall_not_primitive.
      apply PTHREADINIT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PTHREADINITCODE.set_tail_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PTHREADINIT.kernel_mode.
      destruct (PTHREADINIT.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
      eauto 11.
    Qed.

    Let tcb_init_spec:
      forall r' b m'0 n b0 m1 m2 sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_tdq_init)
          -> Genv.find_symbol tge TDQPool_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 8) (Vint (Int.repr num_proc)) = Some m1
          -> Mem.store Mint32 m1 b0 (Int.unsigned n * 8 + 4) (Vint (Int.repr num_proc)) = Some m2
          -> 0 <= Int.unsigned n <= num_chan
          -> PTHREADINIT.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREADINIT.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint :: nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PQUEUEINTRO.PTDQInit)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n :: nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m2)) f' 
               /\ Memtype.Mem.inject f' m2 m0'
               /\ Mem.nextblock m2 <= Mem.nextblock m0'
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit tdqpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PQUEUEINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PTHREADINIT.primitive_call)
                 (is_primitive_call := PTHREADINIT.is_primitive_call)
                 (kernel_mode := PTHREADINIT.kernel_mode)
              ).
      apply PTHREADINIT.exec_load_exec_loadex.
      apply PTHREADINIT.exec_store_exec_storeex.
      apply PTHREADINIT.extcall_not_primitive.
      apply PTHREADINIT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PTHREADINITCODE.tdq_init_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PTHREADINIT.kernel_mode.
      destruct (PTHREADINIT.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
      eauto 11.
    Qed.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (PQUEUEINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                                 (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmmh) (HPS4:= HPS4) (Hnpc:= Hnpc)
                                 (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                                 (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                                 (num_chan:= num_chan) (real_tcb:= real_tcb) prog) 
          (PTHREADINIT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                                 (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmml) (HPS4:= HPS4) 
                                 (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt)
                                 (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                                 (real_tcb:= real_tcb) tprog).  
    Proof.
      eapply QUEUEINTROGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
      vm_compute; reflexivity.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End QUEUEINTROGENIMPL.
