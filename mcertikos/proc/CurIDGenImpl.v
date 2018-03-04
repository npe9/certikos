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
Require Import PCurID.
Require Import PAbQueue.
Require Export CurIDGen.
Require Import PAbQueueCode.
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

Module CURIDGENIMPL.
  Export CurIDGen.CURIDGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PCURID.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PCURID.PAlloc)...
    destruct (Q_dec PCURID.PFree)...
    destruct (Q_dec PCURID.PSetPT)...
    destruct (Q_dec PCURID.PPTRead)...
    destruct (Q_dec PCURID.PPTResv)...
    destruct (Q_dec PCURID.PKCtxtNew)...
    destruct (Q_dec PCURID.PThreadFree)...
    destruct (Q_dec PCURID.PKCtxtSwitch)...
    destruct (Q_dec PCURID.PGetState)...
    destruct (Q_dec PCURID.PSetState)...
    destruct (Q_dec PCURID.PDeQueue)...
    destruct (Q_dec PCURID.PEnQueue)...
    destruct (Q_dec PCURID.PQueueRmv)...
    destruct (Q_dec PCURID.PGetCurID)...
    destruct (Q_dec PCURID.PSetCurID)...
    destruct (Q_dec PCURID.PPTIn)...
    destruct (Q_dec PCURID.PPTOut)...
    destruct (Q_dec PCURID.PTrapIn)...
    destruct (Q_dec PCURID.PTrapOut)...
    destruct (Q_dec PCURID.PHostIn)...
    destruct (Q_dec PCURID.PHostOut)...
    destruct (Q_dec PCURID.PTrapGet)...
    destruct (Q_dec PCURID.PTrapRet)...
    destruct (Q_dec PCURID.PTDQueueInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PCURID.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                                    (kern_high:=kern_high) (maxpage:=maxpage) (num_chan := num_chan)).   
    Notation LDATA := (PABQUEUE.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                      (kern_high:=kern_high) (maxpage:=maxpage) (num_chan := num_chan)).                             
  
    Notation Hfundef := (Asm.fundef (external_function:= PCURID.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PABQUEUE.primOp)).

    Notation funkind := (funkind (low:= PABQUEUE.primOp) Asm.code (Clight.fundef (external_function := PABQUEUE.primOp))).

    Definition source_implem_extfuns (p: PCURID.primOp): funkind :=
      match p with
        | PCURID.PAlloc => Code _ (AST.External PABQUEUE.PAlloc)
        | PCURID.PFree => Code _ (AST.External PABQUEUE.PFree)
        | PCURID.PSetPT => Code _ (AST.External PABQUEUE.PSetPT)
        | PCURID.PPTRead => Code _ (AST.External PABQUEUE.PPTRead)
        | PCURID.PPTResv => Code _ (AST.External PABQUEUE.PPTResv)
        | PCURID.PKCtxtNew => Code _ (AST.External PABQUEUE.PKCtxtNew)
        | PCURID.PThreadFree => Code _ (AST.External PABQUEUE.PThreadFree)
        | PCURID.PKCtxtSwitch => Code _ (AST.External PABQUEUE.PKCtxtSwitch)
        | PCURID.PGetState => Code _ (AST.External PABQUEUE.PGetState)
        | PCURID.PSetState => Code _ (AST.External PABQUEUE.PSetState)
        | PCURID.PDeQueue => Code _ (AST.External PABQUEUE.PDeQueue)
        | PCURID.PEnQueue => Code _ (AST.External PABQUEUE.PEnQueue)
        | PCURID.PQueueRmv => Code _ (AST.External PABQUEUE.PQueueRmv)
        | PCURID.PGetCurID => SourceFun (Clight.Internal PABQUEUECODE.f_get_curid) (AST.Internal nil)
        | PCURID.PSetCurID => SourceFun (Clight.Internal PABQUEUECODE.f_set_curid) (AST.Internal nil)
        | PCURID.PPTIn => Code _ (AST.External PABQUEUE.PPTIn)
        | PCURID.PPTOut => Code _ (AST.External PABQUEUE.PPTOut)
        | PCURID.PTrapIn => Code _ (AST.External PABQUEUE.PTrapIn)
        | PCURID.PTrapOut => Code _ (AST.External PABQUEUE.PTrapOut)
        | PCURID.PHostIn => Code _ (AST.External PABQUEUE.PHostIn)
        | PCURID.PHostOut => Code _ (AST.External PABQUEUE.PHostOut)
        | PCURID.PTrapGet => Code _ (AST.External PABQUEUE.PTrapGet)
        | PCURID.PTrapRet => Code _ (AST.External PABQUEUE.PTrapRet)
        | PCURID.PTDQueueInit => Code _ (AST.External PABQUEUE.PTDQueueInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
        (CURID_LOC, Some (Gvar (mkglobvar (SourceVar tint tt) (wrap_init_data 1) false)))
        :: nil.

    Let NOREPET: list_norepet (CURID_LOC :: nil).
    Proof.
      case_eq (list_norepet_dec peq (CURID_LOC :: nil)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PCURID.primOp (low := PABQUEUE.primOp) (Clight.fundef (external_function := PABQUEUE.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let im : implem Asm.code unit PCURID.primOp (low := PABQUEUE.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PCURID.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PABQUEUE.primOp)).

    Let Im_get_curid: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PCURID.PGetCurID).
    Let Im_set_curid: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PCURID.PSetCurID).

    Notation new_glbl := (new_glbl CURID_LOC).

    Let impl_glbl :  list (ident * option (globdef Lfundef unit)) := nil.

    (* This is basically an axiom that can be easily checked because PCURID.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: CURIDGEN.transf_program Im_get_curid Im_set_curid CURID_LOC impl_glbl prog = OK tprog.
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

    Let VALID_LOC: (CURID_LOC <> (prog_main prog)).
    Proof.
      intro.
      exploit (get_next_symbol_prop CURID_LOC (map fst (source_implem_new_globs))).
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

    Let sprog : Clight.program (external_function := PABQUEUE.primOp) := source_program_only source_implem prog.
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
      exploit (transf_clight_fundef_to_program (external_function := PABQUEUE.primOp)); eauto.
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
    
    Lemma curid_loc_prop:
      forall b0,
        Genv.find_symbol tge CURID_LOC = Some b0 ->
        Genv.find_symbol sge CURID_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some tint.
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   CURID_LOC
                                   (mkglobvar (SourceVar tint tt) (wrap_init_data 1) false)
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

    Let CURID_LOC_not_in: ~ In CURID_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge CURID_LOC <> None) by congruence.
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
      
      Local Instance HdataOp:AbstractDataOps HDATA:= (PCURID.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{Hlmmh: !LayerMemoryModel HDATA mem__H}
              `{Hlmml: !LayerMemoryModel LDATA mem__L}
              `{Hlmi: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= Hlmmh) HDATA PCURID.primOp mem__H :=
        PCURID.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                         (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_abtcb := real_abtcb)
                         (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                         (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                         (num_chan:= num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).
      
      Instance LLayer: LayerDefinition (layer_mem:= Hlmml) LDATA PABQUEUE.primOp mem__L :=
        PABQUEUE.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                           (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_abtcb := real_abtcb)
                           (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                           (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                           (num_chan:= num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).    

      Notation LLoad := (PABQUEUE.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PABQUEUE.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (PCURID.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PCURID.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PABQUEUE.step (NPT_LOC:=NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                       (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                       (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                       (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(real_abtcb:=real_abtcb)
                                       (Hnchan := Hnchan) (real_abq:= real_abq)).

      Notation LADT := PABQUEUE.ADT.

      Let get_curid_spec:
        forall r' b m'0 b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_curid)
          -> Genv.find_funct_ptr ge b = Some (External PCURID.PGetCurID)
          -> Genv.find_symbol tge CURID_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 0 = Some (Vint r)
          -> PABQUEUE.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> PABQUEUE.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PABQUEUE.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature nil (Some Tint)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig nil                     
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
          exploit curid_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PCURID.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PABQUEUE.primitive_call)
                     (is_primitive_call := PABQUEUE.is_primitive_call)
                     (kernel_mode := PABQUEUE.kernel_mode)
                  ).
          apply PABQUEUE.exec_load_exec_loadex.
          apply PABQUEUE.exec_store_exec_storeex.
          apply PABQUEUE.extcall_not_primitive.
          apply PABQUEUE.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PABQUEUECODE.get_curid_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PABQUEUE.kernel_mode.
          destruct (PABQUEUE.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H20.
          eauto 11.
        Qed.

    Let set_curid_spec:
      forall r' b m'0 b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_curid)
          -> Genv.find_funct_ptr ge b = Some (External PCURID.PSetCurID)
          -> Genv.find_symbol tge CURID_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 0 (Vint i) = Some m0
          -> PABQUEUE.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> PABQUEUE.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PABQUEUE.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint::nil) None
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint i:: nil)                     
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
      exploit curid_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PCURID.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := PABQUEUE.primitive_call)
                 (is_primitive_call := PABQUEUE.is_primitive_call)
                 (kernel_mode := PABQUEUE.kernel_mode)
              ).
      apply PABQUEUE.exec_load_exec_loadex.
      apply PABQUEUE.exec_store_exec_storeex.
      apply PABQUEUE.extcall_not_primitive.
      apply PABQUEUE.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply PABQUEUECODE.set_curid_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold PABQUEUE.kernel_mode.
      destruct (PABQUEUE.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
      eauto 11.
    Qed.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (PCURID.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                            (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmmh) (HPS4:= HPS4) (Hnpc:= Hnpc)
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abq:= real_abq)
                            (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                            (num_chan:= num_chan) (real_abtcb:= real_abtcb) (Hnchan:= Hnchan) prog) 
          (PABQUEUE.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                              (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmml) (HPS4:= HPS4) 
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt)
                              (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                              (real_abtcb:= real_abtcb) (Hnchan:= Hnchan) (real_abq:= real_abq) tprog).
    Proof.
      eapply CURIDGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End CURIDGENIMPL.
