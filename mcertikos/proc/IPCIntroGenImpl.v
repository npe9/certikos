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
Require Import PIPCIntro.
Require Import PThread.
Require Export IPCIntroGen.
Require Import PThreadCode.
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

Module IPCINTROGENIMPL.
  Export IPCIntroGen.IPCINTROGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PIPCINTRO.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PIPCINTRO.PAlloc)...
    destruct (Q_dec PIPCINTRO.PFree)...
    destruct (Q_dec PIPCINTRO.PSetPT)...
    destruct (Q_dec PIPCINTRO.PPTRead)...
    destruct (Q_dec PIPCINTRO.PPTResv)...
    destruct (Q_dec PIPCINTRO.PThreadSpawn)...
    destruct (Q_dec PIPCINTRO.PThreadKill)...
    destruct (Q_dec PIPCINTRO.PThreadWakeup)...
    destruct (Q_dec PIPCINTRO.PThreadYield)...
    destruct (Q_dec PIPCINTRO.PThreadSleep)...
    destruct (Q_dec PIPCINTRO.PGetCurID)...
    destruct (Q_dec PIPCINTRO.PPTIn)...
    destruct (Q_dec PIPCINTRO.PPTOut)...
    destruct (Q_dec PIPCINTRO.PTrapIn)...
    destruct (Q_dec PIPCINTRO.PTrapOut)...
    destruct (Q_dec PIPCINTRO.PHostIn)...
    destruct (Q_dec PIPCINTRO.PHostOut)...
    destruct (Q_dec PIPCINTRO.PTrapGet)...
    destruct (Q_dec PIPCINTRO.PTrapRet)...
    destruct (Q_dec PIPCINTRO.PGetChanInfo)...
    destruct (Q_dec PIPCINTRO.PGetChanContent)...
    destruct (Q_dec PIPCINTRO.PSetChanInfo)...
    destruct (Q_dec PIPCINTRO.PSetChanContent)...
    destruct (Q_dec PIPCINTRO.PInitChan)...
    destruct (Q_dec PIPCINTRO.PSchedInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PIPCINTRO.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                                       (kern_high:=kern_high) (maxpage:=maxpage) (num_chan:= num_chan)).   
    Notation LDATA := (PTHREAD.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                     (kern_high:=kern_high) (maxpage:=maxpage) (num_chan:= num_chan)).                            
  
    Notation Hfundef := (Asm.fundef (external_function:= PIPCINTRO.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PTHREAD.primOp)).

    Notation funkind := (funkind (low:= PTHREAD.primOp) Asm.code (Clight.fundef (external_function := PTHREAD.primOp))).

    Definition source_implem_extfuns (p: PIPCINTRO.primOp): funkind :=
      match p with
        | PIPCINTRO.PAlloc => Code _ (AST.External PTHREAD.PAlloc)
        | PIPCINTRO.PFree => Code _ (AST.External PTHREAD.PFree)
        | PIPCINTRO.PSetPT => Code _ (AST.External PTHREAD.PSetPT)
        | PIPCINTRO.PPTRead => Code _ (AST.External PTHREAD.PPTRead)
        | PIPCINTRO.PPTResv => Code _ (AST.External PTHREAD.PPTResv)
        | PIPCINTRO.PThreadSpawn => Code _ (AST.External PTHREAD.PThreadSpawn)
        | PIPCINTRO.PThreadKill => Code _ (AST.External PTHREAD.PThreadKill)
        | PIPCINTRO.PThreadWakeup => Code _ (AST.External PTHREAD.PThreadWakeup)
        | PIPCINTRO.PThreadYield => Code _ (AST.External PTHREAD.PThreadYield)
        | PIPCINTRO.PThreadSleep => Code _ (AST.External PTHREAD.PThreadSleep)
        | PIPCINTRO.PGetCurID => Code _ (AST.External PTHREAD.PGetCurID)
        | PIPCINTRO.PPTIn => Code _ (AST.External PTHREAD.PPTIn)
        | PIPCINTRO.PPTOut => Code _ (AST.External PTHREAD.PPTOut)
        | PIPCINTRO.PTrapIn => Code _ (AST.External PTHREAD.PTrapIn)
        | PIPCINTRO.PTrapOut => Code _ (AST.External PTHREAD.PTrapOut)
        | PIPCINTRO.PHostIn => Code _ (AST.External PTHREAD.PHostIn)
        | PIPCINTRO.PHostOut => Code _ (AST.External PTHREAD.PHostOut)
        | PIPCINTRO.PTrapGet => Code _ (AST.External PTHREAD.PTrapGet)
        | PIPCINTRO.PTrapRet => Code _ (AST.External PTHREAD.PTrapRet)
        | PIPCINTRO.PGetChanInfo => SourceFun (Clight.Internal PTHREADCODE.f_get_chan_info) (AST.Internal nil)
        | PIPCINTRO.PGetChanContent => SourceFun (Clight.Internal PTHREADCODE.f_get_chan_content) (AST.Internal nil)
        | PIPCINTRO.PSetChanInfo => SourceFun (Clight.Internal PTHREADCODE.f_set_chan_info) (AST.Internal nil)
        | PIPCINTRO.PSetChanContent => SourceFun (Clight.Internal PTHREADCODE.f_set_chan_content) (AST.Internal nil)
        | PIPCINTRO.PInitChan => SourceFun (Clight.Internal PTHREADCODE.f_init_chan) (AST.Internal nil)
        | PIPCINTRO.PSchedInit => Code _ (AST.External PTHREAD.PSchedInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
        (CHPOOL_LOC, Some (Gvar (mkglobvar (SourceVar (tarray t_struct_Chan num_chan) tt) ((Init_space (num_chan*8))::nil) false)))
        :: nil.

    Let NOREPET: list_norepet (CHPOOL_LOC :: nil).
    Proof.
      case_eq (list_norepet_dec peq (CHPOOL_LOC :: nil)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PIPCINTRO.primOp (low := PTHREAD.primOp) (Clight.fundef (external_function := PTHREAD.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let im : implem Asm.code unit PIPCINTRO.primOp (low := PTHREAD.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PIPCINTRO.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PTHREAD.primOp)).

    Let Im_get_chan_info: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPCINTRO.PGetChanInfo).
    Let Im_get_chan_content: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPCINTRO.PGetChanContent).
    Let Im_set_chan_info: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPCINTRO.PSetChanInfo).
    Let Im_set_chan_content: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPCINTRO.PSetChanContent).
    Let Im_init_chan: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PIPCINTRO.PInitChan).

    Notation new_glbl := (new_glbl (num_chan:= num_chan) CHPOOL_LOC).

    Let impl_glbl :  list (ident * option (globdef Lfundef unit)) := nil.

    (* This is basically an axiom that can be easily checked because PIPCINTRO.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: IPCINTROGEN.transf_program (num_chan:= num_chan) Im_get_chan_info Im_get_chan_content Im_set_chan_info Im_set_chan_content Im_init_chan CHPOOL_LOC impl_glbl prog = OK tprog.
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

    Let VALID_LOC: (CHPOOL_LOC <> (prog_main prog)).
    Proof.
      intro.
      exploit (get_next_symbol_prop CHPOOL_LOC (map fst (source_implem_new_globs))).
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

    Let sprog : Clight.program (external_function := PTHREAD.primOp) := source_program_only source_implem prog.
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
      exploit (transf_clight_fundef_to_program (external_function := PTHREAD.primOp)); eauto.
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
    
    Lemma chpool_loc_prop:
      forall b0,
        Genv.find_symbol tge CHPOOL_LOC = Some b0 ->
        Genv.find_symbol sge CHPOOL_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some (tarray t_struct_Chan num_chan).
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   CHPOOL_LOC
                                   (mkglobvar (SourceVar (tarray t_struct_Chan num_chan) tt) ((Init_space (num_chan*8))::nil) false)
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

    Let CHPOOL_LOC_not_in: ~ In CHPOOL_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge CHPOOL_LOC <> None) by congruence.
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
      
      Local Instance HdataOp:AbstractDataOps HDATA:= (PIPCINTRO.abstract_data (Hnpc:= Hnpc)).
      Local Instance LdataOp:AbstractDataOps LDATA:= (PTHREAD.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{Hlmmh: !LayerMemoryModel HDATA mem__H}
              `{Hlmml: !LayerMemoryModel LDATA mem__L}
              `{Hlmi: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= Hlmmh) HDATA PIPCINTRO.primOp mem__H :=
        PIPCINTRO.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                            (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_abtcb := real_abtcb)
                            (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                            (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                            (num_chan:= num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).
      
      Instance LLayer: LayerDefinition (layer_mem:= Hlmml) LDATA PTHREAD.primOp mem__L :=
        PTHREAD.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                          (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_abtcb := real_abtcb)
                          (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                          (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                          (num_chan:= num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).        

      Notation LLoad := (PTHREAD.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PTHREAD.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (PIPCINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PIPCINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PTHREAD.step (NPT_LOC:=NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                      (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                      (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                      (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(real_abtcb:=real_abtcb)
                                      (Hnchan := Hnchan) (real_abq:= real_abq)).

      Notation LADT := PTHREAD.ADT.

      Let get_chan_info_spec:
        forall r' b m'0 n b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_chan_info) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PIPCINTRO.PGetChanInfo)
          -> Genv.find_symbol tge CHPOOL_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * 8) = Some (Vint r)
          -> 0 <= (Int.unsigned n) < num_chan
          -> PTHREAD.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint::nil) (Some Tint)
          -> extcall_arguments r' m'0 sig (Vint n ::nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
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
          exploit chpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPCINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREAD.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PTHREAD.is_primitive_call)
                     (kernel_mode := PTHREAD.kernel_mode)
                  ).
          apply PTHREAD.exec_load_exec_loadex.
          apply PTHREAD.exec_store_exec_storeex.
          apply PTHREAD.extcall_not_primitive.
          apply PTHREAD.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADCODE.get_chan_info_correct; eauto.
          omega.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREAD.kernel_mode.
          destruct (PTHREAD.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H21.
          eauto 11.
        Qed.

      Let get_chan_content_spec:
        forall r' b m'0 n b1 r sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_get_chan_content) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PIPCINTRO.PGetChanContent)
          -> Genv.find_symbol tge CHPOOL_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * 8 + 4) = Some (Vint r)
          -> 0 <= (Int.unsigned n) < num_chan
          -> PTHREAD.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint::nil) (Some Tint)
          -> extcall_arguments r' m'0 sig (Vint n ::nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
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
          exploit chpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPCINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREAD.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PTHREAD.is_primitive_call)
                     (kernel_mode := PTHREAD.kernel_mode)
                  ).
          apply PTHREAD.exec_load_exec_loadex.
          apply PTHREAD.exec_store_exec_storeex.
          apply PTHREAD.extcall_not_primitive.
          apply PTHREAD.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADCODE.get_chan_content_correct; eauto.
          omega.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREAD.kernel_mode.
          destruct (PTHREAD.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H21.
          eauto 11.
        Qed.

      Let set_chan_info_spec:
        forall r' b m'0 n b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_chan_info) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PIPCINTRO.PSetChanInfo)
          -> Genv.find_symbol tge CHPOOL_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 8) (Vint i) = Some m0
          -> 0 <= Int.unsigned n < num_chan
          -> PTHREAD.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint::Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vint n :: Vint i:: nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
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
          exploit chpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPCINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREAD.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PTHREAD.is_primitive_call)
                     (kernel_mode := PTHREAD.kernel_mode)
                  ).
          apply PTHREAD.exec_load_exec_loadex.
          apply PTHREAD.exec_store_exec_storeex.
          apply PTHREAD.extcall_not_primitive.
          apply PTHREAD.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADCODE.set_chan_info_correct; eauto.
          omega.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREAD.kernel_mode.
          destruct (PTHREAD.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
          eauto 11.
        Qed.

      Let set_chan_content_spec:
        forall r' b m'0 n b0 m0 i sig,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_set_chan_content) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PIPCINTRO.PSetChanContent)
          -> Genv.find_symbol tge CHPOOL_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 8 + 4) (Vint i) = Some m0
          -> 0 <= Int.unsigned n < num_chan
          -> PTHREAD.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint::Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vint n :: Vint i:: nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
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
          exploit chpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPCINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREAD.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PTHREAD.is_primitive_call)
                     (kernel_mode := PTHREAD.kernel_mode)
                  ).
          apply PTHREAD.exec_load_exec_loadex.
          apply PTHREAD.exec_store_exec_storeex.
          apply PTHREAD.extcall_not_primitive.
          apply PTHREAD.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADCODE.set_chan_content_correct; eauto.
          omega.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREAD.kernel_mode.
          destruct (PTHREAD.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
          eauto 11.
        Qed.

      Let init_chan_spec:
        forall r' b m'0 n b0 m1 m2 sig v1 v2,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_init_chan) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PIPCINTRO.PInitChan)
          -> Genv.find_symbol tge CHPOOL_LOC = Some b0
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 8) (Vint v1) = Some m1
          -> Mem.store Mint32 m1 b0 (Int.unsigned n * 8 + 4) (Vint v2) = Some m2
          -> 0 <= Int.unsigned n < num_chan
          -> PTHREAD.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PTHREAD.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> sig = mksignature (Tint::Tint::Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vint n :: Vint v1:: Vint v2::nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
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
          exploit chpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PIPCINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PTHREAD.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PTHREAD.is_primitive_call)
                     (kernel_mode := PTHREAD.kernel_mode)
                  ).
          apply PTHREAD.exec_load_exec_loadex.
          apply PTHREAD.exec_store_exec_storeex.
          apply PTHREAD.extcall_not_primitive.
          apply PTHREAD.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PTHREADCODE.init_chan_correct; eauto.
          omega.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PTHREAD.kernel_mode.
          destruct (PTHREAD.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
          eauto 11.
        Qed.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (PIPCINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                               (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmmh) (HPS4:= HPS4) (Hnpc:= Hnpc)
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abq:= real_abq)
                               (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                               (num_chan:= num_chan) (real_abtcb:= real_abtcb) (Hnchan:= Hnchan) prog) 
          (PTHREAD.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                             (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmml) (HPS4:= HPS4) 
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt)
                             (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                             (real_abtcb:= real_abtcb) (Hnchan:= Hnchan) (real_abq:= real_abq) tprog).
    Proof.
      eapply IPCINTROGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End IPCINTROGENIMPL.
