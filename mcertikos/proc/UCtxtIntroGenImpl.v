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
Require Import ProcDataType.
Require Import LAsm.
Require Import CDataTypes.
Require Import AsmExtra.
Require Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import PUCtxtIntro.
Require Import PIPC.
Require Export UCtxtIntroGen.
Require Import UCtxtIntroGenAsm.
Require Import PIPCCode.
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

Module UCTXTINTROGENIMPL.
  Export UCtxtIntroGen.UCTXTINTROGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PUCTXTINTRO.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PUCTXTINTRO.PAlloc)...
    destruct (Q_dec PUCTXTINTRO.PFree)...
    destruct (Q_dec PUCTXTINTRO.PSetPT)...
    destruct (Q_dec PUCTXTINTRO.PPTRead)...
    destruct (Q_dec PUCTXTINTRO.PPTResv)...
    destruct (Q_dec PUCTXTINTRO.PThreadSpawn)...
    destruct (Q_dec PUCTXTINTRO.PThreadKill)...
    destruct (Q_dec PUCTXTINTRO.PThreadWakeup)...
    destruct (Q_dec PUCTXTINTRO.PThreadYield)...
    destruct (Q_dec PUCTXTINTRO.PThreadSleep)...
    destruct (Q_dec PUCTXTINTRO.PGetCurID)...
    destruct (Q_dec PUCTXTINTRO.PRestoreUCTX)...
    destruct (Q_dec PUCTXTINTRO.PSaveUCTX)...
    destruct (Q_dec PUCTXTINTRO.PUCTXGet)...
    destruct (Q_dec PUCTXTINTRO.PUCTXSet)...
    destruct (Q_dec PUCTXTINTRO.PUCTXSetEIP)...
    destruct (Q_dec PUCTXTINTRO.PPTIn)...
    destruct (Q_dec PUCTXTINTRO.PPTOut)...
    destruct (Q_dec PUCTXTINTRO.PTrapIn)...
    destruct (Q_dec PUCTXTINTRO.PHostIn)...
    destruct (Q_dec PUCTXTINTRO.PHostOut)...
    destruct (Q_dec PUCTXTINTRO.PTrapGet)...
    destruct (Q_dec PUCTXTINTRO.PTrapRet)...
    destruct (Q_dec PUCTXTINTRO.PIsChanReady)...
    destruct (Q_dec PUCTXTINTRO.PSendToChan)...
    destruct (Q_dec PUCTXTINTRO.PReceiveChan)...
    destruct (Q_dec PUCTXTINTRO.PELFLoad)...
    destruct (Q_dec PUCTXTINTRO.PProcInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PUCTXTINTRO.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                                         (kern_high:=kern_high) (maxpage:=maxpage)(num_chan:= num_chan)).
    Notation LDATA := (PIPC.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                  (kern_high:=kern_high) (maxpage:=maxpage) (num_chan:= num_chan)).                          
  
    Notation Hfundef := (Asm.fundef (external_function:= PUCTXTINTRO.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PIPC.primOp)).

    Notation funkind := (funkind (low:= PIPC.primOp) Asm.code (Clight.fundef (external_function := PIPC.primOp))).

    Notation Im_restore_uctx := UCTXTINTROGEN_ASM.Im_restore_uctx.
    Notation Im_elf_load := UCTXTINTROGEN_ASM.Im_elf_load.

    Definition source_implem_extfuns (p: PUCTXTINTRO.primOp): funkind :=
      match p with
        | PUCTXTINTRO.PAlloc => Code _ (AST.External PIPC.PAlloc)
        | PUCTXTINTRO.PFree => Code _ (AST.External PIPC.PFree)
        | PUCTXTINTRO.PSetPT => Code _ (AST.External PIPC.PSetPT)
        | PUCTXTINTRO.PPTRead => Code _ (AST.External PIPC.PPTRead)
        | PUCTXTINTRO.PPTResv => Code _ (AST.External PIPC.PPTResv)
        | PUCTXTINTRO.PThreadSpawn => Code _ (AST.External PIPC.PThreadSpawn)
        | PUCTXTINTRO.PThreadKill => Code _ (AST.External PIPC.PThreadKill)
        | PUCTXTINTRO.PThreadWakeup => Code _ (AST.External PIPC.PThreadWakeup)
        | PUCTXTINTRO.PThreadYield => Code _ (AST.External PIPC.PThreadYield)
        | PUCTXTINTRO.PThreadSleep => Code _ (AST.External PIPC.PThreadSleep)
        | PUCTXTINTRO.PGetCurID => Code _ (AST.External PIPC.PGetCurID)
        | PUCTXTINTRO.PRestoreUCTX => Code _ Im_restore_uctx
        | PUCTXTINTRO.PSaveUCTX => SourceFun (Clight.Internal PIPCCODE.f_save_uctx) (AST.Internal nil)
        | PUCTXTINTRO.PUCTXGet => SourceFun (Clight.Internal PIPCCODE.f_uctx_get) (AST.Internal nil)
        | PUCTXTINTRO.PUCTXSet => SourceFun (Clight.Internal PIPCCODE.f_uctx_set) (AST.Internal nil)
        | PUCTXTINTRO.PUCTXSetEIP => SourceFun (Clight.Internal PIPCCODE.f_uctx_set_eip) (AST.Internal nil)
        | PUCTXTINTRO.PPTIn => Code _ (AST.External PIPC.PPTIn)
        | PUCTXTINTRO.PPTOut => Code _ (AST.External PIPC.PPTOut)
        | PUCTXTINTRO.PTrapIn => Code _ (AST.External PIPC.PTrapIn)
        | PUCTXTINTRO.PHostIn => Code _ (AST.External PIPC.PHostIn)
        | PUCTXTINTRO.PHostOut => Code _ (AST.External PIPC.PHostOut)
        | PUCTXTINTRO.PTrapGet => Code _ (AST.External PIPC.PTrapGet)
        | PUCTXTINTRO.PTrapRet => Code _ (AST.External PIPC.PTrapRet)
        | PUCTXTINTRO.PIsChanReady => Code _ (AST.External PIPC.PIsChanReady)
        | PUCTXTINTRO.PSendToChan => Code _ (AST.External PIPC.PSendToChan)
        | PUCTXTINTRO.PReceiveChan => Code _ (AST.External PIPC.PReceiveChan)
        | PUCTXTINTRO.PProcInit => Code _ (AST.External PIPC.PProcInit)
        | PUCTXTINTRO.PELFLoad => Code _ Im_elf_load
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Notation UCTXT_SIZE := 17.

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
        (UCTX_LOC, Some (Gvar (mkglobvar (SourceVar (tarray (tarray tint UCTXT_SIZE) num_proc) tt) ((Init_space (num_proc*UCTXT_SIZE*4))::nil) false)))
        :: (get_curid2, Some (Gfun (SourceFun (Clight.External (PIPC.PGetCurID) (Ctypes.Tnil) tint) (AST.Internal nil))))
        :: (trap_out, Some (Gfun (SourceFun (Clight.External (PIPC.PTrapOut) (Ctypes.Tnil) tvoid) (AST.Internal nil))))
        :: nil.

    Definition source_implem : source_implem Asm.code unit PUCTXTINTRO.primOp (low := PIPC.primOp) (Clight.fundef (external_function := PIPC.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let NOREPET: list_norepet (map fst (Implementation.source_implem_new_globs source_implem)).
    Proof.
      case_eq (list_norepet_dec peq (map fst (Implementation.source_implem_new_globs source_implem))); try discriminate; tauto.
    Qed.

    Let im : implem Asm.code unit PUCTXTINTRO.primOp (low := PIPC.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PUCTXTINTRO.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PIPC.primOp)).

    Notation Im_uctx_get := (transf_source_fun' transf_clight_fundef (source_implem_extfuns PUCTXTINTRO.PUCTXGet)).
    Notation Im_uctx_set := (transf_source_fun' transf_clight_fundef (source_implem_extfuns PUCTXTINTRO.PUCTXSet)).
    Notation Im_uctx_set_eip := (transf_source_fun' transf_clight_fundef (source_implem_extfuns PUCTXTINTRO.PUCTXSetEIP)).
    Notation Im_save_uctx := (transf_source_fun' transf_clight_fundef (source_implem_extfuns PUCTXTINTRO.PSaveUCTX)).

    Notation new_glbl := (new_glbl (num_proc:= num_proc) UCTX_LOC).

    Let impl_glbl :  list (ident * option (globdef Lfundef unit)) := 
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        ((get_curid2, Some (Gfun (SourceFun (Clight.External (PIPC.PGetCurID) (Ctypes.Tnil) tint) (AST.Internal nil)))) 
           :: (trap_out, Some (Gfun (SourceFun (Clight.External (PIPC.PTrapOut) (Ctypes.Tnil) tvoid) (AST.Internal nil))))::nil).
    
    (* This is basically an axiom that can be easily checked because PUCTXTINTRO.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: UCTXTINTROGEN.transf_program (num_proc:= num_proc) Im_save_uctx Im_restore_uctx Im_uctx_get Im_uctx_set Im_uctx_set_eip Im_elf_load UCTX_LOC impl_glbl prog = OK tprog.
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

    Let VALID_LOC: (UCTX_LOC <> (prog_main prog)).
    Proof.
      intro.
      exploit (get_next_symbol_prop UCTX_LOC (map fst (source_implem_new_globs))).
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
                                     ~ In s' (map fst (new_glbl++impl_glbl))).
    Proof.
      change (new_glbl++impl_glbl) with (implem_new_globs im).
      eapply new_ids_fresh.
      assumption.
    Qed.

    Let sprog : Clight.program (external_function := PIPC.primOp) := source_program_only source_implem prog.
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
      exploit (transf_clight_fundef_to_program (external_function := PIPC.primOp)); eauto.
      unfold sprog in H.
      congruence.
      assumption.
      simpl. destruct 1; try discriminate.
      destruct H0 as [HT1| [HT2|HT3]].
      inversion HT1. rewrite transf_clight_fundef_external; eauto.
      inversion HT2. rewrite transf_clight_fundef_external; eauto.
      inversion HT3. 
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
    
    Lemma uctx_loc_prop:
      forall b0,
        Genv.find_symbol tge UCTX_LOC = Some b0 ->
        Genv.find_symbol sge UCTX_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some (tarray (tarray tint UCTXT_SIZE) num_proc).
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   UCTX_LOC
                                   (mkglobvar (SourceVar (tarray (tarray tint UCTXT_SIZE) num_proc) tt) ((Init_space (num_proc*UCTXT_SIZE*4))::nil) false)
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

    Let UCTX_LOC_not_in: ~ In UCTX_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge UCTX_LOC <> None) by congruence.
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

   (** get_curid2 *)

    Let bget_curid2: block := Genv.genv_next ge + Z.of_nat 1.

    Let hget_curid21 : Genv.find_symbol sge get_curid2 = Some bget_curid2. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_curid2).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hget_curid22 : Genv.find_funct sge (Vptr bget_curid2 Int.zero) = Some (Clight.External (PIPC.PGetCurID) (Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_curid2 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hget_curid23 : Clight.type_of_global sge bget_curid2 = Some (Ctypes.Tfunction (Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      unfold Genv.find_funct in hget_curid22.
      destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      rewrite hget_curid22.
      case_eq (Genv.find_var_info sge bget_curid2).
      intros. exfalso.
      unfold sge in hget_curid22.
      eapply Genv.find_funct_ptr_not_varinfo.
      eassumption.
      eassumption.
      reflexivity.
    Qed.

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.
      
      Local Instance HdataOp:AbstractDataOps HDATA:= (PUCTXTINTRO.abstract_data (Hnpc:= Hnpc)).
      Local Instance LdataOp:AbstractDataOps LDATA:= (PIPC.abstract_data (Hnpc:= Hnpc)).

      Context {mem__H} {mem__L}
              `{Hlmmh: !LayerMemoryModel HDATA mem__H}
              `{Hlmml: !LayerMemoryModel LDATA mem__L}
              `{Hlmi: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= Hlmmh) HDATA PUCTXTINTRO.primOp mem__H :=
        PUCTXTINTRO.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                              (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_abtcb := real_abtcb)
                              (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                              (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                              (num_chan:= num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool := real_chpool).
      
      Instance LLayer: LayerDefinition (layer_mem:= Hlmml) LDATA PIPC.primOp mem__L :=
        PIPC.layer_def (Hnpc:=Hnpc)(PgSize:=PgSize) (num_proc:=num_proc)(HPS4:=HPS4)(Hlow:=Hlow)(Hhigh:=Hhigh)
                       (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_abtcb := real_abtcb)
                       (real_nps:=real_nps) (real_AT := real_AT)(real_ptp:=real_ptp)(real_pt:=real_pt) 
                       (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                       (num_chan:= num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool := real_chpool).        

      Notation LLoad := (PIPC.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PIPC.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (PUCTXTINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PUCTXTINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (PIPC.step (NPT_LOC:=NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                   (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                   (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                   (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(real_abtcb:=real_abtcb)
                                   (Hnchan := Hnchan) (real_abq:= real_abq) (real_chpool:= real_chpool)).

      Notation LADT := PIPC.ADT.

      Lemma uctx_get_spec:
        forall r' b m'0 n b1 r sig ofs,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_uctx_get) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PUCTXTINTRO.PUCTXGet)
          -> Genv.find_symbol tge UCTX_LOC = Some b1
          -> Mem.load Mint32 m'0 b1 (Int.unsigned n * UCTXT_SIZE * 4 + Int.unsigned ofs * 4) = Some (Vint r)
          -> 0 <= (Int.unsigned n) < num_proc
          -> is_UCTXT_ptr (Int.unsigned ofs) = false
          -> PIPC.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint::Tint::nil) (Some Tint)
          -> extcall_arguments r' m'0 sig (Vint n ::Vint ofs::nil)
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
          exploit uctx_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PUCTXTINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPC.is_primitive_call)
                     (kernel_mode := PIPC.kernel_mode)
                  ).
          apply PIPC.exec_load_exec_loadex.
          apply PIPC.exec_store_exec_storeex.
          apply PIPC.extcall_not_primitive.
          apply PIPC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PIPCCODE.uctx_get_correct; eauto.
          replace (Int.unsigned n * 68) with (Int.unsigned n * 17 * 4) by omega.
          eassumption.
          functional inversion H5; omega.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPC.kernel_mode.
          destruct (PIPC.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          inv H22.
          eauto 11.
        Qed.

      Lemma uctx_set_spec:
        forall r' b m'0 n b1 r sig ofs m0,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_uctx_set) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PUCTXTINTRO.PUCTXSet)
          -> Genv.find_symbol tge UCTX_LOC = Some b1
          -> Mem.store Mint32 m'0 b1 (Int.unsigned n * UCTXT_SIZE * 4 + Int.unsigned ofs * 4) (Vint r) = Some m0 
          -> 0 <= (Int.unsigned n) < num_proc
          -> is_UCTXT_ptr (Int.unsigned ofs) = false
          -> PIPC.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint::Tint::Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vint n ::Vint ofs::Vint r::nil)
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
          exploit uctx_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PUCTXTINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPC.is_primitive_call)
                     (kernel_mode := PIPC.kernel_mode)
                  ).
          apply PIPC.exec_load_exec_loadex.
          apply PIPC.exec_store_exec_storeex.
          apply PIPC.extcall_not_primitive.
          apply PIPC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PIPCCODE.uctx_set_correct; eauto.
          replace (Int.unsigned n * 68) with (Int.unsigned n * 17 * 4) by omega.
          eassumption.
          functional inversion H5; omega.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPC.kernel_mode.
          destruct (PIPC.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
          eauto 11.
        Qed.

      Lemma uctx_set_eip_spec:
        forall r' b m'0 n b1 sig m0 bf ofs,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_uctx_set_eip) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PUCTXTINTRO.PUCTXSetEIP)
          -> Genv.find_symbol tge UCTX_LOC = Some b1
          -> Mem.store Mint32 m'0 b1 (Int.unsigned n * UCTXT_SIZE * 4 + U_EIP * 4) (Vptr bf ofs) = Some m0 
          -> 0 <= (Int.unsigned n) < num_proc
          -> PIPC.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> (exists fun_id, Genv.find_symbol tge fun_id = Some bf) 
          -> sig = mksignature (Tint::Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vint n ::Vptr bf ofs::nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ inject_incr (Mem.flat_inj (Genv.genv_next tge)) f' 
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
          exploit uctx_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PUCTXTINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPC.is_primitive_call)
                     (kernel_mode := PIPC.kernel_mode)
                  ).
          apply PIPC.exec_load_exec_loadex.
          apply PIPC.exec_store_exec_storeex.
          apply PIPC.extcall_not_primitive.
          apply PIPC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PIPCCODE.uctx_set_eip_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPC.kernel_mode.
          destruct (PIPC.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
          assert (Hincr: inject_incr (Mem.flat_inj (Genv.genv_next tge)) x).
          inv H15.
          inv INJECT_NEUTRAL.
          unfold inject_incr.
          intros.
          apply H18.
          unfold Mem.flat_inj in *.
          destruct (zlt b0 (Genv.genv_next tge)); try discriminate H10.
          rewrite zlt_true.
          trivial.
          unfold LdataOp in *.
          omega.
          eauto 12.
        Qed.

        Lemma saveuctx_spec:
        forall r' b m'0 n b1 sig m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 
               m15 m16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16,
          r' PC = Vptr b Int.zero 
          -> Genv.find_symbol tge UCTX_LOC = Some b1
          -> PIPC.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.store Mint32 m'0 b1 (UCTXT_SIZE * 4 * n + 4 * U_EDI) (Vint u0) = Some m1 
          -> Mem.store Mint32 m1 b1 (UCTXT_SIZE * 4 * n + 4 * U_ESI) (Vint u1) = Some m2 
          -> Mem.store Mint32 m2 b1 (UCTXT_SIZE * 4 * n + 4 * U_EBP) (Vint u2) = Some m3 
          -> Mem.store Mint32 m3 b1 (UCTXT_SIZE * 4 * n + 4 * U_OESP) (Vint u3) = Some m4 
          -> Mem.store Mint32 m4 b1 (UCTXT_SIZE * 4 * n + 4 * U_EBX) (Vint u4) = Some m5 
          -> Mem.store Mint32 m5 b1 (UCTXT_SIZE * 4 * n + 4 * U_EDX) (Vint u5) = Some m6 
          -> Mem.store Mint32 m6 b1 (UCTXT_SIZE * 4 * n + 4 * U_ECX) (Vint u6) = Some m7 
          -> Mem.store Mint32 m7 b1 (UCTXT_SIZE * 4 * n + 4 * U_EAX) (Vint u7) = Some m8 
          -> Mem.store Mint32 m8 b1 (UCTXT_SIZE * 4 * n + 4 * U_ES) (Vint u8) = Some m9 
          -> Mem.store Mint32 m9 b1 (UCTXT_SIZE * 4 * n + 4 * U_DS) (Vint u9) = Some m10 
          -> Mem.store Mint32 m10 b1 (UCTXT_SIZE * 4 * n + 4 * U_TRAPNO) (Vint u10) = Some m11 
          -> Mem.store Mint32 m11 b1 (UCTXT_SIZE * 4 * n + 4 * U_ERR) (Vint u11) = Some m12 
          -> Mem.store Mint32 m12 b1 (UCTXT_SIZE * 4 * n + 4 * U_EIP) (Vint u12) = Some m13 
          -> Mem.store Mint32 m13 b1 (UCTXT_SIZE * 4 * n + 4 * U_CS) (Vint u13) = Some m14 
          -> Mem.store Mint32 m14 b1 (UCTXT_SIZE * 4 * n + 4 * U_EFLAGS) (Vint u14) = Some m15 
          -> Mem.store Mint32 m15 b1 (UCTXT_SIZE * 4 * n + 4 * U_ESP) (Vint u15) = Some m16 
          -> Mem.store Mint32 m16 b1 (UCTXT_SIZE * 4 * n + 4 * U_SS) (Vint u16) = Some m0
          -> Mem.tget m'0 b1 = Some Tag_global
          -> Genv.find_funct_ptr tge b = Some (Im_save_uctx) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PUCTXTINTRO.PSaveUCTX)
          -> PIPC.cid (PIPC.ADT (Mem.get_abstract_data m'0)) = n
          -> sig = mksignature (Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::
                                    Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vint u0::Vint u1::Vint u2::Vint u3::Vint u4::Vint u5::Vint u6::
                                                Vint u7::Vint u8::Vint u9::Vint u10::Vint u11::Vint u12::Vint u13
                                                ::Vint u14::Vint u15::Vint u16::nil)
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
          exploit uctx_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PUCTXTINTRO.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PIPC.primitive_call (Hnchan:= Hnchan))
                     (is_primitive_call := PIPC.is_primitive_call)
                     (kernel_mode := PIPC.kernel_mode)
                  ).
          apply PIPC.exec_load_exec_loadex.
          apply PIPC.exec_store_exec_storeex.
          apply PIPC.extcall_not_primitive.
          apply PIPC.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          rewrite <- H24 in *.
          intros; eapply PIPCCODE.save_uctx_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PIPC.kernel_mode.
          destruct (PIPC.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H20).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H19).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H18).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H17).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H16).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H15).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H14).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H13).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H12).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H11).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H10).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H9).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H8).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H7).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H6).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H5).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
          eauto 12.
        Qed.

      Let AndImplies: forall A B: Prop, (A /\ (A -> B)) -> (A /\ B).
      Proof.
        intros.
        destruct H.
        split.
        assumption.
        apply H0; assumption.
      Qed.

      Let btrap_out: block := Genv.genv_next ge + Z.of_nat 2.
      Let htrap_out_tge: exists b_trapout, Genv.find_symbol tge trap_out = Some b_trapout
                                             /\ Genv.find_funct_ptr tge b_trapout = Some (External PIPC.PTrapOut).
      Proof.
        exists btrap_out.
        apply AndImplies.
        split.
        eapply add_globals_transf_augment_option.
        2: eapply transf_program_eq.
        assumption.
        intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
        eapply (NEW_INJ trap_out).
        congruence.
        simpl; tauto.
        reflexivity.
        intro.
        refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ trap_out _ _)).
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

      Lemma restoreuctx_spec:
        forall r' b m'0 b0 v0 v1 v2 v4 v5 v6 v7 v8 v9 n sig r'' abd,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_restore_uctx)
          -> Genv.find_symbol tge UCTX_LOC = Some b0
          -> PIPC.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> PIPC.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> sig = mksignature (Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vint n ::nil)
          -> 0<= Int.unsigned n < num_proc
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EDI) = Some v0
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ESI * 4) = Some v1
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EBP * 4) = Some v2
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EBX * 4) = Some v4
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EDX * 4) = Some v5
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ECX * 4) = Some v6
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EAX * 4) = Some v7
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ESP * 4) = Some v8
          -> Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EIP * 4) = Some v9
          -> r'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: Asm.RA :: nil) r')
          -> PIPC.trapout (Mem.get_abstract_data m'0) = Some abd
          -> exists r_,
               plus lstep tge (State r' m'0) E0 (State r_ (Mem.put_abstract_data m'0 abd))
               /\ (forall l,
                     Val.lessdef (Pregmap.get l (r''#Asm.EDI <- v0 #Asm.ESI <- v1 #Asm.EBP <- v2 #Asm.ESP<- v8#Asm.EBX <- v4
                                                    #EDX<- v5 #ECX<-v6 #EAX <- v7)# PC <- v9)
                                 (Pregmap.get l r_)).
      Proof.
        eapply UCTXTINTROGEN_ASM.restoreuctx_spec; eauto.
      Qed.

      Lemma elf_load_spec:
        forall r' b m'0 n b1 sig be ofse,
          r' PC = Vptr b Int.zero 
          -> Genv.find_funct_ptr tge b = Some (Im_elf_load) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_funct_ptr ge b = Some (External PUCTXTINTRO.PELFLoad)
          -> (exists elf_id, Genv.find_symbol tge elf_id = Some be)
          -> Genv.find_symbol tge UCTX_LOC = Some b1
          -> sig = mksignature (Tint::Tint::nil) None
          -> extcall_arguments r' m'0 sig (Vptr be ofse ::Vint n::nil)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> asm_invariant tge (State r' m'0)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
               /\ Memtype.Mem.inject f' m'0 m0'
               /\ Mem.nextblock m'0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
      Proof.
        intros.
        eapply UCTXTINTROGEN_ASM.elf_load_spec; eauto.
      Qed.

      Local Hint Resolve elf_load_spec restoreuctx_spec saveuctx_spec uctx_set_eip_spec
            uctx_get_spec uctx_set_spec.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (PUCTXTINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                                 (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmmh) (HPS4:= HPS4) (Hnpc:= Hnpc)
                                 (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abq:= real_abq)
                                 (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)
                                 (num_chan:= num_chan) (real_abtcb:= real_abtcb) (Hnchan:= Hnchan) (real_chpool:= real_chpool) prog) 
          (PIPC.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                          (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmml) (HPS4:= HPS4) (real_chpool:= real_chpool)
                          (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt)
                          (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                          (real_abtcb:= real_abtcb) (Hnchan:= Hnchan) (real_abq:= real_abq) tprog).
    Proof.
      Opaque Z.mul.
      eapply UCTXTINTROGEN.transf_program_correct; simpl; eauto.
      eapply NOREPET.
      Grab Existential Variables.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End UCTXTINTROGENIMPL.
