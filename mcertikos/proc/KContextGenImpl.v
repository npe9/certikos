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
Require Import PKContext.
Require Import MPTNew.
Require Export KContextGen.
Require Import MPTNewCode.
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
Require Import KContextGenAsm.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module KCONTEXTGENIMPL.
  Export KContextGen.KCONTEXTGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PKCONTEXT.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PKCONTEXT.PAlloc)...
    destruct (Q_dec PKCONTEXT.PFree)...
    destruct (Q_dec PKCONTEXT.PSetPT)...
    destruct (Q_dec PKCONTEXT.PPTRead)...
    destruct (Q_dec PKCONTEXT.PPTResv)...
    destruct (Q_dec PKCONTEXT.PPTNew)...
    destruct (Q_dec PKCONTEXT.PPTFree)...
    destruct (Q_dec PKCONTEXT.PKCtxtRA)...
    destruct (Q_dec PKCONTEXT.PKCtxtSP)...
    destruct (Q_dec PKCONTEXT.PKCtxtSwitch)...
    destruct (Q_dec PKCONTEXT.PPTIn)...
    destruct (Q_dec PKCONTEXT.PPTOut)...
    destruct (Q_dec PKCONTEXT.PTrapIn)...
    destruct (Q_dec PKCONTEXT.PTrapOut)...
    destruct (Q_dec PKCONTEXT.PHostIn)...
    destruct (Q_dec PKCONTEXT.PHostOut)...
    destruct (Q_dec PKCONTEXT.PTrapGet)...
    destruct (Q_dec PKCONTEXT.PTrapRet)...
    destruct (Q_dec PKCONTEXT.PPMapInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PKCONTEXT.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).   
    Notation LDATA := (MPTNEW.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                    (kern_high:=kern_high) (maxpage:=maxpage)).  
  
    Notation Hfundef := (Asm.fundef (external_function:= PKCONTEXT.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= MPTNEW.primOp)).

    Notation funkind := (funkind (low:= MPTNEW.primOp) Asm.code (Clight.fundef (external_function := MPTNEW.primOp))).

    Let Im_cswitch: Lfundef := KCONTEXTGEN_ASM.Im_cswitch.

    Definition source_implem_extfuns (p: PKCONTEXT.primOp): funkind :=
      match p with
        | PKCONTEXT.PAlloc => Code _ (AST.External MPTNEW.PAlloc)
        | PKCONTEXT.PFree => Code _ (AST.External MPTNEW.PFree)
        | PKCONTEXT.PSetPT => Code _ (AST.External MPTNEW.PSetPT)
        | PKCONTEXT.PPTRead => Code _ (AST.External MPTNEW.PPTRead)
        | PKCONTEXT.PPTResv => Code _ (AST.External MPTNEW.PPTResv)
        | PKCONTEXT.PPTNew => Code _ (AST.External MPTNEW.PPTNew)
        | PKCONTEXT.PPTFree => Code _ (AST.External MPTNEW.PPTFree)
        | PKCONTEXT.PKCtxtRA => SourceFun (Clight.Internal MPTNEWCODE.f_set_RA) (AST.Internal nil)
        | PKCONTEXT.PKCtxtSP => SourceFun (Clight.Internal MPTNEWCODE.f_set_SP) (AST.Internal nil)
        | PKCONTEXT.PKCtxtSwitch => Code _ Im_cswitch
        | PKCONTEXT.PPTIn => Code _ (AST.External MPTNEW.PPTIn)
        | PKCONTEXT.PPTOut => Code _ (AST.External MPTNEW.PPTOut)
        | PKCONTEXT.PTrapIn => Code _ (AST.External MPTNEW.PTrapIn)
        | PKCONTEXT.PTrapOut => Code _ (AST.External MPTNEW.PTrapOut)
        | PKCONTEXT.PHostIn => Code _ (AST.External MPTNEW.PHostIn)
        | PKCONTEXT.PHostOut => Code _ (AST.External MPTNEW.PHostOut)
        | PKCONTEXT.PTrapGet => Code _ (AST.External MPTNEW.PTrapGet)
        | PKCONTEXT.PTrapRet => Code _ (AST.External MPTNEW.PTrapRet)
        | PKCONTEXT.PPMapInit => Code _ (AST.External MPTNEW.PPMapInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
        (KCtxtPool_LOC, Some (Gvar (mkglobvar (SourceVar (tarray t_struct_KCtxt num_proc) tt) ((Init_space (num_proc*24))::nil) false)))
        :: nil.

    Let NOREPET: list_norepet (KCtxtPool_LOC :: nil).
    Proof.
      case_eq (list_norepet_dec peq (KCtxtPool_LOC :: nil)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PKCONTEXT.primOp (low := MPTNEW.primOp) (Clight.fundef (external_function := MPTNEW.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let im : implem Asm.code unit PKCONTEXT.primOp (low := MPTNEW.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PKCONTEXT.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MPTNEW.primOp)).

    Let Im_set_RA: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PKCONTEXT.PKCtxtRA).
    Let Im_set_SP: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PKCONTEXT.PKCtxtSP).

    Notation new_glbl := (new_glbl (num_proc:= num_proc) KCtxtPool_LOC).

    Let impl_glbl :  list (ident * option (globdef Lfundef unit)) := nil.

    (* This is basically an axiom that can be easily checked because PKCONTEXT.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: KCONTEXTGEN.transf_program (num_proc:= num_proc) Im_set_RA Im_set_SP Im_cswitch KCtxtPool_LOC impl_glbl prog = OK tprog.
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

    Let VALID_LOC: (KCtxtPool_LOC <> (prog_main prog)).
    Proof.
      intro.
      exploit (get_next_symbol_prop KCtxtPool_LOC (map fst (source_implem_new_globs))).
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

    Let sprog : Clight.program (external_function := MPTNEW.primOp) := source_program_only source_implem prog.
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
      exploit (transf_clight_fundef_to_program (external_function := MPTNEW.primOp)); eauto.
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
    
    Lemma kctxtpool_loc_prop:
      forall b0,
        Genv.find_symbol tge KCtxtPool_LOC = Some b0 ->
        Genv.find_symbol sge KCtxtPool_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some (tarray t_struct_KCtxt num_proc).
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   KCtxtPool_LOC
                                   (mkglobvar (SourceVar (tarray t_struct_KCtxt num_proc) tt) ((Init_space (num_proc*24))::nil) false)
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

    Let KCtxtPool_LOC_not_in: ~ In KCtxtPool_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge KCtxtPool_LOC <> None) by congruence.
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

      Instance HLayer: LayerDefinition (layer_mem:= Hlmmh) HDATA PKCONTEXT.primOp mem__H :=
        PKCONTEXT.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (real_ptp:= real_ptp)
                            (Hmem:= Hlmmh) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_pt:= real_pt) (Hnpc:= Hnpc)
                            (real_ptb:= real_ptb) (real_free_pt:= real_free_pt).
      
      Instance LLayer: LayerDefinition (layer_mem:= Hlmml) LDATA MPTNEW.primOp mem__L :=
        MPTNEW.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= Hlmml)
                         (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (Hnpc:= Hnpc)
                         (real_ptb:= real_ptb) (real_free_pt:= real_free_pt).

      Notation LLoad := (MPTNEW.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (MPTNEW.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (PKCONTEXT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PKCONTEXT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (MPTNEW.step (NPT_LOC:=NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                     (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                     (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                     (real_free_pt:= real_free_pt)).

      Notation LADT := MPTNEW.ADT.

      Let setRA_spec:
        forall r' b m'0 n b0 b1 m0 sig ofs,
          r' PC = Vptr b Int.zero
          -> (exists id, Genv.find_symbol tge id = Some b0) 
          -> (exists id, Genv.find_symbol ge id = Some b0) 
          -> Genv.find_funct_ptr tge b = Some (Im_set_RA) (*implementation Im_setRA has type ident-> code*)
          -> Genv.find_symbol tge KCtxtPool_LOC = Some b1
          -> Mem.store Mint32 m'0 b1
                       (Int.unsigned n * 24 + 5 * 4) (Vptr b0 ofs) = Some m0
          -> 0 < (Int.unsigned n) < num_proc
          -> MPTNEW.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> MPTNEW.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> MPTNEW.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint::Tint::nil) None 
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PKCONTEXT.PKCtxtRA)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n :: (Vptr b0 ofs):: nil)                     
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
          exploit kctxtpool_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PKCONTEXT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTNEW.primitive_call)
                     (is_primitive_call := MPTNEW.is_primitive_call)
                     (kernel_mode := MPTNEW.kernel_mode)
                  ).
          apply MPTNEW.exec_load_exec_loadex.
          apply MPTNEW.exec_store_exec_storeex.
          apply MPTNEW.extcall_not_primitive.
          apply MPTNEW.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply MPTNEWCODE.set_RA_correct; eauto.
          destruct H1.
          esplit.
          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          destruct H21.
          subst.
          apply NEW_INJ in H20.
          simpl in H20.
          destruct H20.
          left; reflexivity.
          contradiction.
          eassumption.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTNEW.kernel_mode.
          destruct (MPTNEW.INV (Mem.get_abstract_data m'0)).
          auto.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
          assert (Hincr: inject_incr (Mem.flat_inj (Genv.genv_next tge)) x).
          inv H15.
          inv INJECT_NEUTRAL.
          unfold inject_incr.
          intros.
          apply H19.
          unfold Mem.flat_inj in *.
          destruct (zlt b2 (Genv.genv_next tge)).
          rewrite zlt_true.
          trivial.
          omega.
          inv H10.
          eauto 12.
        Qed.

    Let setSP_spec:
      forall r' b m'0 n b0 b1 m0 ofs sig,
          r' PC = Vptr b Int.zero
          -> (exists id, Genv.find_symbol tge id = Some b0) 
          -> (exists id, Genv.find_symbol ge id = Some b0)
          -> Genv.find_funct_ptr tge b = Some (Im_set_SP) (*implementation Im_setSP has type ident-> code*)
          -> Genv.find_symbol tge KCtxtPool_LOC = Some b1
          -> Mem.store Mint32 m'0 b1
                       (Int.unsigned n * 24) (Vptr b0 ofs) = Some m0
          -> 0 < (Int.unsigned n) < num_proc
          -> MPTNEW.ipt (LADT (Mem.get_abstract_data m'0)) = true
          -> MPTNEW.pe (LADT (Mem.get_abstract_data m'0)) = true
          -> MPTNEW.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Int.unsigned ofs = (Int.unsigned n + 1) * PgSize - 4 
          -> Mem.tget m'0 b1 = Some Tag_global
          -> sig = mksignature (Tint::Tint::nil) None 
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PKCONTEXT.PKCtxtSP)
          -> asm_invariant tge (State r' m'0)
          -> extcall_arguments r' m'0 sig (Vint n :: (Vptr b0 ofs):: nil)                     
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
      exploit kctxtpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 PKCONTEXT.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MPTNEW.primitive_call)
                 (is_primitive_call := MPTNEW.is_primitive_call)
                 (kernel_mode := MPTNEW.kernel_mode)
              ).
      apply MPTNEW.exec_load_exec_loadex.
      apply MPTNEW.exec_store_exec_storeex.
      apply MPTNEW.extcall_not_primitive.
      apply MPTNEW.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply MPTNEWCODE.set_SP_correct; eauto.
      destruct H1.
      esplit.
      eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
      eapply Implementation.source_program_only_prop.
      simpl.
      intros.
      intro.
      destruct H22.
      subst.
      apply NEW_INJ in H21.
      simpl in H21.
      destruct H21.
      left; reflexivity.
      contradiction.
      eassumption.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold MPTNEW.kernel_mode.
      destruct (MPTNEW.INV (Mem.get_abstract_data m'0)).
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      assert (Hincr: inject_incr (Mem.flat_inj (Genv.genv_next tge)) x).
      inv H16.
      inv INJECT_NEUTRAL.
      unfold inject_incr.
      intros.
      apply H20.
      unfold Mem.flat_inj in *.
      destruct (zlt b2 (Genv.genv_next tge)).
      rewrite zlt_true.
      trivial.
      omega.
      inv H11.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
      eauto 12.
    Qed.

      Let cswitch_spec:
        forall r' r'' b m'0 n n' b0 m0 m1 m2 m3 m4 m5 v0 v1 v2 v3 v4 v5,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_cswitch) (*implementation Im_setSP has type ident-> code*)
          -> Genv.find_symbol tge KCtxtPool_LOC = Some b0
          -> 0 <= (Int.unsigned n) < num_proc
          -> 0 <= (Int.unsigned n') < num_proc
          -> MPTNEW.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> MPTNEW.pe (LADT (Mem.get_abstract_data m'0)) = true 
          -> MPTNEW.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.store Mint32 m'0 b0 (Int.unsigned n * 24) (r' Asm.ESP) = Some m0
          -> Mem.store Mint32 m0 b0 (Int.unsigned n * 24 + 4) (r' Asm.EDI) = Some m1
          -> Mem.store Mint32 m1 b0 (Int.unsigned n * 24 + 8) (r' Asm.ESI) = Some m2
          -> Mem.store Mint32 m2 b0 (Int.unsigned n * 24 + 12) (r' Asm.EBX) = Some m3
          -> Mem.store Mint32 m3 b0 (Int.unsigned n * 24 + 16) (r' Asm.EBP) = Some m4
          -> Mem.store Mint32 m4 b0 (Int.unsigned n * 24 + 20) (r' Asm.RA) = Some m5
          -> Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 0) = Some v0
          -> Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 4) = Some v1
          -> Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 8) = Some v2
          -> Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 12) = Some v3
          -> Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 16) = Some v4
          -> Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 20) = Some v5
          -> r' Asm.EAX = Vint n
          -> r' Asm.EDX = Vint n'
          -> r'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: IR EDX :: IR ECX :: IR EAX :: Asm.RA :: nil) r')
          -> exists r_,
               plus lstep tge (State r' m'0) E0 (State r_ m5)
               /\ (forall l,
                     Val.lessdef (Pregmap.get l ((((((r''# Asm.ESP <- v0)#Asm.EDI <- v1)#Asm.ESI <- v2)#Asm.EBX<- v3)
                                                    #Asm.EBP <- v4)# PC <- v5))
                                 (Pregmap.get l r_)).
      Proof.
        eapply KCONTEXTGEN_ASM.cswitch_spec.
      Qed.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (PKCONTEXT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                               (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmmh) (HPS4:= HPS4) (Hnpc:= Hnpc)
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                               (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) prog) 
          (MPTNEW.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                            (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmml) (HPS4:= HPS4) 
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                            (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) tprog).  
    Proof.
      eapply KCONTEXTGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End KCONTEXTGENIMPL.
