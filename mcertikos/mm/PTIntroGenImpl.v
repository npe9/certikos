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
Require Import MPTIntro.
Require Import MAL.
Require Import MALOp.
Require Export PTIntroGen.
Require Import ZArith.Zwf.
Require Import MALCode.
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

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module PTINTROGENIMPL.
  Export PTIntroGen.PTINTROGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MPTINTRO.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MPTINTRO.PSetPE)...
    destruct (Q_dec MPTINTRO.PAlloc)...
    destruct (Q_dec MPTINTRO.PFree)...
    destruct (Q_dec MPTINTRO.PSetPT)...
    destruct (Q_dec MPTINTRO.PSetPDX)...
    destruct (Q_dec MPTINTRO.PGetPTX)...
    destruct (Q_dec MPTINTRO.PSetPTX)...
    destruct (Q_dec MPTINTRO.PRmvPTX)...
    destruct (Q_dec MPTINTRO.PPTIn)...
    destruct (Q_dec MPTINTRO.PPTOut)...
    destruct (Q_dec MPTINTRO.PTrapIn)...
    destruct (Q_dec MPTINTRO.PTrapOut)...
    destruct (Q_dec MPTINTRO.PHostIn)...
    destruct (Q_dec MPTINTRO.PHostOut)...
    destruct (Q_dec MPTINTRO.PTrapGet)...
    destruct (Q_dec MPTINTRO.PTrapRet)...
    destruct (Q_dec MPTINTRO.PMemInit)...
    left; destruct p; assumption.
  Defined.    

 Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MPTINTRO.AbData (num_proc:=num_proc)(PgSize:=PgSize) (kern_low:=kern_low)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).
    Notation LDATA := (MALOP.AbData (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (fundef (external_function:= MPTINTRO.primOp)).
    Notation Lfundef := (fundef (external_function:= MALT.primOp)).

    Notation funkind := (funkind (low:= MALT.primOp) Asm.code (Clight.fundef (external_function := MALT.primOp))).

    Let Im_ptIn : Lfundef := AST.Internal (Pret::nil).
    Let Im_ptOut : Lfundef := AST.Internal (Pret::nil).
        
    Definition source_implem_extfuns (p: MPTINTRO.primOp): funkind :=
      match p with
        | MPTINTRO.PSetPE => Code _ (AST.External MALT.PSetPE)
        | MPTINTRO.PAlloc => Code _ (AST.External MALT.PAlloc)
        | MPTINTRO.PFree => Code _ (AST.External MALT.PFree)
        | MPTINTRO.PSetPT => SourceFun (Clight.Internal MALCODE.f_set_pt) (AST.Internal nil)
        | MPTINTRO.PSetPDX => SourceFun (Clight.Internal MALCODE.f_set_pdx) (AST.Internal nil)
        | MPTINTRO.PGetPTX => SourceFun (Clight.Internal MALCODE.f_get_ptx) (AST.Internal nil)
        | MPTINTRO.PSetPTX => SourceFun (Clight.Internal MALCODE.f_set_ptx) (AST.Internal nil)
        | MPTINTRO.PRmvPTX => SourceFun (Clight.Internal MALCODE.f_rmv_ptx) (AST.Internal nil)
        | MPTINTRO.PPTIn => Code _ (Im_ptIn)
        | MPTINTRO.PPTOut => Code _ (Im_ptOut)
        | MPTINTRO.PTrapIn => Code _ (AST.External MALT.PTrapIn)
        | MPTINTRO.PTrapOut => Code _ (AST.External MALT.PTrapOut)
        | MPTINTRO.PHostIn => Code _ (AST.External MALT.PHostIn)
        | MPTINTRO.PHostOut => Code _ (AST.External MALT.PHostOut)
        | MPTINTRO.PTrapGet => Code _ (AST.External MALT.PTrapGet)
        | MPTINTRO.PTrapRet => Code _ (AST.External MALT.PTrapRet)
        | MPTINTRO.PMemInit => Code _ (AST.External MALT.PMemInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
        (PTPool_LOC, Some (Gvar (mkglobvar (SourceVar (tarray t_struct_PT num_proc) tt) ((Init_space (num_proc*1025*PgSize))::nil) false)))
        :: (set_pt, Some (Gfun (SourceFun (Clight.External (MALT.PSetPT) (Ctypes.Tcons (tptr (tptr tchar)) Ctypes.Tnil) Ctypes.Tvoid) (AST.Internal nil))))
        :: nil.

    Definition source_implem : source_implem Asm.code unit MPTINTRO.primOp (low := MALT.primOp) (Clight.fundef (external_function := MALT.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let NOREPET: list_norepet (map fst (Implementation.source_implem_new_globs source_implem)).
    Proof.
      case_eq (list_norepet_dec peq (map fst (Implementation.source_implem_new_globs source_implem))); try discriminate; tauto.
    Qed.

    Let im : implem Asm.code unit MPTINTRO.primOp (low := MALT.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MPTINTRO.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MALT.primOp)).

    Let Im_set_cr3: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTINTRO.PSetPT).
    Let Im_set_PDX: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTINTRO.PSetPDX).
    Let Im_set_PTX: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTINTRO.PSetPTX).
    Let Im_get_PTX: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTINTRO.PGetPTX).
    Let Im_rmv_PTX: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTINTRO.PRmvPTX).

    Notation new_glbl := (new_glbl (PgSize:= PgSize) (num_proc:= num_proc) PTPool_LOC).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) := 
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        ((set_pt, Some (Gfun (SourceFun (Clight.External (MALT.PSetPT) (Ctypes.Tcons (tptr (tptr tchar)) Ctypes.Tnil) Ctypes.Tvoid) (AST.Internal nil)))):: nil).

    (* This is basically an axiom that can be easily checked because MPTINTRO.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: PTINTROGEN.transf_program (PgSize:= PgSize) (num_proc:= num_proc) Im_set_cr3 Im_set_PDX Im_get_PTX Im_set_PTX Im_rmv_PTX Im_ptIn Im_ptOut PTPool_LOC impl_glbl prog = OK tprog.
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

    Let VALID_LOC: (PTPool_LOC <> (prog_main prog)).
    Proof.
      intro.
      exploit (get_next_symbol_prop PTPool_LOC (map fst (source_implem_new_globs))).
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

    Let sprog : Clight.program (external_function := MALT.primOp) := source_program_only source_implem prog.
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
      exploit transf_clight_fundef_to_program; eauto.
      unfold sprog in H.
      congruence.
      assumption.
      simpl. destruct 1; try discriminate.
      destruct H0.
      inversion H0; rewrite transf_clight_fundef_external; eauto.
      inversion H0.
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
    
    Lemma ptpool_loc_prop:
      forall b0,
        Genv.find_symbol tge PTPool_LOC = Some b0 ->
        Genv.find_symbol sge PTPool_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some (tarray t_struct_PT num_proc).
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   PTPool_LOC
                                   (mkglobvar (SourceVar (tarray t_struct_PT num_proc) tt) ((Init_space (num_proc*1025*PgSize))::nil) false)
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
    
    Let PTPool_LOC_not_in:  ~ In PTPool_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge PTPool_LOC <> None) by congruence.
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

      Instance HLayer: LayerDefinition HDATA MPTINTRO.primOp mem__H :=
        MPTINTRO.layer_def (num_proc:=num_proc)(PgSize:=PgSize) (kern_low:=kern_low) (HPS:= CDataTypes.HPS)
                           (kern_high:=kern_high) (maxpage:=maxpage) (real_AT:= real_AT) (real_nps:= real_nps).

      Instance LLayer: LayerDefinition LDATA MALT.primOp mem__L :=
        MALT.layer_def (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) (real_AT:= real_AT) (real_nps:= real_nps).

      Notation LLoad := (MALT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (MALT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (MPTINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (MPTINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (MALT.step(PgSize:=PgSize)(NPT_LOC:=NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)
                                  (real_AT := real_AT) (real_nps:= real_nps)).

      Notation LADT := MALOP.ADT.

      Let rmv_PTX_spec:
      forall r' b b0 m'0 m0 n i vadr sg,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_rmv_PTX)
          -> Genv.find_symbol tge PTPool_LOC = Some b0
          -> 0 <= Int.unsigned n < num_proc
          -> 0 <= Int.unsigned i <= PDX Int.max_unsigned
          -> 0 <= Int.unsigned vadr <= PTX Int.max_unsigned
          -> Mem.store Mint32 m'0 b0
                       ((Int.unsigned n * (PDX Int.max_unsigned + 2) + Int.unsigned i + 1) * PgSize + Int.unsigned vadr * 4)
                       (Vint Int.zero)
             = Some m0
          -> MALOP.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> MALOP.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTINTRO.PRmvPTX)
          -> asm_invariant tge (State r' m'0)
          -> sg = mksignature (Tint :: Tint :: Tint :: nil) None
          -> extcall_arguments r' m'0 sg (Vint n :: Vint i :: Vint vadr :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep (Genv.globalenv tprog) (State r' m'0) E0 (State r_ m0')
               /\ True (* r_ # (loc_external_result {| sig_args := Tint::Tint::nil; sig_res := None |}) =
                          Vundef *)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit ptpool_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MPTINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MALT.primitive_call)
                 (is_primitive_call := MALT.is_primitive_call)
                 (kernel_mode := MALOP.kernel_mode)
              ).
      apply MALT.exec_load_exec_loadex.
      apply MALT.exec_store_exec_storeex.
      apply MALT.extcall_not_primitive.
      apply MALT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply MALCODE.rmv_ptx_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      rewrite H14.
      unfold Ctypes.signature_of_type.
      simpl.
      reflexivity.
      unfold MALOP.kernel_mode.
      auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H5).
      eauto 11.
    Qed.

    Let set_PTX_spec:
      forall r' b b0 m'0 m0 n i vadr padr p p0 sg,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_set_PTX)
          -> Genv.find_symbol tge PTPool_LOC = Some b0
          -> 0 <= Int.unsigned n < num_proc
          -> 0 <= Int.unsigned i <= PDX Int.max_unsigned
          -> 0 <= Int.unsigned vadr <= PTX Int.max_unsigned
          -> 0 <= Int.unsigned padr <= Int.max_unsigned + 1 - PgSize
          -> ZtoPerm (Int.unsigned p) = Some p0
          -> (PgSize | Int.unsigned padr)
          -> Mem.store Mint32 m'0 b0
                       ((Int.unsigned n * (PDX Int.max_unsigned + 2) + Int.unsigned i + 1) * PgSize + Int.unsigned vadr * 4)
                       (Vint (Int.repr (Int.unsigned padr + Int.unsigned p)))
             = Some m0
          -> MALOP.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> MALOP.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTINTRO.PSetPTX)
          -> asm_invariant tge (State r' m'0)
          -> sg = mksignature (Tint :: Tint :: Tint :: Tint :: Tint :: nil) None
          -> extcall_arguments r' m'0 sg (Vint n :: Vint i :: Vint vadr :: Vint padr :: Vint p :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep (Genv.globalenv tprog) (State r' m'0) E0 (State r_ m0')
               /\ True (* r_ # (loc_external_result {| sig_args := Tint::Tint::nil; sig_res := None |}) =
                          Vundef *)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit ptpool_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MPTINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MALT.primitive_call)
                 (is_primitive_call := MALT.is_primitive_call)
                 (kernel_mode := MALOP.kernel_mode)
              ).
      apply MALT.exec_load_exec_loadex.
      apply MALT.exec_store_exec_storeex.
      apply MALT.extcall_not_primitive.
      apply MALT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MALCODE.set_ptx_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      rewrite H17.
      reflexivity.
      unfold MALOP.kernel_mode; auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H8).
      eauto 11.
    Qed.

    Let set_PDX_spec:
      forall r' b b0 m'0 m0 n i sg,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_set_PDX)
          -> Genv.find_symbol tge PTPool_LOC = Some b0
          -> 0 <= Int.unsigned n < num_proc
          -> 0 <= Int.unsigned i <= PDX Int.max_unsigned
          -> Mem.store Mint32 m'0 b0
                       (Int.unsigned n * (PDX Int.max_unsigned + 2) * PgSize + Int.unsigned i * 4)
                       (Vptr b0 (Int.repr ((Int.unsigned n * (PDX Int.max_unsigned + 2) + Int.unsigned i + 1) * PgSize + PDXPERM))) 
             =  Some m0
          -> MALOP.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> MALOP.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTINTRO.PSetPDX)
          -> asm_invariant tge (State r' m'0)
          -> sg = mksignature (Tint :: Tint :: nil) None
          -> extcall_arguments r' m'0 sg (Vint n :: Vint i :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State r' m'0) E0 (State r_ m0')
               /\ True (* r_ # (loc_external_result {| sig_args := Tint::Tint::nil; sig_res := None |}) =
                          Vundef *)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit ptpool_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MPTINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MALT.primitive_call)
                 (is_primitive_call := MALT.is_primitive_call)
                 (kernel_mode := MALOP.kernel_mode)
              ).
      apply MALT.exec_load_exec_loadex.
      apply MALT.exec_store_exec_storeex.
      apply MALT.extcall_not_primitive.
      apply MALT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MALCODE.set_pdx_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      rewrite H13.
      reflexivity.
      unfold MALOP.kernel_mode; auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
      eauto 11.
    Qed.

    Let get_PTX_spec:
      forall r' b b0 m'0 n i vadr padr sg,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_get_PTX)
          -> Genv.find_symbol tge PTPool_LOC = Some b0
          -> 0 <= Int.unsigned n < num_proc
          -> 0 <= Int.unsigned i <= PDX Int.max_unsigned
          -> 0 <= Int.unsigned vadr <= PTX Int.max_unsigned
          -> Mem.load Mint32 m'0 b0
                      ((Int.unsigned n * (PDX Int.max_unsigned + 2) + Int.unsigned i + 1) * PgSize + Int.unsigned vadr * 4)
             = Some (Vint padr)
          -> MALOP.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> MALOP.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> Mem.tget m'0 b0 = Some Tag_global
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTINTRO.PGetPTX)
          -> asm_invariant tge (State r' m'0)
          -> sg = mksignature (Tint :: Tint :: Tint :: nil) (Some Tint)
          -> extcall_arguments r' m'0 sg (Vint n :: Vint i :: Vint vadr :: nil)
          -> exists f' m0' r_ , 
               inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
               /\ Memtype.Mem.inject f' m'0 m0'
               /\ Mem.nextblock m'0 <= Mem.nextblock m0'
               /\ plus lstep (Genv.globalenv tprog) (State r' m'0) E0 (State r_ m0')
               /\ r_ # (loc_external_result sg) = (Vint padr)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit ptpool_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MPTINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MALT.primitive_call)
                 (is_primitive_call := MALT.is_primitive_call)
                 (kernel_mode := MALOP.kernel_mode)
              ).
      apply MALT.exec_load_exec_loadex.
      apply MALT.exec_store_exec_storeex.
      apply MALT.extcall_not_primitive.
      apply MALT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MALCODE.get_ptx_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      rewrite H14.
      reflexivity.
      unfold MALOP.kernel_mode; auto.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      inversion H22.
      eauto 11.
    Qed.

   (** set_pt *)

    Let bset_pt: block := Genv.genv_next ge + Z.of_nat 1.

    Let hset_pt1 : Genv.find_symbol sge set_pt = Some bset_pt. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_pt).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_pt2 : Genv.find_funct sge (Vptr bset_pt Int.zero) = Some (Clight.External (MALT.PSetPT) (Ctypes.Tcons (tptr (tptr tchar)) Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_pt _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_pt3 : Clight.type_of_global sge bset_pt = Some (Ctypes.Tfunction (Ctypes.Tcons (tptr (tptr tchar)) Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      unfold Genv.find_funct in hset_pt2.
      destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      rewrite hset_pt2.
      case_eq (Genv.find_var_info sge bset_pt).
      intros. exfalso.
      unfold sge in hset_pt2.
      eapply Genv.find_funct_ptr_not_varinfo.
      eassumption.
      eassumption.
      reflexivity.
    Qed.

    Let set_cr3_spec:
      forall r' b m'0 n labd' ofs sg b0,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_set_cr3)
          -> Genv.find_symbol tge PTPool_LOC = Some b0
          -> ofs = (Int.repr (Int.unsigned n * (PDX Int.max_unsigned + 2) * PgSize))
          -> MALOP.setPT (Mem.get_abstract_data m'0) (GLOBP PTPool_LOC ofs) = Some labd'
          -> 0 <= (Int.unsigned n) < num_proc
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTINTRO.PSetPT)
          -> asm_invariant tge (State r' m'0)
          -> sg = mksignature (Tint :: nil) None
          -> extcall_arguments r' m'0 sg (Vint n :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
               /\ Memtype.Mem.inject f' m'0 m0'
               /\ Mem.nextblock m'0 <= Mem.nextblock m0'
               /\ plus lstep tge (State r' m'0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ True (* r_ # (loc_external_result {| sig_args := Tint::Tint::nil; sig_res := None |}) =
                          Vundef *)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit ptpool_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MPTINTRO.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MALT.primitive_call)
                 (is_primitive_call := MALT.is_primitive_call)
                 (kernel_mode := MALOP.kernel_mode)
              ).
      apply MALT.exec_load_exec_loadex.
      apply MALT.exec_store_exec_storeex.
      apply MALT.extcall_not_primitive.
      apply MALT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MALCODE.set_pt_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      unfold MALOP.kernel_mode.
      apply MALOP.setPT_eq in H3.
      destruct (MALOP.INV (Mem.get_abstract_data m'0)).
      functional inversion H3; unfold adt in *; auto.
      destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
      generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m'0)).
      rewrite Mem.put_put_abstract_data.
      rewrite Mem.put_get_abstract_data.
      intro.
      replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m'0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
      replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m'0)) labd') in PLUS.
      eauto 11.
      rewrite Mem.put_put_abstract_data.
      replace labd' with (Mem.get_abstract_data m_asm).
      rewrite Mem.put_get_abstract_data.
      reflexivity.
      erewrite <- Mem.get_abstract_data_inject_inside; eauto.
      rewrite Mem.get_put_abstract_data.
      reflexivity.
    Qed.

      Let ptin_spec:
        forall r' b b0 m'0,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_ptIn)
          -> Genv.find_symbol tge PTPool_LOC = Some b0
          -> MALOP.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> MALOP.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> plus lstep tge (State r' m'0) E0
                  (State (r'#RA<-Vundef#PC<-(r' RA)) m'0).
      Proof.
        intros.
        apply plus_one.
        econstructor; eauto.
        simpl.
        rewrite zeq_true; trivial.
        simpl.
        trivial.
      Qed.

      Let ptout_spec:
        forall r' b b0 m'0,
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_ptOut)
          -> Genv.find_symbol tge PTPool_LOC = Some b0
          -> MALOP.ikern (LADT (Mem.get_abstract_data m'0)) = true
          -> MALOP.ihost (LADT (Mem.get_abstract_data m'0)) = true
          -> plus lstep (Genv.globalenv tprog) (State r' m'0) E0
                  (State (r'#RA<-Vundef#PC<-(r' RA)) m'0).
      Proof.
        intros.
        apply plus_one.
        econstructor; eauto.
        simpl.
        rewrite zeq_true; trivial.
        trivial.
      Qed.

    Lemma valid_pdx_perm: 0<= PDXPERM < PgSize.
    Proof. omega. Qed.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (MPTINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                              (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmmh) (HPS:= HPS) prog) 
          (MALT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                          (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= Hlmml) tprog).
    Proof.
      eapply PTINTROGEN.transf_program_correct; simpl; eauto.
      econstructor.
      simpl.
      intro.
      destruct H; try discriminate H.
      contradiction.
      econstructor.
      simpl.
      intro; contradiction.
      econstructor.
      Grab Existential Variables.
      vm_compute; intro contra; discriminate contra.
      vm_compute; intro contra; discriminate contra.
      omega.
      vm_compute; intro contra; discriminate contra.
      vm_compute; reflexivity.
      vm_compute; reflexivity.
      unfold Z.divide.
      exists 1024; omega.
      omega.
      omega.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End PTINTROGENIMPL.
