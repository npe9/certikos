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
Require Import MPTOp.
Require Import MPTIntro.
Require Export PTOpGen.
Require Import MPTIntroCode.
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

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module PTOPGENIMPL.
  Export PTOpGen.PTOPGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MPTOP.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MPTOP.PSetPE)...
    destruct (Q_dec MPTOP.PAlloc)...
    destruct (Q_dec MPTOP.PFree)...
    destruct (Q_dec MPTOP.PSetPT)...
    destruct (Q_dec MPTOP.PSetPDX)...
    destruct (Q_dec MPTOP.PPTRead)...
    destruct (Q_dec MPTOP.PPTInsert)...
    destruct (Q_dec MPTOP.PPTRmv)...
    destruct (Q_dec MPTOP.PPTIn)...
    destruct (Q_dec MPTOP.PPTOut)...
    destruct (Q_dec MPTOP.PTrapIn)...
    destruct (Q_dec MPTOP.PTrapOut)...
    destruct (Q_dec MPTOP.PHostIn)...
    destruct (Q_dec MPTOP.PHostOut)...
    destruct (Q_dec MPTOP.PTrapGet)...
    destruct (Q_dec MPTOP.PTrapRet)...
    destruct (Q_dec MPTOP.PMemInit)...
    left; destruct p; assumption.
  Defined.    

 Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MPTINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                      (kern_high:=kern_high) (maxpage:=maxpage)).
    Notation LDATA := (MPTINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                      (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (fundef (external_function:= MPTOP.primOp)).
    Notation Lfundef := (fundef (external_function:= MPTINTRO.primOp)).

    Notation funkind := (funkind (low := MPTINTRO.primOp) Asm.code (Clight.fundef (external_function := MPTINTRO.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: MPTOP.primOp): funkind :=
      match p with
        | MPTOP.PSetPE => Code _ (AST.External MPTINTRO.PSetPE)
        | MPTOP.PAlloc => Code _ (AST.External MPTINTRO.PAlloc)
        | MPTOP.PFree => Code _ (AST.External MPTINTRO.PFree)
        | MPTOP.PSetPT => Code _ (AST.External MPTINTRO.PSetPT)
        | MPTOP.PSetPDX => Code _ (AST.External MPTINTRO.PSetPDX)
        | MPTOP.PPTRead => SourceFun (Clight.Internal MPTINTROCODE.f_pt_read) dummy
        | MPTOP.PPTInsert => SourceFun (Clight.Internal MPTINTROCODE.f_pt_insert) dummy
        | MPTOP.PPTRmv => SourceFun (Clight.Internal MPTINTROCODE.f_pt_rmv) dummy
        | MPTOP.PPTIn => Code _ (AST.External MPTINTRO.PPTIn)
        | MPTOP.PPTOut => Code _ (AST.External MPTINTRO.PPTOut)
        | MPTOP.PTrapIn => Code _ (AST.External MPTINTRO.PTrapIn)
        | MPTOP.PTrapOut => Code _ (AST.External MPTINTRO.PTrapOut)
        | MPTOP.PHostIn => Code _ (AST.External MPTINTRO.PHostIn)
        | MPTOP.PHostOut => Code _ (AST.External MPTINTRO.PHostOut)
        | MPTOP.PTrapGet => Code _ (AST.External MPTINTRO.PTrapGet)
        | MPTOP.PTrapRet => Code _ (AST.External MPTINTRO.PTrapRet)
        | MPTOP.PMemInit => Code _ (AST.External MPTINTRO.PMemInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (get_PTX, Some (Gfun (SourceFun (Clight.External (MPTINTRO.PGetPTX) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tint) dummy)))
        :: (set_PTX, Some (Gfun (SourceFun (Clight.External (MPTINTRO.PSetPTX) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))))) Ctypes.Tvoid) dummy)))
        :: (rmv_PTX, Some (Gfun (SourceFun (Clight.External (MPTINTRO.PRmvPTX) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MPTOP.primOp (low := MPTINTRO.primOp) (Clight.fundef (external_function := MPTINTRO.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit MPTOP.primOp (low := MPTINTRO.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MPTOP.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MPTINTRO.primOp)).

    Let Im_pt_read: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTOP.PPTRead).
    Let Im_pt_insert: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTOP.PPTInsert).
    Let Im_pt_rmv: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTOP.PPTRmv).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because MPTOP.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: PTOPGEN.transf_program Im_pt_insert Im_pt_rmv Im_pt_read impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := MPTINTRO.primOp) := source_program_only source_implem prog.
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

    (** get_PTX *)

    Let bget_PTX: block := Genv.genv_next ge + Z.of_nat 0.

    Let hget_PTX1 : Genv.find_symbol sge get_PTX = Some bget_PTX. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_PTX).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hget_PTX2 : Genv.find_funct sge (Vptr bget_PTX Int.zero) = Some (Clight.External (MPTINTRO.PGetPTX) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_PTX _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hget_PTX3 : Clight.type_of_global sge bget_PTX = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_PTX).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_PTX. unfold Asm.fundef. omega.
      intros.
      simpl in hget_PTX2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_PTX2. reflexivity.
    Qed. 

    (** set_PTX *)

    Let bset_PTX: block := Genv.genv_next ge + Z.of_nat 1.

    Let hset_PTX1 : Genv.find_symbol sge set_PTX = Some bset_PTX. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_PTX).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_PTX2 : Genv.find_funct sge (Vptr bset_PTX Int.zero) = Some (Clight.External (MPTINTRO.PSetPTX) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))))) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_PTX _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_PTX3 : Clight.type_of_global sge bset_PTX = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))))) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_PTX).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_PTX. unfold Asm.fundef. omega.
      intros.
      simpl in hset_PTX2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_PTX2. reflexivity.
    Qed.     

    (** rmv_PTX *)

    Let brmv_PTX: block := Genv.genv_next ge + Z.of_nat 2.

    Let hrmv_PTX1 : Genv.find_symbol sge rmv_PTX = Some brmv_PTX. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ rmv_PTX).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hrmv_PTX2 : Genv.find_funct sge (Vptr brmv_PTX Int.zero) = Some (Clight.External (MPTINTRO.PRmvPTX) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ rmv_PTX _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hrmv_PTX3 : Clight.type_of_global sge brmv_PTX = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil))) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge brmv_PTX).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold brmv_PTX. unfold Asm.fundef. omega.
      intros.
      simpl in hrmv_PTX2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hrmv_PTX2. reflexivity.
    Qed.

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.
      
      Context {mem__MPTOP} {mem__MPTINTRO}
              `{HHmem: !LayerMemoryModel HDATA mem__MPTOP}
              `{HLmem: !LayerMemoryModel LDATA mem__MPTINTRO}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__MPTOP mem__MPTINTRO}.

      Notation LLoad := (MPTINTRO.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (MPTINTRO.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HLoad := (MPTOP.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (MPTOP.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA MPTOP.primOp mem__MPTOP :=
        MPTOP.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= HHmem) (HPS:= HPS).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA MPTINTRO.primOp mem__MPTINTRO :=
        MPTINTRO.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= HLmem) (HPS:= HPS).

      Notation lstep := (MPTINTRO.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS:= HPS)
                                       (real_nps:= real_nps) (real_AT:= real_AT)).

      Let pt_insert_spec:
        forall m rs b adt n sig p vadr padr,
          rs PC = Vptr b Int.zero
          -> MPTINTRO.ptInsert (HPS:=HPS) (Mem.get_abstract_data m) (Int.unsigned n)
                               (Int.unsigned vadr) (Int.unsigned padr) (Int.unsigned p) = Some adt
          -> Genv.find_funct_ptr tge b = Some (Im_pt_insert)
          -> sig = mksignature (Tint :: Tint :: Tint :: Tint :: nil) None 
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTOP.PPTInsert)
          -> asm_invariant tge (State rs m)
          -> extcall_arguments rs m sig (Vint n :: Vint vadr :: Vint padr :: Vint p :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m)) f' 
               /\ Memtype.Mem.inject f' m m0'
               /\ Mem.nextblock m <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m) E0 (State r_ (Mem.put_abstract_data m0' adt))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.   
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MPTOP.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTINTRO.primitive_call)
                     (is_primitive_call := MPTINTRO.is_primitive_call)
                     (kernel_mode := MPTINTRO.kernel_mode)
                  ).
          apply MPTINTRO.exec_load_exec_loadex.
          apply MPTINTRO.exec_store_exec_storeex.
          apply MPTINTRO.extcall_not_primitive.
          apply MPTINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.
          eapply MPTINTROCODE.pt_insert_correct.
          2: eassumption. eassumption. assumption.
          assumption.
          (* BEGIN hypotheses coming from refinement proof *)
          eassumption.
          reflexivity.
          (* END hypotheses coming from refinement proof *)
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTINTRO.kernel_mode.
          apply MPTINTRO.ptInsert_eq in H0.
          functional inversion H0.
          functional inversion H10.
          unfold adt0 in *.
          destruct (MPTINTRO.INV (Mem.get_abstract_data m)).
          auto.
          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m)) adt) in PLUS.
          unfold loc_external_result.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace adt with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

    Let pt_rmv_spec:
        forall m rs b adt n vadr sig,
          rs PC = Vptr b Int.zero
          -> MPTINTRO.ptRmv (Mem.get_abstract_data m) (Int.unsigned n)
                            (Int.unsigned vadr) = Some adt
          -> Genv.find_funct_ptr tge b = Some (Im_pt_rmv)
          -> sig = mksignature (Tint :: Tint ::  nil) None 
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTOP.PPTRmv)
          -> asm_invariant tge (State rs m)
          -> extcall_arguments rs m sig (Vint n :: Vint vadr :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m)) f' 
               /\ Memtype.Mem.inject f' m m0'
               /\ Mem.nextblock m <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m) E0 (State r_ (Mem.put_abstract_data m0' adt))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.   
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MPTOP.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTINTRO.primitive_call)
                     (is_primitive_call := MPTINTRO.is_primitive_call)
                     (kernel_mode := MPTINTRO.kernel_mode)
                  ).
          apply MPTINTRO.exec_load_exec_loadex.
          apply MPTINTRO.exec_store_exec_storeex.
          apply MPTINTRO.extcall_not_primitive.
          apply MPTINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.
          eapply MPTINTROCODE.pt_rmv_correct.
          2: eassumption. eassumption. assumption.
          assumption.
          (* BEGIN hypotheses coming from refinement proof *)
          eassumption.
          reflexivity.
          (* END hypotheses coming from refinement proof *)
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTINTRO.kernel_mode.
          apply MPTINTRO.ptRmv_eq in H0.
          functional inversion H0.
          destruct (MPTINTRO.INV (Mem.get_abstract_data m)).
          functional inversion H10; unfold adt1 in *; auto.
          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m)) adt) in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace adt with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

    Let pt_read_spec:
        forall m rs b n sig vadr padr,
          rs PC = Vptr b Int.zero
          -> MPTINTRO.ptRead (Mem.get_abstract_data m) (Int.unsigned n)
                             (Int.unsigned vadr) = Some (Int.unsigned padr)
          -> Genv.find_funct_ptr tge b = Some (Im_pt_read)
          -> sig = mksignature (Tint :: Tint ::  nil) (Some Tint) 
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTOP.PPTRead)
          -> asm_invariant tge (State rs m)
          -> extcall_arguments rs m sig (Vint n :: Vint vadr :: nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m)) f' 
               /\ Memtype.Mem.inject f' m m0'
               /\ Mem.nextblock m <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m) E0 (State r_  m0')
               /\ r_ # (loc_external_result sig) = (Vint padr)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.   
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MPTOP.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTINTRO.primitive_call)
                     (is_primitive_call := MPTINTRO.is_primitive_call)
                     (kernel_mode := MPTINTRO.kernel_mode)
                  ).
          apply MPTINTRO.exec_load_exec_loadex.
          apply MPTINTRO.exec_store_exec_storeex.
          apply MPTINTRO.extcall_not_primitive.
          apply MPTINTRO.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.
          eapply MPTINTROCODE.pt_read_correct.
          2: eassumption. eassumption. assumption.
          assumption.
          eassumption.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTINTRO.kernel_mode.
          unfold MPTINTRO.ptRead in H0.
          unfold MPTINTRO.getPTX in H0.
          destruct (MPTINTRO.INV (Mem.get_abstract_data m)).
          destruct (MPTOP.ipt (MPTINTRO.ADT (Mem.get_abstract_data m))); try discriminate H0.
          destruct (MPTOP.ihost (MPTINTRO.ADT (Mem.get_abstract_data m))); try discriminate H0.
          auto.
          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m)).
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m)) (Mem.get_abstract_data m)) in PLUS.
          inversion H10.
          rewrite Mem.put_put_abstract_data in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          rewrite (Mem.get_abstract_data_inject_inside x m m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          assumption.
        Qed.

    Theorem transf_program_correct:
        Smallstep.backward_simulation 
          (MPTOP.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                           (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS:= HPS) prog) 
          (MPTINTRO.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                              (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS:= HPS) tprog).  
    Proof.
      eapply PTOPGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End PTOPGENIMPL.
