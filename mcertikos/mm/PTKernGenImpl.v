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
Require Import MPTKern.
Require Import MPTCommon.
Require Export PTKernGen.
Require Import MPTCommonCode.
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

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module PTKERNGENIMPL.
  Export PTKernGen.PTKERNGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MPTKERN.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MPTKERN.PSetPE)...
    destruct (Q_dec MPTKERN.PAlloc)...
    destruct (Q_dec MPTKERN.PFree)...
    destruct (Q_dec MPTKERN.PSetPT)...
    destruct (Q_dec MPTKERN.PPTRead)...
    destruct (Q_dec MPTKERN.PPTInsert)...
    destruct (Q_dec MPTKERN.PPTRmv)...
    destruct (Q_dec MPTKERN.PPTIn)...
    destruct (Q_dec MPTKERN.PPTOut)...
    destruct (Q_dec MPTKERN.PTrapIn)...
    destruct (Q_dec MPTKERN.PTrapOut)...
    destruct (Q_dec MPTKERN.PHostIn)...
    destruct (Q_dec MPTKERN.PHostOut)...
    destruct (Q_dec MPTKERN.PTrapGet)...
    destruct (Q_dec MPTKERN.PTrapRet)...
    destruct (Q_dec MPTKERN.PPTInitKern)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MPTKERN.AbData(PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage)).
    Notation LDATA := (MPTCOMM.AbData(PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (fundef (external_function:= MPTKERN.primOp)).
    Notation Lfundef := (fundef (external_function:= MPTCOMM.primOp)).

    Notation funkind := (funkind (low := MPTCOMM.primOp) Asm.code (Clight.fundef (external_function := MPTCOMM.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: MPTKERN.primOp): funkind :=
      match p with
        | MPTKERN.PSetPE => Code _ (AST.External MPTCOMM.PSetPE)
        | MPTKERN.PAlloc => Code _ (AST.External MPTCOMM.PAlloc)
        | MPTKERN.PFree => Code _ (AST.External MPTCOMM.PFree)
        | MPTKERN.PSetPT => Code _ (AST.External MPTCOMM.PSetPT)
        | MPTKERN.PPTRead => Code _ (AST.External MPTCOMM.PPTRead)
        | MPTKERN.PPTInsert => SourceFun (Clight.External MPTCOMM.PPTInsert (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) tvoid) dummy
        | MPTKERN.PPTRmv => Code _ (AST.External MPTCOMM.PPTRmv)
        | MPTKERN.PPTIn => Code _ (AST.External MPTCOMM.PPTIn)
        | MPTKERN.PPTOut => Code _ (AST.External MPTCOMM.PPTOut)
        | MPTKERN.PTrapIn => Code _ (AST.External MPTCOMM.PTrapIn)
        | MPTKERN.PTrapOut => Code _ (AST.External MPTCOMM.PTrapOut)
        | MPTKERN.PHostIn => Code _ (AST.External MPTCOMM.PHostIn)
        | MPTKERN.PHostOut => Code _ (AST.External MPTCOMM.PHostOut)
        | MPTKERN.PTrapGet => Code _ (AST.External MPTCOMM.PTrapGet)
        | MPTKERN.PTrapRet => Code _ (AST.External MPTCOMM.PTrapRet)
        | MPTKERN.PPTInitKern => SourceFun (Clight.Internal MPTCOMMCODE.f_pt_init_kern) dummy
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (pt_init_comm, Some (Gfun (SourceFun (Clight.External (MPTCOMM.PPTInitComm) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (pt_insert1, Some (Gfun (SourceFun (Clight.External (MPTCOMM.PPTInsert) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MPTKERN.primOp (low := MPTCOMM.primOp) (Clight.fundef (external_function := MPTCOMM.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit MPTKERN.primOp (low := MPTCOMM.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MPTKERN.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MPTCOMM.primOp)).

    Let Im_pt_init_kern: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTKERN.PPTInitKern).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because MPTKERN.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: PTKERNGEN.transf_program Im_pt_init_kern impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := MPTCOMM.primOp) := source_program_only source_implem prog.
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

    (** pt_init_comm *)

    Let bpt_init_comm: block := Genv.genv_next ge + Z.of_nat 0.

    Let hpt_init_comm1 : Genv.find_symbol sge pt_init_comm = Some bpt_init_comm. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_init_comm).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_init_comm2 : Genv.find_funct sge (Vptr bpt_init_comm Int.zero) = Some (Clight.External (MPTCOMM.PPTInitComm) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_init_comm _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hpt_init_comm3 : Clight.type_of_global sge bpt_init_comm = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_init_comm).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_init_comm. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_init_comm2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_init_comm2. reflexivity.
    Qed.     

    (** pt_insert1 *)

    Let bpt_insert: block := Genv.genv_next ge + Z.of_nat 1.

    Let hpt_insert1 : Genv.find_symbol sge pt_insert1 = Some bpt_insert. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_insert1).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_insert2 : Genv.find_funct sge (Vptr bpt_insert Int.zero) = Some (Clight.External (MPTCOMM.PPTInsert) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_insert1 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hpt_insert3 : Clight.type_of_global sge bpt_insert = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_insert).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_insert. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_insert2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_insert2. reflexivity.
    Qed.     

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.
      
      Context {mem__MPTKERN} {mem__MPTCOMM}
              `{HHmem: !LayerMemoryModel HDATA mem__MPTKERN}
              `{HLmem: !LayerMemoryModel LDATA mem__MPTCOMM}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__MPTKERN mem__MPTCOMM}.

      Notation HLoad := (MPTKERN.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (MPTKERN.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (MPTCOMM.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (MPTCOMM.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA MPTKERN.primOp mem__MPTKERN :=
        MPTKERN.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (real_ptp:= real_ptp)
                          (Hmem:= HHmem) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_pt:= real_pt).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA MPTCOMM.primOp mem__MPTCOMM :=
        MPTCOMM.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= HLmem)
                          (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp).

      Notation lstep := (MPTCOMM.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                      (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                      (real_ptp := real_ptp)).

      Let pt_init_kern_spec:
        forall m0 rs b sig labd' mbi_adr,
          let labd := Mem.get_abstract_data m0 in
          rs PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_pt_init_kern)
          -> sig = mksignature (Tint::nil) None 
          -> MPTCOMM.pt_init_kern (kern_high:=kern_high) (maxpage:=maxpage) labd real_nps 
                                  (real_AT (MPTCOMM.AT (MPTCOMM.ADT labd)))
                                  (real_ptp (MPTCOMM.ptpool (MPTCOMM.ADT labd)))
                                  (real_pt (MPTCOMM.ptpool (MPTCOMM.ADT labd))) (Int.unsigned mbi_adr) = Some labd'
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTKERN.PPTInitKern)
          -> asm_invariant tge (State rs m0)
          -> extcall_arguments rs m0 sig (Vint mbi_adr ::  nil)                            
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.   
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MPTKERN.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTCOMM.primitive_call)
                     (is_primitive_call := MPTCOMM.is_primitive_call)
                     (kernel_mode := MPTCOMM.kernel_mode)
                  ).
          apply MPTCOMM.exec_load_exec_loadex.
          apply MPTCOMM.exec_store_exec_storeex.
          apply MPTCOMM.extcall_not_primitive.
          apply MPTCOMM.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.
          apply (MPTCOMMCODE.pt_init_kern_correct sge bpt_insert hpt_insert1 hpt_insert2 hpt_insert3 bpt_init_comm hpt_init_comm1 hpt_init_comm2 hpt_init_comm3 _ H9 _ _ _ _ H2 refl_equal).
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTCOMM.kernel_mode.
          apply MPTCOMM.pt_init_kern_eq in H2.
          functional inversion H2.
          functional inversion H10.
          unfold adt0, labd in *.
          destruct (MPTCOMM.INV (Mem.get_abstract_data m0)).
          auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
          unfold loc_external_result.
          inversion H10.
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
          (MPTKERN.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                             (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) 
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) prog) 
          (MPTCOMM.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                             (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) 
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) tprog).
    Proof.
      eapply PTKERNGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End PTKERNGENIMPL.
