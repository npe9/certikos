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
Require Import MPTInit.
Require Import MPTKern.
Require Import ZArith.Zwf.
Require Import MPTKernCode.
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
Require Export PTInitGen.
Require Import Implementation.
Require Import SeparateCompiler.
Require Import ClightImplemExtra.
Require Import LayerDefinition.
Require Import RealParams.
Require Import CInitSpecsMPTOp.
Require Import CInitSpecsMPTCommon.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module PTINITGENIMPL.
  Export PTInitGen.PTINITGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MPTINIT.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MPTINIT.PAlloc)...
    destruct (Q_dec MPTINIT.PFree)...
    destruct (Q_dec MPTINIT.PSetPT)...
    destruct (Q_dec MPTINIT.PPTRead)...
    destruct (Q_dec MPTINIT.PPTInsert)...
    destruct (Q_dec MPTINIT.PPTRmv)...
    destruct (Q_dec MPTINIT.PPTIn)...
    destruct (Q_dec MPTINIT.PPTOut)...
    destruct (Q_dec MPTINIT.PTrapIn)...
    destruct (Q_dec MPTINIT.PTrapOut)...
    destruct (Q_dec MPTINIT.PHostIn)...
    destruct (Q_dec MPTINIT.PHostOut)...
    destruct (Q_dec MPTINIT.PTrapGet)...
    destruct (Q_dec MPTINIT.PTrapRet)...
    destruct (Q_dec MPTINIT.PPTInit)...
    left; destruct p; assumption.
  Defined.    

 Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MPTINIT.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) 
                                     (kern_high:=kern_high) (maxpage:=maxpage)) .
    Notation LDATA := (MPTKERN.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                     (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (fundef (external_function:= MPTINIT.primOp)).
    Notation Lfundef := (fundef (external_function:= MPTKERN.primOp)).

    Notation funkind := (funkind (low := MPTKERN.primOp) Asm.code (Clight.fundef (external_function := MPTKERN.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: MPTINIT.primOp): funkind :=
      match p with
        | MPTINIT.PAlloc => Code _ (AST.External MPTKERN.PAlloc)
        | MPTINIT.PFree => Code _ (AST.External MPTKERN.PFree)
        | MPTINIT.PSetPT => SourceFun (Clight.External (MPTKERN.PSetPT) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy
        | MPTINIT.PPTRead => Code _ (AST.External MPTKERN.PPTRead)
        | MPTINIT.PPTInsert => Code _ (AST.External MPTKERN.PPTInsert)
        | MPTINIT.PPTRmv => Code _ (AST.External MPTKERN.PPTRmv)
        | MPTINIT.PPTIn => Code _ (AST.External MPTKERN.PPTIn)
        | MPTINIT.PPTOut => Code _ (AST.External MPTKERN.PPTOut)
        | MPTINIT.PTrapIn => Code _ (AST.External MPTKERN.PTrapIn)
        | MPTINIT.PTrapOut => Code _ (AST.External MPTKERN.PTrapOut)
        | MPTINIT.PHostIn => Code _ (AST.External MPTKERN.PHostIn)
        | MPTINIT.PHostOut => Code _ (AST.External MPTKERN.PHostOut)
        | MPTINIT.PTrapGet => Code _ (AST.External MPTKERN.PTrapGet)
        | MPTINIT.PTrapRet => Code _ (AST.External MPTKERN.PTrapRet)
        | MPTINIT.PPTInit => SourceFun (Clight.Internal (MPTKERNCODE.f_pt_init)) dummy
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (set_pe, Some (Gfun (SourceFun (Clight.External (MPTKERN.PSetPE) (Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: (pt_init_kern, Some (Gfun (SourceFun (Clight.External (MPTKERN.PPTInitKern) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: (set_cr3, Some (Gfun (SourceFun (Clight.External (MPTKERN.PSetPT) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MPTINIT.primOp (low := MPTKERN.primOp) (Clight.fundef (external_function := MPTKERN.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit MPTINIT.primOp (low := MPTKERN.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MPTINIT.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MPTKERN.primOp)).

    Let Im_ptinit: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTINIT.PPTInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because MPTINIT.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: PTINITGEN.transf_program Im_ptinit impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := MPTKERN.primOp) := source_program_only source_implem prog.
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

    (** set_pe *)

    Let bset_pe: block := Genv.genv_next ge + Z.of_nat 0.

    Let hset_pe1 : Genv.find_symbol sge set_pe = Some bset_pe. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_pe).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_pe2 : Genv.find_funct sge (Vptr bset_pe Int.zero) = Some (Clight.External (MPTKERN.PSetPE) (Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_pe _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_pe3 : Clight.type_of_global sge bset_pe = Some (Ctypes.Tfunction (Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_pe).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_pe. unfold Asm.fundef. omega.
      intros.
      simpl in hset_pe2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_pe2. reflexivity.
    Qed.

(*
    Lemma hset_pe_t1 : Genv.find_symbol tge set_pe = Some bset_pe. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply transf_program_eq.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_pe).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Lemma hset_pe_t2 : Genv.find_funct_ptr tge bset_pe = Some (AST.External (MPTKERN.PSetPE)).
    Proof.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_pe _ _)).
       2: exact (transf_program_eq im prog).
       3: simpl; eauto 8.
       2: assumption.
      fold tprog tge.
      rewrite transf_clight_fundef_external.
      destruct 1 as [? [? ?]].
      generalize hset_pe_t1; intro.
      unfold Asm.fundef in *.
      congruence.
      reflexivity.
      reflexivity.
    Qed. 
*)     

    (** pt_init_kern *)

    Let bpt_init_kern: block := Genv.genv_next ge + Z.of_nat 1.

    Let hpt_init_kern1 : Genv.find_symbol sge pt_init_kern = Some bpt_init_kern. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_init_kern).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hpt_init_kern2 : Genv.find_funct sge (Vptr bpt_init_kern Int.zero) = Some (Clight.External (MPTKERN.PPTInitKern) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_init_kern _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hpt_init_kern3 : Clight.type_of_global sge bpt_init_kern = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_init_kern).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_init_kern. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_init_kern2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_init_kern2. reflexivity.
    Qed. 

    (** set_cr3 *)

    Let bset_cr3: block := Genv.genv_next ge + Z.of_nat 2.

    Let hset_cr31 : Genv.find_symbol sge set_cr3 = Some bset_cr3. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_cr3).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hset_cr32 : Genv.find_funct sge (Vptr bset_cr3 Int.zero) = Some (Clight.External (MPTKERN.PSetPT) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_cr3 _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hset_cr33 : Clight.type_of_global sge bset_cr3 = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_cr3).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_cr3. unfold Asm.fundef. omega.
      intros.
      simpl in hset_cr32. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_cr32. reflexivity.
    Qed. 

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.
      
    Context {mem__MPTINIT mem__MPTKERN}
      `{HHmem: !LayerMemoryModel HDATA mem__MPTINIT}
      `{HLmem: !LayerMemoryModel LDATA mem__MPTKERN}
      `{HLayerInject: !LayerMemoryInjections HDATA LDATA _ _}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA MPTINIT.primOp mem__MPTINIT :=
        MPTINIT.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (real_ptp:= real_ptp)
                          (Hmem:= HHmem) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_pt:= real_pt) (Hnpc:= Hnpc).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA MPTKERN.primOp mem__MPTKERN :=
        MPTKERN.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= HLmem)
                          (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt).

      Notation HLoad := (MPTINIT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (MPTINIT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (MPTKERN.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (MPTKERN.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation lstep := (MPTKERN.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                      (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                      (real_ptp := real_ptp) (real_pt:= real_pt)).

      Notation LADT := MPTKERN.ADT.

        Let pt_init_spec:
        forall m0 rs b sig labd' mbi_adr,
          let labd := Mem.get_abstract_data m0 in
          rs PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_ptinit)
          -> sig = mksignature (Tint::nil) None 
          -> MPTKERN.pt_init (Hnpc:=Hnpc)(kern_high:=kern_high) (maxpage:=maxpage) 
                             labd real_nps 
                             (real_AT (MPTKERN.AT (LADT labd)))
                             (real_ptp (MPTKERN.ptpool (LADT labd)))
                             (real_pt (MPTKERN.ptpool (LADT labd)))
                             (Int.unsigned mbi_adr) = Some labd'
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTINIT.PPTInit)
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
          assert(H10: MPTKERN.ikern (LADT (Mem.get_abstract_data m0)) = true).
            unfold labd in *.
            apply MPTKERN.pt_init_eq in H2.
            functional inversion H2.
            functional inversion H10.
            unfold adt0 in *.
            destruct (MPTKERN.INV (Mem.get_abstract_data m0)).
            apply valid_iptt.
            assumption.
          assert(ihost: MPTKERN.ihost (LADT (Mem.get_abstract_data m0)) = true).
            unfold labd in *.
            apply MPTKERN.pt_init_eq in H2.
            functional inversion H2.
            functional inversion H11.
            unfold adt0 in *.
            assumption.      
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MPTINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTKERN.primitive_call)
                     (is_primitive_call := MPTKERN.is_primitive_call)
                     (kernel_mode := MPTKERN.kernel_mode)
                  ).
          apply MPTKERN.exec_load_exec_loadex.
          apply MPTKERN.exec_store_exec_storeex.
          apply MPTKERN.extcall_not_primitive.
          apply MPTKERN.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.

          apply (MPTKERNCODE.pt_init_correct sge bset_cr3 hset_cr31 hset_cr32 hset_cr33 bset_pe hset_pe1 hset_pe2 hset_pe3 bpt_init_kern hpt_init_kern1 hpt_init_kern2 hpt_init_kern3 _ H9 _ _ _ _ H10 H2 refl_equal).
          assumption.
          assumption.
          assumption.
          assumption.
          subst; reflexivity.
          unfold MPTKERN.kernel_mode.
          split; assumption.

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
          (MPTINIT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                             (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) prog) 
          (MPTKERN.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                             (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) 
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) tprog). 
    Proof.
      eapply PTINITGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End PTINITGENIMPL.
