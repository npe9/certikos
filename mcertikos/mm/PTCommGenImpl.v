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
Require Import MPTCommon.
Require Import MPTOp.
Require Import MPTIntro.
Require Export PTCommGen.
Require Import MPTOpCode.
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

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module PTCOMMGENIMPL.
  Export PTCommGen.PTCOMMGEN.

  Lemma hprim_finite_type':
    forall
      (Q: MPTCOMM.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      (forall p, Q p) + {p | ~ Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MPTCOMM.PSetPE)...
    destruct (Q_dec MPTCOMM.PAlloc)...
    destruct (Q_dec MPTCOMM.PFree)...
    destruct (Q_dec MPTCOMM.PSetPT)...
    destruct (Q_dec MPTCOMM.PPTRead)...
    destruct (Q_dec MPTCOMM.PPTInsert)...
    destruct (Q_dec MPTCOMM.PPTRmv)...
    destruct (Q_dec MPTCOMM.PPTIn)...
    destruct (Q_dec MPTCOMM.PPTOut)...
    destruct (Q_dec MPTCOMM.PTrapIn)...
    destruct (Q_dec MPTCOMM.PTrapOut)...
    destruct (Q_dec MPTCOMM.PHostIn)...
    destruct (Q_dec MPTCOMM.PHostOut)...
    destruct (Q_dec MPTCOMM.PTrapGet)...
    destruct (Q_dec MPTCOMM.PTrapRet)...
    destruct (Q_dec MPTCOMM.PPTInitComm)...
    left; destruct p; assumption.
  Defined.    

  Corollary hprim_finite_type:
    forall
      (Q: MPTCOMM.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof.
    intros.
    destruct (hprim_finite_type' Q Q_dec).
     left; trivial.
    destruct s.
    right.
    intro ABS.
    apply n.
    apply ABS.
  Defined.


 Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MPTCOMM.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) 
                                     (kern_high:=kern_high) (maxpage:=maxpage)) .
    Notation LDATA := (MPTINTRO.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                      (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (fundef (external_function:= MPTCOMM.primOp)).
    Notation Lfundef := (fundef (external_function:= MPTOP.primOp)).

    Notation funkind := (funkind (low := MPTOP.primOp) Asm.code (Clight.fundef (external_function := MPTOP.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: MPTCOMM.primOp): funkind :=
      match p with
        | MPTCOMM.PSetPE => Code _ (AST.External MPTOP.PSetPE)
        | MPTCOMM.PAlloc => Code _ (AST.External MPTOP.PAlloc)
        | MPTCOMM.PFree => Code _ (AST.External MPTOP.PFree)
        | MPTCOMM.PSetPT => Code _ (AST.External MPTOP.PSetPT)
        | MPTCOMM.PPTRead => Code _ (AST.External MPTOP.PPTRead)
        | MPTCOMM.PPTInsert => SourceFun (Clight.External MPTOP.PPTInsert (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) tvoid) dummy
        | MPTCOMM.PPTRmv => SourceFun (Clight.External MPTOP.PPTRmv (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) tvoid) dummy
        | MPTCOMM.PPTIn => Code _ (AST.External MPTOP.PPTIn)
        | MPTCOMM.PPTOut => Code _ (AST.External MPTOP.PPTOut)
        | MPTCOMM.PTrapIn => Code _ (AST.External MPTOP.PTrapIn)
        | MPTCOMM.PTrapOut => Code _ (AST.External MPTOP.PTrapOut)
        | MPTCOMM.PHostIn => Code _ (AST.External MPTOP.PHostIn)
        | MPTCOMM.PHostOut => Code _ (AST.External MPTOP.PHostOut)
        | MPTCOMM.PTrapGet => Code _ (AST.External MPTOP.PTrapGet)
        | MPTCOMM.PTrapRet => Code _ (AST.External MPTOP.PTrapRet)
        | MPTCOMM.PPTInitComm => SourceFun (Clight.Internal MPTOPCODE.f_pt_init_comm) dummy 
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
        (set_PDX, Some (Gfun (SourceFun (Clight.External (MPTOP.PSetPDX) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: (mem_init, Some (Gfun (SourceFun (Clight.External (MPTOP.PMemInit) (Ctypes.Tcons tint Ctypes.Tnil) tvoid) dummy)))
        :: (pt_insert, Some (Gfun (SourceFun (Clight.External (MPTOP.PPTInsert) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) Ctypes.Tvoid) dummy)))
        :: (pt_rmv, Some (Gfun (SourceFun (Clight.External (MPTOP.PPTRmv) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MPTCOMM.primOp (low := MPTOP.primOp) (Clight.fundef (external_function := MPTOP.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit MPTCOMM.primOp (low := MPTOP.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MPTCOMM.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MPTOP.primOp)).

    Let Im_pt_init_comm: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTCOMM.PPTInitComm).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because MPTCOMM.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

    Lemma extfun_compilation_succeeds_dec:
      (forall p clight asmfallback, 
        source_implem_extfuns p = SourceFun clight asmfallback ->
        exists asm, transf_clight_fundef clight = OK asm) +
      { ep |
      exists e p clight asmfallback, 
        source_implem_extfuns p = SourceFun clight asmfallback /\
        transf_clight_fundef clight = Error e /\
        ep = (e, p)}.
    Proof.
      refine (_ (hprim_finite_type' (fun p => ~ exists e clight asmfallback,
                                                source_implem_extfuns p = SourceFun clight asmfallback /\
        transf_clight_fundef clight = Error e
                                    ) _)).
      destruct 1.
       left. intros.
       case_eq (transf_clight_fundef clight); eauto.
       intros. destruct (n p). eauto.
      destruct s.
      right.
      revert n.
      case_eq (source_implem_extfuns x).
       intros until 1.
       case_eq (transf_clight_fundef sf).
        intros. destruct n. intro. destruct H1 as [? [? [? [? ?]]]]. congruence.
       intros. exists (e, x). esplit. esplit. esplit. esplit. split. eassumption. split. eassumption. reflexivity.
      intros. destruct n. intro.  destruct H0 as [? [? [? [? ?]]]]. congruence.
     intro.
     destruct (source_implem_extfuns p).
      case_eq (transf_clight_fundef sf).
       intros. left. intro. destruct H0  as [? [? [? [? ?]]]]. congruence.
      right. intro. apply H0. eauto.
     left. intro. destruct H  as [? [? [? [? ?]]]]. congruence.
   Defined.
    
    Lemma extfun_compilation_succeeds_dec':
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

    Let TRANSF: PTCOMMGEN.transf_program Im_pt_init_comm impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := MPTOP.primOp) := source_program_only source_implem prog.
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

    (** set_PDX *)

    Let bset_PDX: block := Genv.genv_next ge + Z.of_nat 0.

    Let hset_PDX1 : Genv.find_symbol sge set_PDX = Some bset_PDX. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_PDX).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_PDX2 : Genv.find_funct sge (Vptr bset_PDX Int.zero) = Some (Clight.External (MPTOP.PSetPDX) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_PDX _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_PDX3 : Clight.type_of_global sge bset_PDX = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_PDX).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_PDX. unfold Asm.fundef. omega.
      intros.
      simpl in hset_PDX2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_PDX2. reflexivity.
    Qed.     

    (** mem_init *)

    Let bmem_init: block := Genv.genv_next ge + Z.of_nat 1.

    Let hmem_init1 : Genv.find_symbol sge mem_init = Some bmem_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ mem_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hmem_init2 : Genv.find_funct sge (Vptr bmem_init Int.zero) = Some (Clight.External (MPTOP.PMemInit) (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ mem_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hmem_init3 : Clight.type_of_global sge bmem_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bmem_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bmem_init. unfold Asm.fundef. omega.
      intros.
      simpl in hmem_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hmem_init2. reflexivity.
    Qed. 

    (** pt_insert *)

    Let bpt_insert: block := Genv.genv_next ge + Z.of_nat 2.

    Let hpt_insert1 : Genv.find_symbol sge pt_insert = Some bpt_insert. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_insert).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_insert2 : Genv.find_funct sge (Vptr bpt_insert Int.zero) = Some (Clight.External (MPTOP.PPTInsert) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_insert _ _)).
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

    (** pt_rmv *)

    Let bpt_rmv: block := Genv.genv_next ge + Z.of_nat 3.

    Let hpt_rmv1 : Genv.find_symbol sge pt_rmv = Some bpt_rmv. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_rmv).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_rmv2 : Genv.find_funct sge (Vptr bpt_rmv Int.zero) = Some (Clight.External (MPTOP.PPTRmv) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_rmv _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hpt_rmv3 : Clight.type_of_global sge bpt_rmv = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_rmv).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_rmv. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_rmv2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_rmv2. reflexivity.
    Qed.     

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Context {mem__MPTCOMM} {mem__MPTOP}
              `{HHmem: !LayerMemoryModel HDATA mem__MPTCOMM}
              `{HLmem: !LayerMemoryModel LDATA mem__MPTOP}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__MPTCOMM mem__MPTOP}.

      Notation HLoad := (MPTCOMM.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (MPTCOMM.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (MPTOP.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (MPTOP.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA MPTCOMM.primOp mem__MPTCOMM :=
        MPTCOMM.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (real_ptp:= real_ptp)
                          (Hmem:= HHmem) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA MPTOP.primOp mem__MPTOP :=
        MPTOP.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (HPS:= HPS).

      Notation lstep := (MPTOP.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS:= HPS)
                                    (real_nps:= real_nps) (real_AT:= real_AT)).

      Let pt_init_comm_spec:
        forall m0 rs b sig labd' mbi_adr,
          let labd := Mem.get_abstract_data m0 in
          rs PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_pt_init_comm)
          -> sig = mksignature (Tint::nil) None 
          -> MPTOP.pt_init_comm (real_AT:= real_AT) (kern_high:=kern_high) (maxpage:=maxpage) labd real_nps 
                                (real_AT (MPTINTRO.AT (MPTINTRO.ADT labd)))
                                (real_ptp (MPTINTRO.ptpool (MPTINTRO.ADT labd)))
                                (Int.unsigned mbi_adr) = Some labd'
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTCOMM.PPTInitComm)
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
                     MPTCOMM.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTOP.primitive_call)
                     (is_primitive_call := MPTOP.is_primitive_call)
                     (kernel_mode := MPTINTRO.kernel_mode)
                  ).
          apply MPTOP.exec_load_exec_loadex.
          apply MPTOP.exec_store_exec_storeex.
          apply MPTOP.extcall_not_primitive.
          apply MPTOP.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.
          eapply MPTOPCODE.pt_init_comm_correct.
          2: eassumption. eassumption. assumption.
          2: eassumption. eassumption. assumption.
          2: eassumption. eassumption. assumption.
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
          apply MPTOP.pt_init_comm_eq in H2.
          unfold MPTOP.pt_init_comm_aux in H2.
          case_eq (MPTINTRO.mem_init_aux labd real_nps
           (real_AT (MPTOP.AT (MPTINTRO.ADT labd))) 
           (Int.unsigned mbi_adr)); [intros ? mi | intro mi]; rewrite mi in H2; try discriminate H2.
          functional inversion mi.
          unfold adt, labd in *.
          destruct (MPTINTRO.INV (Mem.get_abstract_data m0)).
          auto.
          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
          unfold loc_external_result.
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
          (MPTCOMM.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                             (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= CDataTypes.HPS4) 
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= CInitSpecsMPTOp.real_ptp) prog) 
          (MPTOP.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                           (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS:= HPS) tprog). 
    Proof.
      eapply (PTCOMMGEN.transf_program_correct); simpl; eauto.
      Grab Existential Variables.
      vm_compute.
      reflexivity.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End PTCOMMGENIMPL.
