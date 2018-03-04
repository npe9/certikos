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
Require Import MPTNew.
Require Import MPTBit.
Require Export PTNewGen.
Require Import MPTBitCode.
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

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module PTNEWGENIMPL.
  Export PTNewGen.PTNEWGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MPTNEW.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec MPTNEW.PAlloc)...
    destruct (Q_dec MPTNEW.PFree)...
    destruct (Q_dec MPTNEW.PSetPT)...
    destruct (Q_dec MPTNEW.PPTRead)...
    destruct (Q_dec MPTNEW.PPTResv)...
    destruct (Q_dec MPTNEW.PPTNew)...
    destruct (Q_dec MPTNEW.PPTFree)...
    destruct (Q_dec MPTNEW.PPTIn)...
    destruct (Q_dec MPTNEW.PPTOut)...
    destruct (Q_dec MPTNEW.PTrapIn)...
    destruct (Q_dec MPTNEW.PTrapOut)...
    destruct (Q_dec MPTNEW.PHostIn)...
    destruct (Q_dec MPTNEW.PHostOut)...
    destruct (Q_dec MPTNEW.PTrapGet)...
    destruct (Q_dec MPTNEW.PTrapRet)...
    destruct (Q_dec MPTNEW.PPMapInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MPTNEW.AbData(PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                                    (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA := (MPTBIT.AbData(PgSize:=PgSize)(num_proc:=num_proc) (kern_low:=kern_low)
                                    (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (Asm.fundef (external_function:= MPTNEW.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= MPTBIT.primOp)).

    Notation funkind := (funkind (low:= MPTBIT.primOp) Asm.code (Clight.fundef (external_function := MPTBIT.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: MPTNEW.primOp): funkind :=
      match p with
        | MPTNEW.PAlloc => Code _ (AST.External MPTBIT.PAlloc)
        | MPTNEW.PFree => Code _ (AST.External MPTBIT.PFree)
        | MPTNEW.PSetPT => Code _ (AST.External MPTBIT.PSetPT)
        | MPTNEW.PPTRead => Code _ (AST.External MPTBIT.PPTRead)
        | MPTNEW.PPTResv => SourceFun (Clight.Internal MPTBITCODE.f_pt_resv) (AST.Internal nil)
        | MPTNEW.PPTNew => SourceFun (Clight.Internal MPTBITCODE.f_pt_new) (AST.Internal nil)
        | MPTNEW.PPTFree => SourceFun (Clight.Internal MPTBITCODE.f_pt_free) (AST.Internal nil)
        | MPTNEW.PPTIn => Code _ (AST.External MPTBIT.PPTIn)
        | MPTNEW.PPTOut => Code _ (AST.External MPTBIT.PPTOut)
        | MPTNEW.PTrapIn => Code _ (AST.External MPTBIT.PTrapIn)
        | MPTNEW.PTrapOut => Code _ (AST.External MPTBIT.PTrapOut)
        | MPTNEW.PHostIn => Code _ (AST.External MPTBIT.PHostIn)
        | MPTNEW.PHostOut => Code _ (AST.External MPTBIT.PHostOut)
        | MPTNEW.PTrapGet => Code _ (AST.External MPTBIT.PTrapGet)
        | MPTNEW.PTrapRet => Code _ (AST.External MPTBIT.PTrapRet)
        | MPTNEW.PPMapInit => SourceFun (Clight.Internal MPTBITCODE.f_pmap_init) (AST.Internal nil)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (is_used, Some (Gfun (SourceFun (Clight.External (MPTBIT.PIsUsed) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (set_bit, Some (Gfun (SourceFun (Clight.External (MPTBIT.PSetBit) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: (pt_rmv1, Some (Gfun (SourceFun (Clight.External (MPTBIT.PPTRmv) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: (pt_init, Some (Gfun (SourceFun (Clight.External (MPTBIT.PPTInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: (palloc, Some (Gfun (SourceFun (Clight.External (MPTBIT.PAlloc) (Ctypes.Tnil) tint) dummy)))
        :: (pt_insert2, Some (Gfun (SourceFun (Clight.External (MPTBIT.PPTInsert) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) Ctypes.Tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MPTNEW.primOp (low := MPTBIT.primOp) (Clight.fundef (external_function := MPTBIT.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit MPTNEW.primOp (low := MPTBIT.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MPTNEW.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MPTBIT.primOp)).

    Let Im_pt_new: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTNEW.PPTNew).
    Let Im_pt_free: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTNEW.PPTFree).
    Let Im_pt_resv: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTNEW.PPTResv).
    Let Im_pmap_init: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MPTNEW.PPMapInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because MPTNEW.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: PTNEWGEN.transf_program Im_pt_new Im_pt_free Im_pt_resv Im_pmap_init impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := MPTBIT.primOp) := source_program_only source_implem prog.
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

    (** is_used *)

    Let bis_used: block := Genv.genv_next ge + Z.of_nat 0.

    Let his_used1 : Genv.find_symbol sge is_used = Some bis_used. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ is_used).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let his_used2 : Genv.find_funct sge (Vptr bis_used Int.zero) = Some (Clight.External (MPTBIT.PIsUsed) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ is_used _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let his_used3 : Clight.type_of_global sge bis_used = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bis_used).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bis_used. unfold Asm.fundef. omega.
      intros.
      simpl in his_used2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite his_used2. reflexivity.
    Qed.   

    (** set_bit *)

    Let bset_bit: block := Genv.genv_next ge + Z.of_nat 1.

    Let hset_bit1 : Genv.find_symbol sge set_bit = Some bset_bit. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_bit).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hset_bit2 : Genv.find_funct sge (Vptr bset_bit Int.zero) = Some (Clight.External (MPTBIT.PSetBit) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_bit _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hset_bit3 : Clight.type_of_global sge bset_bit = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_bit).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_bit. unfold Asm.fundef. omega.
      intros.
      simpl in hset_bit2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_bit2. reflexivity.
    Qed. 

    (** pt_rmv1 *)

    Let bpt_rmv: block := Genv.genv_next ge + Z.of_nat 2.

    Let hpt_rmv1 : Genv.find_symbol sge pt_rmv1 = Some bpt_rmv. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_rmv1).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hpt_rmv2 : Genv.find_funct sge (Vptr bpt_rmv Int.zero) = Some (Clight.External (MPTBIT.PPTRmv) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_rmv1 _ _)).
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

    (** pt_init *)

    Let bpt_init: block := Genv.genv_next ge + Z.of_nat 3.

    Let hpt_init1 : Genv.find_symbol sge pt_init = Some bpt_init. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_init).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hpt_init2 : Genv.find_funct sge (Vptr bpt_init Int.zero) = Some (Clight.External (MPTBIT.PPTInit) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_init _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hpt_init3 : Clight.type_of_global sge bpt_init = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_init).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_init. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_init2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_init2. reflexivity.
    Qed. 

    (** palloc *)

    Let bpalloc: block := Genv.genv_next ge + Z.of_nat 4.

    Let hpalloc1 : Genv.find_symbol sge palloc = Some bpalloc. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ palloc).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hpalloc2 : Genv.find_funct sge (Vptr bpalloc Int.zero) = Some (Clight.External (MPTBIT.PAlloc) (Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ palloc _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hpalloc3 : Clight.type_of_global sge bpalloc = Some (Ctypes.Tfunction (Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpalloc).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpalloc. unfold Asm.fundef. omega.
      intros.
      simpl in hpalloc2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpalloc2. reflexivity.
    Qed. 

    (** pt_insert2 *)

    Let bpt_insert: block := Genv.genv_next ge + Z.of_nat 5.

    Let hpt_insert1 : Genv.find_symbol sge pt_insert2 = Some bpt_insert. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_insert2).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hpt_insert2 : Genv.find_funct sge (Vptr bpt_insert Int.zero) = Some (Clight.External (MPTBIT.PPTInsert) (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)))) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_insert2 _ _)).
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
      
      Context {mem__MPTNEW} {mem__MPTBIT}
              `{HHmem: !LayerMemoryModel HDATA mem__MPTNEW}
              `{HLmem: !LayerMemoryModel LDATA mem__MPTBIT}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__MPTNEW mem__MPTBIT}.

      Notation HLoad := (MPTNEW.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (MPTNEW.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (MPTBIT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (MPTBIT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA MPTNEW.primOp mem__MPTNEW :=
        MPTNEW.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (real_ptp:= real_ptp)
                         (Hmem:= HHmem) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_pt:= real_pt) (Hnpc:= Hnpc)
                         (real_free_pt := real_free_pt) (real_ptb:= real_ptb).
      
      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA MPTBIT.primOp mem__MPTBIT :=
        MPTBIT.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= HLmem)
                         (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (Hnpc:= Hnpc).

      Notation lstep := (MPTBIT.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                     (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                     (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc)).

      Notation LADT := MPTBIT.ADT.

      Let pt_new_spec:
        forall m0 rs b sig labd' n,
          let labd := Mem.get_abstract_data m0 in
          rs PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_pt_new)
          -> sig = mksignature nil (Some Tint) 
          -> MPTBIT.pt_new labd = Some (labd', Int.unsigned n)
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTNEW.PPTNew)
          -> asm_invariant tge (State rs m0)
          -> extcall_arguments rs m0 sig nil                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ r_ # (loc_external_result sig) = (Vint n)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MPTNEW.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTBIT.primitive_call)
                     (is_primitive_call := MPTBIT.is_primitive_call)
                     (kernel_mode := MPTBIT.kernel_mode)
                  ).
          apply MPTBIT.exec_load_exec_loadex.
          apply MPTBIT.exec_store_exec_storeex.
          apply MPTBIT.extcall_not_primitive.
          apply MPTBIT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intro.
          exact (MPTBITCODE.pt_new_correct sge bis_used his_used1 his_used2 his_used3 bset_bit hset_bit1 hset_bit2 hset_bit3 _ H9 _ _ _ _ H2 refl_equal).
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTBIT.kernel_mode.
          apply MPTBIT.pt_new_eq in H2.
          functional inversion H2.
          unfold adt, labd in *.
          destruct (MPTBIT.INV (Mem.get_abstract_data m0)).
          auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
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

      Let pt_free_spec:
        forall m0 rs b sig labd' n,
          let labd := Mem.get_abstract_data m0 in
          rs PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_pt_free)
          -> sig = mksignature (Tint::nil) None 
          -> MPTBIT.pt_free labd (Int.unsigned n) (real_free_pt (MPTBIT.ptpool (LADT labd)) n) = Some (labd')
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTNEW.PPTFree)
          -> asm_invariant tge (State rs m0)
          -> extcall_arguments rs m0 sig (Vint n ::  nil)                     
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
                     MPTNEW.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTBIT.primitive_call)
                     (is_primitive_call := MPTBIT.is_primitive_call)
                     (kernel_mode := MPTBIT.kernel_mode)
                  ).
          apply MPTBIT.exec_load_exec_loadex.
          apply MPTBIT.exec_store_exec_storeex.
          apply MPTBIT.extcall_not_primitive.
          apply MPTBIT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intro.
          exact (MPTBITCODE.pt_free_correct sge bset_bit hset_bit1 hset_bit2 hset_bit3 bpt_rmv hpt_rmv1 hpt_rmv2 hpt_rmv3 _ H9 _ _ _ _ H2 refl_equal).
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTBIT.kernel_mode.
          apply MPTBIT.pt_free_eq in H2.
          functional inversion H2.
          unfold adt, labd in *.
          destruct (MPTBIT.INV (Mem.get_abstract_data m0)).
          auto.

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

      Let pt_resv_spec:
        forall m0 rs b adt n sig p vadr,
          rs PC = Vptr b Int.zero
          -> MPTBIT.ptResv (HPS4:=HPS4) (Hlow:=Hlow) (Hhigh:=Hhigh) 
                           (Mem.get_abstract_data m0) (Int.unsigned n)
                           (Int.unsigned vadr) (Int.unsigned p) = Some adt
          -> Genv.find_funct_ptr tge b = Some (Im_pt_resv)
          -> sig = mksignature (Tint :: Tint :: Tint :: nil) None 
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTNEW.PPTResv)
          -> asm_invariant tge (State rs m0)
          -> extcall_arguments rs m0 sig (Vint n:: Vint vadr :: Vint p :: nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m0) E0 (State r_ (Mem.put_abstract_data m0' adt))
               /\ True
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MPTNEW.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTBIT.primitive_call)
                     (is_primitive_call := MPTBIT.is_primitive_call)
                     (kernel_mode := MPTBIT.kernel_mode)
                  ).
          apply MPTBIT.exec_load_exec_loadex.
          apply MPTBIT.exec_store_exec_storeex.
          apply MPTBIT.extcall_not_primitive.
          apply MPTBIT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intro.
          functional inversion H0.
          apply MPTBIT.palloc_eq in H11.
          functional inversion H11.
          unfold adt0 in *.
          exact (MPTBITCODE.pt_resv_correct sge bpalloc hpalloc1 hpalloc2 hpalloc3 bpt_insert hpt_insert1 hpt_insert2 hpt_insert3 _ H9 _ _ _ _ _ _ H15 H0 refl_equal).
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTBIT.kernel_mode.
          functional inversion H0.
          apply MPTBIT.palloc_eq in H10.
          functional inversion H10.
          unfold adt0 in *.
          destruct (MPTBIT.INV (Mem.get_abstract_data m0)).
          auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) adt) in PLUS.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace adt with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

      Let pmap_init_spec:
        forall m0 rs b sig labd' mbi_adr,
          let labd := Mem.get_abstract_data m0 in
          rs PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_pmap_init)
          -> sig = mksignature (Tint::nil) None 
          -> MPTBIT.pmap_init (Hnpc:=Hnpc) labd real_nps 
                              (real_AT (MPTBIT.AT (LADT labd)))
                              (real_ptp (MPTBIT.ptpool (LADT labd)))
                              (real_pt (MPTBIT.ptpool (LADT labd)))
                              (real_ptb (MPTBIT.pb (LADT labd))) (Int.unsigned mbi_adr) = Some (labd')
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MPTNEW.PPMapInit)
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
                     MPTNEW.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MPTBIT.primitive_call)
                     (is_primitive_call := MPTBIT.is_primitive_call)
                     (kernel_mode := MPTBIT.kernel_mode)
                  ).
          apply MPTBIT.exec_load_exec_loadex.
          apply MPTBIT.exec_store_exec_storeex.
          apply MPTBIT.extcall_not_primitive.
          apply MPTBIT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intro.
          exact (MPTBITCODE.pmap_init_correct sge bset_bit hset_bit1 hset_bit2 hset_bit3 bpt_init hpt_init1 hpt_init2 hpt_init3 _ H9 _ _ _ _ H2 refl_equal).
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold MPTBIT.kernel_mode.
          apply MPTBIT.pmap_init_eq in H2.
          functional inversion H2.
          functional inversion H10.
          unfold adt0, labd in *.
          destruct (MPTBIT.INV (Mem.get_abstract_data m0)).
          auto.

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
          (MPTNEW.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                            (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                            (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) prog) 
          (MPTBIT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                            (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) 
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                            (Hnpc:= Hnpc) tprog).
    Proof.
      eapply PTNEWGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      vm_compute. 
      intro contra; discriminate contra.
      omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End PTNEWGENIMPL.
