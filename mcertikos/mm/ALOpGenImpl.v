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
Require Import MALOp.
Require Import MALInit.
Require Import ZArith.Zwf.
Require Import MALInitCode.
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
Require Export ALOpGen.
Require Import Implementation.
Require Import SeparateCompiler.
Require Import ClightImplemExtra.
Require Import LayerDefinition.
Require Import RealParams.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module ALOPGENIMPL.
  Export ALOpGen.ALOPGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MALOP.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MALOP.PSetPE)...
    destruct (Q_dec MALOP.PSetPT)...
    destruct (Q_dec MALOP.PGetNps)...
    destruct (Q_dec MALOP.PIsNorm)...
    destruct (Q_dec MALOP.PATGetU)...
    destruct (Q_dec MALOP.PATSetU)...
    destruct (Q_dec MALOP.PTrapIn)...
    destruct (Q_dec MALOP.PTrapOut)...
    destruct (Q_dec MALOP.PHostIn)...
    destruct (Q_dec MALOP.PHostOut)...
    destruct (Q_dec MALOP.PTrapGet)...
    destruct (Q_dec MALOP.PTrapRet)...
    destruct (Q_dec MALOP.PMemInit)...
    left; destruct p; assumption.
  Defined.    

  Local Open Scope Z_scope.

 Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MALOP.AbData (kern_high := kern_high) (kern_low := kern_low) (maxpage:= maxpage)).
    Notation LDATA := (MALINIT.AbData (PgSize := PgSize) (kern_low := kern_low)).
  
    Notation Hfundef := (fundef (external_function:= MALOP.primOp)).
    Notation Lfundef := (fundef (external_function:= MALINIT.primOp)).

    Notation funkind := (funkind Asm.code (Clight.fundef (external_function := MALINIT.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: MALOP.primOp): funkind :=
      match p with
        | MALOP.PSetPE => Code _ (AST.External MALINIT.PSetPE)
        | MALOP.PSetPT => Code _ (AST.External MALINIT.PSetPT)
        | MALOP.PTrapIn => Code _ (AST.External MALINIT.PTrapIn)
        | MALOP.PTrapOut => Code _ (AST.External MALINIT.PTrapOut)
        | MALOP.PHostIn => Code _ (AST.External MALINIT.PHostIn)
        | MALOP.PHostOut => Code _ (AST.External MALINIT.PHostOut)
        | MALOP.PTrapGet => Code _ (AST.External MALINIT.PTrapGet)
        | MALOP.PTrapRet => Code _ (AST.External MALINIT.PTrapRet)
        | MALOP.PGetNps => Code _ (AST.External MALINIT.PGetNps)
        | MALOP.PIsNorm => Code _ (AST.External MALINIT.PIsNorm)
        | MALOP.PATGetU => Code _ (AST.External MALINIT.PATGetU)
        | MALOP.PATSetU => Code _ (AST.External MALINIT.PATSetU)
        | MALOP.PMemInit => SourceFun (Clight.Internal (MALINITCODE.f_mem_init set_nps set_norm get_size get_mms get_mml is_usable boot_loader)) dummy
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (set_nps, Some (Gfun (SourceFun (Clight.External (MALINIT.PSetNps) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: (set_norm, Some (Gfun (SourceFun (Clight.External (MALINIT.PATSetNorm) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: (get_size, Some (Gfun (SourceFun (Clight.External (MALINIT.PGetSize) Ctypes.Tnil tint) dummy)))
        :: (get_mms, Some (Gfun (SourceFun (Clight.External (MALINIT.PMMGetS) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (get_mml, Some (Gfun (SourceFun (Clight.External (MALINIT.PMMGetL) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (is_usable, Some (Gfun (SourceFun (Clight.External (MALINIT.PIsUsable) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (boot_loader, Some (Gfun (SourceFun (Clight.External (MALINIT.PBootLoader) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MALOP.primOp (low := MALINIT.primOp) (Clight.fundef (external_function := MALINIT.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit MALOP.primOp (low := MALINIT.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MALOP.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MALINIT.primOp)).

    Let Im_meminit: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALOP.PMemInit).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because MALOP.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: ALOPGEN.transf_program Im_meminit impl_glbl prog = OK tprog.
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

    Hypothesis prog_nonempty:
      prog_defs_names prog <> nil.

    Hypothesis prog_main_valid:
      ~ Plt' (prog_main prog) (prog_first_symbol prog).

    Hypothesis prog_first_valid:
      ~ Plt' (prog_first_symbol prog) (get_next_symbol (map fst impl_glbl)).
        
    Let NEW_INJ:  (forall s', Genv.find_symbol ge s' <> None -> 
                                     ~ In s' (map fst impl_glbl)).
    Proof.
      change impl_glbl with (implem_new_globs im).
      apply new_ids_fresh.
      assumption.
    Qed.

    Let sprog : Clight.program (external_function := MALINIT.primOp) := source_program_only source_implem prog.
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
      exploit transf_clight_fundef_to_program; eauto.
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

    (** boot_loader *)

    Let bbootloader : block := Genv.genv_next ge + Z.of_nat 6.

    Let hboot_loader1 : Genv.find_symbol sge boot_loader = Some bbootloader. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ boot_loader).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Let hboot_loader2 : Genv.find_funct sge (Vptr bbootloader Int.zero) = Some (Clight.External (MALINIT.PBootLoader) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ boot_loader _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.

    Let hboot_loader3: Clight.type_of_global sge bbootloader = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bbootloader).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bbootloader. unfold Asm.fundef. omega.
      intros.
      simpl in hboot_loader2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hboot_loader2. reflexivity.
    Qed.

    (** get_size *)

    Let bgetsize : block := Genv.genv_next ge + Z.of_nat 2.

    Let hget_size1 : Genv.find_symbol sge get_size = Some bgetsize.
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_size).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.

    Let hget_size2 : Genv.find_funct sge (Vptr bgetsize Int.zero) = Some (Clight.External (MALINIT.PGetSize) Ctypes.Tnil tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_size _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.

    Let hget_size3 : Clight.type_of_global sge bgetsize = Some (Ctypes.Tfunction Ctypes.Tnil tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bgetsize).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bgetsize. unfold Asm.fundef. omega.
      intros.
      simpl in hget_size2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_size2. reflexivity.
    Qed.
    
    (** get_mms *)

    Let bgetmms: block := Genv.genv_next ge + Z.of_nat 3.
    
    Let hget_mms1 : Genv.find_symbol sge get_mms = Some bgetmms. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_mms).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
   
    Let hget_mms2 : Genv.find_funct sge (Vptr bgetmms Int.zero) = Some (Clight.External (MALINIT.PMMGetS) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_mms _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.

    Let hget_mms3 : Clight.type_of_global sge bgetmms = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bgetmms).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bgetmms. unfold Asm.fundef. omega.
      intros.
      simpl in hget_mms2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_mms2. reflexivity.
    Qed.

    (** get_mml *)

    Let bgetmml: block := Genv.genv_next ge + Z.of_nat 4.

    Let hget_mml1 : Genv.find_symbol sge get_mml = Some bgetmml. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_mml).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hget_mml2 : Genv.find_funct sge (Vptr bgetmml Int.zero) = Some (Clight.External (MALINIT.PMMGetL) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_mml _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hget_mml3 : Clight.type_of_global sge bgetmml = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bgetmml).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bgetmml. unfold Asm.fundef. omega.
      intros.
      simpl in hget_mml2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_mml2. reflexivity.
    Qed.
    
    (** is_usable *)

    Let bisusable: block := Genv.genv_next ge + Z.of_nat 5.

    Let his_usable1 : Genv.find_symbol sge is_usable = Some bisusable. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ is_usable).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let his_usable2 : Genv.find_funct sge (Vptr bisusable Int.zero) = Some (Clight.External (MALINIT.PIsUsable) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ is_usable _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let his_usable3 : Clight.type_of_global sge bisusable = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bisusable).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bisusable. unfold Asm.fundef. omega.
      intros.
      simpl in his_usable2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite his_usable2. reflexivity.
    Qed.

    (** set_norm *)

    Let batsetnorm: block := Genv.genv_next ge + Z.of_nat 1.

    Let hset_norm1 : Genv.find_symbol sge set_norm = Some batsetnorm. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_norm).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hset_norm2 : Genv.find_funct sge (Vptr batsetnorm Int.zero) = Some (Clight.External (MALINIT.PATSetNorm) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_norm _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hset_norm3 : Clight.type_of_global sge batsetnorm = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge batsetnorm).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold batsetnorm. unfold Asm.fundef. omega.
      intros.
      simpl in hset_norm2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_norm2. reflexivity.
    Qed.

    (** set_nps *)

    Let bsetnps: block := Genv.genv_next ge + Z.of_nat 0.

    Let hset_nps1 : Genv.find_symbol sge set_nps = Some bsetnps. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_nps).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hset_nps2 : Genv.find_funct sge (Vptr bsetnps Int.zero) = Some (Clight.External (MALINIT.PSetNps) (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_nps _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hset_nps3 : Clight.type_of_global sge bsetnps = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bsetnps).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bsetnps. unfold Asm.fundef. omega.
      intros.
      simpl in hset_nps2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_nps2. reflexivity.
    Qed. 

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.
      
    Context {mem__MALOP mem__MALINIT}
      `{HHmem: !LayerMemoryModel HDATA mem__MALOP}
      `{HLmem: !LayerMemoryModel LDATA mem__MALINIT}
      `{HLayerInject: !LayerMemoryInjections HDATA LDATA _ _}.

    Instance HLayer: LayerDefinition HDATA MALOP.primOp mem__MALOP :=
      MALOP.layer_def (maxpage := maxpage) (real_nps := real_nps) (real_AT := real_AT).

    Instance LLayer: LayerDefinition LDATA MALINIT.primOp mem__MALINIT :=
      MALINIT.layer_def (PgSize := PgSize) (real_size := real_size) (real_mm := real_mm) (kern_low := kern_low) (maxpage := maxpage).

      Notation HLoad:= (MALOP.exec_loadex (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) 
                                          (PageFaultHandler_LOC := PageFaultHandler_LOC)).

      Notation HStore:= (MALOP.exec_storeex (NPT_LOC:= NPT_LOC) (PgSize:= PgSize)
                                            (PageFaultHandler_LOC := PageFaultHandler_LOC)).

      Notation LLoad := (MALINIT.exec_loadex (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC := PageFaultHandler_LOC)).
      
      Notation LStore:= ( MALINIT.exec_storeex (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC := PageFaultHandler_LOC)).

      Notation lstep:= (MALINIT.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC := PageFaultHandler_LOC)
                                     (maxpage:= maxpage) (real_size:= real_size) (real_mm:= real_mm)).

      Notation LADT := MALINIT.ADT.

        Let meminit_spec:
        forall r' b  m0 labd' mbi_adr sg,
          let labd := Mem.get_abstract_data m0 in
          r' PC = Vptr b Int.zero
          -> Genv.find_funct_ptr tge b = Some (Im_meminit)
          -> MALINIT.mem_init (kern_high:=kern_high) (maxpage:=maxpage) labd real_size real_nps real_mm 
                              (real_AT (MALINIT.AT (LADT labd))) (Int.unsigned mbi_adr) = Some labd'
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MALOP.PMemInit)
          -> asm_invariant tge (State r' m0)
          -> sg = mksignature (Tint::nil) None
          -> extcall_arguments r' m0 sg (Vint mbi_adr::nil)
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'
               /\ plus lstep tge (State r' m0) E0
                       (State r_ (Mem.put_abstract_data m0' labd'))
               /\ True
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.          
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MALOP.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MALINIT.primitive_call)
                     (is_primitive_call := MALINIT.is_primitive_call)
                     (kernel_mode := MALINIT.kernel_mode)
                  ).
          apply MALINIT.exec_load_exec_loadex.
          apply MALINIT.exec_store_exec_storeex.
          apply MALINIT.extcall_not_primitive.
          apply MALINIT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply MALINITCODE.mem_init_correct.
           2: eassumption. eassumption. assumption.
           2: eassumption. eassumption. assumption.
           2: eassumption. eassumption. assumption.
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
          unfold MALINIT.kernel_mode.
          destruct (MALINIT.INV (Mem.get_abstract_data m0)).
          apply MALINIT.mem_init_eq in H1.
          functional inversion H1.
          functional inversion H10; unfold adt0 in *; auto.
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
          (MALOP.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage) 
                           (PageFaultHandler_LOC:= PageFaultHandler_LOC) (real_nps:= real_nps) (real_AT:= real_AT) prog) 
          (MALINIT.semantics (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (maxpage:= maxpage) 
                             (real_size:= real_size) (real_mm:= real_mm) tprog).
    Proof.
      eapply ALOPGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      omega.
      inversion real_params; auto.
      inversion real_params; auto.
      inversion real_params; auto. 
      inversion real_params; auto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End ALOPGENIMPL.
