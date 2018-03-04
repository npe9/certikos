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
Require Import MAL.
Require Import MALOp.
Require Import ZArith.Zwf.
Require Import MALOpCode.
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
Require Export ALGen.
Require Import Implementation.
Require Import SeparateCompiler.
Require Import ClightImplemExtra.
Require Import LayerDefinition.
Require Import RealParams.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module ALGENIMPL.
  Export ALGen.ALGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MALT.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MALT.PSetPE)...
    destruct (Q_dec MALT.PSetPT)...
    destruct (Q_dec MALT.PAlloc)...
    destruct (Q_dec MALT.PFree)...
    destruct (Q_dec MALT.PTrapIn)...
    destruct (Q_dec MALT.PTrapOut)...
    destruct (Q_dec MALT.PHostIn)...
    destruct (Q_dec MALT.PHostOut)...
    destruct (Q_dec MALT.PTrapGet)...
    destruct (Q_dec MALT.PTrapRet)...
    destruct (Q_dec MALT.PMemInit)...
    left; destruct p; assumption.
  Defined.    

 Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MALOP.AbData (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage)) .
    Notation LDATA := (MALOP.AbData (kern_low:=kern_low) (kern_high:=kern_high) (maxpage:=maxpage)).
  
    Notation Hfundef := (fundef (external_function:= MALT.primOp)).
    Notation Lfundef := (fundef (external_function:= MALOP.primOp)).

    Notation funkind := (funkind (low := MALOP.primOp) Asm.code (Clight.fundef (external_function := MALOP.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: MALT.primOp): funkind :=
      match p with
        | MALT.PSetPE => Code _ (AST.External MALOP.PSetPE)
        | MALT.PSetPT => Code _ (AST.External MALOP.PSetPT)
        | MALT.PAlloc => SourceFun (Clight.Internal (MALOPCODE.f_palloc)) dummy
        | MALT.PFree => SourceFun (Clight.Internal (MALOPCODE.f_pfree)) dummy
        | MALT.PTrapIn => Code _ (AST.External MALOP.PTrapIn)
        | MALT.PTrapOut => Code _ (AST.External MALOP.PTrapOut)
        | MALT.PHostIn => Code _ (AST.External MALOP.PHostIn)
        | MALT.PHostOut => Code _ (AST.External MALOP.PHostOut)
        | MALT.PTrapGet => Code _ (AST.External MALOP.PTrapGet)
        | MALT.PTrapRet => Code _ (AST.External MALOP.PTrapRet)
        | MALT.PMemInit => Code _ (AST.External MALOP.PMemInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (at_get, Some (Gfun (SourceFun (Clight.External (MALOP.PATGetU) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (at_set, Some (Gfun (SourceFun (Clight.External (MALOP.PATSetU) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: (is_norm, Some (Gfun (SourceFun (Clight.External (MALOP.PIsNorm) (Ctypes.Tcons tint Ctypes.Tnil) tint) dummy)))
        :: (get_nps, Some (Gfun (SourceFun (Clight.External (MALOP.PGetNps) Ctypes.Tnil tint) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MALT.primOp (low := MALOP.primOp) (Clight.fundef (external_function := MALOP.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit MALT.primOp (low := MALOP.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MALT.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MALOP.primOp)).

    Let Im_palloc: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALT.PAlloc).
    Let Im_pfree: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALT.PFree).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because MALT.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: ALGEN.transf_program Im_palloc Im_pfree impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := MALOP.primOp) := source_program_only source_implem prog.
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

    (** at_set *)

    Let bat_set: block := Genv.genv_next ge + Z.of_nat 1.

    Let hat_set1 : Genv.find_symbol sge at_set = Some bat_set. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ at_set).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hat_set2 : Genv.find_funct sge (Vptr bat_set Int.zero) = Some (Clight.External (MALOP.PATSetU) (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ at_set _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hat_set3 : Clight.type_of_global sge bat_set = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons tint Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bat_set).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bat_set. unfold Asm.fundef. omega.
      intros.
      simpl in hat_set2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hat_set2. reflexivity.
    Qed.     

    (** is_norm *)

    Let bis_norm: block := Genv.genv_next ge + Z.of_nat 2.

    Let his_norm1 : Genv.find_symbol sge is_norm = Some bis_norm. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ is_norm).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let his_norm2 : Genv.find_funct sge (Vptr bis_norm Int.zero) = Some (Clight.External (MALOP.PIsNorm) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ is_norm _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let his_norm3 : Clight.type_of_global sge bis_norm = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bis_norm).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bis_norm. unfold Asm.fundef. omega.
      intros.
      simpl in his_norm2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite his_norm2. reflexivity.
    Qed. 

    (** at_get *)

    Let bat_get: block := Genv.genv_next ge + Z.of_nat 0.

    Let hat_get1 : Genv.find_symbol sge at_get = Some bat_get. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ at_get).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hat_get2 : Genv.find_funct sge (Vptr bat_get Int.zero) = Some (Clight.External (MALOP.PATGetU) (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ at_get _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hat_get3 : Clight.type_of_global sge bat_get = Some (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bat_get).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bat_get. unfold Asm.fundef. omega.
      intros.
      simpl in hat_get2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hat_get2. reflexivity.
    Qed.

    (** get_nps *)

    Let bget_nps: block := Genv.genv_next ge + Z.of_nat 3.

    Let hget_nps1 : Genv.find_symbol sge get_nps = Some bget_nps. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ get_nps).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hget_nps2 : Genv.find_funct sge (Vptr bget_nps Int.zero) = Some (Clight.External (MALOP.PGetNps) (Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ get_nps _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hget_nps3 : Clight.type_of_global sge bget_nps = Some (Ctypes.Tfunction (Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bget_nps).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bget_nps. unfold Asm.fundef. omega.
      intros.
      simpl in hget_nps2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hget_nps2. reflexivity.
    Qed.

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.
      

    Context {mem__MALT} {mem__MALOP}
            `{HHmem: !LayerMemoryModel HDATA mem__MALT}
            `{HLmem: !LayerMemoryModel LDATA mem__MALOP}
            `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__MALT mem__MALOP}.

    Notation HLoad:= (MALT.exec_loadex (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (Hmem:= HHmem)
                                         (PageFaultHandler_LOC := PageFaultHandler_LOC)).

    Notation HStore:= (MALT.exec_storeex (NPT_LOC:= NPT_LOC) (PgSize:= PgSize) (Hmem:= HHmem)
                                           (PageFaultHandler_LOC := PageFaultHandler_LOC)
                                           (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage)).      
      
    Notation LLoad:= (MALOP.exec_loadex (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (Hmem:= HLmem)
                                          (PageFaultHandler_LOC := PageFaultHandler_LOC)).

    Notation LStore:= (MALOP.exec_storeex (NPT_LOC:= NPT_LOC) (PgSize:= PgSize) (Hmem:= HLmem)
                                            (PageFaultHandler_LOC := PageFaultHandler_LOC)).

    Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA MALT.primOp mem__MALT :=
        MALT.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= HHmem).

    Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA MALOP.primOp mem__MALOP :=
        MALOP.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (Hmem:= HLmem).

    Notation lstep := (MALOP.step (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)
                                    (real_nps:= real_nps) (real_AT:= real_AT)).

    Let palloc_spec:
        forall m rs b adt n sg,
          rs PC = Vptr b Int.zero
          -> MALOP.palloc (Mem.get_abstract_data m) = Some (adt, Int.unsigned n)
          -> Genv.find_funct_ptr tge b = Some Im_palloc
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MALT.PAlloc)
          -> asm_invariant tge (State rs m)
          -> sg = mksignature nil (Some Tint)
          -> extcall_arguments rs m sg nil
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m)) f' 
               /\ Memtype.Mem.inject f' m m0'
               /\ Mem.nextblock m <= Mem.nextblock m0'
               /\ plus lstep tge (State rs m) E0 (State r_ (Mem.put_abstract_data m0' adt))
               /\ r_ # (loc_external_result sg) = (Vint n)
               /\ r_ PC = rs RA
               /\ r_ # ESP = rs # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (rs (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.   
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MALT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MALOP.primitive_call)
                     (is_primitive_call := MALOP.is_primitive_call)
                     (kernel_mode := MALOP.kernel_mode)
                  ).
          apply MALOP.exec_load_exec_loadex.
          apply MALOP.exec_store_exec_storeex.
          apply MALOP.extcall_not_primitive.
          apply MALOP.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.
          eapply MALOPCODE.palloc_correct.
          2: eassumption. eassumption. assumption.
          2: eassumption. eassumption. assumption.
          2: eassumption. eassumption. assumption.
          2: eassumption. eassumption. assumption.
          assumption.
          apply MALOP.palloc_eq in H0.
          functional inversion H0.
          unfold adt0 in *.
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
          unfold MALOP.kernel_mode.
          apply MALOP.palloc_eq in H0.
          functional inversion H0.
          unfold adt0 in *.
          split; assumption.
          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m)) adt) in PLUS.
          unfold loc_external_result.
          inversion H10.
          eauto 11.
          rewrite Mem.put_put_abstract_data.
          replace adt with (Mem.get_abstract_data m_asm).
          rewrite Mem.put_get_abstract_data.
          reflexivity.
          erewrite <- Mem.get_abstract_data_inject_inside; eauto.
          rewrite Mem.get_put_abstract_data.
          reflexivity.
        Qed.

    Let free_spec:
        forall m rs b adt n sg,
          rs PC = Vptr b Int.zero
          -> MALOP.pfree (Mem.get_abstract_data m) (Int.unsigned n) = Some adt
          -> Genv.find_funct_ptr tge b = Some Im_pfree
          -> (forall b o, rs ESP = Vptr b o -> Mem.tget m b = Some Tag_stack)
          -> rs ESP <> Vundef
          -> rs RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External MALT.PFree)
          -> asm_invariant tge (State rs m)
          -> sg = mksignature (Tint::nil) None
          -> extcall_arguments rs m sg (Vint n:: nil)
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
                     MALT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MALOP.primitive_call)
                     (is_primitive_call := MALOP.is_primitive_call)
                     (kernel_mode := MALOP.kernel_mode)
                  ).
          apply MALOP.exec_load_exec_loadex.
          apply MALOP.exec_store_exec_storeex.
          apply MALOP.extcall_not_primitive.
          apply MALOP.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros.
          eapply MALOPCODE.pfree_correct.
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
          unfold MALOP.kernel_mode.
          apply MALOP.pfree_eq in H0.
          functional inversion H0.
          unfold adt0 in *.
          split; assumption.
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

    Theorem transf_program_correct:
        Smallstep.backward_simulation 
          (MALT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                          (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) prog) 
          (MALOP.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                           (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) tprog). 
    Proof.
      eapply ALGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End ALGENIMPL.
