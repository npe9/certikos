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
Require Import PKContextNew.
Require Import PKContext.
Require Export KContextNewGen.
Require Import PKContextCode.
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

Module KCTXTNEWGENIMPL.
  Export KContextNewGen.KCTXTNEWGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PKCTXTNEW.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PKCTXTNEW.PAlloc)...
    destruct (Q_dec PKCTXTNEW.PFree)...
    destruct (Q_dec PKCTXTNEW.PSetPT)...
    destruct (Q_dec PKCTXTNEW.PPTRead)...
    destruct (Q_dec PKCTXTNEW.PPTResv)...
    destruct (Q_dec PKCTXTNEW.PKCtxtNew)...
    destruct (Q_dec PKCTXTNEW.PPTFree)...
    destruct (Q_dec PKCTXTNEW.PKCtxtSwitch)...
    destruct (Q_dec PKCTXTNEW.PPTIn)...
    destruct (Q_dec PKCTXTNEW.PPTOut)...
    destruct (Q_dec PKCTXTNEW.PTrapIn)...
    destruct (Q_dec PKCTXTNEW.PTrapOut)...
    destruct (Q_dec PKCTXTNEW.PHostIn)...
    destruct (Q_dec PKCTXTNEW.PHostOut)...
    destruct (Q_dec PKCTXTNEW.PTrapGet)...
    destruct (Q_dec PKCTXTNEW.PTrapRet)...
    destruct (Q_dec PKCTXTNEW.PPMapInit)...
    left; destruct p; assumption.
  Defined.    

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PKCONTEXT.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                        (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA := HDATA.
  
    Notation Hfundef := (Asm.fundef (external_function:= PKCTXTNEW.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PKCONTEXT.primOp)).

    Notation funkind := (funkind (low:= PKCONTEXT.primOp) Asm.code (Clight.fundef (external_function := PKCONTEXT.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: PKCTXTNEW.primOp): funkind :=
      match p with
        | PKCTXTNEW.PAlloc => Code _ (AST.External PKCONTEXT.PAlloc)
        | PKCTXTNEW.PFree => Code _ (AST.External PKCONTEXT.PFree)
        | PKCTXTNEW.PSetPT => Code _ (AST.External PKCONTEXT.PSetPT)
        | PKCTXTNEW.PPTRead => Code _ (AST.External PKCONTEXT.PPTRead)
        | PKCTXTNEW.PPTResv => Code _ (AST.External PKCONTEXT.PPTResv)
        | PKCTXTNEW.PKCtxtNew => SourceFun (Clight.Internal PKCONTEXTCODE.f_kctxt_new) (AST.Internal nil)
        | PKCTXTNEW.PPTFree => Code _ (AST.External PKCONTEXT.PPTFree)
        | PKCTXTNEW.PKCtxtSwitch => Code _ (AST.External PKCONTEXT.PKCtxtSwitch)
        | PKCTXTNEW.PPTIn => Code _ (AST.External PKCONTEXT.PPTIn)
        | PKCTXTNEW.PPTOut => Code _ (AST.External PKCONTEXT.PPTOut)
        | PKCTXTNEW.PTrapIn => Code _ (AST.External PKCONTEXT.PTrapIn)
        | PKCTXTNEW.PTrapOut => Code _ (AST.External PKCONTEXT.PTrapOut)
        | PKCTXTNEW.PHostIn => Code _ (AST.External PKCONTEXT.PHostIn)
        | PKCTXTNEW.PHostOut => Code _ (AST.External PKCONTEXT.PHostOut)
        | PKCTXTNEW.PTrapGet => Code _ (AST.External PKCONTEXT.PTrapGet)
        | PKCTXTNEW.PTrapRet => Code _ (AST.External PKCONTEXT.PTrapRet)
        | PKCTXTNEW.PPMapInit => Code _ (AST.External PKCONTEXT.PPMapInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (pt_new, Some (Gfun (SourceFun (Clight.External (PKCONTEXT.PPTNew) (Ctypes.Tnil) tint) dummy)))
        :: (set_RA, Some (Gfun (SourceFun (Clight.External (PKCONTEXT.PKCtxtRA) (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: (set_SP, Some (Gfun (SourceFun (Clight.External (PKCONTEXT.PKCtxtSP) (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) Ctypes.Tvoid) dummy)))
        :: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PKCTXTNEW.primOp (low := PKCONTEXT.primOp) (Clight.fundef (external_function := PKCONTEXT.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PKCTXTNEW.primOp (low := PKCONTEXT.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PKCTXTNEW.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PKCONTEXT.primOp)).

    Let Im_kctxt_new: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns PKCTXTNEW.PKCtxtNew).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PKCTXTNEW.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: KCTXTNEWGEN.transf_program Im_kctxt_new impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PKCONTEXT.primOp) := source_program_only source_implem prog.
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

    (** pt_new *)

    Let bpt_new: block := Genv.genv_next ge + Z.of_nat 0.

    Let hpt_new1 : Genv.find_symbol sge pt_new = Some bpt_new. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ pt_new).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.
    
    Let hpt_new2 : Genv.find_funct sge (Vptr bpt_new Int.zero) = Some (Clight.External (PKCONTEXT.PPTNew) (Ctypes.Tnil) tint).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ pt_new _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.      

    Let hpt_new3 : Clight.type_of_global sge bpt_new = Some (Ctypes.Tfunction (Ctypes.Tnil) tint).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bpt_new).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bpt_new. unfold Asm.fundef. omega.
      intros.
      simpl in hpt_new2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hpt_new2. reflexivity.
    Qed.   

    (** set_RA *)

    Let bset_RA: block := Genv.genv_next ge + Z.of_nat 1.

    Let hset_RA1 : Genv.find_symbol sge set_RA = Some bset_RA. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_RA).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hset_RA2 : Genv.find_funct sge (Vptr bset_RA Int.zero) = Some (Clight.External (PKCONTEXT.PKCtxtRA) (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_RA _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hset_RA3 : Clight.type_of_global sge bset_RA = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_RA).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_RA. unfold Asm.fundef. omega.
      intros.
      simpl in hset_RA2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_RA2. reflexivity.
    Qed. 

    (** set_SP *)

    Let bset_SP: block := Genv.genv_next ge + Z.of_nat 2.

    Let hset_SP1 : Genv.find_symbol sge set_SP = Some bset_SP. 
    Proof.
      eapply add_globals_transf_augment_option.
      2: eapply source_program_only_prop.
      assumption.
      intro. exploit Genv.find_symbol_exists_ex. eassumption. destruct 1.
      eapply (NEW_INJ set_SP).
      congruence.
      simpl; tauto.
      reflexivity.
    Qed.      
    
    Let hset_SP2 : Genv.find_funct sge (Vptr bset_SP Int.zero) = Some (Clight.External (PKCONTEXT.PKCtxtSP) (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      simpl. destruct (Int.eq_dec Int.zero Int.zero); try congruence.
      refine (_ (Genv.find_new_funct_ptr_exists_option _ _ _ _ _ _ _ set_SP _ _)).
       2: exact (source_program_only_prop source_implem prog).
       3: simpl; eauto 8.
       2: assumption.
      fold sprog sge.
      destruct 1 as [? [? ?]].
      congruence.
    Qed.            

    Let hset_SP3 : Clight.type_of_global sge bset_SP = Some (Ctypes.Tfunction (Ctypes.Tcons tint (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) Ctypes.Tvoid).
    Proof.
      unfold Clight.type_of_global.
      case_eq (Genv.find_var_info sge bset_SP).
       intros. exfalso.
       exploit Genv.find_var_info_rev_transf_augment_option.
       exact (source_program_only_prop source_implem prog).
       eassumption.
      rewrite zlt_false.
       simpl.
       intro K.
       let t _ := discriminate in elim_or K t.
      unfold bset_SP. unfold Asm.fundef. omega.
      intros.
      simpl in hset_SP2. destruct (Int.eq_dec Int.zero Int.zero); try congruence. rewrite hset_SP2. reflexivity.
    Qed. 

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel HDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA HDATA mem__H mem__L}.

      Notation HLoad := (PKCTXTNEW.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PKCTXTNEW.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PKCONTEXT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PKCONTEXT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PKCTXTNEW.primOp mem__H :=
        PKCTXTNEW.layer_def (Hmem:= HHmem) (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                            (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                            (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) HDATA PKCONTEXT.primOp mem__L :=
        PKCONTEXT.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low)
                            (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc)
                            (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                            (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb).

      Notation lstep := (PKCONTEXT.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4)
                                        (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh)
                                        (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb)
                                        (real_free_pt:= real_free_pt)).

      Notation LADT := PKCONTEXT.ADT.

      Let kctxt_new_spec:
        forall r' n b b0 b' m0 ofs labd' sig ofs',
          r' PC = Vptr b Int.zero
          -> Genv.find_symbol tge STACK_LOC = Some b0
          -> Genv.find_symbol ge STACK_LOC = Some b0
          -> (exists id, Genv.find_symbol tge id = Some b') 
          -> (exists id, Genv.find_symbol ge id = Some b') 
          -> Genv.find_funct_ptr tge b = Some (Im_kctxt_new)
          -> Int.unsigned ofs = (Int.unsigned n + 1) * PgSize - 4 
          -> sig = mksignature (Tint :: nil) (Some Tint)
          -> PKCONTEXT.kctxt_new (Mem.get_abstract_data m0) b0 ofs b' ofs'= Some (labd', Int.unsigned n)
          -> (forall b o, r' ESP = Vptr b o -> Mem.tget m0 b = Some Tag_stack)
          -> r' ESP <> Vundef
          -> r' RA  <> Vundef
          -> Genv.find_funct_ptr ge b = Some (External PKCTXTNEW.PKCtxtNew)
          -> asm_invariant tge (State r' m0)
          -> extcall_arguments r' m0 sig (Vptr b' ofs' ::  nil)                     
          -> exists f' m0' r_, 
               inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
               /\ Memtype.Mem.inject f' m0 m0'
               /\ Mem.nextblock m0 <= Mem.nextblock m0'              
               /\ plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0' labd'))
               /\ r_ # (loc_external_result sig) = (Vint n)
               /\ r_ PC = r' RA
               /\ r_ # ESP = r' # ESP
               /\ (forall l,
                     ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
                     -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.        
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     PKCTXTNEW.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := PKCONTEXT.primitive_call)
                     (is_primitive_call := PKCONTEXT.is_primitive_call)
                     (kernel_mode := PKCONTEXT.kernel_mode)
                  ).
          apply PKCONTEXT.exec_load_exec_loadex.
          apply PKCONTEXT.exec_store_exec_storeex.
          apply PKCONTEXT.extcall_not_primitive.
          apply PKCONTEXT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply PKCONTEXTCODE.kctxt_new_correct; eauto.

          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          apply NEW_INJ in H15.
          simpl in H15.
          destruct H16; subst.
          destruct H15.
          left; reflexivity.
          destruct H16; subst.
          destruct H15.
          right; left; reflexivity.
          destruct H6; subst.
          destruct H15.
          right; right; left; reflexivity.
          contradiction.
          eassumption.
          destruct H3.
          esplit.
          eapply Globalenvs.Genv.find_symbol_transf_augment'_option.
          eapply Implementation.source_program_only_prop.
          simpl.
          intros.
          intro.
          apply NEW_INJ in H15.
          simpl in H15.
          destruct H16; subst.
          destruct H15.
          left; reflexivity.
          destruct H16; subst.
          destruct H15.
          right; left; reflexivity.
          destruct H6; subst.
          destruct H15.
          right; right; left; reflexivity.
          contradiction.
          eassumption.

          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          unfold PKCONTEXT.kernel_mode.
          functional inversion H7.
          apply PKCONTEXT.pt_new_eq in H16.
          functional inversion H16.
          unfold adt in *.
          destruct (PKCONTEXT.INV (Mem.get_abstract_data m0)).
          auto.

          destruct 1 as [? [? [m_asm [? [INJ [NB [PLUS [? [? [? ?]]]]]]]]]].
          generalize (Mem.put_abstract_data_inject_inside _ _ _ INJ (Mem.get_abstract_data m0)).
          rewrite Mem.put_put_abstract_data.
          rewrite Mem.put_get_abstract_data.
          intro.
          replace (Mem.nextblock m_asm) with (Mem.nextblock (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0))) in NB by (rewrite Mem.nextblock_put_abstract_data; reflexivity).
          replace m_asm with (Mem.put_abstract_data (Mem.put_abstract_data m_asm (Mem.get_abstract_data m0)) labd') in PLUS.
          inv H15.
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
          (PKCTXTNEW.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                               (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                               (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) prog) 
          (PKCONTEXT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                               (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) 
                               (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) 
                               (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) tprog).  
    Proof.
      eapply KCTXTNEWGEN.transf_program_correct; simpl; eauto.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End KCTXTNEWGENIMPL.
