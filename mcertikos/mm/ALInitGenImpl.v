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
Require Import MALInit.
Require Import MBoot.
Require Import ZArith.Zwf.
Require Import MBootCode.
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
Require Import LayerTemplate.
Require Export ALInitGen.
Require Import Implementation.
Require Import SeparateCompiler.
Require Import ClightImplemExtra.
Require Import LayerDefinition.
Require Import RealParams.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module ALINITGENIMPL.
  Export ALInitGen.ALINITGEN.

  Lemma hprim_finite_type:
    forall
      (Q: MALINIT.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.
    destruct (Q_dec MALINIT.PSetPE)...
    destruct (Q_dec MALINIT.PSetPT)...
    destruct (Q_dec MALINIT.PGetSize)...
    destruct (Q_dec MALINIT.PIsUsable)...
    destruct (Q_dec MALINIT.PMMGetS)...
    destruct (Q_dec MALINIT.PMMGetL)...
    destruct (Q_dec MALINIT.PGetNps)...
    destruct (Q_dec MALINIT.PSetNps)...
    destruct (Q_dec MALINIT.PIsNorm)...
    destruct (Q_dec MALINIT.PATSetNorm)...
    destruct (Q_dec MALINIT.PATGetU)...
    destruct (Q_dec MALINIT.PATSetU)...
    destruct (Q_dec MALINIT.PTrapIn)...
    destruct (Q_dec MALINIT.PTrapOut)...
    destruct (Q_dec MALINIT.PHostIn)...
    destruct (Q_dec MALINIT.PHostOut)...
    destruct (Q_dec MALINIT.PTrapGet)...
    destruct (Q_dec MALINIT.PTrapRet)...
    destruct (Q_dec MALINIT.PBootLoader)...
    left; destruct p; assumption.
  Defined.    

 Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (MALINIT.AbData (PgSize := PgSize) (kern_low := kern_low)).
    Notation LDATA := MBOOT.RData.
  
    Notation Hfundef := (Asm.fundef (external_function:= MALINIT.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= MBOOT.primOp)).

    Notation funkind := (funkind Asm.code (Clight.fundef (external_function := MBOOT.primOp))).

    Definition source_implem_extfuns (p: MALINIT.primOp): funkind :=
      match p with
        | MALINIT.PSetPE => Code _ (AST.External MBOOT.PSetPE)
        | MALINIT.PSetPT => Code _ (AST.External MBOOT.PSetPT)
        | MALINIT.PGetSize => Code _ (AST.External MBOOT.PGetSize)
        | MALINIT.PIsUsable => Code _ (AST.External MBOOT.PIsUsable)
        | MALINIT.PMMGetS => Code _ (AST.External MBOOT.PMMGetS)
        | MALINIT.PMMGetL => Code _ (AST.External MBOOT.PMMGetL)
        | MALINIT.PGetNps => SourceFun (Clight.Internal MBOOTCODE.f_get_nps) (AST.Internal nil)
        | MALINIT.PSetNps => SourceFun (Clight.Internal MBOOTCODE.f_set_nps) (AST.Internal nil)
        | MALINIT.PIsNorm => SourceFun (Clight.Internal MBOOTCODE.f_is_norm) (AST.Internal nil)
        | MALINIT.PATSetNorm => SourceFun (Clight.Internal MBOOTCODE.f_set_norm) (AST.Internal nil)
        | MALINIT.PATGetU => SourceFun (Clight.Internal MBOOTCODE.f_at_get) (AST.Internal nil)
        | MALINIT.PATSetU => SourceFun (Clight.Internal MBOOTCODE.f_at_set) (AST.Internal nil)
        | MALINIT.PTrapIn => Code _ (AST.External MBOOT.PTrapIn)
        | MALINIT.PTrapOut => Code _ (AST.External MBOOT.PTrapOut)
        | MALINIT.PHostIn => Code _ (AST.External MBOOT.PHostIn)
        | MALINIT.PHostOut => Code _ (AST.External MBOOT.PHostOut)
        | MALINIT.PTrapGet => Code _ (AST.External MBOOT.PTrapGet)
        | MALINIT.PTrapRet => Code _ (AST.External MBOOT.PTrapRet)
        | MALINIT.PBootLoader => Code _ (AST.External MBOOT.PBootLoader)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_new_globs : list (ident * option (globdef funkind varkind)) :=
      (NPS_LOC, Some (Gvar (mkglobvar (SourceVar tint tt) (wrap_init_data 1) false)))
        :: (AT_LOC, Some (Gvar (mkglobvar (SourceVar (tarray t_struct_A maxpage) tt) ((Init_space (maxpage*8))::nil) false)))
        :: nil.

    Let NOREPET: list_norepet (NPS_LOC :: AT_LOC :: nil).
    Proof.
      case_eq (list_norepet_dec peq (NPS_LOC :: AT_LOC :: nil)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit MALINIT.primOp (low := MBOOT.primOp) (Clight.fundef (external_function := MBOOT.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_new_globs.
    Defined.

    Let im : implem Asm.code unit MALINIT.primOp (low := MBOOT.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= MALINIT.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= MBOOT.primOp)).

    Let Im_getnps: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALINIT.PGetNps).
    Let Im_setnps: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALINIT.PSetNps).
    Let Im_isnorm: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALINIT.PIsNorm).
    Let Im_setnorm: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALINIT.PATSetNorm).
    Let Im_atgetu: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALINIT.PATGetU).
    Let Im_atsetu: Lfundef := transf_source_fun' transf_clight_fundef (source_implem_extfuns MALINIT.PATSetU).

    Notation new_glbl := (new_glbl (maxpage := maxpage) NPS_LOC AT_LOC).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) := nil.

    (* This is basically an axiom that can be easily checked because MALINIT.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)

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

    Let TRANSF: ALINITGEN.transf_program (maxpage := maxpage) Im_getnps Im_setnps Im_isnorm Im_setnorm Im_atgetu Im_atsetu NPS_LOC AT_LOC impl_glbl prog = OK tprog.
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

    Let VALID_LOC': (NPS_LOC <> (prog_main prog)) /\ (AT_LOC <> (prog_main prog)).
    Proof.
      split.
       intro.
       exploit (get_next_symbol_prop NPS_LOC (map fst (source_implem_new_globs))).
       simpl; tauto. 
       eapply Ple_not_Plt.
       apply Ple_Ple'.
       eapply Ple'_trans.
       apply not_Plt'_Ple'.
       eassumption.
       apply not_Plt'_Ple'.
       congruence.
      intro.
      exploit (get_next_symbol_prop AT_LOC (map fst (source_implem_new_globs))).
      simpl; tauto.
      eapply Ple_not_Plt.
      apply Ple_Ple'.
      eapply Ple'_trans.
      apply not_Plt'_Ple'.
      eassumption.
      apply not_Plt'_Ple'.
      congruence.
    Qed.       

    Let VALID_LOC: (NPS_LOC <> (prog_main prog)) /\ (AT_LOC <> (prog_main prog) /\ NPS_LOC <> AT_LOC).
    Proof.
      destruct VALID_LOC'.
      split; auto.
      split; auto.
      vm_compute. congruence.
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

    Let sprog : Clight.program (external_function := MBOOT.primOp) := source_program_only source_implem prog.
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
      simpl. destruct 1; try discriminate. destruct H0; try discriminate. contradiction.
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
    
    Lemma at_loc_prop:
      forall b0,
        Genv.find_symbol tge AT_LOC = Some b0 ->
        Genv.find_symbol sge AT_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some (tarray t_struct_A maxpage).
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   AT_LOC
                                   (mkglobvar (SourceVar (tarray t_struct_A maxpage) tt) ((Init_space (maxpage*8))::nil) false)
                                   _ (refl_equal _) H)).
      destruct 1.
      split; auto.
      unfold Clight.type_of_global.
      unfold sge, sprog.
      rewrite H1.
      reflexivity.
      simpl; tauto.
    Qed.

    Lemma nps_loc_prop:
      forall b0,
        Genv.find_symbol tge NPS_LOC = Some b0 ->
        Genv.find_symbol sge NPS_LOC = Some b0 /\
        Clight.type_of_global sge b0 = Some tint.
    Proof.
      intros.
      refine (_ (find_new_var_prop _ _ source_implem NOREPET _ NEW_INJ
                                   NPS_LOC
                                   (mkglobvar (SourceVar tint tt) (wrap_init_data 1) false)
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

    Let NPS_LOC_not_in: ~ In NPS_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge NPS_LOC <> None) by congruence.
      eapply NEW_INJ; eauto.
      simpl; tauto.
    Qed.
    
    Let AT_LOC_not_in:  ~ In AT_LOC (prog_defs_names prog).
    Proof.
      intro. exploit Genv.find_symbol_exists_ex; eauto. destruct 1.
      assert (Genv.find_symbol ge AT_LOC <> None) by congruence.
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
      
    Context {mem__MALINIT mem__MBOOT}
      `{HHmem: !LayerMemoryModel HDATA mem__MALINIT}
      `{HLmem: !LayerMemoryModel LDATA mem__MBOOT}
      `{HLayerInject: !LayerMemoryInjections HDATA LDATA _ _}.

    Instance HLayer: LayerDefinition HDATA MALINIT.primOp mem__MALINIT :=
      MALINIT.layer_def (maxpage := maxpage) (real_size := real_size) (real_mm := real_mm).

    Instance LLayer: LayerDefinition LDATA MBOOT.primOp mem__MBOOT :=
      MBOOT.layer_def (PgSize := PgSize) (real_size := real_size) (real_mm := real_mm) (kern_low := kern_low).

    Notation HLoad := (MALINIT.exec_loadex (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (PgSize:= PgSize)
                                           (kern_low:=kern_low) ).

    Notation LLoad := (MBOOT.exec_loadex (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (PgSize:= PgSize)
                                          ).

    Notation HStore := (MALINIT.exec_storeex (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (PgSize:= PgSize)
                                             (kern_low:=kern_low)  ).

    Notation LStore := (MBOOT.exec_storeex (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (PgSize:= PgSize)
                                            ).

    Notation Lstep := (MBOOT.step (NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC) (PgSize := PgSize) (real_size := real_size) (real_mm := real_mm) (kern_low := kern_low)).

        Let atsetu_spec:
      forall r' b m'0 n b0  m0 v,
        r' PC = Vptr b Int.zero
        -> Genv.find_funct_ptr tge b = Some (Im_atsetu)
        -> Mem.store Mint32 m'0 b0
                     (Int.unsigned (Int.repr (Int.unsigned n * 8 + 4))) (Vint v) = Some m0
        -> 0 <= (Int.unsigned n) < maxpage
        -> Genv.find_symbol tge AT_LOC = Some b0
        -> MBOOT.ikern (Mem.get_abstract_data m'0) = true
        -> MBOOT.ihost (Mem.get_abstract_data m'0) = true
        -> Mem.tget m'0 b0 = Some Tag_global
        -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
        -> r' ESP <> Vundef
        -> r' RA  <> Vundef
        -> Genv.find_funct_ptr ge b = Some (AST.External MALINIT.PATSetU)
        -> asm_invariant tge (Asm.State r' m'0)
        -> extcall_arguments r' m'0 {| sig_args := Tint::Tint::nil; sig_res := None |} (Vint n :: Vint v :: nil)
        -> exists f' m0' r_, 
             inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
             /\ Memtype.Mem.inject f' m0 m0'
             /\ Mem.nextblock m0 <= Mem.nextblock m0'
             /\ plus Lstep tge (Asm.State r' m'0) E0
                (Asm.State r_ m0')
             /\ True (* r_ # (loc_external_result {| sig_args := Tint::Tint::nil; sig_res := None |}) =
                          Vundef *)
             /\ r_ PC = r' RA
             /\ r_ # ESP = r' # ESP
             /\ (forall l,
                   ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
        Proof.
          intros.          
          exploit at_loc_prop; eauto.
          destruct 1.
          exploit (ClightImplemExtra.bigstep_clight_to_lsem
                     MALINIT.primOp
                     (exec_load := LLoad)
                     (exec_store := LStore)
                     (primitive_call := MBOOT.primitive_call)
                     (is_primitive_call := MBOOT.is_primitive_call)
                     (kernel_mode := MBOOT.kernel_mode)
                  ).
          apply MBOOT.exec_load_exec_loadex.
          apply MBOOT.exec_store_exec_storeex.
          apply MBOOT.extcall_not_primitive.
          apply MBOOT.primitive_kernel_mode.
          3: eassumption.
          assumption.
          assumption.
          2: eassumption.
          5: eassumption.
          9: eassumption.
          7: reflexivity.
          intros; eapply MBOOTCODE.at_set_correct; eauto.
          assumption.
          assumption.
          assumption.
          assumption.
          reflexivity.
          split; assumption.
          destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
          erewrite Mem.nextblock_store by eassumption.
          eauto 11.
        Qed.

    Let atgetu_spec:
      forall r' b m'0 n b0 v v',
        r' PC = Vptr b Int.zero
        -> Genv.find_funct_ptr tge b = Some (Im_atgetu)
        -> Mem.loadv Mint32 m'0 (Vptr b0 (Int.repr ((Int.unsigned n) * 8 + 4))) = Some (Vint v)
        -> Genv.find_symbol tge AT_LOC = Some b0
        -> Int.unsigned v' = Int.unsigned (IntToBoolZ v)
        -> 0 <= (Int.unsigned n) < maxpage
        -> MBOOT.ikern (Mem.get_abstract_data m'0) = true
        -> MBOOT.ihost (Mem.get_abstract_data m'0) = true
        -> Mem.tget m'0 b0 = Some Tag_global
        -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
        -> r' ESP <> Vundef
        -> r' RA  <> Vundef
        -> Genv.find_funct_ptr ge b = Some (External MALINIT.PATGetU)
        -> asm_invariant tge (State r' m'0)
        -> extcall_arguments r' m'0 {| sig_args := Tint:: nil; sig_res := Some Tint |} (Vint n :: nil)
        -> exists f' m0' r_, 
             inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
             /\ Memtype.Mem.inject f' m'0 m0'
             /\ Mem.nextblock m'0 <= Mem.nextblock m0'
             /\ plus Lstep tge (State r' m'0) E0
                (State r_ m0')
             /\ r_ # (loc_external_result {| sig_args := Tint:: nil; sig_res := Some Tint |}) =
                          (Vint v')
             /\ r_ PC = r' RA
             /\ r_ # ESP = r' # ESP
             /\ (forall l,
                   ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit at_loc_prop; eauto.
      destruct 1.      
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MALINIT.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MBOOT.primitive_call)
                 (is_primitive_call := MBOOT.is_primitive_call)
                 (kernel_mode := MBOOT.kernel_mode)
              ).
      apply MBOOT.exec_load_exec_loadex.
      apply MBOOT.exec_store_exec_storeex.
      apply MBOOT.extcall_not_primitive.
      apply MBOOT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.
      intros; eapply MBOOTCODE.at_get_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      reflexivity.
      split; assumption.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      val_inject_inv.
      eauto 11.
    Qed.

    Let isnorm_spec:
      forall r' b m'0 n b0 v v',
        r' PC = Vptr b Int.zero
        -> Genv.find_funct_ptr tge b = Some (Im_isnorm)
        -> Mem.loadv Mint32 m'0 (Vptr b0 (Int.repr ((Int.unsigned n) * 8))) = Some (Vint v)
        -> Genv.find_symbol tge AT_LOC = Some b0
        -> Int.unsigned v' = Int.unsigned (IntToATTypeZ v)
        -> 0 <= (Int.unsigned n) < maxpage
        -> MBOOT.ikern (Mem.get_abstract_data m'0) = true
        -> MBOOT.ihost (Mem.get_abstract_data m'0) = true
        -> Mem.tget m'0 b0 = Some Tag_global
        -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
        -> r' ESP <> Vundef
        -> r' RA  <> Vundef
        -> Genv.find_funct_ptr ge b = Some (External MALINIT.PIsNorm)
        -> asm_invariant tge (State r' m'0)
        -> extcall_arguments r' m'0 {| sig_args := Tint:: nil; sig_res := Some Tint |} (Vint n :: nil)
        -> exists f' m0' r_, 
             inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
             /\ Memtype.Mem.inject f' m'0 m0'
             /\ Mem.nextblock m'0 <= Mem.nextblock m0'
             /\ plus Lstep tge (State r' m'0) E0
                (State r_ m0')
             /\ r_ # (loc_external_result {| sig_args := Tint:: nil; sig_res := Some Tint |}) =
                           (Vint v')
             /\ r_ PC = r' RA
             /\ r_ # ESP = r' # ESP
             /\ (forall l,
                   ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit at_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MALINIT.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MBOOT.primitive_call)
                 (is_primitive_call := MBOOT.is_primitive_call)
                 (kernel_mode := MBOOT.kernel_mode)
              ).
      apply MBOOT.exec_load_exec_loadex.
      apply MBOOT.exec_store_exec_storeex.
      apply MBOOT.extcall_not_primitive.
      apply MBOOT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MBOOTCODE.is_norm_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      reflexivity.
      split; assumption.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      val_inject_inv.
      eauto 11.
    Qed.
    
    Let setnorm_spec:
      forall r' b m'0 n b0  m0 m1 v,
        r' PC = Vptr b Int.zero
        -> Genv.find_funct_ptr tge b = Some (Im_setnorm)
        -> Mem.store Mint32 m'0 b0
                     (Int.unsigned (Int.repr (Int.unsigned n * 8))) (Vint v) = Some m0
        -> Mem.store Mint32 m0 b0
                     (Int.unsigned (Int.repr (Int.unsigned n * 8 + 4))) (Vint (Int.zero)) = Some m1
        -> Genv.find_symbol tge AT_LOC = Some b0
        -> 0 <= (Int.unsigned n) < maxpage
        -> MBOOT.ikern (Mem.get_abstract_data m'0) = true
        -> MBOOT.ihost (Mem.get_abstract_data m'0) = true
        -> Mem.tget m'0 b0 = Some Tag_global
        -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
        -> r' ESP <> Vundef
        -> r' RA  <> Vundef
        -> Genv.find_funct_ptr ge b = Some (External MALINIT.PATSetNorm)
        -> asm_invariant tge (State r' m'0)
        -> extcall_arguments r' m'0 {| sig_args := Tint::Tint::nil; sig_res := None |} (Vint n :: Vint v :: nil)
        -> exists f' m0' r_, 
             inject_incr (Mem.flat_inj (Mem.nextblock m1)) f' 
             /\ Memtype.Mem.inject f' m1 m0'
             /\ Mem.nextblock m1 <= Mem.nextblock m0'
             /\ plus Lstep tge (State r' m'0) E0
                (State r_ m0')
             /\ True (* r_ # (loc_external_result {| sig_args := Tint::Tint::nil; sig_res := None |}) =
                          Vundef *)
             /\ r_ PC = r' RA
             /\ r_ # ESP = r' # ESP
             /\ (forall l,
                   ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit at_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MALINIT.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MBOOT.primitive_call)
                 (is_primitive_call := MBOOT.is_primitive_call)
                 (kernel_mode := MBOOT.kernel_mode)
              ).
      apply MBOOT.exec_load_exec_loadex.
      apply MBOOT.exec_store_exec_storeex.
      apply MBOOT.extcall_not_primitive.
      apply MBOOT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MBOOTCODE.set_norm_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      reflexivity.
      split; assumption.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      erewrite Mem.nextblock_store by eassumption.
      erewrite Mem.nextblock_store by eassumption.
      eauto 11.
    Qed.

    Let getnps_spec:
      forall r' b m'0 n b0,
        r' PC = Vptr b Int.zero
        -> Genv.find_funct_ptr tge b = Some (Im_getnps)
        -> Mem.loadv Mint32 m'0 (Vptr b0 Int.zero) = Some (Vint n)
        -> Genv.find_symbol tge NPS_LOC = Some b0
        -> MBOOT.ikern (Mem.get_abstract_data m'0) = true
        -> MBOOT.ihost (Mem.get_abstract_data m'0) = true
        -> Mem.tget m'0 b0 = Some Tag_global
        -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
        -> r' ESP <> Vundef
        -> r' RA  <> Vundef
        -> Genv.find_funct_ptr ge b = Some (External MALINIT.PGetNps)
        -> asm_invariant tge (State r' m'0)
        -> extcall_arguments r' m'0 {| sig_args := nil; sig_res := Some Tint |} nil
        -> exists f' m0' r_, 
             inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
             /\ Memtype.Mem.inject f' m'0 m0'
             /\ Mem.nextblock m'0 <= Mem.nextblock m0'
             /\ plus Lstep tge (State r' m'0) E0
                (State r_ m0')
             /\ r_ # (loc_external_result {| sig_args := nil; sig_res := Some Tint |}) =
                (Vint n)
             /\ r_ PC = r' RA
             /\ r_ # ESP = r' # ESP
             /\ (forall l,
                   ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit nps_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MALINIT.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MBOOT.primitive_call)
                 (is_primitive_call := MBOOT.is_primitive_call)
                 (kernel_mode := MBOOT.kernel_mode)
              ).
      apply MBOOT.exec_load_exec_loadex.
      apply MBOOT.exec_store_exec_storeex.
      apply MBOOT.extcall_not_primitive.
      apply MBOOT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MBOOTCODE.get_nps_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      reflexivity.
      split; assumption.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      val_inject_inv.
      eauto 11.
    Qed.
     
    Let setnps_spec:
      forall r' b m'0 n b0 m2,
        r' PC = Vptr b Int.zero
        -> Genv.find_funct_ptr tge b = Some (Im_setnps)
        -> Mem.store Mint32 m'0 b0 0 (Vint n) = Some m2
        -> Genv.find_symbol tge NPS_LOC = Some b0
        -> MBOOT.ikern (Mem.get_abstract_data m'0) = true
        -> MBOOT.ihost (Mem.get_abstract_data m'0) = true
        -> Mem.tget m'0 b0 = Some Tag_global
        -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
        -> r' ESP <> Vundef
        -> r' RA  <> Vundef
        -> Genv.find_funct_ptr ge b = Some (External MALINIT.PSetNps)
        -> asm_invariant tge (State r' m'0)
        -> extcall_arguments r' m'0 {| sig_args := Tint::nil; sig_res := None |} (Vint n :: nil)
        -> exists f' m0' r_, 
             inject_incr (Mem.flat_inj (Mem.nextblock m2)) f' 
             /\ Memtype.Mem.inject f' m2 m0'
             /\ Mem.nextblock m2 <= Mem.nextblock m0'
             /\ plus Lstep tge (State r' m'0) E0
                (State r_ m0')
             /\ True (* r_ # (loc_external_result {| sig_args := Tint::nil; sig_res := None |}) = Vundef *)
             /\ r_ PC = r' RA
             /\ r_ # ESP = r' # ESP
             /\ (forall l,
                   ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).
    Proof.
      intros.
      exploit nps_loc_prop; eauto.
      destruct 1.
      exploit (ClightImplemExtra.bigstep_clight_to_lsem
                 MALINIT.primOp
                 (exec_load := LLoad)
                 (exec_store := LStore)
                 (primitive_call := MBOOT.primitive_call)
                 (is_primitive_call := MBOOT.is_primitive_call)
                 (kernel_mode := MBOOT.kernel_mode)
              ).
      apply MBOOT.exec_load_exec_loadex.
      apply MBOOT.exec_store_exec_storeex.
      apply MBOOT.extcall_not_primitive.
      apply MBOOT.primitive_kernel_mode.
      3: eassumption.
      assumption.
      assumption.
      2: eassumption.
      5: eassumption.
      9: eassumption.
      7: reflexivity.      
      intros; eapply MBOOTCODE.set_nps_correct; eauto.
      assumption.
      assumption.
      assumption.
      assumption.
      reflexivity.
      split; assumption.
      destruct 1 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
      erewrite Mem.nextblock_store by eassumption.
      eauto 11.
    Qed.      

    Theorem transf_program_correct:
      Smallstep.backward_simulation
        (MALINIT.semantics (real_mm := real_mm) (real_size := real_size) (PageFaultHandler_LOC := PageFaultHandler_LOC) 
                           (NPT_LOC := NPT_LOC) (maxpage := maxpage) prog)
        (MBOOT.semantics (PageFaultHandler_LOC := PageFaultHandler_LOC) (NPT_LOC := NPT_LOC) (kern_low := kern_low) 
                         (real_mm := real_mm) (real_size := real_size) (PgSize := PgSize) tprog).
    Proof.
      eapply ALINITGEN.transf_program_correct; simpl; eauto.
      Grab Existential Variables.
      vm_compute; reflexivity.
      instantiate (1 := 262145). omega.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End ALINITGENIMPL.
