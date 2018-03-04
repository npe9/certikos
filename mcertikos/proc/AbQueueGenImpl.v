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
Require Import ProcDataType.
Require Import LAsm.
Require Import CDataTypes.
Require Import AsmExtra.
Require Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import PAbQueue.
Require Import PQueueInit.
Require Export AbQueueGen.
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

Module ABQUEUEGENIMPL.
  Export AbQueueGen.ABQUEUEGEN.

  Lemma hprim_finite_type:
    forall
      (Q: PABQUEUE.primOp -> Prop)
      (Q_dec: forall p, {Q p} + {~ Q p}),
      {forall p, Q p} + {~ forall p, Q p}.
  Proof with (try (right; eauto; fail)).
    intros.    
    destruct (Q_dec PABQUEUE.PAlloc)...
    destruct (Q_dec PABQUEUE.PFree)...
    destruct (Q_dec PABQUEUE.PSetPT)...
    destruct (Q_dec PABQUEUE.PPTRead)...
    destruct (Q_dec PABQUEUE.PPTResv)...
    destruct (Q_dec PABQUEUE.PKCtxtNew)...
    destruct (Q_dec PABQUEUE.PThreadFree)...
    destruct (Q_dec PABQUEUE.PKCtxtSwitch)...
    destruct (Q_dec PABQUEUE.PGetState)...
    destruct (Q_dec PABQUEUE.PSetState)...
    destruct (Q_dec PABQUEUE.PDeQueue)...
    destruct (Q_dec PABQUEUE.PEnQueue)...
    destruct (Q_dec PABQUEUE.PQueueRmv)...
    destruct (Q_dec PABQUEUE.PPTIn)...
    destruct (Q_dec PABQUEUE.PPTOut)...
    destruct (Q_dec PABQUEUE.PTrapIn)...
    destruct (Q_dec PABQUEUE.PTrapOut)...
    destruct (Q_dec PABQUEUE.PHostIn)...
    destruct (Q_dec PABQUEUE.PHostOut)...
    destruct (Q_dec PABQUEUE.PTrapGet)...
    destruct (Q_dec PABQUEUE.PTrapRet)...
    destruct (Q_dec PABQUEUE.PTDQueueInit)...
    left; destruct p; assumption.
  Defined.    

  (* FIXME: lousy name, inconsistent with [AbQ_RealQ_init]. *)
  Lemma real_data abtcb abq tcb tdq:
    AbQ_RealQ (num_proc := num_proc) (num_chan := num_chan)
              (real_abtcb abtcb) (real_abq abq) (real_tcb tcb) (real_tdq tdq).
  Proof.
    constructor.
    * unfold abqueue_match_dllist, real_abq, real_tcb, real_tdq.
      intros qi l Hqi.
      rewrite !init_zmap_inside by omega.
      intro H; inv H.
      exists 64.
      exists 64.
      unfold abqueue_match_next_prev_rec.
      tauto.
    * unfold abtcbpool_tcbpool, real_abtcb, real_tcb.
      intros i tds inq Hi.
      rewrite !init_zmap_inside by assumption.
      intro H; inv H.
      exists 64.
      exists 64.
      reflexivity.
  Qed.

  Section WithPrimitives.

  Context `{real_params: RealParams}.

    Notation HDATA := (PABQUEUE.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low)
                                       (num_chan:= num_chan) (kern_high:=kern_high) (maxpage:=maxpage)).

    Notation LDATA :=(PQUEUEINIT.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) 
                                        (kern_high:=kern_high) (maxpage:=maxpage) (num_chan:= num_chan)).
  
    Notation Hfundef := (Asm.fundef (external_function:= PABQUEUE.primOp)).
    Notation Lfundef := (Asm.fundef (external_function:= PQUEUEINIT.primOp)).

    Notation funkind := (funkind (low:= PQUEUEINIT.primOp) Asm.code (Clight.fundef (external_function := PQUEUEINIT.primOp))).

    Notation dummy := (AST.Internal nil).

    Definition source_implem_extfuns (p: PABQUEUE.primOp): funkind :=
      match p with
        | PABQUEUE.PAlloc => Code _ (AST.External PQUEUEINIT.PAlloc)
        | PABQUEUE.PFree => Code _ (AST.External PQUEUEINIT.PFree)
        | PABQUEUE.PSetPT => Code _ (AST.External PQUEUEINIT.PSetPT)
        | PABQUEUE.PPTRead => Code _ (AST.External PQUEUEINIT.PPTRead)
        | PABQUEUE.PPTResv => Code _ (AST.External PQUEUEINIT.PPTResv)
        | PABQUEUE.PKCtxtNew => Code _ (AST.External PQUEUEINIT.PKCtxtNew)
        | PABQUEUE.PThreadFree => Code _ (AST.External PQUEUEINIT.PThreadFree)
        | PABQUEUE.PKCtxtSwitch => Code _ (AST.External PQUEUEINIT.PKCtxtSwitch)
        | PABQUEUE.PGetState => Code _ (AST.External PQUEUEINIT.PGetState)
        | PABQUEUE.PSetState => Code _ (AST.External PQUEUEINIT.PSetState)
        | PABQUEUE.PEnQueue => Code _ (AST.External PQUEUEINIT.PEnQueue)
        | PABQUEUE.PDeQueue => Code _ (AST.External PQUEUEINIT.PDeQueue)
        | PABQUEUE.PQueueRmv => Code _ (AST.External PQUEUEINIT.PQueueRmv)
        | PABQUEUE.PPTIn => Code _ (AST.External PQUEUEINIT.PPTIn)
        | PABQUEUE.PPTOut => Code _ (AST.External PQUEUEINIT.PPTOut)
        | PABQUEUE.PTrapIn => Code _ (AST.External PQUEUEINIT.PTrapIn)
        | PABQUEUE.PTrapOut => Code _ (AST.External PQUEUEINIT.PTrapOut)
        | PABQUEUE.PHostIn => Code _ (AST.External PQUEUEINIT.PHostIn)
        | PABQUEUE.PHostOut => Code _ (AST.External PQUEUEINIT.PHostOut)
        | PABQUEUE.PTrapGet => Code _ (AST.External PQUEUEINIT.PTrapGet)
        | PABQUEUE.PTrapRet => Code _ (AST.External PQUEUEINIT.PTrapRet)
        | PABQUEUE.PTDQueueInit => Code _ (AST.External PQUEUEINIT.PTDQueueInit)
      end.

    Notation varkind := (varkind unit Ctypes.type).

    Definition source_implem_impl_globs : list (ident * option (globdef funkind varkind)) :=
      (AbQueueGenImplDummy, None):: nil.

    Let NOREPET_IMPL: list_norepet (map fst source_implem_impl_globs).
    Proof.
      case_eq (list_norepet_dec peq (map fst source_implem_impl_globs)); try discriminate; tauto.
    Qed.

    Definition source_implem : source_implem Asm.code unit PABQUEUE.primOp (low := PQUEUEINIT.primOp) (Clight.fundef (external_function := PQUEUEINIT.primOp)) Ctypes.type.
    Proof.
      split.
       exact source_implem_extfuns.
       exact source_implem_impl_globs.
    Defined.

    Let im : implem Asm.code unit PABQUEUE.primOp (low := PQUEUEINIT.primOp) := implem_of_source_implem transf_clight_fundef Cshmgen.transl_globvar source_implem.

    Notation Hprogram := (Asm.program (external_function:= PABQUEUE.primOp)). 
    Notation Lprogram := (Asm.program (external_function:= PQUEUEINIT.primOp)).

    Definition impl_glbl :  list (ident * option (globdef Lfundef unit)) :=
      map
        (transf_source_def' transf_clight_fundef
                            Cshmgen.transl_globvar)
        source_implem_impl_globs.

    Let well_new_glb: Genv.well_idglob_list impl_glbl = true.
    Proof. reflexivity. Qed.
                           
    (* This is basically an axiom that can be easily checked because PABQUEUE.primOp is a finite type. However, in practice, generation of CertiKOS code will be very slow because compilation will have to occur twice, one for this check, and a second independently for the generation of the actual code. *)
    
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

    Let TRANSF: ABQUEUEGEN.transf_program impl_glbl prog = OK tprog.
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

    Let sprog : Clight.program (external_function := PQUEUEINIT.primOp) := source_program_only source_implem prog.
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

    Context `{PageFaultHandler_LOC: ident}.

    Section WITHMEM.

      Context {mem__H} {mem__L}
              `{HHmem: !LayerMemoryModel HDATA mem__H}
              `{HLmem: !LayerMemoryModel LDATA mem__L}
              `{HLayerInject: !LayerMemoryInjections HDATA LDATA mem__H mem__L}.

      Instance HLayer: LayerDefinition (layer_mem:= HHmem) HDATA PABQUEUE.primOp mem__H :=
        PABQUEUE.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                           (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                           (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                           (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                           (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan).

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA PQUEUEINIT.primOp mem__L :=
        PQUEUEINIT.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (num_chan := num_chan) (real_tcb:= real_tcb)
                             (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                             (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt) 
                             (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                             (real_tdq:= real_tdq).    

      Notation HLoad := (PABQUEUE.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation HStore := (PABQUEUE.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LLoad := (PQUEUEINIT.exec_loadex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).
      Notation LStore := (PQUEUEINIT.exec_storeex (PgSize:=PgSize)(NPT_LOC:= NPT_LOC) (PageFaultHandler_LOC:= PageFaultHandler_LOC)).

      Notation LADT := PQUEUEINIT.ADT.

    Theorem transf_program_correct:
      Smallstep.backward_simulation 
          (PABQUEUE.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC)  
                              (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HHmem) (HPS4:= HPS4) (Hnpc:= Hnpc)
                              (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_abtcb:= real_abtcb)
                              (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                              (real_abq:= real_abq) (Hnchan:= Hnchan) prog) 
          (PQUEUEINIT.semantics (NPT_LOC:= NPT_LOC) (PgSize:=PgSize) (PageFaultHandler_LOC:= PageFaultHandler_LOC) 
                                (real_AT:= real_AT) (real_nps:= real_nps) (Hmem:= HLmem) (HPS4:= HPS4) (num_chan:= num_chan)
                                (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_tcb:= real_tcb)
                                (Hnpc:= Hnpc) (real_ptb:= real_ptb) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) 
                                (real_tdq:= real_tdq) tprog).
    Proof.
      eapply ABQUEUEGEN.transf_program_correct; simpl; eauto.
      apply real_TCB_init.
      apply real_tdq_valid.
      apply real_data.
    Qed.

    End WITHMEM.

    End WithProg.

 End WithPrimitives.

End ABQUEUEGENIMPL.
