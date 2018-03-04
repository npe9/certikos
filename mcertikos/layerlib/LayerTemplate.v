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
(* *********************************************************************)
(*                                                                     *)
(*              Refinement Proof Template                              *)
(*                                                                     *)
(*          Pattern1: dealing with memory hidden                       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the template for contextual refinement proof between layers*)
Require Import Coqlib.
Require Import Errors.
Require Import ASTExtra.
Require Import Integers.
Require Import Op.
Require Import Locations.
Require Import AsmExtra.
Require Import LAsm.
Require Import EventsExtra.
Require Import GlobalenvsExtra.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import MemoryExtra.
Require Import Maps.
Require Import Floats.
Require Import CommonTactic.
Require Import AuxLemma.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Module TEMPLATE.

  Section LAYER_TMPLT.

    Context `{Hli: LayerInjections}.
    Context `{HLayer: !LayerConfiguration datah primh memh}.
    Context `{LLayer: !LayerConfiguration datal priml meml}.

    Definition Hfundef := fundef(external_function := primh).
    Definition Lfundef := fundef(external_function:= priml).

    (** Function translator: Asm commands remain the same*)
    Context `{transf_fundef : Hfundef ->  (res Lfundef)}.
    
    Definition Hprogram := program(external_function:= primh).
    Definition Lprogram := program(external_function:= priml).

    Context `{new_glbl : list (ident* option (globdef Lfundef unit))}.

    Definition transf_program (p: Hprogram) : res Lprogram :=      
      transform_partial_augment_program transf_fundef (fun v => OK v) new_glbl (prog_main p) p.

    Context `{prog: Hprogram}.
    Context `{tprog: Lprogram}.

    Context `{TRANSF: transf_program prog = OK tprog}.
    
    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Context `{NEW_INJ:  (forall s', Genv.find_symbol ge s' <> None -> 
                                    ~ In s' (map fst new_glbl))}.

    Context `{Hexec_load: Asm.genv (external_function := primh) -> memory_chunk
                          -> memh -> addrmode
                          -> regset-> preg-> (outcome(mem:=memh))}.

    Context `{Hexec_store: Asm.genv (external_function := primh) -> memory_chunk
                           -> memh -> addrmode
                           -> regset-> preg-> (outcome(mem:=memh))}.

    Context `{Lexec_load: Asm.genv (external_function:=priml) -> memory_chunk
                          -> meml -> addrmode
                          -> regset-> preg-> (outcome(mem:=meml))}.

    Context `{Lexec_store: Asm.genv (external_function:=priml) -> memory_chunk
                           -> meml -> addrmode
                           -> regset-> preg-> (outcome(mem:=meml))}.
    
    Context `{ Hprimitive_call: primh -> primcall_sem(mem := memh)}.
    Context `{ His_primitive_call: primh -> bool}.
    Context `{ Lprimitive_call: priml -> primcall_sem(mem:=meml)}.
    Context `{ Lis_primitive_call: priml -> bool}.

    Definition hstep := (stepl (exec_load:=Hexec_load)(exec_store:=Hexec_store)
                               (primitive_call:=Hprimitive_call)(is_primitive_call:=His_primitive_call)). 
    Definition lstep := (stepl (exec_load:=Lexec_load)(exec_store:=Lexec_store)
                               (primitive_call:=Lprimitive_call)(is_primitive_call:=Lis_primitive_call)). 

    Definition hsemantics := Semantics hstep (Asm.initial_state prog) Asm.final_state ge.
    Definition lsemantics := Semantics lstep (Asm.initial_state tprog) Asm.final_state tge.

    (** Relation between the abstract data at two layers*)      
    Context `{relate_AbData: meminj -> datah
                             -> datal -> Prop}.
    
    Context `{match_AbData: datah
                            -> meml -> meminj -> Prop}.

    (** Relation between the machine states at two layers*)
    Inductive match_states: state hsemantics -> state lsemantics -> Prop :=
    | MATCH_STATE: forall r r' m m' habd labd f,
                     habd = Mem.get_abstract_data m 
                     -> labd = Mem.get_abstract_data m'
                     -> match_AbData habd m' f           
                     -> Mem.inject (relate_AbData f) f m m'
                     -> (forall reg, val_inject f (Pregmap.get reg r) (Pregmap.get reg r'))
                     -> inject_incr (Mem.flat_inj (Genv.genv_next ge)) f
                     -> (forall b1 b2 delta, f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)
                     -> (Mem.nextblock m <= Mem.nextblock m')
                     -> match_states (State r m) (State r' m').

    Context `{well_new_glb: Genv.well_idglob_list new_glbl = true}.
    (** Prove that the global symbols are preserved*)
    Lemma symbols_preserved:
      forall id b, Genv.find_symbol ge id = Some b -> Genv.find_symbol tge id = Some b.
    Proof.
      intros. unfold ge, tge. 
      unfold transf_program in TRANSF.
      specialize (Genv.find_symbol_transf_augment _ _ _ _ _ TRANSF id).
      intros.
      specialize (NEW_INJ id).
      assert(HP: ~ In id (map fst new_glbl)).
      apply NEW_INJ.
      rewrite H.
      discriminate.
      specialize (H0 HP).
      rewrite H0.
      trivial.
    Qed.

    Context `{init_relate_correct: relate_AbData (Mem.flat_inj (Genv.genv_next ge)) empty_data empty_data}.

    Context `{init_match_correct:
                forall (m0: memh) m',
                forall HTAG : (forall (s : ident) (b : block),
                                 Genv.find_symbol tge s = Some b -> Mem.tget m' b = Some Tag_global),
                forall HW: Genv__alloc_globals (F:=Lfundef) (V:=unit) tge
                                               (Mem.put_abstract_data m0 empty_data)
                                               (map no_event_symbols (new_glbl)) = Some m',
                forall  HGEQ : Genv.genv_next ge = Mem.nextblock m0,
                  match_AbData empty_data m' (Mem.flat_inj (Genv.genv_next ge))}.

    Context `{store_match_correct:
                forall abd m0 m0' f b b2 delta v v' chunk,
                  match_AbData abd m0 f ->
                  f b = Some (b2, delta) ->
                  Mem.store chunk m0 b2 v v' = Some m0' ->
                  match_AbData abd m0' f}.
    
    (* Here tag was missing. *)
    Context `{alloc_match_correct:
                forall t m m'0  m'1 f f' ofs sz b0 b'1,
                  match_AbData (Mem.get_abstract_data m) m'0 f->
                  Mem.alloc t m'0 ofs sz = (m'1, b'1) ->
                  f' b0 = Some (b'1, 0) ->
                  (forall b : block, b <> b0 -> f' b = f b) ->
                  inject_incr f f' ->
                  match_AbData (Mem.get_abstract_data m) m'1 f'}.

    Context `{free_match_correct:
                forall m m'0  m2' f ofs sz b0 b2 delta,
                  match_AbData (Mem.get_abstract_data m) m'0 f->
                  Mem.free m'0 b2 ofs sz = Some m2' ->
                  f b0 = Some (b2 , delta) ->
                  match_AbData (Mem.get_abstract_data m) m2' f}.

    Context `{storebytes_match_correct:
                forall abd m0 m2' f b b2 delta v v',
                  match_AbData abd m0 f ->
                  f b = Some (b2, delta) ->
                  Mem.storebytes m0 b2 v v' = Some m2' ->
                  match_AbData abd m2' f}.
        
    Context`{relate_incr:  
               forall abd abd' f f',
                 relate_AbData f abd abd'
                 -> inject_incr f f'
                 -> relate_AbData f' abd abd'}.

    Lemma transf_initial_states:
      forall st1, 
        initial_state hsemantics st1 ->
        exists st2, initial_state lsemantics st2 
                    /\ match_states st1 st2.
    Proof.
      intros. inv H.
      unfold transf_program in *.
      specialize (Genv.init_mem_transf_augment_ex _ _ _ _ _ _ _ _ _ _ TRANSF NEW_INJ _ H0).
      intro HP.
      
      specialize (Genv.alloc_globals_augment_exist
                    (Genv.globalenv tprog) _ (Mem.put_abstract_data m0 empty_data) well_new_glb).
      intro HW.
      destruct HW as [m' HW].
      rewrite HW in HP.

      (*Tag*)
      specialize (Genv.init_mem_tget _ _ _ _ HP).
      intros HTAG.

      specialize (Genv.init_mem_inject_transf_augment_ex _ _ _ _ _ _ _ _ _ _ TRANSF NEW_INJ _ H0 _ HP _ init_relate_correct).
      intro HINJ.
      
      econstructor.
      split.
      constructor.
      instantiate (1:= m').
      apply HP.
      
      subst rs0.
      simpl.
      specialize (Genv.init_mem_genv_next _ H0).
      intro HGEQ.
      rewrite <- HGEQ in HINJ.
      
      apply MATCH_STATE with (empty_data) (empty_data) ((Mem.flat_inj (Genv.genv_next ge))); auto.
      
      specialize (Genv.init_mem_get_abstract_data _ _ H0).
      auto.
      
      specialize (Genv.init_mem_get_abstract_data _ _ HP).
      auto.
      
      eapply init_match_correct; eauto.

      (* reg *)
      Next_NF_Simpl.
      destruct (Pregmap.elt_eq reg ESP); trivial.

      unfold Mem.nullptr.
      apply val_inject_ptr with 0.
      unfold Mem.flat_inj.
      rewrite zlt_true; trivial.
      specialize (Genv.genv_next_pos ge).
      intros HG.
      omega.

      rewrite Int.add_zero.
      trivial.

      destruct (Pregmap.elt_eq reg RA); trivial.
      constructor.

      destruct (Pregmap.elt_eq reg PC); trivial.

      unfold symbol_offset. 
      specialize (transform_partial_augment_program_main _  _ _  _ _ TRANSF). 
      intro HPM.
      rewrite HPM.
      subst ge0.
      caseEq (Genv.find_symbol ge (prog_main prog)).
      intros.
      specialize(symbols_preserved _ _ H).
      intros.
      unfold ge, tge in *.
      rewrite H, H1.
      apply val_inject_ptr with 0.
      unfold Mem.flat_inj.
      rewrite zlt_true; trivial.
      specialize (Genv.genv_symb_range _ _ H).
      intros HB'.
      omega.

      rewrite Int.add_zero.
      trivial.

      unfold ge.
      intros HRW.
      rewrite HRW.
      trivial.

      (* inject *)
      intros.
      unfold Mem.flat_inj in H.
      destruct (zlt b1 (Genv.genv_next ge)); inv H.
      split; trivial.
      omega.
      
      (* nextblock*)
      specialize (Genv.alloc_globals_nextblock _ _ _ HW).
      intros.
      rewrite H.
      rewrite Mem.nextblock_put_abstract_data.
      omega.
      
    Qed.

    (** ** Show that the final states can be matched*)

    Lemma transf_final_states:
      forall st1 st2 r, 
        match_states st1 st2 -> 
        final_state hsemantics st1 r 
        -> final_state lsemantics st2 r.
    Proof.
      intros. inv H0. inversion H.
      constructor.
      specialize (H8 PC).
      unfold Pregmap.get in H8.
      rewrite H1 in H8.
      inv H8.
      
      trivial.
      
      specialize (H8 EAX).
      unfold Pregmap.get in H8.
      rewrite H2 in H8.
      inv H8.
      trivial.
    Qed.      

    Section LOAD_STORE.

      Hypothesis symbols_preserved':
        forall id b, Genv.find_symbol ge id = Some b -> Genv.find_symbol tge id = Some b.

      Lemma eval_addrmode_correct:
        forall rs r0 f a,
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) 
          -> inject_incr (Mem.flat_inj (Genv.genv_next ge)) f
          -> val_inject f (eval_addrmode ge a rs) (eval_addrmode tge a r0).
      Proof.          
        intros; unfold Pregmap.get in H.
        unfold eval_addrmode; destruct a.
        generalize H; intros HM.
        destruct const. destruct ofs. destruct p.
        specialize (HM i0).
        destruct base. 
        specialize (H i2).
        destruct (Int.eq i1 Int.one);
          destruct (rs i2); inv H; destruct (rs i0); inv HM; simpl;
          econstructor; eauto; Int_Add_Simpl.

        destruct (Int.eq i1 Int.one);
          destruct (rs i0); inv HM; simpl;
          econstructor; eauto; Int_Add_Simpl.
        
        destruct base.
        specialize (HM i0).
        destruct (rs i0); inv HM; simpl;
        econstructor; eauto; Int_Add_Simpl.
        constructor.

        destruct p.
        unfold symbol_offset.
        caseEq (Genv.find_symbol ge i); intros.
        assert (HW:f b = Some (b, 0)) by (eapply find_symbol_inject; eauto).
        
        specialize (symbols_preserved' _ _ H1); rewrite symbols_preserved'.
        destruct base. specialize (HM i1).
        destruct ofs. destruct p. specialize (H i2).
        
        destruct (Int.eq i3 Int.one);
          destruct (rs i1); inv HM; destruct (rs i2); inv H; simpl;         
          econstructor; eauto;
          rewrite Int.add_zero; trivial.
        
        destruct (rs i1); inv HM; simpl;         
        econstructor; eauto; repeat (rewrite Int.add_zero); trivial.
        
        destruct ofs. destruct p. specialize (HM i1).
        destruct (Int.eq i2 Int.one);
          destruct (rs i1); inv HM; simpl; econstructor; eauto;
          repeat (rewrite Int.add_zero); trivial.
        
        econstructor; eauto;
        repeat (rewrite Int.add_zero); trivial.
        
        destruct base; destruct ofs; simpl. destruct p.
        destruct (Int.eq i3 Int.one); destruct (rs i1); destruct (rs i2); simpl; constructor.
        
        destruct (rs i1); simpl; constructor. destruct p.
        destruct (Int.eq i2 Int.one); destruct (rs i1); simpl; constructor.
        
        constructor.
      Qed.
      
    End LOAD_STORE.

    Section EXT_CALL.

      Lemma varinfo_preserved:
        forall b gv,  Genv.find_var_info ge b = Some gv -> Genv.find_var_info tge b = Some gv.
      Proof.
        intros. 
        unfold transf_program in TRANSF.
        specialize (Genv.find_var_info_transf_augment _ _ _ _ _ TRANSF _ H).
        intros HEX.
        destruct HEX as [v'[HF HT]].
        inv HT.
        destruct gv.
        simpl in *.
        trivial.
      Qed.

      (* New symbols are never volatile per the new type for new_globs. Thus, the following is no longer necessary. *)
      Lemma block_volatile_preserved:
        forall b0 : block,
          block_is_volatile tge b0 = block_is_volatile ge b0.
      Proof.
        unfold tge, ge. eapply Genv.block_is_volatile_transf_augment. eassumption.
      Qed.

      Lemma block_volatile_preserved_ex:
        forall b b' delta f m m',
          block_is_volatile ge b = false
          -> f b = Some (b', delta)
          ->  inject_incr (Mem.flat_inj (Genv.genv_next ge)) f
          -> Mem.inject (relate_AbData f) f m m'
          -> (forall (b1 b2 : block) (delta : Z),
                f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)
          -> block_is_volatile tge b' = false.
      Proof.
        intros.
        case_eq (block_is_volatile tge b'); try reflexivity.
        rewrite block_volatile_preserved.
        intro ABS; exfalso.
        exploit Genv.block_is_volatile_range; eauto.
        intro.
        exploit H3; eauto.
        destruct 1; subst.
        generalize (H1 b).
        unfold Mem.flat_inj. rewrite zlt_true. intros.
        exploit H5; eauto.
        intros.        
        congruence.
        omega.
      Qed.

      Lemma event_symbols_preserved:
        forall s,
          Genv.find_event_symbol tge s = Genv.find_event_symbol ge s.
      Proof.
        eapply Genv.find_event_symbol_transf_augment.
        eassumption.
        assumption.
      Qed.

      Lemma evental_match_inject:
        forall res sg v,
          eventval_match ge res (sg) v
          -> eventval_match tge res ( sg) v.
      Proof.
        intros.
        induction res;  inv H;
        try constructor.
        rewrite event_symbols_preserved.
        trivial.
      Qed.
      
      Lemma evental_list_match_inject:
        forall res sg vl,
          eventval_list_match ge res (sg) vl
          -> eventval_list_match tge res ( sg) vl.
      Proof.
        induction res.
        intros; inv H.
        constructor.
        intros.
        inv H.
        constructor.
        apply evental_match_inject.
        trivial.
        apply IHres; trivial.
      Qed. 

      Local Hint Resolve evental_match_inject evental_list_match_inject symbols_preserved
            block_volatile_preserved block_volatile_preserved_ex.

      Lemma eventval_match_inject_ex:
        forall f res ty v1 v2,
          eventval_match ge res ty v1 -> val_inject f v1 v2 -> 
          inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
          eventval_match tge res ty v2.
      Proof.
        intros. inv H; inv H0. constructor.  constructor.
        generalize (Genv.find_event_symbol_find_symbol _ _ H2).
        intro SYMB.
        specialize (find_symbol_inject _  _ _ H1 SYMB).
        intro HB.
        rewrite H4 in HB.
        inv HB.
        rewrite Int.add_zero.
        econstructor; eauto. 
        rewrite event_symbols_preserved.
        auto.
      Qed.

      Lemma eventval_match_inject_2_ex:
        forall f res ty v,
          eventval_match ge res ty v -> 
          inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
          val_inject f v v.
      Proof.
        intros.
        inv H; try constructor.
        econstructor.
        eapply find_symbol_inject.
        eassumption.
        eapply Genv.find_event_symbol_find_symbol.
        eassumption.
        rewrite Int.add_zero.
        trivial.
      Qed.

      Lemma eventval_list_match_inject_ex:
        forall f evl tyl vl1, 
          eventval_list_match ge evl tyl vl1 ->
          forall vl2, val_list_inject f vl1 vl2 -> 
                      inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
                      eventval_list_match tge evl tyl vl2.
      Proof.
        induction evl; intros. 
        inv H.  inv H0. constructor.
        
        inv H. inv H0.
        constructor.
        eapply eventval_match_inject_ex; eauto. 
        eauto.
      Qed.

      Local Hint Resolve eventval_match_inject_ex eventval_match_inject_2_ex eventval_list_match_inject_ex.

      Lemma annot_preserved:
        forall args rs r' m m' vargs f,
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r')) ->
          Mem.inject (relate_AbData f) f m m' ->
          annot_arguments rs m args vargs ->
          (forall (b1 b2 : block) (delta : Z),
             f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)->
          exists vargs',
            annot_arguments r' m' args vargs'
            /\ val_list_inject f vargs vargs'.
      Proof.
        intro args.
        induction args; intros.
        inv H1.
        exists nil.
        split.
        apply list_forall2_nil.
        constructor.
        
        inv H1.
        specialize (IHargs _ _ _ _ _ _ H H0 H7 H2). 
        unfold Pregmap.get in H.
        destruct IHargs as [vargs' [HAN HVL]].
        simpl in *.
        assert(HP: exists b1', annot_arg r' m' a b1' /\ val_inject f b1 b1').
        inv H5.
        exists (r' r).
        split.
        constructor.
        apply H.
        
        specialize (H ESP).
        rewrite H1 in H.
        inv H.
        
        specialize (proj1 (H2 _ _ _ H8)).
        intro HD.
        subst delta.
        rewrite Int.add_zero in H6.
        specialize (Mem.load_inject _ _ _ _ _ _ _ _ _ H0 H3 H8).
        intros [v2[HL HINJ]].
        rewrite Z.add_0_r in HL.
        exists v2.
        split; trivial.
        econstructor; eauto.
        
        destruct HP as [b1' [HAN' HVL']].
        exists (b1'::vargs').
        split.
        apply list_forall2_cons; trivial.
        
        constructor; trivial.
      Qed.

      Lemma list_forall2_correct:
        forall vargs rs r' m m' f n e,
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r')) ->
          Mem.inject (relate_AbData f) f m m' ->
          (forall (b1 b2 : block) (delta : Z),
             f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2) ->
          list_forall2 (extcall_arg rs m)
                       (Conventions1.loc_arguments_rec (sig_args e) n) vargs ->
          exists vargs', list_forall2 (extcall_arg r' m')
                                      (Conventions1.loc_arguments_rec (sig_args e) n) vargs' 
                         /\ val_list_inject f vargs vargs'.
      Proof.
        intros vargs.
        simpl in *.
        induction vargs; intros.
        inv H2.
        exists nil.
        split.
        apply list_forall2_nil.
        constructor.
        
        inv H2.
        assert(HP: exists a', extcall_arg r' m' a1 a' /\ val_inject f a a').
        inv H6.
        exists (r' (preg_of r)).
        split.
        constructor.
        apply H.
        
        specialize (H ESP).
        unfold Pregmap.get in H.
        unfold Val.add in H4.
        destruct (rs ESP).
        inv H4.
        inv H4.
        inv H4.
        inv H.
        specialize (proj1(H1 _ _ _ H8)).
        intros.
        subst delta.
        assert (HV: val_inject f  (Vptr b (Int.add i (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))) 
                               (Vptr b2 (Int.add i (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs))))).
        econstructor; eauto.
        rewrite Int.add_zero.
        trivial.
        specialize (Mem.loadv_inject _ _ _ _ _ _ _ H0 H4 HV).
        intros [v2[HL HINJ]].
        exists v2.
        split; trivial.
        econstructor; eauto.
        rewrite <- H6.
        rewrite Int.add_zero.
        simpl.
        trivial.

        specialize (H ESP).
        unfold Pregmap.get in H.
        unfold Val.add in H4.
        destruct (rs ESP).
        inv H4.
        inv H4.
        inv H4.
        inv H.
        specialize (proj1(H1 _ _ _ H8)).
        intros.
        subst delta.
        assert (HV: val_inject f (Vptr b (Int.add i (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs))))
                               (Vptr b2 (Int.add i (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs))))).
        econstructor; eauto.
        rewrite Int.add_zero.
        trivial.
        specialize (Mem.loadv_inject _ _ _ _ _ _ _ H0 H4 HV).
        intros [v2[HL HINJ]].
        exists v2.
        split; trivial.
        econstructor; eauto.
        rewrite <- H6.
        rewrite Int.add_zero.
        simpl.
        trivial.

        destruct HP as [a' [HEX HVL]].
        unfold Conventions1.loc_arguments_rec in H3.
        induction (sig_args e).
        inv H3.
        clear IHl.
        induction a0.
        inv H3.
        fold Conventions1.loc_arguments_rec in *.
        specialize (IHvargs _ _ _ _ _ (n+1)  (mksignature l (sig_res e)) H H0 H1 H7).
        destruct IHvargs as [varg'[HL' HVL']]. 
        exists (a'::varg').
        split.
        apply list_forall2_cons; trivial.
        econstructor; eauto.
        
        inv H3.
        fold Conventions1.loc_arguments_rec in *.
        specialize (IHvargs _ _ _ _ _ (n+2)  (mksignature l (sig_res e)) H H0 H1 H7).
        destruct IHvargs as [varg'[HL' HVL']]. 
        exists (a'::varg').
        split.
        apply list_forall2_cons; trivial.
        econstructor; eauto.
      Qed.

      Lemma extargu_preserved:
        forall args rs r' m m' vargs f,
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r')) ->
          Mem.inject (relate_AbData f) f m m' ->
          extcall_arguments rs m args vargs ->
          (forall (b1 b2 : block) (delta : Z),
             f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)->
          exists vargs',
            extcall_arguments r' m' args vargs'
            /\ val_list_inject f vargs vargs'.
      Proof.
        intro args.
        unfold extcall_arguments.
        unfold Conventions1.loc_arguments.
        intros.
        eapply list_forall2_correct; eauto.
      Qed.

      Lemma valid_event_symbol_inject:
        forall f,
          inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
          forall m' m0,
            Mem.inject (relate_AbData f) f m' m0 ->
            (forall (id' : ident) (b' : block),
               Genv.find_event_symbol ge id' = Some b' ->
               Mem.valid_block m' b') ->
            forall (id' : ident) (b' : block),
              Genv.find_event_symbol tge id' = Some b' -> Mem.valid_block m0 b'.
      Proof.
        intros until b'. rewrite event_symbols_preserved. intros. 
        eapply (Mem.valid_block_inject_2 (Mem__inject := Mem.inject (relate_AbData f))); eauto.
        eapply H. unfold Mem.flat_inj. instantiate (2 := b'). rewrite zlt_true. reflexivity.
        exploit Genv.find_event_symbol_find_symbol; eauto. intro. exploit (Genv.genv_symb_range); eauto. omega.
      Qed.

      Lemma external_call'_inject: 
        forall (ef: BuiltinFunctions.builtin_function) args args' m m' m0 t v f,
          external_call ef (ge) (args) m t v m' ->
          Mem.inject (relate_AbData f) f m m0 ->
          (forall (b1 b2 : block) (delta : Z),
             f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)->
          val_list_inject f args args' ->
          inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
          (Mem.nextblock m <= Mem.nextblock m0) ->
          match_AbData (Mem.get_abstract_data m) m0 f ->
          exists f', exists v', exists m'0,
                                  external_call ef (tge) (args') m0 t v' m'0
                                  /\ val_inject f' v v'
                                  /\ Mem.inject (relate_AbData f') f' m' m'0
                                  /\ inject_incr f f'
                                  /\  (forall (b1 b2 : block) (delta : Z),
                                         f' b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)
                                  /\ (Mem.nextblock m' <= Mem.nextblock m'0)
                                  /\ match_AbData (Mem.get_abstract_data m') m'0 f' .
      Proof.
        intros.
        rename H4 into HNEXT.
        rename H5 into HMATCH.
        destruct ef; simpl.    
        (*volatile_load*)
        inv H.
        inv H2. inv H8. inv H6. inv H4. 
        pose proof (Genv.find_event_symbol_find_symbol _ _ H2) as H2'.
        specialize (find_symbol_inject _  _ _ H3 H2'). intros EQ.
        rewrite H5 in EQ; inv EQ.
        rewrite Int.add_zero. exists f. exists (Val.load_result chunk v0). exists m0.
        repeat (split; eauto).
        constructor; eauto.
        rewrite event_symbols_preserved; eauto.
        eapply valid_event_symbol_inject; now eauto.
        apply val_load_result_inject. eauto. 

        assert(HL: Mem.loadv chunk m' (Vptr b ofs) = Some v).
        simpl.
        trivial.
        exploit (Mem.loadv_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto. 
        simpl; intros [v' [A B]]. exists f. exists v'. exists m0.
        repeat (split; eauto).
        constructor; eauto. 
        inv B; congruence.

        (*store*)
        inv H.
        inv H2. inv H6. inv H8. inv H9.
        inv H4.
        pose proof (Genv.find_event_symbol_find_symbol _ _ H2) as H2'.
        specialize (find_symbol_inject _  _ _ H3 H2'). intros EQ. rewrite H5 in EQ; inv EQ.
        rewrite Int.add_zero. exists f. exists Vundef. exists m0.
        repeat (split; eauto).
        constructor; eauto.  
        rewrite event_symbols_preserved; eauto.
        eapply valid_event_symbol_inject; now eauto.

        assert (Mem.storev chunk m (Vptr b ofs) v0 = Some m'). simpl; auto.
        exploit (Mem.storev_mapped_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto. intros [m0' [A B]].
        exists f. exists Vundef. exists m0'.
        repeat (split; eauto).
        constructor; eauto. 
        inv H6; congruence.
        erewrite (Mem.tget_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto.
        rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
        inv A.
        rewrite (Mem.nextblock_store _ _ _ _ _ _ H8).
        trivial.
        
        assert(HAB: Mem.get_abstract_data m' = Mem.get_abstract_data m).
        rewrite (Mem.store_get_abstract_data _ _ _ _ _ _ H2).
        trivial.
        rewrite HAB.
        simpl in H4.
        eapply store_match_correct; eauto.
        
        (*load_global*)
        inv H.
        inv H2. inv H5.  
        exists f. exists (Val.load_result chunk v0). exists m0.
        repeat (split; eauto).
        apply BuiltinFunctions.volatile_load_global_sem_intro with b; eauto.
        constructor; eauto.
        rewrite event_symbols_preserved; eauto.
        eapply valid_event_symbol_inject; now eauto.
        apply val_load_result_inject. eauto. 
        
        specialize (find_symbol_inject _  _ _ H3 H4). intros EQ.
        assert(val_inject f (Vptr b ofs) (Vptr b ofs)).
        econstructor.
        eapply EQ.
        rewrite Int.add_zero.
        trivial.

        assert(HL: Mem.loadv chunk m' (Vptr b ofs) = Some v).
        simpl.
        trivial.
        exploit (Mem.loadv_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto. simpl; intros [v' [A B]]. 
        exists f. exists v'. exists m0.
        repeat (split; eauto).        
        apply BuiltinFunctions.volatile_load_global_sem_intro with b; eauto.  
        constructor; eauto. 
        inv B; congruence.
        
        (*store global*)
        inv H.
        inv H2. inv H9.
        inv H5.
        exists f. exists Vundef. exists m0.
        repeat (split; eauto).
        apply BuiltinFunctions.volatile_store_global_sem_intro with b; eauto.
        constructor; eauto. 
        rewrite event_symbols_preserved; eauto.
        eapply valid_event_symbol_inject; now eauto.

        assert (Mem.storev chunk m (Vptr b ofs) v0 = Some m'). simpl; auto.
        specialize (find_symbol_inject _  _ _ H3 H4). intros EQ.
        assert(val_inject f (Vptr b ofs) (Vptr b ofs)).
        econstructor.
        eapply EQ.
        rewrite Int.add_zero.
        trivial.

        exploit (Mem.storev_mapped_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto. intros [m0' [A B]].
        exists f. exists Vundef. exists m0'.
        repeat (split; eauto).
        apply BuiltinFunctions.volatile_store_global_sem_intro with b; eauto.
        constructor; eauto. 
        inv H7; congruence.
        erewrite (Mem.tget_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto.
        rewrite (Mem.nextblock_store _ _ _ _ _ _ H2).
        inv A.
        rewrite (Mem.nextblock_store _ _ _ _ _ _ H9).
        trivial.
        
        assert(HAB: Mem.get_abstract_data m' = Mem.get_abstract_data m).
        rewrite (Mem.store_get_abstract_data _ _ _ _ _ _ H2).
        trivial.
        rewrite HAB.
        simpl in H5.
        eapply store_match_correct; eauto.

        (*memcpy*)
        inv H. inv H2. inv H13. inv H15. inv H13. inv H16.
        exploit (Mem.loadbytes_length m); eauto. intros LEN.
        assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + sz) Cur Nonempty).
        eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
        assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + sz) Cur Nonempty).
        replace sz with (Z_of_nat (length bytes)).
        eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
        rewrite LEN. apply nat_of_Z_eq. omega.
        assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
        apply RPSRC. omega.
        assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
        apply RPDST. omega.
        exploit (Mem.address_inject (Mem__inject := Mem.inject (relate_AbData f))).  eauto. eexact PSRC. eauto. intros EQ1.
        exploit (Mem.address_inject (Mem__inject := Mem.inject (relate_AbData f))).  eauto. eexact PDST. eauto. intros EQ2.
        exploit (Mem.loadbytes_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto. intros [bytes2 [A B]].
        exploit (Mem.storebytes_mapped_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto. intros [m2' [C D]].
        exists f; exists Vundef; exists m2'.
        split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto.
        eapply Mem.aligned_area_inject with (m1 := m); eauto.
        eapply Mem.aligned_area_inject with (m1 := m); eauto.
        eapply Mem.disjoint_or_equal_inject with (m1 := m); eauto.
        apply Mem.range_perm_max with Cur; auto.
        apply Mem.range_perm_max with Cur; auto.
        erewrite (Mem.tget_inject (Mem__inject := Mem.inject (relate_AbData f))); eauto.
        repeat (split; eauto).
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ C).
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H11).
        trivial.
        
        assert(HAB: Mem.get_abstract_data m' = Mem.get_abstract_data m).
        rewrite (Mem.storebytes_get_abstract_data _ _ _ _ _ H11).
        trivial.
        rewrite HAB.
        eapply storebytes_match_correct with (b2:= b2); eauto.
        
        (*annot*)
        inv H. 
        exists f; exists Vundef; exists m0.
        repeat (split; eauto).
        
        (*annot_val*)
        inv H.
        inv H2. inv H8.
        exists f; exists v'; exists m0.
        repeat (split; eauto).
        
        (*annot_sem*)
        inv H. 
        exists f; exists Vundef; exists m0.
        repeat (split; eauto).
      Qed.
      
    End EXT_CALL.

    Section INSTR.

      Lemma symbol_inj:
        forall f,
          inject_incr (Mem.flat_inj (Genv.genv_next ge)) f
          -> (forall id ofs, val_inject f (symbol_offset ge id ofs) (symbol_offset (Genv.globalenv tprog) id ofs)).
      Proof.
        intros.
        unfold symbol_offset.
        caseEq (Genv.find_symbol ge id).
        intros b0 HGF.
        specialize (symbols_preserved _ _ HGF).
        intro HGF'.
        simpl in *.
        unfold tge in HGF'.   
        rewrite HGF'.
        apply val_inject_ptr with 0.
        assert(HP': (Mem.flat_inj (Genv.genv_next ge)) b0 = Some (b0,0)).
        unfold Mem.flat_inj.
        destruct( zlt b0 (Genv.genv_next ge)).
        trivial.
        unfold Genv.find_symbol in HGF.
        specialize (Genv.genv_symb_range _ _ HGF).
        intro HB'.
        inv HB'.
        contradict H1.
        apply Zle_not_lt.
        apply Zge_le.
        trivial.
        specialize (H _ _ _ HP').
        trivial.
        rewrite Int.add_zero; trivial.
        intros.
        constructor.
      Qed.
      
      Lemma exist_step_simpl:
        forall r' b ofs c i m'0 m' rs',
          r' PC = Vptr b ofs ->
          Genv.find_funct_ptr tge b = Some (Internal c) ->
          find_instr (Int.unsigned ofs) c = Some i ->
          (exists r m0,
             LSemantics.exec_instr (exec_load:= Lexec_load) (exec_store := Lexec_store) tge c i r' m'0 = Next r m0 /\
             match_states (State rs' m') (State r m0)) ->
          (exists s2',
             plus lstep tge (State r' m'0) E0 s2' /\
             match_states (State rs' m') s2').
      Proof.
        intros.
        destruct H2 as [r[m0 [HSTP HMACH]]].
        exists (State r m0).
        split; trivial.
        apply plus_one.
        apply LSemantics.exec_step_internal with b ofs c i; trivial.
      Qed.

      Context `{functions_preserved:
                  forall fb f,
                    Genv.find_funct_ptr ge fb = Some (Internal f) 
                    -> Genv.find_funct_ptr tge fb = Some (Internal f)}.

      Context`{high_level_invariant: datah -> Prop}.

      Hypothesis store_correct:
        forall t m a rs rd rs' m' r0 m0 f,
          LSemantics.exec_storeex (exec_store:= Hexec_store) ge t m a rs rd = Next rs' m'
          -> match_AbData (Mem.get_abstract_data m) m0 f
          -> Mem.inject (relate_AbData f) f m m0
          -> (forall reg : PregEq.t,
                val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) 
          -> val_inject f (Val.add (rs PC) Vone) (Val.add (r0 PC) Vone)
          -> inject_incr (Mem.flat_inj (Genv.genv_next ge)) f
          -> (forall b1 b2 delta, f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)
          -> (Mem.nextblock m <= Mem.nextblock m0)
          -> forall HIGH_LEVEL_INVARIANT: high_level_invariant (Mem.get_abstract_data m),
             exists r'0 m'0,
               LSemantics.exec_storeex (exec_store:= Lexec_store) tge t m0 a r0 rd 
               = Next r'0 m'0
               /\ match_states (State rs' m') (State r'0 m'0).

      Hypothesis load_correct:
        forall t m a rs rd rs' m' r0 m0 f,
          LSemantics.exec_loadex (exec_load:=Hexec_load) ge t m a rs rd = Next rs' m'
          -> match_AbData (Mem.get_abstract_data m) m0 f
          -> Mem.inject (relate_AbData f) f m m0
          -> (forall reg : PregEq.t,
                val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) 
          -> val_inject f (Val.add (rs PC) Vone) (Val.add (r0 PC) Vone)
          -> inject_incr (Mem.flat_inj (Genv.genv_next ge)) f
          -> (forall b1 b2 delta, f b1 = Some (b2, delta) -> delta = 0 /\ b1 <= b2)
          -> (Mem.nextblock m <= Mem.nextblock m0)
          -> forall HIGH_LEVEL_INVARIANT: high_level_invariant (Mem.get_abstract_data m),
             exists r'0 m'0,
               LSemantics.exec_loadex (exec_load := Lexec_load) tge t m0 a r0 rd 
               = Next r'0 m'0
               /\ match_states (State rs' m') (State r'0 m'0).

      (** ** Show that the internal instructions satisfy the refinement relation*)
      Lemma instruct_correct:
        forall c i rs m rs' m' s2 b ofs,
          LSemantics.exec_instr (exec_load:=Hexec_load) 
                                (exec_store := Hexec_store) ge c i rs m = Next rs' m'
          -> Genv.find_funct_ptr ge b = Some (Internal c)
          -> find_instr (Int.unsigned ofs) c = Some i
          -> rs PC = Vptr b ofs
          -> match_states (State rs m) s2
          -> forall HIGH_LEVEL_INVARIANT: high_level_invariant (Mem.get_abstract_data m),
             exists s2' : state lsemantics,
               Plus lsemantics s2 E0 s2' /\
               match_states (State rs' m') s2'.
      Proof.
        intros.
        generalize H3.
        intro HM.
        inv H3.
        rename H12 into HESP.
        rename H14 into HNEXT.
        
        generalize (flat_inj_func _ _ H0).
        intro HP.
        
        generalize (functions_preserved _ _ H0).
        intro HFIND.
        
        generalize (symbol_inj _ H11).
        intros HSYMBOL.
        
        generalize (PC_ofs_inj _ _ _ _ _ H10 H11 HP H2).
        intros [HPC HINJ].

        generalize (PC_add _ _ _ _ _ Int.one H2 HPC HINJ).
        fold Vone.
        intro HVAL_ONE.
        
        generalize (undef_inj _ _ _ H10 HVAL_ONE).
        intro HVAL_UNDEF.
        
        generalize (undef_inj' _ _ _ H10).
        intro HVAL_UNDEF'.
        
        simpl.
        apply (exist_step_simpl _ _ _ _ _ _ _ _ HPC HFIND H1).
        
        clear HFIND NEW_INJ.
        Opaque preg_eq Mem.load Mem.store Mem.alloc Mem.free.
        caseEq i;
          intros;
          inv H; simpl in H5; simpl;  Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl.

        *
          (*Int to float *)      
          destruct (Float.intoffloat f0); constructor.
          
        *
          (* addr mode*)        
          eapply eval_addrmode_correct; eauto.
          eapply symbols_preserved; eauto.
          
        *
          (*sub*)
          apply val_inject_ptr with delta; trivial.
          apply Int.sub_add_l.
          
        *
          (*zeq b0 b1*)
          rewrite e in H5.
          rewrite H5 in H7.
          inv H7.
          caseEq (zeq b4 b4).
          intros.
          rewrite Int.sub_shifted.
          constructor.
          intros.
          clear H.
          contradict n4.
          trivial.
          
        (* division *)
        * revert H5. 
          case_eq (exec_division div r1 rs); try discriminate.
          intros until 1. intro J. inv J.
          exploit exec_division_inject.
          eexact H10.
          eassumption.
          destruct 1 as [? [DIV ?]].
          rewrite DIV.
          esplit. esplit. split. reflexivity.
          econstructor.
          3: eassumption.
          reflexivity.
          reflexivity.
          assumption.
          apply nextinstr_nf_inject. assumption.
          assumption.
          assumption.
          assumption.

        (* wrap division *)
        * destruct (preg_eq rd EAX); try discriminate.
          revert H5.
          case_eq (exec_division div ECX (rs # EAX <- (rs rd) # ECX <- (rs r1))); try discriminate.
          intros until 1. intro J. inv J.
          exploit exec_division_inject.         
          2: eassumption.
          instantiate (1 := ((r' # EAX <- (r' rd)) # ECX <- (r' r1))).
          eapply set_reg_inject; eauto.
          apply set_reg_inject; eauto.
          destruct 1 as [? [DIV ?]].
          rewrite DIV.
          esplit. esplit. split. reflexivity.
          econstructor.
          3: eassumption.
          reflexivity.
          reflexivity.
          assumption.
          apply nextinstr_nf_inject.
          apply undef_reg_inject.
          apply set_reg_inject; eauto.
          apply set_reg_inject; eauto.
          assumption.
          assumption.
          assumption.

        (* wrap mod *)
        * destruct (preg_eq rd EAX); try discriminate.
          revert H5.
          case_eq (exec_division div ECX (rs # EAX <- (rs rd) # ECX <- (rs r1))); try discriminate.
          intros until 1. intro J. inv J.
          exploit exec_division_inject.         
          2: eassumption.
          instantiate (1 := ((r' # EAX <- (r' rd)) # ECX <- (r' r1))).
          eapply set_reg_inject; eauto.
          apply set_reg_inject; eauto.
          destruct 1 as [? [DIV ?]].
          rewrite DIV.
          esplit. esplit. split. reflexivity.
          econstructor.
          3: eassumption.
          reflexivity.
          reflexivity.
          assumption.
          apply nextinstr_nf_inject.
          apply undef_reg_inject.
          apply set_reg_inject; eauto.
          apply set_reg_inject; eauto.
          assumption.
          assumption.
          assumption.

        *        
          (* compare_ints*) 
          unfold compare_ints.
          repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl).
          IF_Simpl.
          generalize H10.
          intro HT.
          unfold Pregmap.get in HT.
          generalize HT.
          intro HTT.
          specialize (HT r1).
          specialize (HTT r2).
          IF_Simpl.

          unfold Val.cmp.
          unfold Val.of_optbool.
          caseEq(Val.cmp_bool Clt (rs r1) (rs r2)).
          intros.
          specialize (val_cmp_bool_inject _ Clt _ _ _ _ _ HT HTT H). 
          intro HB.
          rewrite HB.
          destruct b0; constructor.
          
          intros; constructor.
          
          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq(Val.cmpu_bool (Mem.valid_pointer m') Clt (rs r1) (rs r2)).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.
          destruct b0; constructor.
          
          intros.
          constructor.
          
          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq(Val.cmpu_bool (Mem.valid_pointer m') Ceq (rs r1) (rs r2)).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.        
          destruct b0; constructor.
          
          intros.
          constructor.

        *
          (* compare_ints*) 
          unfold compare_ints.
          repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl).
          IF_Simpl.
          generalize H10.
          intro HT.
          unfold Pregmap.get in HT.
          specialize (HT r1).
          assert (HTT: val_inject f (Vint n) (Vint n)).
          constructor.
          IF_Simpl.

          unfold Val.cmp.
          unfold Val.of_optbool.
          caseEq(Val.cmp_bool Clt (rs r1) (Vint n)).
          intros.
          specialize (val_cmp_bool_inject _ Clt _ _ _ _ _ HT HTT H). 
          intro HB.
          rewrite HB.
          destruct b0; constructor.
          
          intros; constructor.
          
          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq(Val.cmpu_bool (Mem.valid_pointer m') Clt (rs r1) (Vint n)).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.
          destruct b0; constructor.

          intros.
          constructor.

          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq(Val.cmpu_bool (Mem.valid_pointer m') Ceq (rs r1) (Vint n)).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.
          destruct b0; constructor.

          intros.
          constructor.

        *
          (* compare_ints*) 
          unfold compare_ints.
          repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl).
          IF_Simpl.
          
          assert (HT: val_inject f (Val.and (rs r1) (rs r2)) (Val.and (r' r1) (r' r2))).
          Val_Calculate H10.  

          assert (HTT: val_inject f Vzero Vzero).
          constructor.
          IF_Simpl.

          unfold Val.cmp.
          unfold Val.of_optbool.
          caseEq(Val.cmp_bool Clt (Val.and (rs r1) (rs r2)) Vzero).
          intros.
          specialize (val_cmp_bool_inject _ Clt _ _ _ _ _ HT HTT H). 
          intro HB.
          rewrite HB.
          destruct b0; constructor.
          
          intros; constructor.
          
          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq (Val.cmpu_bool (Mem.valid_pointer m') Clt (Val.and (rs r1) (rs r2))
                                Vzero).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.
          destruct b0; constructor.

          intros.
          constructor.

          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq (Val.cmpu_bool (Mem.valid_pointer m') Ceq (Val.and (rs r1) (rs r2))
                                Vzero).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.
          destruct b0; constructor.

          intros.
          constructor.

        *
          (* compare_ints*) 
          unfold compare_ints.
          repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl).
          IF_Simpl.
          
          assert (HT: val_inject f (Val.and (rs r1) (Vint n)) (Val.and (r' r1) (Vint n))).
          Val_Calculate H10.  

          assert (HTT: val_inject f Vzero Vzero).
          constructor.
          IF_Simpl.

          unfold Val.cmp.
          unfold Val.of_optbool.
          caseEq(Val.cmp_bool Clt (Val.and (rs r1) (Vint n)) Vzero).
          intros.
          specialize (val_cmp_bool_inject _ Clt _ _ _ _ _ HT HTT H). 
          intro HB.
          rewrite HB.
          destruct b0; constructor.
          
          intros; constructor.
          
          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq (Val.cmpu_bool (Mem.valid_pointer m') Clt (Val.and (rs r1) (Vint n))
                                Vzero).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.
          destruct b0; constructor.

          intros.
          constructor.

          IF_Simpl.
          unfold Val.cmpu.
          unfold Val.of_optbool.
          simpl in *.
          caseEq (Val.cmpu_bool (Mem.valid_pointer m') Ceq (Val.and (rs r1) (Vint n))
                                Vzero).
          intros.
          specialize (mem_cmpu_bool_inject _ _ _ H9 _ _ _ _ _ _ HT HTT H). 
          intros.
          setoid_rewrite H3.
          destruct b0; constructor.

          intros.
          constructor.

        *
          (*eval_testcond*)
          caseEq (eval_testcond c0 rs).
          intros.
          specialize (eval_testcond_inj _ _ _ _ _ H10 H).
          intros.
          rewrite H3.
          rewrite H in H5.
          destruct b0; Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl.
          
          intros.
          rewrite H in H5.
          destruct (eval_testcond c0 r').
          destruct b0; Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl.
          Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl.

        *
          (*eval_testcond*)
          unfold Val.of_optbool.
          caseEq ( eval_testcond c0 rs).
          intros.
          specialize (eval_testcond_inj _ _ _ _ _ H10 H).
          intros.
          setoid_rewrite H3.
          simpl.
          destruct b0; constructor.

          intros.
          constructor.

        *
          (* compare_floats*) 
          unfold compare_floats.
          generalize H10.
          intros HT.
          unfold Pregmap.get in HT.
          generalize HT.
          intro HTT.
          specialize (HT r1).
          destruct (rs r1); inv HT; trivial.
          destruct (r' r1); trivial.
          
          destruct (r' r2); trivial.
          unfold undef_regs;
            repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
            trivial.
          
          specialize (HTT r2).
          destruct (rs r2); inv HTT; trivial.
          destruct (r' r2); trivial.

        *
          (* compare_floats*) 
          unfold compare_floats.
          generalize H10.
          intros HT.
          unfold Pregmap.get in HT.
          generalize HT.
          intro HTT.
          specialize (HT r1).
          destruct (rs r1); inv HT; trivial.
          destruct (r' r1); trivial.
          
          destruct (r' r2); trivial.
          unfold undef_regs;
            repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
            trivial.
          repeat IF_Simpl.

          specialize (HTT r2).
          destruct (rs r2); inv HTT; trivial.
          destruct (r' r2); trivial.

          unfold undef_regs;
            repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
            trivial.
          repeat IF_Simpl.

          repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
          trivial.
          repeat IF_Simpl.
          
          destruct (negb (Float.cmp Ceq f0 f1 || Float.cmp Clt f0 f1 || Float.cmp Cgt f0 f1)); simpl; constructor.
          destruct (negb (Float.cmp Cge f0 f1)); simpl; constructor.
          destruct  (negb (Float.cmp Cne f0 f1)); simpl; constructor.

        *
          (*goto_label*)
          Goto_Label H5 H10 H2 HPC MATCH_STATE Pregmap_Simpl.
          
        *
          (*eval_testcond*)
          caseEq (eval_testcond c0 rs).
          intros.
          specialize (eval_testcond_inj _ _ _ _ _ H10 H).
          intros.
          rewrite H3.
          rewrite H in H5.
          destruct b0; Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl.
          
          Goto_Label H5 H10 H2 HPC MATCH_STATE Pregmap_Simpl.

          intros.
          rewrite H in H5.
          inv H5.

        *
          (*eval_testcond*)
          caseEq (eval_testcond c1 rs).
          intros.
          specialize (eval_testcond_inj _ _ _ _ _ H10 H).
          intros.
          rewrite H3.
          rewrite H in H5.
          caseEq (eval_testcond c2 rs).
          intros.
          specialize (eval_testcond_inj _ _ _ _ _ H10 H4).
          intros.
          rewrite H6.
          rewrite H4 in H5.

          destruct b0; Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl.
          destruct b1; Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl.

          Goto_Label H5 H10 H2 HPC MATCH_STATE Pregmap_Simpl.

          intros.
          rewrite H4 in H5.
          destruct b0; inv H5.
          
          intros.
          rewrite H in H5.
          inv H5.

        *
          (* match list_nth_Z *)
          generalize H10.
          unfold Pregmap.get.
          intro HT.
          generalize HT.
          intro HTT.
          specialize (HT r).
          destruct (rs r);
            match goal with
              | [ H: Stuck = _ |- _] => inv H
              | _ => inv HT
            end.
          
          destruct (list_nth_z tbl (Int.unsigned i)).
          unfold goto_label in *.
          generalize H5.
          clear H5.
          repeat (rewrite Pregmap_Simpl; simpl).
          rewrite H2.
          rewrite HPC.  
          intro H5.
          destruct (label_pos l 0 c); 
            match goal with
              | [ |- exists _ _, Stuck = _ /\ _] => inv H5
              | _ =>  Normal_Next H5 H10 MATCH_STATE Pregmap_Simpl;apply val_inject_ptr with 0; auto;  rewrite Int.add_zero; trivial
            end.
          inv H5.
          
        (*alloc*) 
        * case_eq (Mem.alloc Tag_stack m 0 sz);
          intros.
          specialize (Mem.alloc_parallel_inject _ _ _ _ _ _ _ _ _ H9 H (Zle_refl 0) (Zle_refl sz)).
          intro HEX.
          destruct HEX as [f' [m'1 [b'1[ HAL1[HINJ1 [HINCR1 [HF1 HBB1]]]]]]].
          setoid_rewrite HAL1.
          setoid_rewrite H in H5.
          assert (HVJ:forall reg, val_inject f' (Pregmap.get reg rs) (Pregmap.get reg r')).
          intros.
          specialize (H10 reg).
          eapply val_inject_incr; eauto.
          
          generalize HVJ.
          unfold Pregmap.get.
          intro HT.
          generalize HT.
          intro HTT.
          specialize (HT ESP).
          case_eq (Mem.store Mint32 m0 b0
                             (Int.unsigned (Int.add Int.zero ofs_link)) 
                             (rs ESP));
            intros.
          specialize (Mem.store_mapped_inject _ _ _ _ _ _ _ _ _ _ _ HINJ1 H3 HF1 HT).
          intro HEX.
          destruct HEX as [n2 [HST2 HINJ2]].
          simpl in H5; setoid_rewrite H3 in H5; simpl in H5.
          rewrite Z.add_0_r in HST2.
          setoid_rewrite HST2.
          case_eq (Mem.store Mint32 m1 b0
                             (Int.unsigned (Int.add Int.zero ofs_ra)) 
                             (rs RA));
            intros.
          setoid_rewrite H4 in H5.
          specialize (HTT RA).
          specialize (Mem.store_mapped_inject _ _ _ _ _ _ _ _ _ _ _ HINJ2 H4 HF1 HTT).
          intro HEX.
          destruct HEX as [n3 [HST3 HINJ3]].
          rewrite Z.add_0_r in HST3.
          setoid_rewrite HST3.
          
          exists (nextinstr (r' # EDX <- (r' ESP)) # ESP <- (Vptr b'1 Int.zero)); exists n3.
          split; trivial.
          inv H5; eapply MATCH_STATE with (f:=f'); eauto.

          assert(HAB: Mem.get_abstract_data m' = Mem.get_abstract_data m).
          symmetry.
          etransitivity.
          eapply Mem.alloc_get_abstract_data; eauto.
          etransitivity.
          eapply Mem.store_get_abstract_data; eauto.
          eapply Mem.store_get_abstract_data; eauto.

          simpl in HAB.
          rewrite HAB.
          
          assert(HM1: match_AbData (Mem.get_abstract_data m) n2 f').
          assert(HM1: match_AbData (Mem.get_abstract_data m) m'1 f').
          eapply alloc_match_correct; eauto.
          eapply store_match_correct; eauto.
          eapply store_match_correct; eauto.
          
          eapply Mem.inject_extends_compose.
          eassumption.
          eauto.

          Next_NF_Simpl.
          destruct (Pregmap.elt_eq reg PC); trivial.
          apply val_inject_incr with f; trivial.

          repeat (Var_Inject_Simpl H10). 
          apply val_inject_ptr with 0; trivial.
          
          apply inject_incr_trans with f; trivial.
          
          intros.
          caseEq(zeq b1 b0); intros.
          subst b1.
          rewrite H5 in HF1.
          inv HF1; split; trivial.
          rewrite (Mem.alloc_result _ _ _ _ _ H).
          rewrite (Mem.alloc_result _ _ _ _ _ HAL1).
          trivial.
          
          apply HESP.
          rewrite <- H5.
          rewrite HBB1; trivial.
          
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H4).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ HST3).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
          rewrite (Mem.nextblock_store _ _ _ _ _ _ HST2).
          rewrite (Mem.nextblock_alloc _ _ _ _ _ H).
          rewrite (Mem.nextblock_alloc _ _ _ _ _ HAL1).
          omega.

          setoid_rewrite H4 in H5.
          inv H5.
          
          simpl in H5.
          setoid_rewrite H3 in H5.
          inv H5.

        *
          (*free*)
          case_eq (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra)));
          intros.
          generalize H10.
          unfold Pregmap.get.
          intro HT.
          generalize HT.
          intro HTT.
          specialize (HT ESP).
          assert (HVJ1:val_inject f (Val.add (rs ESP) (Vint ofs_ra))  (Val.add (r' ESP) (Vint ofs_ra)) ).
          destruct (rs ESP); inv HT; simpl; try constructor.
          apply val_inject_ptr with delta; trivial.
          repeat (rewrite Int.add_assoc).
          rewrite (Int.add_commut (Int.repr delta) ofs_ra).
          trivial.

          specialize(Mem.loadv_inject _ _ _ _ _ _ _ H9 H HVJ1).
          intro HEX.
          destruct HEX as [v2[ HLD1 HINJ1]].
          setoid_rewrite HLD1.
          simpl in H.
          rewrite H in H5.

          case_eq (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link)));
            intros.
          assert (HVJ2:val_inject f (Val.add (rs ESP) (Vint ofs_link))  (Val.add (r' ESP) (Vint ofs_link)) ).
          destruct (rs ESP); inv HT; simpl; try constructor.
          apply val_inject_ptr with delta; trivial.
          repeat (rewrite Int.add_assoc).
          rewrite (Int.add_commut (Int.repr delta) ofs_link).
          trivial.

          specialize(Mem.loadv_inject _ _ _ _ _ _ _ H9 H3 HVJ2).
          intro HEX.
          destruct HEX as [v3[ HLD2 HINJ2]].
          setoid_rewrite HLD2.
          simpl in H3.
          rewrite H3 in H5.
          
          destruct (rs ESP).
          inv H5.
          inv H5.
          inv H5.
          inv HT.
          generalize (HESP).
          intro HESP'.
          specialize (HESP' _ _ _  H12).
          destruct HESP' as [HESP' _].
          subst delta.
          caseEq(Mem.free m b0 0 sz); simpl; intros.
          rewrite H4 in H5.
          specialize (Mem.free_parallel_inject _ _ _ _ _ _ _ _ _ H9 H12 H4).
          intro HEX.
          destruct HEX as [m2' [HFREE3 HINJ3]].
          repeat rewrite Z.add_0_r in HFREE3.
          setoid_rewrite HFREE3.
          exists (nextinstr (r' # ESP <- v3) # RA <- v2); exists m2'.
          split; trivial;inv H5; eapply MATCH_STATE; eauto.

          assert(HAB: Mem.get_abstract_data m' = Mem.get_abstract_data m).
          simpl.
          rewrite (Mem.free_get_abstract_data _ _ _ _ _ H4).
          trivial.
          
          simpl in HAB.
          rewrite HAB.
          eapply free_match_correct; eauto.
          
          Next_NF_Simpl.
          destruct (Pregmap.elt_eq reg PC); trivial.
          apply val_inject_incr with f; trivial.

          repeat (Var_Inject_Simpl H10). 
          
          setoid_rewrite (Mem.nextblock_free m b0 0 sz m' H4).
          rewrite (Mem.nextblock_free _ _ _ _ _ HFREE3).
          trivial.

          rewrite H4 in H5.
          inv H5.
          
          simpl in H3.
          rewrite H3 in H5.
          inv H5.
          
          simpl in H.
          rewrite H in H5.
          inv H5.

      Qed.

      Context`{low_level_invariant: Z -> datal -> Prop}.
      Context`{Lhigh_level_invariant: datal -> Prop}.

      Hypothesis transf_external_correct:
        forall (t : trace)  (s2 : state lsemantics) (rs: regset) m m' b ef args res,
        forall ASM_INVARIANT : asm_invariant tge s2,
        forall LOW_LEVEL_INVARIANT : low_level_invariant (Mem.nextblock (LSemantics.get_mem s2))
                                                         (Mem.get_abstract_data (LSemantics.get_mem s2)),
        forall HIGH_LEVEL_INVARIANT: high_level_invariant (Mem.get_abstract_data m),
        forall L_HIGH_LEVEL_INVARIANT: Lhigh_level_invariant (Mem.get_abstract_data (LSemantics.get_mem s2)),
        forall SP_NOT_VUNDEF : rs ESP <> Vundef,
        forall RA_NOT_VUNDEF : rs RA <> Vundef,
        forall SP_STACK : (forall (b : block) (o : int),
                             rs ESP = Vptr b o -> Mem.tget m b = Some Tag_stack),
        forall HMATCH: match_states (State rs m) s2,
        forall HCPC: rs PC = Vptr b Int.zero,
        forall HFIND_FUN: Genv.find_funct_ptr ge b = Some (External ef),
        forall HEXTCALL_SEM: external_call ef ge args m t res m',
        forall HEXTCALL_ARG: extcall_arguments rs m (ef_sig ef) args,
        exists s2' : state lsemantics,
          Plus lsemantics s2 t s2' /\
          match_states
            (State
               ((undef_regs (RA :: (CR ZF) :: (CR CF) :: (CR PF) :: (CR SOF) :: nil)
                            (undef_regs (map preg_of Conventions1.temporary_regs)
                                        (undef_regs
                                           (map preg_of Conventions1.destroyed_at_call_regs) rs)))
                  # (loc_external_result (ef_sig ef)) <- res) # PC <- 
               (rs RA) m') s2'.

      Hypothesis transf_primitive_correct:
        forall (t : trace)  (s2 : state lsemantics) (rs rs': regset) m m' b ef args res,
        forall ASM_INVARIANT : asm_invariant tge s2,
        forall LOW_LEVEL_INVARIANT : low_level_invariant (Mem.nextblock (LSemantics.get_mem s2))
                                                         (Mem.get_abstract_data (LSemantics.get_mem s2)),
        forall HIGH_LEVEL_INVARIANT: high_level_invariant (Mem.get_abstract_data m),
        forall L_HIGH_LEVEL_INVARIANT: Lhigh_level_invariant (Mem.get_abstract_data (LSemantics.get_mem s2)),
        forall HMATCH: match_states (State rs m) s2,
        forall HCPC: rs PC = Vptr b Int.zero,
        forall HFIND_FUN: Genv.find_funct_ptr ge b = Some (External ef),
        forall HEXTCALL_SEM: Hprimitive_call ef fundef unit ge args rs m t res rs' m',
        forall HEXTCALL_ARG: extcall_arguments rs m (ef_sig ef) args,
        exists s2' : state lsemantics,
          Plus lsemantics s2 t s2' /\ match_states (State rs' m') s2'.

      Lemma transf_correct:
        forall s1 t s1',
          Step hsemantics s1 t s1' ->
          forall s2,
            match_states s1 s2 ->
            forall ASM_INVARIANT: asm_invariant tge s2,
            forall LOW_LEVEL_INVARIANT: low_level_invariant (Mem.nextblock (get_mem s2)) (Mem.get_abstract_data (get_mem s2)),
            forall HIGH_LEVEL_INVARIANT: high_level_invariant (Mem.get_abstract_data (get_mem s1)),
            forall L_HIGH_LEVEL_INVARIANT: Lhigh_level_invariant (Mem.get_abstract_data (get_mem s2)),
            exists s2',
              Plus (lsemantics) s2 t s2' /\ match_states s1' s2'.
      Proof.
        intros.  
        inv H.
        +(*internal instruction *)
          eapply instruct_correct; eauto.

        +(*buildin*)
          inversion H0.
          specialize (val_list_inject_args _ _ args _ H10).
          intro HVL.
          subst habd.
          specialize (external_call'_inject  _ _ _ _ _ _ _ _ _ H4 H9 H12 HVL H11 H14 H8).
          intros [f'[v'[m'1[HCALL [HVJ[HINJ[Hincr[HB [HN HM]]]]]]]]].    
          exists (State
                    (nextinstr_nf
                       (((((r' # EDX <- Vundef) # ECX <- Vundef) # XMM6 <- Vundef)
                           # XMM7 <- Vundef) # ST0 <- Vundef) # res <- v') m'1).
          generalize (flat_inj_func _ _ H2).
          intro HP.
          
          generalize (PC_ofs_inj _ _ _ _ _ H10 H11 HP H1).
          intros [HPC _].

          split.
          simpl in *.
          apply plus_one.
          apply LSemantics.exec_step_builtin with b ofs c ef args; auto.
          
          eapply MATCH_STATE; eauto.
          assert (HF': forall reg : PregEq.t,
                         val_inject f' (Pregmap.get reg rs) (Pregmap.get reg r')).
          intros.
          specialize (H10 reg).
          apply (val_inject_incr _ _ _ _ Hincr H10).
          
          Next_NF_Simpl.
          destruct (Pregmap.elt_eq reg PC); trivial.
          unfold Val.add.
          destruct res;
            repeat (rewrite Pregmap_Simpl; simpl); 
            try (rewrite H1; rewrite (HPC); econstructor; eauto; rewrite Int.add_zero; trivial).
          destruct v; inv HVJ; try constructor.
          econstructor; eauto.
          Int_Add_Simpl.

          repeat (Var_Inject_Simpl HF'); 
            Val_Calculate H10; repeat IF_Simpl.
          
          apply inject_incr_trans with f; trivial.

        +(*annotation*)
          inversion H0.
          specialize annot_preserved.
          simpl.
          intros Hano.
          specialize (Hano _ _ _ _ _ _ _ H11 H10 H4 H13).
          destruct Hano as  [vargs' [HAN HVL]].

          subst habd.
          specialize (external_call'_inject _ _ _ _ _ _ _ _ _ H5 H10 H13 HVL H12 H15 H9).
          intros [f'[v'[m'1[HCALL [HVJ[HINJ[Hincr[HB [HN HM]]]]]]]]].    
          exists (State (nextinstr r') m'1).

          generalize (flat_inj_func _ _ H2).
          intro HP.     
          generalize (PC_ofs_inj _ _ _ _ _ H11 H12 HP H1).
          intros [HPC _].

          split.
          simpl in *.
          apply plus_one.
          apply LSemantics.exec_step_annot with b ofs c ef args vargs' v'; auto.
          
          eapply MATCH_STATE; eauto.
          assert (HF':  forall reg : PregEq.t,
                          val_inject f' (Pregmap.get reg rs) (Pregmap.get reg r')).
          intros.
          specialize (H11 reg).
          apply (val_inject_incr _ _ _ _ Hincr H11).
          
          Next_NF_Simpl.
          destruct (Pregmap.elt_eq reg PC); trivial.
          unfold Vone.
          Val_Calculate HF'.
          econstructor; eauto.
          Int_Add_Simpl.
          
          apply inject_incr_trans with f; trivial.
          
        +(*external call*)
          eapply transf_external_correct; eauto.
          
        +(*Prim_Call*)

          eapply transf_primitive_correct; eauto.
      Qed.

      Context `{ empty_data_low_level_invariant:
                   forall n, low_level_invariant n empty_data}.

      Context `{ empty_data_high_level_invariant:
                   high_level_invariant empty_data}.

      Context `{ empty_data_L_high_level_invariant:
                   Lhigh_level_invariant empty_data}.

      Context `{ lsem_plus_invariant:
                   forall (ge: Asm.genv) s t s',
                     plus (lstep) ge s t s' ->
                     asm_invariant ge s ->
                     asm_invariant ge s'}.

      Context `{ lsem_plus_low_level_invariant:
                   forall (ge: Asm.genv) s t s',
                     plus lstep ge s t s' ->
                     asm_invariant ge s ->
                     low_level_invariant (Mem.nextblock (get_mem s)) (Mem.get_abstract_data (get_mem s)) ->
                     low_level_invariant (Mem.nextblock (get_mem s')) (Mem.get_abstract_data (get_mem s'))}.

      Context `{lsem_high_level_invariant:
                  forall (ge: Asm.genv) s t s',
                    hstep ge s t s' ->
                    high_level_invariant (Mem.get_abstract_data (get_mem s)) ->
                    high_level_invariant (Mem.get_abstract_data (get_mem s'))}.

      Context `{lsem_L_plus_high_level_invariant:
                  forall (ge: Asm.genv) s t s',
                    plus lstep ge s t s' ->
                    Lhigh_level_invariant (Mem.get_abstract_data (get_mem s)) ->
                    Lhigh_level_invariant (Mem.get_abstract_data (get_mem s'))}.

      Lemma forward_simulation:
        forward_simulation hsemantics lsemantics.
      Proof.
        apply forward_simulation_plus with
        (match_states := fun s1 s2 => match_states s1 s2 /\ asm_invariant tge s2 
                                      /\ low_level_invariant (Mem.nextblock (get_mem s2)) (Mem.get_abstract_data (get_mem s2))
                                      /\ high_level_invariant (Mem.get_abstract_data (get_mem s1))
                                      /\ Lhigh_level_invariant (Mem.get_abstract_data (get_mem s2))).

        apply event_symbols_preserved.
        intros. exploit transf_initial_states; eauto. destruct 1 as [? [? ?]].
        exists x.
        split; trivial.
        split; trivial.
        split.
        apply Asm.initial_state_invariant; trivial.
        split.
        inv H0.
        simpl.
        rewrite (Genv.init_mem_get_abstract_data _ _ H2).
        trivial.
        split.
        inv H.
        simpl.
        rewrite (Genv.init_mem_get_abstract_data _ _ H2).
        trivial.
        
        inv H0. simpl.
        rewrite (Genv.init_mem_get_abstract_data _ _ H2).
        trivial.

        destruct 1; eauto.
        apply transf_final_states; trivial.
        destruct 2.  destruct H1 as [HA [HL [HH HLH]]].
        exploit transf_correct; eauto. 
        destruct 1 as [? [? ?]]. esplit. split. eassumption. split. assumption. 
        split. eapply lsem_plus_invariant; eauto.
        split. eapply lsem_plus_low_level_invariant; eauto.
        split. eapply lsem_high_level_invariant; eauto.
        eapply lsem_L_plus_high_level_invariant; eauto.
      Qed.
      
      Context `{ hprimitive_call_trace_length:
                   forall ef F V (ge:Genv.t F V) t r m r' m' args res,
                     Hprimitive_call ef _ _ ge args r m t res r' m' ->
                     (length t <= 1)%nat}.

      Context `{ lprimitive_call_trace_length:
                   forall ef F V (ge:Genv.t F V) t r m r' m' args res,
                     Lprimitive_call ef _ _ ge args r m t res r' m' ->
                     (length t <= 1)%nat}.
      
      Context `{ hprimitive_call_receptive:
                   forall ef F V (ge: Genv.t F V) args rs m t1 res1 rs1 m1,
                     Hprimitive_call ef _ _ ge args rs m t1 res1 rs1 m1 ->
                     forall t2,
                       match_traces ge t1 t2 ->
                       exists res2, exists rs2, exists m2,
                                                  Hprimitive_call ef _ _ ge args rs m t2 res2 rs2 m2}.
      
      Context `{ lprimitive_call_determ: 
                   forall ef F V (ge:Genv.t F V)  r m t1 t2 r1 m1 r2 m2 args res1 res2,
                     Lprimitive_call ef _ _ ge args r m t1 res1 r1 m1 ->
                     Lprimitive_call ef _ _ ge args r m t2 res2 r2 m2 ->
                     match_traces ge t1 t2 /\ (t1 = t2 -> m1 = m2 /\ r1 = r2 /\ res1 = res2)}.

      Theorem backward_simulation:
        backward_simulation hsemantics lsemantics.
      Proof.
        apply forward_to_backward_simulation.
        apply forward_simulation.
        apply semantics_receptive; auto.
        apply semantics_determinate; auto.
      Qed.

    End INSTR.

  End LAYER_TMPLT.

End TEMPLATE.
