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
(*           Layers of PM: Assembly Verification for Thread            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Locations.
Require Import AuxStateDataType.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import FlatMemory.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import Constant.
Require Import AsmImplLemma.
Require Import AsmImplTactic.
Require Import GlobIdent.
Require Import CommonTactic.

Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compcertx.MakeProgram.
Require Import LAsmModuleSem.
Require Import LAsm.
Require Import liblayers.compat.CompatGenSem.
Require Import PrimSemantics.
Require Import Conventions.

Require Import PThreadSched.
Require Import ThreadGenAsmSource.
Require Import AbstractDataType.

Section ASM_DATA.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.
  Notation LDATAOps := (cdata (cdata_ops := pthreadsched_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Section ThreadSleep.

      Lemma Hneq:
        forall n v v',
          v' <= n < v ->
          v <> n.
      Proof.
        intros. omega.
      Qed.

      Lemma threadsleep_generate:
        forall r' (m0: mem) labd labd' r'0 n,
          thread_sleep_spec labd ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                                     # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                                     (r' EBP) # RA <- (r' RA)) (Int.unsigned n) = Some (labd', r'0)
          -> low_level_invariant (Mem.nextblock m0) labd
          -> high_level_invariant labd
          -> exists labd0 labd1,
               get_curid_spec labd = Some (cid labd)
               /\ set_state1_spec (cid labd) (Int.unsigned (Int.repr 2)) labd = Some labd0
               /\ enqueue0_spec (Int.unsigned n) 
                               (cid labd) labd0 = Some labd1
               /\ thread_sched_spec labd1 ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                                 # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                                 (r' EBP) # RA <- (r' RA)) = Some (labd', r'0)
               /\ (forall v r, ZtoPreg v = Some r -> Val.has_type (r'0 r) Tint)
               /\ (forall v r, ZtoPreg v = Some r -> val_inject (Mem.flat_inj (Mem.nextblock m0)) (r'0 r) (r'0 r))
               /\ ikern labd = true
               /\ ihost labd = true
               /\ ikern labd0 = true
               /\ ihost labd0 = true
               /\ ikern labd1 = true
               /\ ihost labd1 = true
               /\ 0<= (cid labd) < num_proc.
      Proof.
        intros. inv H0.
        assert (HOS': 0 <= 64 <= Int.max_unsigned) by
            (rewrite int_max; omega).
        rename H1 into Hhigh.
        assert (HIK: ikern labd = true/\
                     ihost labd = true /\
                     ipt labd = true/\
                     pg labd = true).
        {
          specialize (valid_iptt _ Hhigh). intros HR.
          functional inversion H. rewrite HR; auto.
        }
        unfold thread_sleep_spec in *.
        destruct HIK as [HIK1 [HIH1 [HIPT1 HPE1]]].        
        specialize (correct_curid labd Hhigh). intros Hused.
        specialize (valid_TDQ labd Hhigh). intros HTrange.          
        specialize (valid_inQ labd Hhigh). intros HinQ.
        specialize (valid_notinQ labd Hhigh). intros HnotinQ.
        rewrite HIK1, HIH1, HIPT1, HPE1 in *.
        specialize (Hused refl_equal).
        specialize (HTrange refl_equal).
        specialize (HinQ refl_equal).
        specialize (HnotinQ refl_equal).
        specialize (valid_curid labd Hhigh). intros HCID_range. 
        assert (HEX1: get_curid_spec labd = Some (cid labd)).
        {
          unfold get_curid_spec in *.
          rewrite HIK1, HPE1, HIH1. trivial.
        }
        destruct (zle_lt 0 (Int.unsigned n) 64); contra_inv.
        assert (HRDQ: exists rdq, ZMap.get num_chan (abq labd) = AbQValid rdq).
        {
          destruct (ZMap.get 64 (abq labd)); contra_inv. eauto 2.
        }
        destruct HRDQ as [rdq HRDQ].
        rewrite HRDQ in H.          
        assert (HSLPQ: exists slq, ZMap.get (Int.unsigned n) (abq labd) = AbQValid slq).
        {
          destruct (ZMap.get (Int.unsigned n) (abq labd)); contra_inv. eauto 2.
        }
        destruct HSLPQ as [slq HSLPQ].
        rewrite HSLPQ in H.          
        assert (HRUN: ZMap.get (cid labd)
                               (abtcb labd) = (AbTCBValid RUN (-1))).
        {
          subdestruct. trivial.
        }
        rewrite HRUN in H.
        subdestruct.
        assert(HIn: In (last rdq num_proc) rdq).
        {
          apply last_correct; auto.
        }
        assert (HOS: 0<= num_proc <= num_proc) by omega.
        assert (Hrange: 0<= (last rdq num_proc) < num_proc).
        {
          unfold AbQCorrect in *.
          destruct (HTrange _ HOS) as [lt[HM HP]].
          rewrite HRDQ in HM. inv HM.
          apply HP; trivial.
        }
        specialize (HinQ _ _ _ Hrange HOS HRDQ HIn).
        destruct HinQ as [s2 HinQ].
        assert (Hlast_used: cused (ZMap.get (last rdq num_chan) (AC labd)) = true).
        {
          specialize (HnotinQ _ s2 64 Hrange).
          destruct (cused (ZMap.get (last rdq 64) (AC labd))); trivial.
          specialize (HnotinQ refl_equal HinQ). inv HnotinQ.
        }
        clear HnotinQ.
        assert(HNL: (cid labd <> (last rdq num_proc))).
        {
          red; intros.
          rewrite H0 in HRUN.
          rewrite HinQ in HRUN. inv HRUN. 
        }
        esplit; esplit.
        unfold get_curid_spec, set_state1_spec.
        subrewrite'.
        split; trivial.
        rewrite zle_lt_true; [|omega].
        change (Int.unsigned (Int.repr 2)) with 2; simpl.
        destruct (ThreadState_dec SLEEP RUN); try discriminate.
        split; trivial.
        unfold enqueue0_spec; simpl.
        subrewrite'.
        unfold Queue_arg. simpl.
        rewrite zle_lt_true; [|omega].
        rewrite zle_le_true; [|omega].
        rewrite ZMap.gss.
        rewrite zeq_true; trivial.
        rewrite ZMap.set2.
        split; trivial.
        unfold thread_sched_spec; simpl.
        subrewrite'.
        rewrite ZMap.gss.
        rewrite ZMap.gso.
        rewrite HRDQ.
        rewrite zeq_false; trivial. 
        rewrite Hlast_used.
        rewrite ZMap.gso; auto.
        rewrite HinQ.
        destruct (ThreadState_dec SLEEP RUN); try discriminate.
        rewrite zeq_false; auto.
        inv H. split; trivial. 
        repeat (split; trivial); try eapply kctxt_INJECT; trivial. 
        eapply Hneq; eassumption.
      Qed.

    End ThreadSleep.

    Section ThreadYield.

      Lemma threadyield_generate:
        forall r' (m0: mem) labd labd' r'0,
          thread_yield_spec labd ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                        # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                        (r' EBP) # RA <- (r' RA)) = Some (labd', r'0)
          -> low_level_invariant (Mem.nextblock m0) labd
          -> high_level_invariant labd
          -> exists labd0 labd1,
               get_curid_spec labd = Some (cid labd)
               /\ set_state1_spec (cid labd) (Int.unsigned (Int.repr 0)) labd = Some labd0
               /\ enqueue0_spec (Int.unsigned (Int.repr num_chan)) 
                                (cid labd) labd0 = Some labd1
               /\ thread_sched_spec labd1 ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                                              # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                                              (r' EBP) # RA <- (r' RA)) = Some (labd', r'0)
               /\ (forall v r, ZtoPreg v = Some r -> Val.has_type (r'0 r) Tint)
               /\ (forall v r, ZtoPreg v = Some r -> val_inject (Mem.flat_inj (Mem.nextblock m0)) (r'0 r) (r'0 r))
               /\ ikern labd = true
               /\ ihost labd = true
               /\ ikern labd0 = true
               /\ ihost labd0 = true
               /\ ikern labd1 = true
               /\ ihost labd1 = true
               /\ 0<= (cid labd) < num_proc.
      Proof.
        intros. inv H0.
        assert (HOS': 0 <= 64 <= Int.max_unsigned)
          by (rewrite int_max; omega).
        rename H1 into Hhigh.
        assert (HIK: ikern labd = true/\
                     ihost labd = true /\
                     ipt labd = true/\
                     pg labd = true).
        {
          specialize (valid_iptt labd Hhigh). intros HR.
          functional inversion H. rewrite HR; auto.
        }
        unfold thread_yield_spec in *.
        destruct HIK as [HIK1 [HIH1 [HIPT1 HPE1]]].        
        specialize (correct_curid labd Hhigh). intros Hused.
        specialize (valid_TDQ labd Hhigh). intros HTrange.          
        specialize (valid_inQ labd Hhigh). intros HinQ.
        specialize (valid_notinQ labd Hhigh). intros HnotinQ.
        rewrite HIK1, HIH1, HIPT1, HPE1 in *.
        specialize (Hused refl_equal).
        specialize (HTrange refl_equal).
        specialize (HinQ refl_equal).
        specialize (HnotinQ refl_equal).
        specialize (valid_curid labd Hhigh).
        intros HCID_range.
        assert (HEX1: get_curid_spec labd = Some (cid labd)).
        {
          unfold get_curid_spec in *.
          rewrite HIK1, HPE1, HIH1. trivial.
        }          
        assert (HRUN: ZMap.get (cid labd) (abtcb labd) = (AbTCBValid RUN (-1))).
        {
          subdestruct; trivial.
        }
        rewrite HRUN in H.
        assert (HRDQ: exists rdq, ZMap.get num_chan (abq labd) = AbQValid rdq).
        {
          subdestruct; eauto.
        }
        destruct HRDQ as [rdq HRDQ].
        rewrite HRDQ in H.          
        Opaque remove.
        subdestruct.
        assert(HIn: In (last rdq num_proc) rdq).
        {
          apply last_correct; auto.
        } 
        assert (HOS: 0<= num_proc <= num_proc) by omega.
        assert (Hrange: 0<= (last rdq num_proc) < num_proc).
        {
          unfold AbQCorrect in *.
          destruct (HTrange _ HOS) as [lt[HM HP]].
          rewrite HRDQ in HM. inv HM.
          apply HP; trivial.
        } 
        specialize (HinQ _ _ _ Hrange HOS HRDQ HIn).
        destruct HinQ as [s2 HinQ].
        assert (Hlast_used: cused (ZMap.get (last rdq num_chan) (AC labd)) = true).
        {
          specialize (HnotinQ _ s2 64 Hrange).
          destruct (cused (ZMap.get (last rdq 64) (AC labd))); trivial.
          specialize (HnotinQ refl_equal HinQ).
          inv HnotinQ.
        }
        clear HnotinQ.
        assert(HNL: (cid labd <> (last rdq num_proc))).
        {
          red; intros.
          rewrite H0 in HRUN.
          rewrite HinQ in HRUN. inv HRUN. 
        }
        esplit; esplit.
        unfold get_curid_spec, set_state1_spec.
        subrewrite'.
        split; trivial.
        rewrite zle_lt_true; [|omega].
        change (Int.unsigned (Int.repr 0)) with 0; simpl.
        destruct (ThreadState_dec READY RUN); try discriminate.
        split; trivial.
        unfold enqueue0_spec; simpl.
        subrewrite'.
        unfold Queue_arg. simpl.
        change (Int.unsigned (Int.repr 64)) with 64.
        rewrite zle_le_true; [|omega].
        rewrite zle_lt_true; [|omega].
        rewrite HRDQ.
        rewrite ZMap.gss.
        rewrite zeq_true; trivial.
        rewrite ZMap.set2.
        split; trivial.
        unfold thread_sched_spec; simpl.
        subrewrite'.
        rewrite ZMap.gss.
        assert (HEQ: (last (cid labd :: rdq) 64) = last rdq 64).
        {
          destruct rdq.
          assert (HNE: 64 <> last nil 64) by auto.
          inv HIn. trivial.
        }
        rewrite HEQ.
        rewrite zeq_false; trivial. 
        rewrite Hlast_used.
        rewrite ZMap.gso; auto.
        rewrite HinQ.
        rewrite ZMap.gss.
        destruct (ThreadState_dec READY RUN); try discriminate.
        rewrite zeq_false; auto.
        rewrite ZMap.set2. 
        inv H. simpl; split; trivial. 
        repeat (split; trivial); eapply kctxt_INJECT; trivial.
      Qed.

    End ThreadYield.

    Lemma Hget_curid: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm pthreadsched = ret ge ->
        (exists b_get_curid, Genv.find_symbol ge get_curid = Some b_get_curid
                             /\ Genv.find_funct_ptr ge b_get_curid = 
                                Some (External (EF_external get_curid get_curid_sig)))
        /\ get_layer_primitive get_curid pthreadsched = OK (Some (gensem get_curid_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive get_curid pthreadsched = OK (Some (gensem get_curid_spec)))
        by (unfold pthreadsched; reflexivity).
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Hset_state: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm pthreadsched = ret ge ->
        (exists b_set_state, Genv.find_symbol ge set_state = Some b_set_state
                             /\ Genv.find_funct_ptr ge b_set_state = 
                                Some (External (EF_external set_state set_state_sig)))
        /\ get_layer_primitive set_state pthreadsched = OK (Some (gensem set_state1_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive set_state pthreadsched = OK (Some (gensem set_state1_spec)))
        by (unfold pthreadsched; reflexivity).
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Henqueue: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm pthreadsched = ret ge ->
        (exists b_enqueue, Genv.find_symbol ge enqueue = Some b_enqueue
                           /\ Genv.find_funct_ptr ge b_enqueue = 
                              Some (External (EF_external enqueue enqueue_sig)))
        /\ get_layer_primitive enqueue pthreadsched = OK (Some (gensem enqueue0_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive enqueue pthreadsched = OK (Some (gensem enqueue0_spec)))
        by (unfold pthreadsched; reflexivity).
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.
    
    Lemma Hthread_sched: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm pthreadsched = ret ge ->
        (exists b_thread_sched, Genv.find_symbol ge thread_sched = Some b_thread_sched
                                /\ Genv.find_funct_ptr ge b_thread_sched = 
                                   Some (External (EF_external thread_sched null_signature)))
        /\ get_layer_primitive thread_sched pthreadsched = OK (Some (primcall_thread_schedule_compatsem 
                                                                       thread_sched_spec
                                                                       (prim_ident:= thread_sched))).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive thread_sched pthreadsched = OK (Some (primcall_thread_schedule_compatsem 
                                                                                 thread_sched_spec
                                                                                 (prim_ident:= thread_sched))))
        by (unfold pthreadsched; reflexivity).
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Hthread_yield:
      forall ge s b,
        make_globalenv s (thread_yield ↦ threadyield_function) pthreadsched = ret ge ->
        find_symbol s thread_yield = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal threadyield_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function thread_yield (thread_yield ↦ threadyield_function)
                       = OK (Some threadyield_function)) by
          reflexivity.
      assert (HInternal: make_internal threadyield_function = OK (AST.Internal threadyield_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    Lemma Hthread_sleep:
      forall ge s b,
        make_globalenv s (thread_sleep ↦ threadsleep_function) pthreadsched = ret ge ->
        find_symbol s thread_sleep = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal threadsleep_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function thread_sleep (thread_sleep ↦ threadsleep_function) = OK (Some threadsleep_function)) by
          reflexivity.
      assert (HInternal: make_internal threadsleep_function = OK (AST.Internal threadsleep_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

  End WITHMEM.

End ASM_DATA.