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
(*           Layers of PM: Assembly Verification for ThreadSched       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
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

Require Import PCurID.
Require Import ThreadSchedGenAsmSource.
Require Import AbstractDataType.

Section ASM_DATA.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

    (*	
	.globl thread_sched
thread_sched:

        movr    num_chan, %eax
        movl    %eax, (%esp) // arguments for dequeue (num_chan)
        call    dequeue

        movl    %eax, 0(%esp) // return vaule :last l, also the arguments
        movr    1, %eax
        movl    %eax, 4(%esp) // arguements for set_state (last l, 1)
        call    set_state

        call    get_curid   
        movl    %eax, 4(%esp) // save cid

        call    set_curid // argument is already there, set_curid (last l)

        call    clear_cr2 // clear part of the trapinfo for security reasons
        
        movl    0(%esp), %edx
        movl    4(%esp), %eax
        jmp kctxt_switch

     *)

    Notation LDATA := RData.
    Notation LDATAOps := (cdata (cdata_ops := pcurid_data_ops) LDATA).

    Section WITHMEM.

      Context `{Hstencil: Stencil}.
      Context `{Hmem: Mem.MemoryModel}.
      Context `{Hmwd: UseMemWithData mem}.
      Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
      Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

      Section GENERATE.

        Lemma threadsched_generate:
          forall r' (m0: mem) labd labd' r'0,
            thread_sched_spec labd ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                                          # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                                          (r' EBP) # RA <- (r' RA)) = Some (labd', r'0)
            -> low_level_invariant (Mem.nextblock m0) labd
            -> high_level_invariant labd
            -> exists labd0 labd1 labd2 labd3 la,
                 dequeue0_spec (Int.unsigned (Int.repr 64)) labd  = Some (labd0, Int.unsigned la)
                 /\ set_state0_spec (Int.unsigned la) (Int.unsigned Int.one) labd0 = Some labd1
                 /\ get_curid_spec labd1 = Some (cid labd1)
                 /\ set_curid_spec (Int.unsigned la) labd1 = Some labd2
                 /\ clearCR2_spec labd2 = Some labd3
                 /\ kctxt_switch_spec 
                      labd3 (cid labd1) (Int.unsigned la)
                      ((Pregmap.init Vundef) # ESP <- (r' ESP) # EDI <- (r' EDI)
                                             # ESI <- (r' ESI) # EBX <- (r' EBX) # EBP <- 
                                             (r' EBP) # RA <- (r' RA)) = Some (labd', r'0)
                 /\ (forall v r, ZtoPreg v = Some r -> Val.has_type (r'0 r) Tint)
                 /\ (forall v r, ZtoPreg v = Some r -> val_inject (Mem.flat_inj (Mem.nextblock m0)) 
                                                                  (r'0 r) (r'0 r))
                 /\ ikern labd = true
                 /\ ihost labd = true
                 /\ ikern labd0 = true
                 /\ ihost labd0 = true
                 /\ ikern labd1 = true
                 /\ ihost labd1 = true
                 /\ ikern labd2 = true
                 /\ ihost labd2 = true
                 /\ ikern labd3 = true
                 /\ ihost labd3 = true
                 /\ 0<= (cid labd1) < num_proc.
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
            functional inversion H. auto.
          }
          destruct HIK as [HIK1 [HIH1 [HIPT1 HPE1]]].        
          unfold thread_sched_spec in *. 
          unfold dequeue0_spec.
          specialize (valid_TDQ _ Hhigh); intros HIP.
          specialize (valid_curid _ Hhigh). intros HCID_range.
          rewrite HIH1, HIPT1, HPE1, HIK1 in *.
          change (Int.unsigned (Int.repr 64)) with 64. simpl.
          assert (HOS: 0<= num_chan <= num_chan) by omega.
          specialize (HIP refl_equal _ HOS).
          subdestruct.
          assert (Hrange: 0<= (last l num_proc) < num_proc).
          {
            unfold AbQCorrect in *. destruct HIP as [l0[HM HP]].
            inv HM. apply HP. apply last_correct; auto.
          }
          replace (last l 64) with (Int.unsigned(Int.repr (last l 64)))
            by (rewrite Int.unsigned_repr; omega).
          esplit; esplit; esplit; esplit; esplit.
          split; trivial.
          replace (Int.unsigned(Int.repr (last l 64))) with (last l 64)
            by (rewrite Int.unsigned_repr; omega).
          unfold set_state0_spec; simpl.
          subrewrite'.
          rewrite zle_lt_true; [|omega].
          rewrite ZMap.gss.
          change (Int.unsigned Int.one) with 1. simpl.
          split; trivial; simpl.
          unfold get_curid_spec, set_curid_spec, clearCR2_spec; simpl.
          subrewrite'. split; trivial.
          rewrite zle_lt_true; [|omega].
          split; trivial.
          unfold kctxt_switch_spec; simpl.
          subrewrite'.
          rewrite zle_lt_true; [|omega].
          rewrite zle_lt_true; [|omega].
          inv H. rewrite ZMap.set2.
          split; [trivial | simpl; subrewrite'].
          repeat (split; trivial); try eapply kctxt_INJECT; eauto.
        Qed.

      End GENERATE.

      Lemma Hdequeue: 
        forall s ge,
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          (exists b_dequeue, Genv.find_symbol ge dequeue = Some b_dequeue
                             /\ Genv.find_funct_ptr ge b_dequeue = 
                                Some (External (EF_external dequeue dequeue_sig)))
          /\ get_layer_primitive dequeue pcurid = OK (Some (gensem dequeue0_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive dequeue pcurid = OK (Some (gensem dequeue0_spec)))
               by (unfold pcurid; reflexivity).
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hget_curid: 
        forall s ge,
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          (exists b_get_curid, Genv.find_symbol ge get_curid = Some b_get_curid
                             /\ Genv.find_funct_ptr ge b_get_curid = 
                                Some (External (EF_external get_curid get_curid_sig)))
          /\get_layer_primitive get_curid pcurid = OK (Some (gensem get_curid_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive get_curid pcurid = OK (Some (gensem get_curid_spec)))
               by (unfold pcurid; reflexivity).
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hset_curid: 
        forall s ge,
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          (exists b_set_curid, Genv.find_symbol ge set_curid = Some b_set_curid
                             /\ Genv.find_funct_ptr ge b_set_curid = 
                                Some (External (EF_external set_curid set_curid_sig)))
          /\get_layer_primitive set_curid pcurid = OK (Some (gensem set_curid_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive set_curid pcurid = OK (Some (gensem set_curid_spec)))
               by (unfold pcurid; reflexivity).
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hset_state: 
        forall s ge,
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          (exists b_set_state, Genv.find_symbol ge set_state = Some b_set_state
                             /\ Genv.find_funct_ptr ge b_set_state = 
                                Some (External (EF_external set_state set_state_sig)))
          /\get_layer_primitive set_state pcurid = OK (Some (gensem set_state0_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive set_state pcurid = OK (Some (gensem set_state0_spec)))
               by (unfold pcurid; reflexivity).
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hclear_cr2: 
        forall s ge,
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          (exists b_clear_cr2, Genv.find_symbol ge clear_cr2 = Some b_clear_cr2
                             /\ Genv.find_funct_ptr ge b_clear_cr2 = 
                                Some (External (EF_external clear_cr2 clear_cr2_sig)))
          /\get_layer_primitive clear_cr2 pcurid = OK (Some (gensem clearCR2_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive clear_cr2 pcurid = OK (Some (gensem clearCR2_spec)))
               by (unfold pcurid; reflexivity).
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.
      
      Lemma Hkctxt_switch: 
        forall s ge,
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          (exists b_kctxt_switch, Genv.find_symbol ge kctxt_switch = Some b_kctxt_switch
                             /\ Genv.find_funct_ptr ge b_kctxt_switch = 
                                Some (External (EF_external kctxt_switch null_signature)))
          /\get_layer_primitive kctxt_switch pcurid = OK (Some (primcall_kctxt_switch_compatsem kctxt_switch_spec)).
      Proof.
        intros.
        assert (Hprim: get_layer_primitive kctxt_switch pcurid = OK (Some (primcall_kctxt_switch_compatsem kctxt_switch_spec)))
               by (unfold pcurid; reflexivity).
        split; try assumption.
        eapply make_globalenv_get_layer_primitive; eauto.
      Qed.

      Lemma Hthread_sched:
        forall ge s b,
          make_globalenv s (thread_sched ↦ threadsched_function) pcurid = ret ge ->
          find_symbol s thread_sched = Some b ->
          stencil_matches s ge ->
          Genv.find_funct_ptr ge b = Some (Internal threadsched_function).
      Proof.
        intros.
        assert (Hmodule: get_module_function thread_sched (thread_sched ↦ threadsched_function) = OK (Some threadsched_function))
          by apply get_module_function_mapsto.        
        assert (HInternal: make_internal threadsched_function = OK (AST.Internal threadsched_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H; eauto.
        destruct H as [?[Hsymbol ?]].
        inv H1.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H0 in Hsymbol. inv Hsymbol.
        assumption.
      Qed.

    End WITHMEM.

End ASM_DATA.