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
(*                   Proof of functional correctness                   *)
(*         for the C functions implemented in the PQueueIntro layer    *)
(*                                                                     *)
(*                        Xiongnan (Newman) Wu                         *)
(*                                                                     *)
(*                          Yale University                            *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import MemoryX.
Require Import EventsX.
Require Import Globalenvs.
Require Import Locations.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import PQueueIntro.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import LoopProof.
Require Import VCGen.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import QueueInitGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import TacticsForTesting.
Require Import CalRealProcModule.
Require Import AbstractDataType.
Require Import PQueueIntroCSource.


Module PQUEUEINTROCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.
    

    Section ENQUEUE.

      Let L: compatlayer (cdata RData) := set_prev ↦ gensem set_prev_spec
           ⊕ set_next ↦ gensem set_next_spec 
           ⊕ get_tail ↦ gensem get_tail_spec
           ⊕ set_head ↦ gensem set_head_spec
           ⊕ set_tail ↦ gensem set_tail_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section EnqueueBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_prev *)

        Variable bset_prev: block.

        Hypothesis hset_prev1 : Genv.find_symbol ge set_prev = Some bset_prev. 
        
        Hypothesis hset_prev2 : Genv.find_funct_ptr ge bset_prev = Some (External (EF_external set_prev (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).
        
        (** set_next *)

        Variable bset_next: block.

        Hypothesis hset_next1 : Genv.find_symbol ge set_next = Some bset_next. 
        
        Hypothesis hset_next2 : Genv.find_funct_ptr ge bset_next = Some (External (EF_external set_next (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** get_tail *)

        Variable bget_tail: block.

        Hypothesis hget_tail1 : Genv.find_symbol ge get_tail = Some bget_tail. 
        
        Hypothesis hget_tail2 : Genv.find_funct_ptr ge bget_tail = Some (External (EF_external get_tail (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** set_head *)

        Variable bset_head: block.

        Hypothesis hset_head1 : Genv.find_symbol ge set_head = Some bset_head. 
        
        Hypothesis hset_head2 : Genv.find_funct_ptr ge bset_head = Some (External (EF_external set_head (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** set_tail *)

        Variable bset_tail: block.

        Hypothesis hset_tail1 : Genv.find_symbol ge set_tail = Some bset_tail. 
        
        Hypothesis hset_tail2 : Genv.find_funct_ptr ge bset_tail = Some (External (EF_external set_tail (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Lemma enqueue_body_correct: forall m d d' env le chan_index proc_index,
                                      env = PTree.empty _ ->
                                      PTree.get tchan_index le = Some (Vint chan_index) ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get ttail le = Some Vundef ->
                                      enqueue_spec (Int.unsigned chan_index) (Int.unsigned proc_index) d = Some d' ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) enqueue_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold enqueue_body.
          functional inversion H3; rewrite <- H in *; functional inversion H8.

          Case "Int.unsigned tail = num_proc".
          esplit. 
          repeat vcgen.
          unfold get_tail_spec.
          rewrite H7, H6, H5, H4, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_next_spec; simpl.
          rewrite H7, H6, H5, H4. 
          rewrite zle_lt_true.
          rewrite ZMap.gss. 
          repeat zdestruct.
          omega.
          unfold set_head_spec; simpl.
          rewrite H7, H6, H5, H4, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          omega.
          unfold set_tail_spec; simpl.
          rewrite H7, H6, H5, H4.
          rewrite zle_le_true.
          rewrite ZMap.gss.
          repeat zdestruct.
          rewrite ZMap.set2.
          rewrite ZMap.set2.
          reflexivity.
          omega.

          Case "Int.unsigned tail <> 64".

          assert(tcase: Int.unsigned proc_index = t \/ Int.unsigned proc_index <> t) by omega.
          Caseeq tcase.
          intro tmp; rewrite tmp in *.

          SCase "Int.unsigned proc_index = t".
          esplit. 
          repeat vcgen.
          unfold get_tail_spec.
          rewrite H7, H6, H5, H4, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_prev_spec; simpl.
          unfold set_next_spec; simpl.
          rewrite H7, H6, H5, H4, H13.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          rewrite tmp.
          (* rewrite ZMap.gss. 
          rewrite ZMap.set2. *)
          repeat zdestruct.
          omega. omega.
          unfold set_prev_spec; simpl.
          rewrite H7, H6, H5, H4.
          rewrite zle_lt_true. rewrite zle_le_true.
          rewrite tmp. 
          rewrite ZMap.gss.
          repeat zdestruct.
          omega.
          omega.
          unfold set_next_spec; simpl.
          rewrite H7, H6, H5, H4.
          rewrite zle_lt_true.
          rewrite tmp.
          rewrite ZMap.gss.
          repeat zdestruct.
          omega.
          unfold set_tail_spec; simpl.
          rewrite H7, H6, H5, H4, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite ZMap.set2.
          rewrite tmp in *.
          unfold tcb'.
          rewrite ZMap.set2.
          rewrite H13 in H9.
          clear H H3.
          injection H9; intros; subst.
          rewrite ZMap.set2.
          reflexivity.
          omega.

          SCase "Int.unsigned proc_index <> t".
          intro.
          esplit. 
          repeat vcgen.
          unfold get_tail_spec.
          rewrite H4, H5, H6, H7, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_next_spec; simpl.
          rewrite H7, H6, H5, H4.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          rewrite H13.
          repeat zdestruct.
          omega.
          omega.
          unfold set_prev_spec; simpl.
          rewrite H7, H6, H5, H4.
          rewrite zle_lt_true.
          rewrite zle_le_true.                   
          rewrite ZMap.gso.
          rewrite H9.
          repeat zdestruct.
          assumption.
          omega.
          omega.
          unfold set_next_spec; simpl.
          rewrite H7, H6, H5, H4.
          rewrite zle_lt_true.
          rewrite ZMap.gss.
          repeat zdestruct.
          omega.
          unfold set_tail_spec; simpl.
          rewrite H7, H6, H5, H4, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite ZMap.set2.
          unfold tcb'.
          reflexivity.
          omega.
        Qed.

      End EnqueueBody.

      Theorem enqueue_code_correct:
        spec_le (enqueue ↦ enqueue_spec_low) (〚enqueue ↦ f_enqueue 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (enqueue_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_enqueue)
                                                               (Vint n::Vint i::nil)
                                                               (create_undef_temps (fn_temps f_enqueue)))) H0. 
      Qed.

    End ENQUEUE.


    Section DEQUEUE.

      Let L: compatlayer (cdata RData) := set_prev ↦ gensem set_prev_spec
           ⊕ get_head ↦ gensem get_head_spec
           ⊕ get_next ↦ gensem get_next_spec
           ⊕ set_head ↦ gensem set_head_spec
           ⊕ set_tail ↦ gensem set_tail_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section DequeueBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_prev *)

        Variable bset_prev: block.

        Hypothesis hset_prev1 : Genv.find_symbol ge set_prev = Some bset_prev. 
        
        Hypothesis hset_prev2 : Genv.find_funct_ptr ge bset_prev = Some (External (EF_external set_prev (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).
        
        (** get_head *)

        Variable bget_head: block.

        Hypothesis hget_head1 : Genv.find_symbol ge get_head = Some bget_head. 
        
        Hypothesis hget_head2 : Genv.find_funct_ptr ge bget_head = Some (External (EF_external get_head (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** get_next *)

        Variable bget_next: block.

        Hypothesis hget_next1 : Genv.find_symbol ge get_next = Some bget_next. 
        
        Hypothesis hget_next2 : Genv.find_funct_ptr ge bget_next = Some (External (EF_external get_next (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** set_head *)

        Variable bset_head: block.

        Hypothesis hset_head1 : Genv.find_symbol ge set_head = Some bset_head. 
        
        Hypothesis hset_head2 : Genv.find_funct_ptr ge bset_head = Some (External (EF_external set_head (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** set_tail *)

        Variable bset_tail: block.

        Hypothesis hset_tail1 : Genv.find_symbol ge set_tail = Some bset_tail. 
        
        Hypothesis hset_tail2 : Genv.find_funct_ptr ge bset_tail = Some (External (EF_external set_tail (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Lemma dequeue_body_correct: forall m d d' env le chan_index proc_index,
                                      env = PTree.empty _ ->
                                      PTree.get tchan_index le = Some (Vint chan_index) ->
                                      dequeue_spec (Int.unsigned chan_index) d = Some (d', (Int.unsigned proc_index)) ->
                                      high_level_invariant d ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) dequeue_body E0 le' (m, d') (Out_return (Some (Vint proc_index, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold dequeue_body.
          functional inversion H1; subst.

          Case "head = num_proc".
          (* destruct d *)
          destruct H2.
          simpl in *.
          esplit.
          repeat vcgen.
          unfold get_head_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          simpl.
          ptreesolve.
          rewrite H3.
          rewrite Int.repr_unsigned.
          reflexivity.

          Case "head <> num_proc & next = num_proc".
          esplit.
          repeat vcgen.
          unfold get_head_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold get_next_spec; simpl.
          rewrite H4, H5, H6, H7, H12.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_tail_spec; simpl.
          rewrite H4, H5, H6, H7.
          rewrite zle_le_true.
          rewrite ZMap.gss.
          rewrite ZMap.set2.
          repeat zdestruct.
          omega.
          repeat vcgen.

          Case "head <> num_proc & next <> num_proc".
          assert(nextrange: 0 <= next <= num_proc).
            destruct H2.
            generalize (valid_TCB H6); intro validTCB.
            unfold TCBCorrect_range in validTCB.
            unfold TCBCorrect in validTCB.
            assert(tmp: 0 <= Int.unsigned proc_index < num_proc) by omega.
            generalize (validTCB (Int.unsigned proc_index) tmp); clear validTCB; intro validTCB.
            destruct validTCB as [tmps validTCB].
            destruct validTCB as [tmpprev validTCB].
            destruct validTCB as [tmpnext validTCB].
            destruct validTCB as [? validTCB].
            destruct validTCB.
            rewrite H in H12.
            injection H12; intros; subst.
            omega.

          esplit.
          repeat vcgen.
          unfold get_head_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_le_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold get_next_spec; simpl.
          rewrite H4, H5, H6, H7, H12.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          rewrite zle_lt_true.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H14.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.
          unfold set_head_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_le_true.
          repeat zdestruct.
          omega.
          repeat vcgen.
        Qed.

      End DequeueBody.

      Theorem dequeue_code_correct:
        spec_le (dequeue ↦ dequeue_spec_low) (〚dequeue ↦ f_dequeue 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (dequeue_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_dequeue)
                                                               (Vint n::nil)
                                                               (create_undef_temps (fn_temps f_dequeue)))) H0. 
      Qed.

    End DEQUEUE.


    Section QUEUERMV.

      Let L: compatlayer (cdata RData) := set_prev ↦ gensem set_prev_spec
           ⊕ set_next ↦ gensem set_next_spec
           ⊕ get_prev ↦ gensem get_prev_spec
           ⊕ get_next ↦ gensem get_next_spec
           ⊕ set_head ↦ gensem set_head_spec
           ⊕ set_tail ↦ gensem set_tail_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section QueueRmvBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_prev *)

        Variable bset_prev: block.

        Hypothesis hset_prev1 : Genv.find_symbol ge set_prev = Some bset_prev. 
        
        Hypothesis hset_prev2 : Genv.find_funct_ptr ge bset_prev = Some (External (EF_external set_prev (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** set_next *)

        Variable bset_next: block.

        Hypothesis hset_next1 : Genv.find_symbol ge set_next = Some bset_next. 
        
        Hypothesis hset_next2 : Genv.find_funct_ptr ge bset_next = Some (External (EF_external set_next (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).
        
        (** get_prev *)

        Variable bget_prev: block.

        Hypothesis hget_prev1 : Genv.find_symbol ge get_prev = Some bget_prev. 
        
        Hypothesis hget_prev2 : Genv.find_funct_ptr ge bget_prev = Some (External (EF_external get_prev (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** get_next *)

        Variable bget_next: block.

        Hypothesis hget_next1 : Genv.find_symbol ge get_next = Some bget_next. 
        
        Hypothesis hget_next2 : Genv.find_funct_ptr ge bget_next = Some (External (EF_external get_next (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** set_head *)

        Variable bset_head: block.

        Hypothesis hset_head1 : Genv.find_symbol ge set_head = Some bset_head. 
        
        Hypothesis hset_head2 : Genv.find_funct_ptr ge bset_head = Some (External (EF_external set_head (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** set_tail *)

        Variable bset_tail: block.

        Hypothesis hset_tail1 : Genv.find_symbol ge set_tail = Some bset_tail. 
        
        Hypothesis hset_tail2 : Genv.find_funct_ptr ge bset_tail = Some (External (EF_external set_tail (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Lemma queue_rmv_body_correct: forall m d d' env le chan_index proc_index,
                                        env = PTree.empty _ ->
                                        high_level_invariant d ->
                                        PTree.get tchan_index le = Some (Vint chan_index) ->
                                        PTree.get tproc_index le = Some (Vint proc_index) ->
                                        queue_rmv_spec (Int.unsigned chan_index) (Int.unsigned proc_index) d = Some d' ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) queue_rmv_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold queue_rmv_body.
          functional inversion H3; functional inversion H8; subst.

          Case "prev = num_proc & next = num_proc".
          esplit.
          repeat vcgen.
          unfold get_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          unfold get_next_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_tail_spec; simpl.
          rewrite ZMap.gss.
          rewrite ZMap.set2.
          rewrite H4, H5, H6, H7.
          rewrite zle_le_true.
          repeat zdestruct.
          omega.

          Case "prev = num_proc & next <> num_proc".
          assert(nextrange: 0 <= next <= num_proc).
            destruct H0.
            generalize (valid_TCB H6); intro validTCB.
            unfold TCBCorrect_range in validTCB.
            unfold TCBCorrect in validTCB.
            assert(tmp: 0 <= Int.unsigned proc_index < num_proc) by omega.
            generalize (validTCB (Int.unsigned proc_index) tmp); clear validTCB; intro validTCB.
            destruct validTCB as [tmps validTCB].
            destruct validTCB as [tmpprev validTCB].
            destruct validTCB as [tmpnext validTCB].
            destruct validTCB as [? validTCB].
            destruct validTCB.
            rewrite H in H9.
            injection H9; intros; subst.
            omega.
          esplit.
          repeat vcgen.
          unfold get_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          unfold get_next_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          (* This is a new case *)
          unfold set_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H13.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.
          unfold set_head_spec; simpl.
          rewrite H4, H5, H6, H7, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          omega.

          Case "prev <> num_proc & next = num_proc".
          assert(nextrange: 0 <= prev <= num_proc).
            destruct H0.
            generalize (valid_TCB H6); intro validTCB.
            unfold TCBCorrect_range in validTCB.
            unfold TCBCorrect in validTCB.
            assert(tmp: 0 <= Int.unsigned proc_index < num_proc) by omega.
            generalize (validTCB (Int.unsigned proc_index) tmp); clear validTCB; intro validTCB.
            destruct validTCB as [tmps validTCB].
            destruct validTCB as [tmpprev validTCB].
            destruct validTCB as [tmpnext validTCB].
            destruct validTCB as [? validTCB].
            destruct validTCB.
            rewrite H in H9.
            injection H9; intros; subst.
            omega.
          esplit.
          repeat vcgen.
          unfold get_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          unfold get_next_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          (* This is a new case *)
          unfold set_next_spec; simpl.
          rewrite H4, H5, H6, H7, H12.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.
          unfold set_tail_spec; simpl.
          rewrite H4, H5, H6, H7, H10.
          rewrite zle_le_true.
          repeat zdestruct.
          omega.

          Case "prev <> num_proc & next <> num_proc".
          assert(prevrange: 0 <= prev <= num_proc).
            destruct H0.
            generalize (valid_TCB H6); intro validTCB.
            unfold TCBCorrect_range in validTCB.
            unfold TCBCorrect in validTCB.
            assert(tmp: 0 <= Int.unsigned proc_index < num_proc) by omega.
            generalize (validTCB (Int.unsigned proc_index) tmp); clear validTCB; intro validTCB.
            destruct validTCB as [tmps validTCB].
            destruct validTCB as [tmpprev validTCB].
            destruct validTCB as [tmpnext validTCB].
            destruct validTCB as [? validTCB].
            destruct validTCB.
            rewrite H in H9.
            injection H9; intros; subst.
            omega.
          assert(nextrange: 0 <= next <= num_proc).
            destruct H0.
            generalize (valid_TCB H6); intro validTCB.
            unfold TCBCorrect_range in validTCB.
            unfold TCBCorrect in validTCB.
            assert(tmp: 0 <= Int.unsigned proc_index < num_proc) by omega.
            generalize (validTCB (Int.unsigned proc_index) tmp); clear validTCB; intro validTCB.
            destruct validTCB as [tmps validTCB].
            destruct validTCB as [tmpprev validTCB].
            destruct validTCB as [tmpnext validTCB].
            destruct validTCB as [? validTCB].
            destruct validTCB.
            rewrite H in H9.
            injection H9; intros; subst.
            omega.

          assert(prevnext: prev = next \/ prev <> next) by omega.
          Caseeq prevnext.

          SCase "prev = next".
          intro.
          esplit.
          repeat vcgen.
          unfold get_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          unfold get_next_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H14.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          rewrite H.
          rewrite ZMap.set2.
          repeat zdestruct.
          omega.
          omega.

          SCase "prev <> next".
          intro.
          esplit.
          repeat vcgen.
          unfold get_prev_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          unfold get_next_spec; simpl.
          rewrite H4, H5, H6, H7, H9.
          rewrite zle_lt_true.
          repeat zdestruct.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          (* This is a new case *)
          unfold set_next_spec; simpl.
          rewrite H4, H5, H6, H7, H12.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          repeat zdestruct.
          omega.
          omega.
          unfold set_prev_spec; simpl.
          rewrite ZMap.gso.
          rewrite H4, H5, H6, H7, H14.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          repeat zdestruct.
          omega.
          omega.
          intro.
          rewrite H17 in H.
          generalize H; clear; congruence.
        Qed.

      End QueueRmvBody.

      Theorem queue_rmv_code_correct:
        spec_le (queue_rmv ↦ queue_rmv_spec_low) (〚queue_rmv ↦ f_queue_rmv 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (queue_rmv_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_queue_rmv)
                                                               (Vint n::Vint i::nil)
                                                               (create_undef_temps (fn_temps f_queue_rmv)))) H0. 
      Qed.

    End QUEUERMV.


    Section TDQUEUEINIT.

      Let L: compatlayer (cdata RData) := thread_init ↦ gensem thread_init_spec
           ⊕ tdq_init ↦ gensem tdq_init_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section TDQueueInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** tdq_init *)

        Variable btdq_init: block.

        Hypothesis htdq_init1 : Genv.find_symbol ge tdq_init = Some btdq_init. 
        
        Hypothesis htdq_init2 : Genv.find_funct_ptr ge btdq_init = Some (External (EF_external tdq_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** thread_init *)

        Variable bthread_init: block.

        Hypothesis hthread_init1 : Genv.find_symbol ge thread_init = Some bthread_init. 
        
        Hypothesis hthread_init2 : Genv.find_funct_ptr ge bthread_init = Some (External (EF_external thread_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (* Definition tdqueue_init_mk_rdata (adt: RData) (index: Z) := (mkRData (HP adt) (PQueueIntro.ti adt) (pg adt) (ikern adt) (ihost adt) (AT adt) (nps adt) (PT adt) (ptpool adt) (ipt adt) (kctxt adt) (tcb adt) (Calculate_tdq (Z.to_nat index) (tdq adt))). *)
 
        Definition tdqueue_init_mk_rdata (adt: RData) (index: Z) :=
          adt {tdq: (Calculate_tdq (Z.to_nat index) (tdq adt))}.

        Section tdqueue_init_loop_proof.

          Variable minit: memb.
          Variable adt: RData.

          Hypothesis pg: pg adt = true.
          Hypothesis ipt: ipt adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis ikern: ikern adt = true.

          Definition tdqueue_init_loop_body_P (le: temp_env) (m: mem): Prop :=
            PTree.get ti le = Some (Vint (Int.repr 0)) /\ 
            m = (minit, adt).
 
          Definition tdqueue_init_loop_body_Q (le : temp_env) (m: mem): Prop :=
            m = (minit, tdqueue_init_mk_rdata adt num_chan). 

          Lemma tdqueue_init_loop_correct_aux : LoopProofSimpleWhile.t tdqueue_init_while_condition tdqueue_init_while_body ge (PTree.empty _) (tdqueue_init_loop_body_P) (tdqueue_init_loop_body_Q).
          Proof.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get ti le = Some (Vint i) /\
                                    0 <= Int.unsigned i <= num_chan + 1 /\ 
                                    (Int.unsigned i = 0 /\ m = (minit, adt) \/ Int.unsigned i > 0 /\ m = (minit, tdqueue_init_mk_rdata adt (Int.unsigned i - 1))) /\
                                    w = num_chan + 1 - Int.unsigned i 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold tdqueue_init_loop_body_P in H.
            destruct H as [tile msubst].
            subst.
            esplit. esplit.
            repeat vcgen.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [icase nval].
            subst.
            unfold tdqueue_init_while_body.
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.
            destruct m.

            Caseeq ihigh.
            Case "Int.unsigned i < num_chan + 1".
            intro ihigh.

            Caseeq icase.
            SCase "Int.unsigned i = 0".
            intro tmpH; destruct tmpH as [ival mval].
            rewrite ival in *.
            injection mval; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            exists (num_chan + 1 - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            f_equal.
            unfold tdqueue_init_mk_rdata.
            rewrite ival.
            reflexivity.

            SCase "Int.unsigned i > 0".
            intro tmpH; destruct tmpH as [ival mval].
            injection mval; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold tdqueue_init_mk_rdata; simpl.
            unfold tdq_init_spec; simpl.
            rewrite ikern, ihost, pg, ipt.
            rewrite zle_le_true.
            repeat zdestruct.
            reflexivity.
            omega.
            exists (num_chan + 1 - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            f_equal.
            unfold tdqueue_init_mk_rdata.
            replace (Int.unsigned i + 1 - 1) with (Int.unsigned i - 1 + 1) by omega.
            change (Int.unsigned i - 1 + 1) with (Z.succ (Int.unsigned i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(Int.unsigned i - 1)).
            Opaque Z.of_nat.
            simpl.
            rewrite Nat2Z.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            replace (Int.unsigned i - 1 + 1) with (Int.unsigned i) by omega.
            reflexivity.
            omega.
            omega.

            Case "Int.unsigned i = num_chan + 1".
            intro ival.
            rewrite ival.
            esplit. esplit.
            repeat vcgen.
            unfold tdqueue_init_loop_body_Q.
            Caseeq icase; intro tmpH; destruct tmpH as [iv mval].
            exfalso; rewrite iv in ival; omega.
            rewrite ival in mval; assumption.
          Qed.

        End tdqueue_init_loop_proof.

        Lemma tdqueue_init_loop_correct: forall m d d' le,
                                           PTree.get ti le = Some (Vint (Int.repr 0)) -> 
                                           pg d = true ->
                                           ipt d = true ->
                                           ihost d = true ->
                                           ikern d = true ->
                                           d' = tdqueue_init_mk_rdata d num_chan ->
                                           exists le',
                                             exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile tdqueue_init_while_condition tdqueue_init_while_body) E0 le' (m, d') Out_normal.
        Proof.
          intros.
          generalize (tdqueue_init_loop_correct_aux m d H0 H1 H2 H3).
          unfold tdqueue_init_loop_body_P.
          unfold tdqueue_init_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le'' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp m''val].
          exists le''.
          subst.
          assumption.
          auto.
        Qed.

        Lemma tdqueue_init_body_correct: forall m d d' env le mbi_adr,
                                           env = PTree.empty _ ->
                                           PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                           PTree.get ti le = Some Vundef ->
                                           tdqueue_init_spec (Int.unsigned mbi_adr) d = Some d' ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) tdqueue_init_body E0 le' (m, d') Out_normal.
        Proof.
          intros.
          subst.
          unfold tdqueue_init_body.
          functional inversion H2.
          functional inversion H3.
          subst.
          simpl in *.
          

          set (di:= d {vmxinfo: real_vmxinfo} {pg : true} {LAT : real_LAT (LAT d)} {nps : real_nps}
                      {AC: real_AC} {init : true} {PT : 0} {ptpool : CalRealPT.real_pt (ptpool d)}
                      {idpde : CalRealIDPDE.real_idpde (idpde d)}
                      {smspool: CalRealSMSPool.real_smspool (smspool d)} 
                      {tcb : real_tcb (tcb d)}).

          set (df:= d {vmxinfo: real_vmxinfo} {pg : true} {LAT : real_LAT (LAT d)} {nps : real_nps}
                      {AC: real_AC} {init : true} {PT : 0} {ptpool : CalRealPT.real_pt (ptpool d)}
                      {idpde : CalRealIDPDE.real_idpde (idpde d)}
                      {smspool: CalRealSMSPool.real_smspool (smspool d)}
                      {tcb : real_tcb (tcb d)} {tdq : real_tdq (tdq d)}).

          exploit (tdqueue_init_loop_correct m di df (PTree.set ti (Vint (Int.repr 0)) (set_opttemp None Vundef le))); unfold di in *; simpl in *; try assumption. 
          repeat vcgen.
          reflexivity.
          unfold tdqueue_init_mk_rdata. 
          reflexivity.

          intro tempH.
          destruct tempH as [le' stmt].
          unfold df in *.
          esplit.
          repeat vcgen.
      Qed.

      End TDQueueInitBody.

      Theorem tdqueue_init_code_correct:
        spec_le (tdqueue_init ↦ tdqueue_init_spec_low) (〚tdqueue_init ↦ f_tdqueue_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (tdqueue_init_body_correct s (Genv.globalenv p) makeglobalenv b1 Hb1fs Hb1fp b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_tdqueue_init)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_tdqueue_init)))) H0. 
      Qed.

    End TDQUEUEINIT.

  End WithPrimitives.

End PQUEUEINTROCODE.
