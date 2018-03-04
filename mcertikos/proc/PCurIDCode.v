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
(*         for the C functions implemented in the PCurID layer         *)
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
Require Import PCurID.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import VCGen.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import ThreadSchedGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import TacticsForTesting.
Require Import CalRealProcModule.
Require Import PCurIDCSource.
Require Import AbstractDataType.
Require Import CommonTactic.


Module PCURIDCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.

    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.


    Section THREADSPAWN.

      Let L: compatlayer (cdata RData) := kctxt_new ↦ dnew_compatsem kctxt_new_spec
           ⊕ set_state ↦ gensem set_state0_spec
           ⊕ enqueue ↦ gensem enqueue0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ThreadSpawnBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** parameters *)
        Variables (id quota : int).

        (** kctxt_new *)

        Variable bkctxt_new: block.

        Hypothesis hkctxt_new1 : Genv.find_symbol ge kctxt_new = Some bkctxt_new. 
        
        Hypothesis hkctxt_new2 : 
          Genv.find_funct_ptr ge bkctxt_new = 
          Some (External (EF_external kctxt_new (signature_of_type 
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil))) tint cc_default)) 
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil))) tint cc_default).

        (** set_state *)

        Variable bset_state: block.

        Hypothesis hset_state1 : Genv.find_symbol ge set_state = Some bset_state. 
        
        Hypothesis hset_state2 : Genv.find_funct_ptr ge bset_state = Some (External (EF_external set_state (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** enqueue *)

        Variable benqueue: block.

        Hypothesis henqueue1 : Genv.find_symbol ge enqueue = Some benqueue. 
        
        Hypothesis henqueue2 : 
          Genv.find_funct_ptr ge benqueue = 
          Some (External (EF_external enqueue (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) 
                                              (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).


        Lemma thread_spawn_body_correct: 
          forall m d d' env le b bstack_loc i ofs',
            env = PTree.empty _ -> le ! tentry = Some (Vptr b ofs') -> 
            le ! tid = Some (Vint id) -> le ! tquota = Some (Vint quota) ->
            thread_spawn_spec d bstack_loc b ofs' (Int.unsigned id) (Int.unsigned quota) = Some (d', i) ->
            Genv.find_symbol ge STACK_LOC = Some bstack_loc ->
            (exists fun_id : ident, Genv.find_symbol ge fun_id = Some b) ->
            high_level_invariant d ->
            exists le',
              exec_stmt ge env le ((m, d): mem) thread_spawn_body E0 le' (m, d') 
                        (Out_return (Some (Vint (Int.repr i), tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold thread_spawn_body.
          rename H3 into Hspec.
          unfold thread_spawn_spec in Hspec.          
          case_eq (ikern d); intro ikern; rewrite ikern in Hspec; try discriminate Hspec.
          case_eq (ihost d); intro ihost; rewrite ihost in Hspec; try discriminate Hspec.
          case_eq (pg d); intro pe; rewrite pe in Hspec; try discriminate Hspec.
          case_eq (ipt d); intro ipt; rewrite ipt in Hspec; try discriminate Hspec.
          destruct (cused (ZMap.get (Int.unsigned id) (AC d))) eqn:Hused; try discriminate Hspec.
          destruct (zle_lt 0 (Int.unsigned id * max_children + 1 + 
                              Z.of_nat (length (cchildren (ZMap.get (Int.unsigned id) (AC d)))))
                           num_id) eqn:Hchild; try discriminate Hspec.
          destruct (zlt (Z.of_nat (length (cchildren (ZMap.get (Int.unsigned id) (AC d))))) max_children)
                   eqn:Hnc; try discriminate Hspec.
          destruct (zle_le 0 (Int.unsigned quota)
                           (cquota (ZMap.get (Int.unsigned id) (AC d)) -
                            cusage (ZMap.get (Int.unsigned id) (AC d)))) eqn:Hquota; try discriminate Hspec.
          case_eq (ZMap.get num_id (abq d)); [intro abq | intros ? abq]; rewrite abq in Hspec; try discriminate Hspec.
          injection Hspec; clear Hspec; intros.
          destruct H5, H6.
          unfold AbTCBCorrect_range, AbTCBCorrect in valid_TCB.
          assert(tmp: 0 <= i < num_id) by omega.
          generalize (valid_TCB pe i tmp); intro tmpH.
          destruct tmpH as [s' tmpH].
          destruct tmpH as [b' tmpH].
          destruct tmpH as [iget b'range].
          assert(Hunused: cused (ZMap.get i (AC d)) = false) by
            (subst; apply (cvalid_unused_next_child _ valid_container _ Hused l)).
          generalize (valid_notinQ pe i s' b' tmp Hunused iget); intro b'val.

          unfold update_cusage, update_cchildren in *.
          esplit.
          repeat vcgen.
          unfold kctxt_new_spec; simpl.
          rewrite pe, ikern, ipt, ihost, Hused, Hchild, Hnc, Hquota; subst.
          unfold update_cusage, update_cchildren.
          rewrite Int.unsigned_repr; try omega.
          instantiate (2:= bstack_loc); reflexivity.
          erewrite <- stencil_matches_symbols; eauto.
          erewrite <- stencil_matches_symbols; eauto.
          unfold set_state0_spec; simpl.
          rewrite Int.unsigned_repr; try omega.
          rewrite ZMap.gss.
          rewrite iget, ikern, pe, ihost, ipt.
          rewrite zle_lt_true.
          simpl.          
          zmap_solve; omega.
          omega.
          unfold enqueue0_spec; simpl.
          rewrite ikern, pe, ihost, ipt.
          rewrite Int.unsigned_repr; try omega.
          zmap_solve; try omega.
          rewrite abq.
          unfold Queue_arg.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          rewrite b'val.
          repeat zdestruct.
          subst; repeat rewrite ZMap.set2; reflexivity.
          omega.
          omega.
        Qed.

      End ThreadSpawnBody.

      Theorem thread_spawn_code_correct:
        spec_le (thread_spawn ↦ thread_spawn_spec_low) (〚thread_spawn ↦ f_thread_spawn 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct H1.
        fbigsteptest (thread_spawn_body_correct s (Genv.globalenv p) makeglobalenv id q b1 Hb1fs Hb1fp 
                        b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd' (PTree.empty _) 
                        (bind_parameter_temps' (fn_params f_thread_spawn)
                                               (Vptr b' ofs' :: Vint id :: Vint q :: nil)
                                               (create_undef_temps (fn_temps f_thread_spawn)))) H2. 
        esplit; erewrite stencil_matches_symbols; eassumption.
        intro stmt.
        destruct stmt.
        repeat fbigstep_post.
      Qed.

    End THREADSPAWN.


    Section SCHEDINIT.

      Let L: compatlayer (cdata RData) := tdqueue_init ↦ gensem tdqueue_init0_spec
           ⊕ set_curid ↦ gensem set_curid_spec
           ⊕ set_state ↦ gensem set_state0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SchedInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** tdqueue_init *)

        Variable btdqueue_init: block.

        Hypothesis htdqueue_init1 : Genv.find_symbol ge tdqueue_init = Some btdqueue_init. 
        
        Hypothesis htdqueue_init2 : Genv.find_funct_ptr ge btdqueue_init = Some (External (EF_external tdqueue_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** set_curid *)

        Variable bset_curid: block.

        Hypothesis hset_curid1 : Genv.find_symbol ge set_curid = Some bset_curid. 
        
        Hypothesis hset_curid2 : Genv.find_funct_ptr ge bset_curid = Some (External (EF_external set_curid (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** set_state *)

        Variable bset_state: block.

        Hypothesis hset_state1 : Genv.find_symbol ge set_state = Some bset_state. 
        
        Hypothesis hset_state2 : Genv.find_funct_ptr ge bset_state = Some (External (EF_external set_state (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).


        Lemma sched_init_body_correct: forall m d d' env le mbi_adr,
                                         env = PTree.empty _ ->
                                         PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                         sched_init_spec (Int.unsigned mbi_adr) d = Some d' ->
                                         high_level_invariant d ->
                                         exists le',
                                           exec_stmt ge env le ((m, d): mem) sched_init_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold sched_init_body.
          functional inversion H1.
          subst.
          destruct H2.
          assert(tmp: 0 <= 0 < 64) by omega.
          generalize (real_abtcb_valid (abtcb d) 0 tmp); intro.
          unfold AbTCBCorrect in H.
          destruct H as [s [b [tcbget brange]]].
          generalize (real_abtcb_notInQ (abtcb d) 0 s b tmp tcbget); intro.
          subst.
          esplit.
          d3 vcgen.
          repeat vcgen.
          d2 vcgen.
          repeat vcgen. unfold set_curid_spec.
          simpl. repeat vcgen.
          econstructor.
          repeat vcgen.
          econstructor.
          eapply eval_Evar_global; repeat vcgen.
          eapply deref_loc_reference.
          repeat vcgen.
          repeat econstructor; repeat vcgen.
          eassumption.
          repeat vcgen.
          eapply eval_funcall_external.
          econstructor.
          split.
          reflexivity.
          econstructor; esplit; repeat progress (split; simpleproof); (econstructor || eapply extcall_generic_sem_intro'); try econstructor; try econstructor; try econstructor; try econstructor; try econstructor; try econstructor; unfold bind; simpl;
                                                                           repeat progress try reflexivity; match goal with
      | [|- context[Int.unsigned (Int.repr 0)]] => change (Int.unsigned (Int.repr 0)) with 0
      | [|- context[Int.unsigned (Int.repr 1)]] => change (Int.unsigned (Int.repr 1)) with 1
      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr
      | [H: ?x = _ |- match ?x with |_ => _ end = _] => rewrite H
      | _ => repeat discharge_unsigned_range
   end; try reflexivity.
          unfold set_state0_spec; simpl.
          rewrite tcbget.
          change (Int.unsigned (Int.repr 1)) with 1.
          rewrite H4, H5, H6.
          reflexivity.
        Qed.

      End SchedInitBody.

      Theorem sched_init_code_correct:
        spec_le (sched_init ↦ sched_init_spec_low) (〚sched_init ↦ f_sched_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (sched_init_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_sched_init)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_sched_init)))) H0. 
      Qed.

    End SCHEDINIT.

(*
    Section THREADKILL.

      Let L: compatlayer (cdata RData) := set_state ↦ gensem set_state0_spec
           ⊕ thread_free ↦ gensem thread_free_spec
           ⊕ queue_rmv ↦ gensem queue_rmv0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ThreadKillBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_state *)

        Variable bset_state: block.

        Hypothesis hset_state1 : Genv.find_symbol ge set_state = Some bset_state. 
        
        Hypothesis hset_state2 : Genv.find_funct_ptr ge bset_state = Some (External (EF_external set_state (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** queue_rmv *)

        Variable bqueue_rmv: block.

        Hypothesis hqueue_rmv1 : Genv.find_symbol ge queue_rmv = Some bqueue_rmv. 
        
        Hypothesis hqueue_rmv2 : Genv.find_funct_ptr ge bqueue_rmv = Some (External (EF_external queue_rmv (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** thread_free *)

        Variable bthread_free: block.

        Hypothesis hthread_free1 : Genv.find_symbol ge thread_free = Some bthread_free. 
        
        Hypothesis hthread_free2 : Genv.find_funct_ptr ge bthread_free = Some (External (EF_external thread_free (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        Lemma thread_kill_body_correct: forall m d d' env le proc_index chan_index,
                                          env = PTree.empty _ ->
                                          PTree.get tproc_index le = Some (Vint proc_index) ->
                                          PTree.get tchan_index le = Some (Vint chan_index) ->
                                          thread_kill_spec d (Int.unsigned proc_index) (Int.unsigned chan_index) = Some d' ->
                                          high_level_invariant d ->
                                          exists le',
                                            exec_stmt ge env le ((m, d): mem) thread_kill_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          functional inversion H2.
          subst.
          destruct H3.
          unfold thread_kill_body.

          assert(chan_index_range: 0 <= Int.unsigned chan_index <= num_chan).
            assert(tmp: 0 <= Int.unsigned proc_index < num_proc) by omega.
            generalize (valid_TCB H8 (Int.unsigned proc_index) tmp); intro.
            unfold AbTCBCorrect in H.
            destruct H as [s' tmpH].
            destruct tmpH as [b' tmpH].
            destruct tmpH as [b'get b'range].
            rewrite H12 in b'get.
            injection b'get; intros; subst.
            omega.

          esplit.
          d3 vcgen.
          repeat vcgen.
          unfold set_state_spec.
          rewrite H5, H6, H7, H8, H11, H12.
          simpl.
          repeat zdestruct.
          d2 vcgen.
          repeat vcgen.
          unfold queue_rmv_spec; simpl.
          rewrite ZMap.gss.
          unfold Queue_arg.
          rewrite H13.
          repeat zdestruct.
          repeat vcgen.
          unfold thread_free_spec; simpl.
          rewrite ZMap.gss.
          rewrite H11.
          rewrite H5, H6, H7, H8.
          repeat rewrite ZMap.set2.
          repeat zdestruct.
        Qed.

      End ThreadKillBody.

      Theorem thread_kill_code_correct:
        spec_le (thread_kill ↦ thread_kill_spec_low) (〚thread_kill ↦ f_thread_kill 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (thread_kill_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b2 Hb2fs Hb2fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_thread_kill)
                                                               (Vint n::Vint i::nil)
                                                               (create_undef_temps (fn_temps f_thread_kill)))) H0. 
      Qed.

    End THREADKILL.
*)

    Section THREADWAKEUP.

      Let L: compatlayer (cdata RData) := set_state ↦ gensem set_state0_spec
           ⊕ enqueue ↦ gensem enqueue0_spec
           ⊕ dequeue ↦ gensem dequeue0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ThreadWakeupBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_state *)

        Variable bset_state: block.

        Hypothesis hset_state1 : Genv.find_symbol ge set_state = Some bset_state. 
        
        Hypothesis hset_state2 : Genv.find_funct_ptr ge bset_state = Some (External (EF_external set_state (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** enqueue *)

        Variable benqueue: block.

        Hypothesis henqueue1 : Genv.find_symbol ge enqueue = Some benqueue. 
        
        Hypothesis henqueue2 : Genv.find_funct_ptr ge benqueue = Some (External (EF_external enqueue (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).
        
        (** dequeue *)

        Variable bdequeue: block.

        Hypothesis hdequeue1 : Genv.find_symbol ge dequeue = Some bdequeue. 
        
        Hypothesis hdequeue2 : Genv.find_funct_ptr ge bdequeue = Some (External (EF_external dequeue (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        Lemma thread_wakeup_body_correct: forall m d d' env le chan_index,
                                            env = PTree.empty _ ->
                                            PTree.get tchan_index le = Some (Vint chan_index) ->
                                            thread_wakeup_spec (Int.unsigned chan_index) d = Some d' ->
                                            high_level_invariant d ->
                                            exists le',
                                              exec_stmt ge env le ((m, d): mem) thread_wakeup_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold thread_wakeup_body.
          destruct H2.
          functional inversion H1; subst.
          Case "last l num_proc = num_proc".
          esplit.
          repeat vcgen.
          unfold dequeue0_spec.
          rewrite H6, H5, H4, H3, H8. rewrite zle_le_true.
          rewrite Int.unsigned_repr.
          repeat zdestruct.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          (*rewrite H3, H4, H5, H6. *)
          repeat vcgen.

          Case "last l num_proc <> num_proc".
          unfold la in *.
          assert(inl: In (last l num_proc) l).
            assert(l <> nil).
              intro.
              assert(last l num_proc = num_proc).
                rewrite H; reflexivity.
              omega.
            generalize H.
            repeat (match goal with [H: _ |- _] => clear H end).
            intro.
            destruct l.
            congruence.
            clear H.
            induction l.
            simpl.
            left; reflexivity.
            destruct l.
            simpl.
            right.
            left; reflexivity.
            simpl in *.
            destruct IHl.
            left; assumption.
            right; right; assumption.
          assert(lastrange: 0 <= last l num_proc < num_proc).
            assert(tmp: 0 <= Int.unsigned chan_index <= num_chan) by omega.
            generalize (valid_TDQ H5 (Int.unsigned chan_index) tmp); intro abqvalid.
            unfold AbQCorrect in abqvalid.
            destruct abqvalid as [l0 tmpH].
            destruct tmpH as [l0H l0range].
            generalize (l0range (last l num_proc)); intro range.
            rewrite H8 in l0H.
            injection l0H; intros; subst.
            apply range.
            assumption.
          assert(last_used: cused (ZMap.get (last l num_proc) (AC d)) = true).
            destruct (cused (ZMap.get (last l num_proc) (AC d))) eqn:Hused; auto.
              unfold NotInQ in valid_notinQ.
              generalize (valid_notinQ H5 (last l num_proc) _x1 _x2 lastrange Hused H10); intro.
              assert(0 <= Int.unsigned chan_index <= num_chan) by omega.
              unfold InQ in valid_inQ.
              generalize (valid_inQ H5 (last l num_proc) (Int.unsigned chan_index) l lastrange H2 H8 inl); intro.
              destruct H12.
              rewrite H10 in H12.
              injection H12; intros; subst.
              omega.
          esplit.
          repeat vcgen.
          unfold dequeue0_spec.
          rewrite H6, H5, H4, H3, H8, H10. rewrite zle_le_true.
          rewrite Int.unsigned_repr.
          repeat zdestruct.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.
          repeat vcgen.
          unfold set_state0_spec; simpl.
          rewrite ZMap.gss.
          rewrite last_used.
          rewrite H6, H5, H4, H3. rewrite zle_lt_true.
          repeat zdestruct. 
          omega.
          unfold enqueue0_spec; simpl.
          rewrite ZMap.gss.
          repeat rewrite ZMap.set2.
          rewrite ZMap.gso.
          rewrite H6, H5, H4, H3, H11, last_used.
          unfold Queue_arg.
          repeat zdestruct.
          rewrite zle_le_true. rewrite zle_lt_true.
          reflexivity.
          omega.
          omega.
          intro contra. clear H7. rewrite contra in _x. omega.
        Qed.

      End ThreadWakeupBody.

      Theorem thread_wakeup_code_correct:
        spec_le (thread_wakeup ↦ thread_wakeup_spec_low) (〚thread_wakeup ↦ f_thread_wakeup 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (thread_wakeup_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_thread_wakeup)
                                                               (Vint n::nil)
                                                               (create_undef_temps (fn_temps f_thread_wakeup)))) H0. 
      Qed.

    End THREADWAKEUP.

  End WithPrimitives.

End PCURIDCODE.
