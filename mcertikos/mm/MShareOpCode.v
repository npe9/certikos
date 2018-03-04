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
(*       for the C functions implemented in the MShareIntro layer      *)
(*                                                                     *)
(*                                                                     *)
(*                                                                     *)
(*                          Yale University                            *)
(*                                                                     *)
(* *********************************************************************)
Require Import TacticsForTesting.
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
Require Import PTNewGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import XOmega.

Require Import AbstractDataType.

Require Import MShare.
Require Import MShareOpCSource.
Require Import ShareGenSpec.

Module MSHARECODE.

  Lemma shared_mem_arg_rev: forall pid1 pid2,
                              shared_mem_arg (Int.unsigned pid1) (Int.unsigned pid2)
                              = shared_mem_arg (Int.unsigned pid2) (Int.unsigned pid1).
  Proof.
    unfold shared_mem_arg. intros.
    destruct (zle_lt 0 (Int.unsigned pid1) 64), (zle_lt 0 (Int.unsigned pid2) 64),
             (zeq (Int.unsigned pid1) (Int.unsigned pid2)) eqn:peq; trivial;
    try rewrite e, zeq_true; try rewrite zeq_false; trivial; auto.
  Qed.

  Lemma SharedMemInfo2Z_valid: forall x,
                                 SharedMemInfo2Z x =
                                 Int.unsigned (Int.repr (SharedMemInfo2Z x)).
  Proof.
    destruct x; simpl; reflexivity.
  Qed.


  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.


    Section SHAREDMEMSTATUS.

      Let L: compatlayer (cdata RData) :=
        get_shared_mem_seen ↦ gensem get_shared_mem_seen_spec
      ⊕ set_shared_mem_seen ↦ gensem set_shared_mem_seen_spec
      ⊕ get_shared_mem_state ↦ gensem get_shared_mem_state_spec
      ⊕ get_shared_mem_status_seen ↦ gensem get_shared_mem_status_seen_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.


      Section SharedMemStatusBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bget_shared_mem_state: block.

        Hypothesis hget_shared_mem_state1 : Genv.find_symbol ge get_shared_mem_state = Some bget_shared_mem_state.

        Hypothesis hget_shared_mem_state2 : Genv.find_funct_ptr ge bget_shared_mem_state =
        Some (External (EF_external get_shared_mem_state
                                    (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default))
                       (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (**)

        Variable bset_shared_mem_seen: block.

        Hypothesis hset_shared_mem_seen1 : Genv.find_symbol ge set_shared_mem_seen = Some bset_shared_mem_seen.

        Hypothesis hset_shared_mem_seen2 : Genv.find_funct_ptr ge bset_shared_mem_seen =
        Some (External (EF_external set_shared_mem_seen
                                    (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                                       tvoid cc_default))
                       (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default).

        (**)

        Variable bget_shared_mem_seen: block.

        Hypothesis hget_shared_mem_seen1 : Genv.find_symbol ge get_shared_mem_seen = Some bget_shared_mem_seen.

        Hypothesis hget_shared_mem_seen2 : Genv.find_funct_ptr ge bget_shared_mem_seen =
        Some (External (EF_external get_shared_mem_seen
                                    (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default))
                       (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (**)

        Variable bget_shared_mem_status_seen: block.

        Hypothesis hget_shared_mem_status_seen1 : Genv.find_symbol ge get_shared_mem_status_seen =
                                                  Some bget_shared_mem_status_seen.

        Hypothesis hget_shared_mem_status_seen2 : Genv.find_funct_ptr ge bget_shared_mem_status_seen =
        Some (External (EF_external get_shared_mem_status_seen
                                    (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default))
                       (Tcons tint (Tcons tint Tnil)) tint cc_default).

      (*******************)

        Function ll_shared_mem_status_spec (pid1 pid2: Z) (adt: RData) : option (RData * Z) :=
          match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
            | (true, true, true, true, true) =>
              match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
                | SHRDValid i' true _ => 
                  match get_shared_mem_status_seen_spec pid1 pid2 adt with
                    | Some j => Some (adt, j)
                    | _ => None
                  end
                | SHRDValid i' false vadr => 
                  Some (adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid i' true vadr) 
                                                              (ZMap.get pid1 (smspool adt)))
                                               (smspool adt)}, SharedMemInfo2Z i')
                | _ => None
              end 
            | _ => None
          end.

        Lemma ll_shared_mem_status__correct: forall m d d' (z: Z) env le pid1 pid2 n,
                                      env = PTree.empty _ ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      (*pg d = true ->*)
                                      ll_shared_mem_status_spec (Int.unsigned pid1) (Int.unsigned pid2) d
                                      = Some (d', Int.unsigned n) ->
                                      high_level_invariant d ->
                                      exists (le': temp_env),
                                        exec_stmt ge env le ((m, d): mem) shared_mem_status_body E0 le' (m, d') (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          assert (H2: True); auto.
          intros. subst.
          inversion H4. (*high_level_invariant d *)
          functional inversion H3; subst.
          - esplit.
            unfold exec_stmt.
            change E0 with (E0 ** E0).
            repeat vcgen.
            + unfold get_shared_mem_seen_spec.
              rewrite H7, H8, H9, H10, H6.
              rewrite H11.
              unfold BooltoZ.
              cutrewrite (1 = Int.unsigned (Int.repr 1)); reflexivity.
            + repeat vcgen.
            + repeat vcgen.
          - esplit.
            unfold exec_stmt.
            change E0 with (E0 ** E0).
            repeat vcgen.
            + unfold get_shared_mem_seen_spec.
              rewrite H7, H8, H9, H10, H6.
              rewrite H11.
              unfold BooltoZ.
              cutrewrite (0 = Int.unsigned (Int.repr 0)); reflexivity.
            + unfold exec_stmt.
              change E0 with (E0 ** E0).
              repeat vcgen.
              unfold get_shared_mem_state_spec. simpl.
              rewrite H7, H8, H9, H10, H6.
              repeat rewrite ZMap.gss.
              rewrite SharedMemInfo2Z_valid.
              reflexivity.
            + rewrite H5. repeat vcgen.
        Qed.

        Lemma ll_shared_mem_status_spec__correct: forall (pid1 pid2: Z) (adt: RData),
                                                    ll_shared_mem_status_spec pid1 pid2 adt =
                                                    shared_mem_status_spec pid1 pid2 adt.
        Proof.
          intros.
          unfold ll_shared_mem_status_spec, shared_mem_status_spec.
          unfold get_shared_mem_status_seen_spec.
          destruct (ikern adt), (ihost adt), (pg adt), (ipt adt), (shared_mem_arg pid1 pid2); try trivial.
          destruct (ZMap.get pid2 (ZMap.get pid1 (smspool adt))); try trivial.
          destruct seen; try trivial.
          destruct (ZMap.get pid1 (ZMap.get pid2 (smspool adt))); try trivial.
          destruct (SharedMemInfo_dec info0 SHRDPEND); try trivial.
        Qed.

        Lemma shared_mem_status__correct: forall m d d' (z: Z) env le pid1 pid2 n,
                                      env = PTree.empty _ ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      (*pg d = true ->*)
                                      shared_mem_status_spec (Int.unsigned pid1) (Int.unsigned pid2) d
                                      = Some (d', Int.unsigned n) ->
                                      high_level_invariant d ->
                                      exists (le': temp_env),
                                        exec_stmt ge env le ((m, d): mem) shared_mem_status_body E0 le' (m, d') (Out_return (Some (Vint n, tint))).
        Proof.
          intros.
          rewrite <- ll_shared_mem_status_spec__correct in H2.
          apply ll_shared_mem_status__correct with pid1 pid2; auto.
        Qed.

      End SharedMemStatusBody.

      Theorem shared_mem_status_code_correct:
        spec_le (shared_mem_status ↦ shared_mem_status_spec_low) (〚shared_mem_status ↦ f_shared_mem_status 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (shared_mem_status__correct s (Genv.globalenv p) makeglobalenv
                                             b2 Hb2fs Hb2fp
                                             b1 Hb1fs Hb1fp
                                             b0 Hb0fs Hb0fp
                                             b3 Hb3fs Hb3fp
                                             m'0 labd labd'
                                             (Int.unsigned n)
                                             (PTree.empty _) 
                                             (bind_parameter_temps' (fn_params f_shared_mem_status)
                                                                    (Vint pid1 :: Vint pid2 :: nil)
                                                                    (create_undef_temps
                                                                       (fn_temps f_shared_mem_status))))
                 H0.
      Qed.

    End SHAREDMEMSTATUS.


    (**************************************)

    Section OFFERSHAREDMEM.

      Let resv2_sem := pt_resv2 ↦ gensem ptResv2_spec.

      Let L: compatlayer (cdata RData) := 
          resv2_sem
        (*⊕ container_alloc ↦ gensem alloc_spec*)
        ⊕ shared_mem_to_ready ↦ gensem shared_mem_to_ready_spec
        ⊕ shared_mem_to_pending ↦ gensem shared_mem_to_pending_spec
        ⊕ shared_mem_to_dead ↦ gensem shared_mem_to_dead_spec
        ⊕ get_shared_mem_state ↦ gensem get_shared_mem_state_spec.


      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section OfferSharedMemBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).


        (**)

        Variable bpt_resv2: block.

        Hypothesis hpt_resv21 : Genv.find_symbol ge pt_resv2 = Some bpt_resv2.

        Hypothesis hpt_resv22 : Genv.find_funct_ptr ge bpt_resv2 =
                      Some (External (EF_external pt_resv2 (signature_of_type
(Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))))) tint cc_default))
(Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))))) tint cc_default).


        (**)

        Variable bshared_mem_to_ready: block.

        Hypothesis hshared_mem_to_ready1 : Genv.find_symbol ge shared_mem_to_ready = Some bshared_mem_to_ready.

        Hypothesis hshared_mem_to_ready2 : Genv.find_funct_ptr ge bshared_mem_to_ready =
                      Some (External (EF_external shared_mem_to_ready (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default).


        (**)

        Variable bshared_mem_to_dead: block.

        Hypothesis hshared_mem_to_dead1 : Genv.find_symbol ge shared_mem_to_dead = Some bshared_mem_to_dead.

        Hypothesis hshared_mem_to_dead2 : 
          Genv.find_funct_ptr ge bshared_mem_to_dead =
          Some (External (EF_external shared_mem_to_dead
                                      (signature_of_type
                                         (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default))
                         (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        (**)

        Variable bshared_mem_to_pending: block.

        Hypothesis hshared_mem_to_pending1 : Genv.find_symbol ge shared_mem_to_pending = Some bshared_mem_to_pending.

        Hypothesis hshared_mem_to_pending2 :
          Genv.find_funct_ptr ge bshared_mem_to_pending =
          Some (External (EF_external shared_mem_to_pending
                                      (signature_of_type
                                         (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default))
                         (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        (**)

        Variable bget_shared_mem_state: block.

        Hypothesis hget_shared_mem_state1 : Genv.find_symbol ge get_shared_mem_state = Some bget_shared_mem_state.

        Hypothesis hget_shared_mem_state2 : Genv.find_funct_ptr ge bget_shared_mem_state =
                                            Some (External (EF_external get_shared_mem_state (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (**)

        Require Import CommonTactic.

        Lemma ptInsert0_presv:
          forall pid1 vadr b v d adt n,
            ptInsert0_spec pid1 vadr b v d = Some (adt, n)
            -> pg adt = true /\ ipt adt = true
               /\ smspool adt = smspool d /\ ikern adt = true /\ ihost adt = true.
        Proof.
          intros. functional inversion H; subst.
          - functional inversion H9; simpl; eauto.
          - functional inversion H9; simpl; eauto.
          - functional inversion H9; simpl; eauto 2;
            functional inversion H11; simpl; eauto 2.
            + rewrite <- H19, <- H0 in *. simpl in *.
              refine_split'; try congruence.
            + rewrite <- H20, <- H0 in *. simpl in *.
              refine_split'; try congruence.
        Qed.

        Lemma ptResv2_presv_pg_idt': forall pid1 pid2 d vadr vadr' adt n v v',
                                ptResv2_spec pid1 vadr v pid2 vadr' v' d = Some (adt, n)
                                -> pg adt = true /\ ipt adt = true
                                   /\ smspool adt = smspool d /\ ikern adt = true /\ ihost adt = true.
        Proof.
          intros. functional inversion H; subst.
          - functional inversion H2; subst; eauto.
          - functional inversion H2; subst; eauto.
            + eapply ptInsert0_presv in H4. assumption.
            + eapply ptInsert0_presv; eauto.
          - functional inversion H1; subst; eauto.
            + eapply ptInsert0_presv in H0. 
              eapply ptInsert0_presv in H3. simpl in *.
              destruct H0 as (HE1 & HE2 & HE3 & HE4 & H6).
              destruct H3 as ( _ & _ & HE5 & _ & _).
              refine_split'; eauto. congruence.
            + eapply ptInsert0_presv in H0. 
              eapply ptInsert0_presv in H3. simpl in *.
              destruct H0 as (HE1 & HE2 & HE3 & Hk & Hh).
              destruct H3 as ( _ & _ & HE5 & _ & _).
              refine_split'; eauto. congruence.
        Qed.

        Hypothesis smspool_vadr_valid: forall pid1 pid2 d vadr i s,
                                      shared_mem_arg (Int.unsigned pid1)
                                                     (Int.unsigned pid2) = true ->
                                      ZMap.get (Int.unsigned pid1)
                                               (ZMap.get (Int.unsigned pid2) (smspool d)) =
                                          SHRDValid i s vadr ->
                                      vadr = Int.unsigned (Int.repr vadr).

        Lemma ptResv2_presv_pg: forall pid1 pid2 d vadr vadr' adt n,
                                  shared_mem_arg (Int.unsigned pid1) (Int.unsigned pid2)
                                     = true
                                -> high_level_invariant d 
                                -> ptResv2_spec (Int.unsigned pid1) (Int.unsigned vadr) 7
                                    (Int.unsigned pid2) vadr' 7 d = Some (adt, Int.unsigned n)
                                -> pg adt = true.
        Proof.
          intros.
          destruct (ptResv2_presv_pg_idt' (Int.unsigned pid1) (Int.unsigned pid2) d (Int.unsigned vadr)
                                          vadr' adt (Int.unsigned n) 7 7 H1) as (a & b & c).
          assumption.
        Qed.

        Lemma ptResv2_presv_ipt: forall pid1 pid2 d vadr vadr' adt n,
                                  shared_mem_arg (Int.unsigned pid1) (Int.unsigned pid2)
                                     = true
                                -> high_level_invariant d 
                                -> ptResv2_spec (Int.unsigned pid1) (Int.unsigned vadr) 7
                                    (Int.unsigned pid2) vadr' 7 d = Some (adt, Int.unsigned n)
                                -> ipt adt = true.
        Proof.
          intros.
          destruct (ptResv2_presv_pg_idt' (Int.unsigned pid1) (Int.unsigned pid2) d (Int.unsigned vadr)
                                          vadr' adt (Int.unsigned n) 7 7 H1) as (a & b & c).
          assumption.
        Qed.

        Lemma ptResv2_presv_ikern: forall pid1 pid2 d vadr vadr' adt n,
                                  shared_mem_arg (Int.unsigned pid1) (Int.unsigned pid2)
                                     = true
                                -> high_level_invariant d 
                                -> ptResv2_spec (Int.unsigned pid1) (Int.unsigned vadr) 7
                                    (Int.unsigned pid2) vadr' 7 d = Some (adt, Int.unsigned n)
                                -> ikern adt = true.
        Proof.
          intros.
          destruct (ptResv2_presv_pg_idt' (Int.unsigned pid1) (Int.unsigned pid2) d (Int.unsigned vadr)
                                          vadr' adt (Int.unsigned n) 7 7 H1) as (a & b & c & r & e).
          assumption.
        Qed.

        Lemma ptResv2_presv_ihost: forall pid1 pid2 d vadr vadr' adt n,
                                  shared_mem_arg (Int.unsigned pid1) (Int.unsigned pid2)
                                     = true
                                -> high_level_invariant d 
                                -> ptResv2_spec (Int.unsigned pid1) (Int.unsigned vadr) 7
                                    (Int.unsigned pid2) vadr' 7 d = Some (adt, Int.unsigned n)
                                -> ihost adt = true.
        Proof.
          intros.
          destruct (ptResv2_presv_pg_idt' (Int.unsigned pid1) (Int.unsigned pid2) d (Int.unsigned vadr)
                                          vadr' adt (Int.unsigned n) 7 7 H1) as (a & b & c & r & e).
          assumption.
        Qed.

        Lemma ptResv2_presv_smspool: forall pid1 pid2 d vadr vadr' adt n,
                                  shared_mem_arg (Int.unsigned pid1) (Int.unsigned pid2)
                                     = true
                                -> high_level_invariant d 
                                -> ptResv2_spec (Int.unsigned pid1) (Int.unsigned vadr) 7
                                    (Int.unsigned pid2) vadr' 7 d = Some (adt, Int.unsigned n)
                                -> smspool adt = smspool d.
        Proof.
          intros.
          destruct (ptResv2_presv_pg_idt' (Int.unsigned pid1) (Int.unsigned pid2) d (Int.unsigned vadr)
                                          vadr' adt (Int.unsigned n) 7 7 H1) as (a & b & c & r & e).
          assumption.
        Qed.


  (*Function ll_offer_shared_mem_spec (pid1 pid2 vadr: Z) (adt: RData) : option (RData * Z) :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid st _ _ => 
            if SharedMemInfo_dec st SHRDPEND then Some (adt, SHARED_MEM_PEND)
            else
              match ZMap.get pid1 (ZMap.get pid2 (smspool adt)) with
                | SHRDValid st' _ vadr' => 
                  if SharedMemInfo_dec st' SHRDPEND then
                    match shared_mem_to_ready_spec pid1 pid2 vadr adt with
                      | Some (adt', re) =>
                        if zeq re MagicNumber
                        then match shared_mem_to_dead_spec pid1 pid2 vadr adt' with
                                 | Some adt'' => Some (adt'', SHARED_MEM_DEAD)
                                 | _ => None
                             end
                        else Some (adt', SHARED_MEM_READY)
                      | _ => None
                    end
                  else match shared_mem_to_pending_spec pid1 pid2 vadr adt with
                                 | Some adt'' => Some (adt'', SHARED_MEM_PEND)
                                 | _ => None
                       end
                | _ => None
              end
          | _ => None
        end
      | _ => None
    end.*)
        Lemma ll_offer_shared_mem_spec__correct: forall (pid1 pid2 vadr: Z) (adt: RData),
                                      ll_offer_shared_mem_spec pid1 pid2 vadr adt =
                                      offer_shared_mem_spec pid1 pid2 vadr adt.
        Proof.
          intros.
          unfold ll_offer_shared_mem_spec, offer_shared_mem_spec.
          unfold shared_mem_to_ready_spec, shared_mem_to_dead_spec, shared_mem_to_pending_spec.
          destruct (ikern adt), (ihost adt), (pg adt), (ipt adt), (shared_mem_arg pid1 pid2); try trivial.
          destruct (ZMap.get pid2 (ZMap.get pid1 (smspool adt))) eqn:M21; try trivial.
          destruct (SharedMemInfo_dec info SHRDPEND); try trivial.
          destruct (ZMap.get pid1 (ZMap.get pid2 (smspool adt))) eqn:M12; try trivial.
          destruct (zle_lt 0 vadr1 4294967296) as [x | x]; try trivial.
          destruct (SharedMemInfo_dec info0 SHRDPEND); try trivial.
          destruct (ptResv2_spec pid1 vadr 7 pid2 vadr1 7 adt) eqn:resq; try trivial.
          destruct p. destruct (zeq z MagicNumber) eqn:zeq; try trivial.
            - simpl.
              destruct (ptResv2_presv_pg_idt' pid1 pid2 adt vadr vadr1 r z 7 7 resq) as (a & b & c & q & t).
              cutrewrite (ikern r = true).
              cutrewrite (ihost r = true).
              cutrewrite (pg r = true).
              cutrewrite (ipt r = true).
              cutrewrite (smspool r = smspool adt).
              rewrite M21, M12. reflexivity.
              assumption. assumption. assumption. assumption. assumption.
            - destruct (Coqlib.zeq z MagicNumber). discriminate zeq.
              simpl. reflexivity.   
         Qed.


        Require Import AuxLemma.

        Lemma ptInsert0_range:
          forall p1 p2 v d d' re n,
            ptInsert0_spec p1 p2 v n d = Some (d', re) ->
            262144 <= nps d <= 1048576 ->
            0 <= re <= Int.max_unsigned.
        Proof.
          intros. rewrite_omega.
          functional inversion H; subst; try omega.
          functional inversion H10; try subst; try omega.
        Qed.

        Lemma ptInsert0_range':
          forall p1 p2 v d d' re n,
            ptInsert0_spec p1 p2 v n d = Some (d', re) ->
            262144 <= nps d <= 1048576 ->
            262144 <= nps d' <= 1048576.
        Proof.
          intros. 
          functional inversion H; subst;
          functional inversion H10; try subst; try subst d'; trivial;
          try rewrite H1 in *; trivial;
          functional inversion H12; trivial.
        Qed.

        Lemma shared_mem_to_ready_range:
          forall p1 p2 v d d' re,
            shared_mem_to_ready_spec p1 p2 v d = Some (d', re) ->
            262144 <= nps d <= 1048576 ->
            0 <= re <= Int.max_unsigned.
        Proof.
          intros. rewrite_omega.
          functional inversion H; clear H; [omega|].
          functional inversion H11; clear H11; subst; try omega.
          eapply ptInsert0_range; eauto.
          eapply ptInsert0_range'; eauto.
          functional inversion H13; clear H13; subst; trivial.
        Qed.

        Lemma ll_offer_shared_mem__correct: forall m d d' (z: Z) env le pid1 pid2 vadr n,
                                      env = PTree.empty _ ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      PTree.get _source_va le = Some (Vint vadr) ->
                                      (*pg d = true ->*)
                                      ll_offer_shared_mem_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) d = Some (d', Int.unsigned n) ->
                                      high_level_invariant d ->
                                      exists (le': temp_env),
                                        exec_stmt ge env le ((m, d): mem) offer_shared_mem_body E0 le' (m, d') (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          assert (H2: True); auto.
          intros. subst.
          inversion H5.
          functional inversion H4; subst.
            - esplit.
              unfold exec_stmt.
              change E0 with (E0 ** E0).
              repeat vcgen.
                + unfold get_shared_mem_state_spec.
                  rewrite H8, H9, H10, H11, H7.
                  rewrite H12.
                  simpl.
                  cutrewrite (1 = Int.unsigned (Int.repr 1));
                    reflexivity.
                + simpl. destruct (zeq (Int.unsigned (Int.repr 1)) 1). reflexivity.
                  contradiction n0. reflexivity.
                + repeat vcgen.
                + rewrite PTree.gss. rewrite H6, Int.repr_unsigned. reflexivity.
            - esplit;
              unfold exec_stmt;
              change E0 with (E0 ** E0);
              repeat vcgen.
                + unfold get_shared_mem_state_spec.
                  rewrite H8, H9, H10, H11, H7.
                  rewrite H12.
                  simpl.
                  rewrite SharedMemInfo2Z_valid.
                  reflexivity.
                + destruct (zeq (Int.unsigned (Int.repr (SharedMemInfo2Z st))) 1).
                    * rewrite <- SharedMemInfo2Z_valid in e.
                      functional inversion e.
                      clear H13. rewrite <- H20 in _x1.
                      apply False_rect; auto.
                    * repeat vcgen.
                + repeat vcgen.
                    * unfold get_shared_mem_state_spec.
                      rewrite shared_mem_arg_rev.
                      rewrite H8, H9, H10, H11, H7.
                      rewrite H14. rewrite SharedMemInfo2Z_valid.
                      reflexivity.
                    * repeat vcgen.
                    * repeat vcgen.
                + rewrite PTree.gss, H6, Int.repr_unsigned. trivial.
            - esplit;
              unfold exec_stmt;
              change E0 with (E0 ** E0);
              repeat vcgen.
                + unfold get_shared_mem_state_spec.
                  rewrite H8, H9, H10, H11, H7.
                  rewrite H12.
                  simpl.
                  rewrite SharedMemInfo2Z_valid.
                  reflexivity.
                + destruct (zeq (Int.unsigned (Int.repr (SharedMemInfo2Z st))) 1).
                    * rewrite <- SharedMemInfo2Z_valid in e.
                      functional inversion e.
                      clear H13. rewrite <- H19 in _x1.
                      apply False_rect; auto.
                    * repeat vcgen.
                + assert (re_range: 0 <= re <= Int.max_unsigned). {
                    eapply shared_mem_to_ready_range; eauto.
                  } 
                  repeat vcgen.
                  * unfold get_shared_mem_state_spec.
                    rewrite shared_mem_arg_rev.
                    rewrite H8, H9, H10, H11, H7.
                    rewrite H14. rewrite SharedMemInfo2Z_valid.
                    reflexivity.
                  * repeat vcgen.
                  * repeat vcgen. 
                + rewrite PTree.gss, H6, Int.repr_unsigned. trivial.
            - esplit.
              unfold exec_stmt.
              change E0 with (E0 ** E0).
              repeat vcgen.
              + unfold get_shared_mem_state_spec.
                rewrite H8, H9, H10, H11, H7.
                rewrite H12.
                simpl.
                rewrite SharedMemInfo2Z_valid.
                reflexivity.
              + destruct (zeq (Int.unsigned (Int.repr (SharedMemInfo2Z st))) 1).
                * rewrite <- SharedMemInfo2Z_valid in e.
                  functional inversion e.
                  clear H13. rewrite <- H18 in _x1.
                  apply False_rect; auto.
                * repeat vcgen.
              + repeat vcgen.
                * unfold get_shared_mem_state_spec.
                  rewrite shared_mem_arg_rev.
                  rewrite H8, H9, H10, H11, H7.
                  rewrite H14. rewrite SharedMemInfo2Z_valid.
                  reflexivity.
                * destruct (zeq (Int.unsigned (Int.repr (SharedMemInfo2Z st'))) 1). 
                  {
                    rewrite <- SharedMemInfo2Z_valid in e.
                    functional inversion e.
                    clear H16. rewrite <- H18 in _x4.
                    apply False_rect; auto.
                  }
                  repeat vcgen.
                * repeat vcgen.
              + rewrite PTree.gss, H6, Int.repr_unsigned. trivial.
        Qed.

        Lemma offer_shared_mem__correct: forall m d d' (z: Z) env le pid1 pid2 vadr n,
                                      env = PTree.empty _ ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      PTree.get _source_va le = Some (Vint vadr) ->
                                      (*pg d = true ->*)
                                      offer_shared_mem_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) d = Some (d', Int.unsigned n) ->
                                      high_level_invariant d ->
                                      exists (le': temp_env),
                                        exec_stmt ge env le ((m, d): mem) offer_shared_mem_body E0 le' (m, d') (Out_return (Some (Vint n, tint))).
        Proof.
          intros.
          rewrite <- ll_offer_shared_mem_spec__correct in H3.
          apply ll_offer_shared_mem__correct with pid1 pid2 vadr; auto.
        Qed.

      End OfferSharedMemBody.

      Theorem offer_shared_mem_code_correct:
        spec_le (offer_shared_mem ↦ offer_shared_mem_spec_low) (〚offer_shared_mem ↦ f_offer_shared_mem 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (offer_shared_mem__correct s (Genv.globalenv p) makeglobalenv
                                             b0 Hb0fs Hb0fp
                                             b2 Hb2fs Hb2fp
                                             b1 Hb1fs Hb1fp
                                             b3 Hb3fs Hb3fp
                                             m'0 labd labd'
                                             (Int.unsigned n)
                                             (PTree.empty _) 
                                             (bind_parameter_temps' (fn_params f_offer_shared_mem)
                                                                    (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                                                    (create_undef_temps
                                                                       (fn_temps f_offer_shared_mem))))
                 H0.
      Qed.

    End OFFERSHAREDMEM.

  End WithPrimitives.

End MSHARECODE.
