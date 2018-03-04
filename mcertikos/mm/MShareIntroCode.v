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
(*       for the C functions implemented in the MShareOp layer         *)
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

Require Import MShareOp.
Require Import MShareIntroCSource.
Require Import ShareOpGenSpec.

Module MSHAREOPCODE.

  (*shared_mem_arg  never checked that the second args is >= 0, but checked
the first one twice*)
  Lemma shared_mem_arg_rev: forall pid1 pid2,
                              shared_mem_arg (Int.unsigned pid1) (Int.unsigned pid2)
                              = shared_mem_arg (Int.unsigned pid2) (Int.unsigned pid1).
  Proof.
    unfold shared_mem_arg. intros.
    destruct (zle_lt 0 (Int.unsigned pid1) 64), (zle_lt 0 (Int.unsigned pid2) 64),
             (zeq (Int.unsigned pid1) (Int.unsigned pid2)) eqn:peq; trivial;
    try rewrite e, zeq_true; try rewrite zeq_false; trivial; auto.
  Qed.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.


    Section GETSHAREDMEMSTATUSSEEN.

      Let L: compatlayer (cdata RData) :=
        get_shared_mem_state ↦ gensem get_shared_mem_state_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.


      Section GetSharedMemStatusSeenBody.

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

        Lemma get_shared_mem_status_seen__correct: forall m d (z: Z) env le pid1 pid2 n,
                                               env = PTree.empty _ ->
                                               PTree.get tpid1 le = Some (Vint pid1) ->
                                               PTree.get tpid2 le = Some (Vint pid2) ->
                                               (*pg d = true ->*)
                                               get_shared_mem_status_seen_spec
                                                 (Int.unsigned pid1) (Int.unsigned pid2) d
                                               = Some (Int.unsigned n) ->
                                               high_level_invariant d ->
                                               exists (le': temp_env),
                                                 exec_stmt ge env le ((m, d): mem) get_shared_mem_status_seen_body
                                                           E0 le' (m, d) (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          assert (H2: True); auto.
          assert (smi2z: forall s, SharedMemInfo2Z s = Int.unsigned (Int.repr (SharedMemInfo2Z s))). {
            intros. unfold SharedMemInfo2Z.
            destruct s; reflexivity.
          }
          intros. subst.
          inversion H4.
          functional inversion H3; subst.
          - esplit.
            unfold exec_stmt.
            change E0 with (E0 ** E0).
            repeat vcgen.
            + unfold get_shared_mem_state_spec.
              rewrite shared_mem_arg_rev.
              rewrite H5, H7, H8, H9, H10, H6.
              rewrite smi2z; reflexivity.
            + repeat vcgen.
            + repeat vcgen.
            + rewrite H. repeat vcgen.
          - esplit.
            unfold exec_stmt.
            change E0 with (E0 ** E0).
            repeat vcgen.
            + unfold get_shared_mem_state_spec.
              rewrite shared_mem_arg_rev.
              rewrite H5, H7, H8, H9, H10, H6.              
              rewrite smi2z.
              reflexivity.
            + simpl. repeat vcgen.
              destruct (zeq (SharedMemInfo2Z st) 1).
                * functional inversion e.
                  clear H11; rewrite <- H14 in _x1.
                  contradiction _x1; trivial.
                * repeat vcgen.
                * unfold SharedMemInfo2Z. destruct st; omega.
                * unfold SharedMemInfo2Z. destruct st; omega.
            + repeat vcgen.
              unfold get_shared_mem_state_spec.
              rewrite H5, H7, H8, H9, H6.
              rewrite H12.
              rewrite smi2z; reflexivity.
            + simpl. rewrite PTree.gss. rewrite H, Int.repr_unsigned. trivial.
        Qed.

      End GetSharedMemStatusSeenBody.

      Theorem get_shared_mem_status_seen_code_correct:
        spec_le (get_shared_mem_status_seen ↦ get_shared_mem_status_seen_spec_low)
                (〚get_shared_mem_status_seen ↦ f_get_shared_mem_status_seen 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (get_shared_mem_status_seen__correct s (Genv.globalenv p) makeglobalenv
                                             b0 Hb0fs Hb0fp
                                             m'0 labd
                                             (Int.unsigned n)
                                             (PTree.empty _) 
                                             (bind_parameter_temps' (fn_params f_get_shared_mem_status_seen)
                                                                    (Vint pid1 :: Vint pid2 :: nil)
                                                                    (create_undef_temps
                                                                       (fn_temps f_get_shared_mem_status_seen))))
                 H0.
      Qed.


    End GETSHAREDMEMSTATUSSEEN.



    Section SHAREDMEMTOREADY.

      Let resv2_sem := pt_resv2 ↦ gensem ptResv2_spec.

      Let L: compatlayer (cdata RData) := 
          pt_resv2 ↦ gensem ptResv2_spec
        (*⊕ palloc ↦ gensem palloc_spec*)
        (*⊕ shared_mem_to_ready ↦ gensem shared_mem_to_ready_spec*)
        ⊕ set_shared_mem_state ↦ gensem set_shared_mem_state_spec
        ⊕ set_shared_mem_seen ↦ gensem set_shared_mem_seen_spec
        ⊕ get_shared_mem_loc ↦ gensem get_shared_mem_loc_spec
        ⊕ set_shared_mem_loc ↦ gensem set_shared_mem_loc_spec.




      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SharedMemToReadyBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bpt_resv2: block.

        Hypothesis hpt_resv21 : Genv.find_symbol ge pt_resv2 = Some bpt_resv2.

        Hypothesis hpt_resv22 : Genv.find_funct_ptr ge bpt_resv2 =
                      Some (External (EF_external pt_resv2 (signature_of_type
(Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))))) tint cc_default))
(Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))))) tint cc_default).

        Variable bset_shared_mem_state: block.

        Hypothesis hset_shared_mem_state1 : Genv.find_symbol ge set_shared_mem_state = Some bset_shared_mem_state. 

        Hypothesis hset_shared_mem_state2 : Genv.find_funct_ptr ge bset_shared_mem_state =
                      Some (External (EF_external set_shared_mem_state (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        (** set_shared_mem_seen *)

        Variable bset_shared_mem_seen: block.

        Hypothesis hset_shared_mem_seen1 : Genv.find_symbol ge set_shared_mem_seen = Some bset_shared_mem_seen. 

        Hypothesis hset_shared_mem_seen2 : Genv.find_funct_ptr ge bset_shared_mem_seen =
                      Some (External (EF_external set_shared_mem_seen (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Variable bget_shared_mem_loc: block.

        Hypothesis hget_shared_mem_loc1 : Genv.find_symbol ge get_shared_mem_loc = Some bget_shared_mem_loc.

        Hypothesis hget_shared_mem_loc2 : Genv.find_funct_ptr ge bget_shared_mem_loc =
                      Some (External (EF_external get_shared_mem_loc (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Variable bset_shared_mem_loc: block.

        Hypothesis hset_shared_mem_loc1 : Genv.find_symbol ge set_shared_mem_loc = Some bset_shared_mem_loc. 

        Hypothesis hset_shared_mem_loc2 : Genv.find_funct_ptr ge bset_shared_mem_loc =
                      Some (External (EF_external set_shared_mem_loc (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Require Import CommonTactic.

        Lemma ptInsert0_presv:
          forall pid1 vadr b v d adt n,
            ptInsert0_spec pid1 vadr b v d = Some (adt, n)
            -> pg adt = true /\ ipt adt = true
               /\ smspool adt = smspool d.
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
                                   /\ smspool adt = smspool d.
        Proof.
          intros. functional inversion H; subst.
          - functional inversion H2; subst; eauto.
          - functional inversion H2; subst; eauto.
            + eapply ptInsert0_presv in H4. assumption.
            + eapply ptInsert0_presv; eauto.
          - functional inversion H1; subst; eauto.
            + eapply ptInsert0_presv in H0. 
              eapply ptInsert0_presv in H3. simpl in *.
              destruct H0 as (HE1 & HE2 & HE3).
              destruct H3 as ( _ & _ & HE4).
              refine_split'; eauto. congruence.
            + eapply ptInsert0_presv in H0. 
              eapply ptInsert0_presv in H3. simpl in *.
              destruct H0 as (HE1 & HE2 & HE3).
              destruct H3 as ( _ & _ & HE4).
              refine_split'; eauto. congruence.
        Qed.

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
                                          vadr' adt (Int.unsigned n) 7 7 H1) as (a & b & c).
          assumption.
        Qed.

        Lemma shared_mem_to_ready_correct: forall m d d' (z: Z) env le pid1 pid2 vadr n,
                                      env = PTree.empty _ ->
                                      PTree.get tpid1 le = Some (Vint pid1) ->
                                      PTree.get tpid2 le = Some (Vint pid2) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      (*pg d = true ->*)
                                      shared_mem_to_ready_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) d = Some (d', Int.unsigned n) ->
                                      high_level_invariant d ->
                                      exists (le': temp_env),
                                        exec_stmt ge env le ((m, d): mem) shared_mem_to_ready_body E0 le' (m, d') (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          assert (H2: True); auto.
          intros. subst.
          inversion H5.
          functional inversion H4; functional inversion H7; subst;
            set (Hvadr' := H13); set (Hvadr'_inv := H13);
            auto; rewrite H13 in Hvadr'_inv; inversion Hvadr'_inv.
          Focus 2.
            - set (adt'inv := H15). set (adt'kminv := H15).
              apply ptResv2_high_level_inv in adt'inv; auto.
              apply ptResv2_kernel_mode in adt'kminv; try (constructor; auto; fail).
              esplit.
              unfold exec_stmt.
              change E0 with (E0 ** E0).
              repeat vcgen.
                + unfold get_shared_mem_loc_spec.
                  rewrite H8, H9, H10, H11, shared_mem_arg_rev, H7, Hvadr'.
                  instantiate (1:= (Int.repr vadr')).
                  rewrite Int.unsigned_repr.
                  reflexivity.
                  omega.
                + repeat vcgen.
                  econstructor.
                  rewrite H15.
                  trivial.
                + vcgen.
                + vcgen. 
                + repeat vcgen.
                    * unfold set_shared_mem_state_spec; simpl.
                      destruct adt'kminv.
                      rewrite (ptResv2_presv_pg pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_ipt pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_smspool pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite H, H7, H6, H12.
                      vcgen.
                    * unfold set_shared_mem_seen_spec; simpl.
                      destruct adt'kminv.
                      rewrite (ptResv2_presv_pg pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_ipt pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite H, H7, H6. repeat rewrite ZMap.gss.
                      repeat rewrite ZMap.set2.
                      try reflexivity.
                      (*cutrewrite (ZtoBool (Int.unsigned (Int.zero_ext 8 (Int.repr 1)))
                                  = Some true); try reflexivity.*)
                    * unfold set_shared_mem_loc_spec; simpl.
                      destruct adt'kminv.
                      rewrite (ptResv2_presv_pg pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_ipt pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite H, H7, H6.
                      repeat rewrite ZMap.gss.
                      reflexivity.
                    * unfold set_shared_mem_state_spec; simpl.
                      destruct adt'kminv.
                      rewrite (ptResv2_presv_pg pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_ipt pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite H, shared_mem_arg_rev, H7, H6.
                      repeat rewrite ZMap.gso; auto.
                      setoid_rewrite Hvadr'.
                      vcgen.
                    * unfold set_shared_mem_seen_spec; simpl.
                      destruct adt'kminv.
                      rewrite (ptResv2_presv_pg pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_ipt pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite H, shared_mem_arg_rev, H7, H6.

                      (*cutrewrite (ZtoBool (Int.unsigned (Int.zero_ext 8 (Int.repr 0)))
                              = Some false); [| reflexivity].*)
                      (*rewrite (ptResv2_presv_smspool pid1 pid2 d vadr vadr' adt' n); auto.*)
                      repeat rewrite ZMap.gss.
                      reflexivity.
                      (*repeat rewrite ZMap.gso.
                      repeat rewrite ZMap.set2.
                      repeat vcgen.*)
                    * unfold set_shared_mem_loc_spec; simpl.
                      destruct adt'kminv.
                      rewrite (ptResv2_presv_pg pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_ipt pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite H, shared_mem_arg_rev, H7, H6.
                      unfold smsp', smsp.
                      rewrite (ptResv2_presv_smspool pid1 pid2 d vadr vadr' adt' n); auto.
                      repeat rewrite ZMap.gss.
                      repeat rewrite ZMap.set2.
                      repeat rewrite ZMap.gso.
                      (*rewrite (ptResv2_presv_pg pid1 pid2 d vadr vadr' adt' n); auto.
                      rewrite (ptResv2_presv_ipt pid1 pid2 d vadr vadr' adt' n); auto.
                      destruct adt'kminv. rewrite H, H21.*)
                      reflexivity. auto.
                 + vcgen. rewrite PTree.gss. trivial.
            - esplit.
              unfold exec_stmt.
              change E0 with (E0 ** E0).
              repeat vcgen.
                + unfold get_shared_mem_loc_spec.
                  rewrite H8, H9, H10, H11, shared_mem_arg_rev, H7, Hvadr'.
                  instantiate (1:= (Int.repr vadr')).
                  rewrite Int.unsigned_repr.
                  reflexivity.
                  omega.
                + repeat vcgen.
                  econstructor.
                  rewrite H15.
                  cutrewrite (MagicNumber = Int.unsigned (Int.repr MagicNumber)).
                  reflexivity. auto.
                + vcgen.
                + reflexivity.
                + vcgen.
                + vcgen. rewrite PTree.gss. simpl MagicNumber.
                  cutrewrite (n = Int.repr (Int.unsigned n)).
                  rewrite <- H6. trivial.
                  rewrite Int.repr_unsigned. trivial.
        Qed.

      End SharedMemToReadyBody.

      Theorem shared_mem_to_ready_code_correct:
        spec_le (shared_mem_to_ready ↦ shared_mem_to_ready_spec_low)
                (〚shared_mem_to_ready ↦ f_shared_mem_to_ready 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (shared_mem_to_ready_correct s (Genv.globalenv p) makeglobalenv
                                             b0 Hb0fs Hb0fp
                                             b1 Hb1fs Hb1fp
                                             b2 Hb2fs Hb2fp
                                             b3 Hb3fs Hb3fp
                                             b4 Hb4fs Hb4fp
                                             m'0 labd labd'
                                             (Int.unsigned n)
                                             (PTree.empty _) 
                                             (bind_parameter_temps' (fn_params f_shared_mem_to_ready)
                                                                    (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                                                    (create_undef_temps
                                                                       (fn_temps f_shared_mem_to_ready))))
                 H0.
      Qed.

    End SHAREDMEMTOREADY.

    Section SHAREDMEMTODEAD.

      Let L: compatlayer (cdata RData) := 
          set_shared_mem_state ↦ gensem  set_shared_mem_state_spec
        ⊕ set_shared_mem_seen ↦ gensem set_shared_mem_seen_spec
        ⊕ set_shared_mem_loc ↦ gensem set_shared_mem_loc_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SharedMemToDeadBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_shared_mem_state *)

        Variable bset_shared_mem_state: block.

        Hypothesis hset_shared_mem_state1 : Genv.find_symbol ge set_shared_mem_state = Some bset_shared_mem_state. 

        Hypothesis hset_shared_mem_state2 : Genv.find_funct_ptr ge bset_shared_mem_state =
                      Some (External (EF_external set_shared_mem_state (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        (** set_shared_mem_seen *)

        Variable bset_shared_mem_seen: block.

        Hypothesis hset_shared_mem_seen1 : Genv.find_symbol ge set_shared_mem_seen = Some bset_shared_mem_seen. 

        Hypothesis hset_shared_mem_seen2 : Genv.find_funct_ptr ge bset_shared_mem_seen =
                      Some (External (EF_external set_shared_mem_seen (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Variable bset_shared_mem_loc: block.

        Hypothesis hset_shared_mem_loc1 : Genv.find_symbol ge set_shared_mem_loc = Some bset_shared_mem_loc. 

        Hypothesis hset_shared_mem_loc2 : Genv.find_funct_ptr ge bset_shared_mem_loc =
                      Some (External(EF_external set_shared_mem_loc (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Lemma shared_mem_to_dead_correct: forall m d d' (z: Z) env le pid1 pid2 vadr,
                                      env = PTree.empty _ ->
                                      PTree.get tpid1 le = Some (Vint pid1) ->
                                      PTree.get tpid2 le = Some (Vint pid2) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->

                                      shared_mem_to_dead_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) d = Some d' ->
                                      high_level_invariant d ->
                                      exists (le': temp_env),
                                        exec_stmt ge env le ((m, d): mem) shared_mem_to_dead_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          assert (H2: True); auto.
          intros. subst.
          functional inversion H4. subst.
          inversion H5.
          functional inversion H6.
          esplit.
          unfold exec_stmt.
          change E0 with (E0 ** E0).
          repeat vcgen.
            - unfold set_shared_mem_seen_spec; simpl.
              repeat rewrite ZMap.gss.
              repeat vcgen.
            - unfold set_shared_mem_loc_spec; simpl.
              repeat rewrite ZMap.gss.
              repeat vcgen.
            - unfold set_shared_mem_state_spec; simpl.
              rewrite shared_mem_arg_rev.
              repeat rewrite ZMap.gso.
              setoid_rewrite H11.
              repeat vcgen. auto. auto. auto.
            - unfold set_shared_mem_seen_spec; simpl.
              rewrite shared_mem_arg_rev.
              rewrite H6, H7, H8, H9, H10.
              repeat rewrite ZMap.gss.
              repeat rewrite ZMap.set2.
              reflexivity.
              (*cutrewrite (ZtoBool (Int.unsigned (Int.zero_ext 8 (Int.repr 0)))
                          = Some false); try reflexivity.*)

            - unfold set_shared_mem_loc_spec; simpl.
              rewrite shared_mem_arg_rev.
              rewrite H6, H7, H8, H9, H10.
              repeat rewrite ZMap.gss.
              repeat rewrite ZMap.set2.
              repeat rewrite ZMap.gso.
              unfold smsp'; unfold smsp.
              unfold smspool. destruct d. repeat rewrite rdata_update.
              repeat rewrite ZMap.gso.
              reflexivity. auto.
        Qed.

      End SharedMemToDeadBody.


      Theorem shared_mem_to_dead_code_correct:
        spec_le (shared_mem_to_dead ↦ shared_mem_to_dead_spec_low)
                (〚shared_mem_to_dead ↦ f_shared_mem_to_dead 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (shared_mem_to_dead_correct s (Genv.globalenv p) makeglobalenv
                                             b0 Hb0fs Hb0fp
                                             b1 Hb1fs Hb1fp
                                             b2 Hb2fs Hb2fp
                                             m'0 labd labd'
                                             (Int.unsigned vadr)
                                             (PTree.empty _) 
                                             (bind_parameter_temps' (fn_params f_shared_mem_to_dead)
                                                                    (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                                                    (create_undef_temps
                                                                       (fn_temps f_shared_mem_to_dead))))
                 H0.
      Qed.

    End SHAREDMEMTODEAD.





    Section SHAREDMEMTOPENDING.

      Let L: compatlayer (cdata RData) := 
          set_shared_mem_state ↦ gensem  set_shared_mem_state_spec
        ⊕ set_shared_mem_seen ↦ gensem set_shared_mem_seen_spec
        ⊕ set_shared_mem_loc ↦ gensem set_shared_mem_loc_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SharedMemToPendingBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_shared_mem_state *)

        Variable bset_shared_mem_state: block.

        Hypothesis hset_shared_mem_state1 : Genv.find_symbol ge set_shared_mem_state = Some bset_shared_mem_state. 

        Hypothesis hset_shared_mem_state2 : Genv.find_funct_ptr ge bset_shared_mem_state =
                      Some (External (EF_external set_shared_mem_state (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        (** set_shared_mem_seen *)

        Variable bset_shared_mem_seen: block.

        Hypothesis hset_shared_mem_seen1 : Genv.find_symbol ge set_shared_mem_seen = Some bset_shared_mem_seen. 

        Hypothesis hset_shared_mem_seen2 : Genv.find_funct_ptr ge bset_shared_mem_seen =
                      Some (External (EF_external set_shared_mem_seen (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Variable bset_shared_mem_loc: block.

        Hypothesis hset_shared_mem_loc1 : Genv.find_symbol ge set_shared_mem_loc = Some bset_shared_mem_loc. 

        Hypothesis hset_shared_mem_loc2 : Genv.find_funct_ptr ge bset_shared_mem_loc =
                      Some (External (EF_external set_shared_mem_loc (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Lemma shared_mem_to_pending_correct: forall m d d' (z: Z) env le pid1 pid2 vadr,
                                      env = PTree.empty _ ->
                                      PTree.get tpid1 le = Some (Vint pid1) ->
                                      PTree.get tpid2 le = Some (Vint pid2) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      shared_mem_to_pending_spec (Int.unsigned pid1) (Int.unsigned pid2) (Int.unsigned vadr) d = Some d' ->
                                      high_level_invariant d ->
                                      exists (le': temp_env),
                                        exec_stmt ge env le ((m, d): mem) shared_mem_to_pending_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          assert (H2: True); auto.
          intros. subst.
          functional inversion H4. subst.
          inversion H5.
          functional inversion H6.
          esplit.
          unfold exec_stmt.
          change E0 with (E0 ** E0).
          repeat vcgen.
            - unfold set_shared_mem_seen_spec; simpl.
              rewrite H6.
              repeat rewrite ZMap.gss.
              repeat vcgen. (*reflexivity.*)
            - unfold set_shared_mem_loc_spec; simpl.
              rewrite H6.
              repeat rewrite ZMap.gss. repeat rewrite ZMap.set2.
              rewrite H7, H8, H9, H10. reflexivity.
        Qed.

      End SharedMemToPendingBody.


      Theorem shared_mem_to_pending_code_correct:
        spec_le (shared_mem_to_pending ↦ shared_mem_to_pending_spec_low)
                (〚shared_mem_to_pending ↦ f_shared_mem_to_pending 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (shared_mem_to_pending_correct s (Genv.globalenv p) makeglobalenv
                                             b0 Hb0fs Hb0fp
                                             b1 Hb1fs Hb1fp
                                             b2 Hb2fs Hb2fp
                                             m'0 labd labd'
                                             (Int.unsigned vadr)
                                             (PTree.empty _) 
                                             (bind_parameter_temps' (fn_params f_shared_mem_to_pending)
                                                                    (Vint pid1 :: Vint pid2 :: Vint vadr :: nil)
                                                                    (create_undef_temps
                                                                       (fn_temps f_shared_mem_to_pending))))
                 H0.
      Qed.

    End SHAREDMEMTOPENDING.

    End WithPrimitives.

End MSHAREOPCODE.