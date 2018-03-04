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
(*         for the C functions implemented in the PThreadIntro layer   *)
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
Require Import PThreadIntro.
Require Import ZArith.Zwf.
Require Import LoopProof.
Require Import VCGen.
Require Import RealParams.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import ThreadInitGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CalRealProcModule.
Require Import CLemmas.
Require Import TacticsForTesting.
Require Import AbstractDataType.
Require Import PThreadIntroCSource.


Module PTHREADINTROCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.
    
(*
    Section THREADFREE.

      Let L: compatlayer (cdata RData) := shared_mem_init ↦ gensem sharedmem_init_spec
           ⊕ tcb_init ↦ gensem tcb_init_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ThreadFreeBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** pt_free *)

        Variable bpt_free: block.

        Hypothesis hpt_free1 : Genv.find_symbol ge pt_free = Some bpt_free. 
        
        Hypothesis hpt_free2 : Genv.find_funct_ptr ge bpt_free = Some (External (EF_external pt_free (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** tcb_init *)

        Variable btcb_init: block.

        Hypothesis htcb_init1 : Genv.find_symbol ge tcb_init = Some btcb_init. 
        
        Hypothesis htcb_init2 : Genv.find_funct_ptr ge btcb_init = Some (External (EF_external tcb_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        Lemma thread_free_body_correct: forall m d d' env le proc_index,
                                          env = PTree.empty _ ->
                                          PTree.get tproc_index le = Some (Vint proc_index) ->
                                          PThreadIntro.thread_free_spec d (Int.unsigned proc_index) = Some d' ->
                                          exists le',
                                            exec_stmt ge env le ((m, d): mem) thread_free_body E0 le' (m, d') Out_normal.
        Proof.
          intros.
          subst.
          unfold thread_free_body.
          functional inversion H1.
          esplit.
          repeat vcgen.
        Qed.

      End ThreadFreeBody.

      Theorem thread_free_code_correct:
        spec_le (thread_free ↦ thread_free_spec_low) (〚thread_free ↦ f_thread_free 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (thread_free_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_thread_free)
                                                               (Vint n::nil)
                                                               (create_undef_temps (fn_temps f_thread_free)))) H0. 
      Qed.

    End THREADFREE. *)


    Section THREADINIT.

      Let L: compatlayer (cdata RData) := shared_mem_init ↦ gensem sharedmem_init_spec
           ⊕ tcb_init ↦ gensem tcb_init_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ThreadInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** sharedmem_init *)

        Variable bsharedmem_init: block.

        Hypothesis hsharedmem_init1 : Genv.find_symbol ge shared_mem_init = Some bsharedmem_init. 
        
        Hypothesis hsharedmem_init2 : Genv.find_funct_ptr ge bsharedmem_init = Some (External (EF_external shared_mem_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** tcb_init *)

        Variable btcb_init: block.

        Hypothesis htcb_init1 : Genv.find_symbol ge tcb_init = Some btcb_init. 
        
        Hypothesis htcb_init2 : Genv.find_funct_ptr ge btcb_init = Some (External (EF_external tcb_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

(*
        Definition thread_init_mk_rdata (adt: RData) (index: Z) :=
          PThreadIntro.mkRData
            (HP adt)
            (PThreadIntro.ti adt)
            (pe adt)
            (ikern adt)
            (ihost adt)
            (AT adt)
            (nps adt)
            (PT adt)
            (ptpool adt)
            (ipt adt)
            (pb adt)
            (kctxt adt)
            (init_zmap (index + 1) (TCBValid DEAD num_proc num_proc) (tcb adt)).
*)

        Definition thread_init_mk_rdata (adt: RData) (index: Z) :=
          adt {tcb: init_zmap (index + 1) (TCBValid DEAD num_proc num_proc) (tcb adt)}.

        Section thread_init_loop_proof.

          Variable minit: memb.
          Variable adt: RData.

          Hypothesis pg: pg adt = true.
          Hypothesis ipt: ipt adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis ikern: ikern adt = true.

          Definition thread_init_loop_body_P (le: temp_env) (m: mem): Prop :=
            PTree.get ti le = Some (Vint Int.zero) /\ 
            m = (minit, adt).

          Definition thread_init_loop_body_Q (le : temp_env) (m: mem): Prop :=
            m = (minit, thread_init_mk_rdata adt (num_proc - 1)). 

          Lemma thread_init_loop_correct_aux : LoopProofSimpleWhile.t thread_init_while_condition thread_init_while_body ge (PTree.empty _) (thread_init_loop_body_P) (thread_init_loop_body_Q).
          Proof.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get ti le = Some (Vint i) /\
                                    0 <= Int.unsigned i <= num_proc /\ 
                                    (Int.unsigned i = 0 /\ m = (minit, adt) \/ Int.unsigned i > 0 /\ m = (minit, thread_init_mk_rdata adt (Int.unsigned i - 1))) /\
                                    w = num_proc - Int.unsigned i 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold thread_init_loop_body_P in H.
            destruct H as [tile msubst].
            subst.
            change (Int.zero) with (Int.repr 0) in tile.
            esplit. esplit.
            repeat vcgen.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [icase nval].
            subst.
            unfold thread_init_while_body.
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.
            destruct m.

            Caseeq ihigh.
            Case "Int.unsigned i < num_proc".
            intro ihigh.

            Caseeq icase.
            SCase "Int.unsigned i = 0".
            intro tmpH; destruct tmpH as [ival mval].
            injection mval; intros; subst.
            rewrite ival in *.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            exists 63.
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            f_equal.
            unfold thread_init_mk_rdata.
            rewrite ival.
            unfold init_zmap.
            simpl.
            reflexivity.

            SCase "Int.unsigned i > 0".
            intro tmpH; destruct tmpH as [ival mval].
            injection mval; intros; subst.
            unfold thread_init_mk_rdata.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold tcb_init_spec.
            simpl.
            rewrite pg, ikern, ihost, ipt.
            rewrite zle_lt_true.
            repeat zdestruct.
            reflexivity.
            omega.
            exists (64 - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            f_equal.
            replace (Int.unsigned i + 1 - 1) with (Int.unsigned i - 1 + 1) by omega.
            replace (Int.unsigned i - 1 + 1) with (Int.unsigned i) by omega.
            rewrite init_zmap_eq by omega.
            reflexivity.

            Case "Int.unsigned i = num_proc".
            intro ival.
            rewrite ival.
            esplit. esplit.
            repeat vcgen.
            unfold thread_init_loop_body_Q.
            Caseeq icase; intro tmpH; destruct tmpH as [iv mval].
            exfalso; rewrite iv in ival; omega.
            rewrite ival in mval; assumption.
          Qed.

        End thread_init_loop_proof.


        Lemma thread_init_loop_correct: forall m d d' le,
                                          PTree.get ti le = Some (Vint Int.zero) -> 
                                          pg d = true ->
                                          ipt d = true ->
                                          ihost d = true ->
                                          ikern d = true ->
                                          d' = thread_init_mk_rdata d (num_proc - 1) ->
                                          exists le',
                                            exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile thread_init_while_condition thread_init_while_body) E0 le' (m, d') Out_normal.
        Proof.
          intros.
          generalize (thread_init_loop_correct_aux m d H0 H1 H2 H3).
          unfold thread_init_loop_body_P.
          unfold thread_init_loop_body_Q.
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

        Lemma thread_init_body_correct: forall m d d' env le mbi_adr,
                                          env = PTree.empty _ ->
                                          PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                          PThreadIntro.thread_init_spec (Int.unsigned mbi_adr) d = Some d' ->
                                          exists le',
                                            exec_stmt ge env le ((m, d): mem) thread_init_body E0 le' (m, d') Out_normal.
        Proof.
          intros.
          subst.
          unfold thread_init_body.
          functional inversion H1.
          functional inversion H2.
          simpl in *.

          exploit (thread_init_loop_correct m adt d' (PTree.set ti (Vint (Int.repr 0)) (set_opttemp None Vundef le))); try rewrite <- H3; repeat vcgen.
          rewrite <- H, <- H3.
          unfold thread_init_mk_rdata.
          simpl in *.
          reflexivity.
          destruct H9.
          rewrite <- H, <- H3 in *.
          simpl in *.

          esplit.
          repeat vcgen.
        Qed.

      End ThreadInitBody.

      Theorem thread_init_code_correct:
        spec_le (thread_init ↦ thread_init_spec_low) (〚thread_init ↦ f_thread_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (thread_init_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_thread_init)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_thread_init)))) H0. 
      Qed.

    End THREADINIT.

  End WithPrimitives.

End PTHREADINTROCODE.
