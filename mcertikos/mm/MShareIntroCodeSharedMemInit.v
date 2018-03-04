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
(*                        Xiongnan (Newman) Wu                         *)
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
Require Import ShareOpGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import AbstractDataType.
Require Import MShareIntroCSource.
Require Import MShareIntro.
Require Import CalRealSMSPool.
Require Import XOmega.


Module MSHAREINTROCODESHAREDMEMINIT.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.

    Section SharedMemInit.

      Let L: compatlayer (cdata RData) := clear_shared_mem ↦ gensem clear_shared_mem_spec
             ⊕ pmap_init ↦ gensem pmap_init_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
      
      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Section SharedMemInitBody.
        
        Context `{Hwb: WritableBlockOps}.
        
        Variable (sc: stencil).
        
        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** pmap_init *)
        
        Variable bpmap_init: block.
        
        Hypothesis hpmap_init1 : Genv.find_symbol ge pmap_init = Some bpmap_init. 
        
        Hypothesis hpmap_init2 : Genv.find_funct_ptr ge bpmap_init = Some (External (EF_external pmap_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** clear_shared_mem *)
        
        Variable bclear_shared_mem: block.
        
        Hypothesis hclear_shared_mem1 : Genv.find_symbol ge clear_shared_mem = Some bclear_shared_mem. 
        
        Hypothesis hclear_shared_mem2 : Genv.find_funct_ptr ge bclear_shared_mem = Some (External (EF_external clear_shared_mem (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Definition shared_mem_init_inner_mk_rdata (i j: Z) (adt: RData) := 
          adt {smspool: Calculate_smsp_inner i (Z.to_nat j) (smspool adt)}.

        Section shared_mem_init_inner_loop_proof.

          Variable minit: memb.
          Variable adt: RData.
          Variable i: Z.

          Hypothesis pg : pg adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ipt: ipt adt = true.
          Hypothesis irange: 0 <= i < num_proc.

          Definition shared_mem_init_inner_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get _j le = Some (Vint Int.zero) /\
            PTree.get _i le = Some (Vint (Int.repr i)) /\
            m = (minit, adt).

          Definition shared_mem_init_inner_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            m = (minit, shared_mem_init_inner_mk_rdata i (num_proc - 1) adt) /\ PTree.get _i le = Some (Vint (Int.repr i)).

          Lemma shared_mem_init_inner_loop_correct_aux : LoopProofSimpleWhile.t shared_mem_init_inner_while_condition shared_mem_init_inner_while_body ge (PTree.empty _) (shared_mem_init_inner_loop_body_P) (shared_mem_init_inner_loop_body_Q).
          Proof.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists j,
                                    PTree.get _i le = Some (Vint (Int.repr i)) /\
                                    PTree.get _j le = Some (Vint j) /\
                                    0 <= Int.unsigned j <= num_proc /\
                                    (Int.unsigned j = 0 /\ m = (minit, adt) \/ 0 < Int.unsigned j /\ m = (minit, shared_mem_init_inner_mk_rdata i (Int.unsigned j - 1) adt)) /\
                                    w = num_proc - Int.unsigned j
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold shared_mem_init_inner_loop_body_P in H.
            destruct H as [tjle tmpH].
            destruct tmpH as [tile msubst].
            subst.
            esplit. esplit.
            repeat vcgen.

            intros.
            unfold shared_mem_init_inner_while_condition.
            unfold shared_mem_init_inner_while_body.
            destruct H as [j tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tjle tmpH].
            destruct tmpH as [jrange tmpH].
            destruct tmpH as [jcase nval].
            subst.
            destruct jrange as [jlow jhigh].
            apply Zle_lt_or_eq in jhigh.
            destruct m.

            Caseeq jhigh.
            intro jhigh.

            Caseeq jcase.
            (* j = 0 *)
            intro tmpH; destruct tmpH as [jval msubst].
            injection msubst; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold clear_shared_mem_spec.
            rewrite pg, ihost, ikern, ipt.
            unfold shared_mem_arg'.
            repeat rewrite zle_lt_true; auto.
            exists (num_proc - Int.unsigned j - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold shared_mem_init_inner_mk_rdata.
            rewrite jval; simpl.
            unfold Calculate_smsp_inner_at_j.
            reflexivity.

            (* j > 0 *)
            intro tmpH.
            destruct tmpH as [jgt0 mval].
            injection mval; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold clear_shared_mem_spec; simpl.
            rewrite pg, ihost, ikern, ipt.
            unfold shared_mem_arg'.
            repeat rewrite zle_lt_true; auto.
            exists (num_proc - Int.unsigned j - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold shared_mem_init_inner_mk_rdata.
            replace (Int.unsigned j + 1 - 1) with (Int.unsigned j - 1 + 1) by omega.
            change (Int.unsigned j - 1 + 1) with (Z.succ (Int.unsigned j - 1)).
            rewrite Z2Nat.inj_succ with (n:=(Int.unsigned j - 1)).
            Opaque Z.to_nat Z.of_nat.
            simpl.
            rewrite Nat2Z.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            replace (Int.unsigned j - 1 + 1) with (Int.unsigned j) by omega.
            unfold Calculate_smsp_inner_at_j.
            reflexivity.
            omega.
            omega.

            (* j = num_proc *)
            intro jval.
            subst.
            esplit. esplit.
            repeat vcgen.
            unfold shared_mem_init_inner_loop_body_Q.
            Caseeq jcase.
            intro tmpH; destruct tmpH.
            rewrite jval in H0.
            discriminate H0.
            intro tmpH; destruct tmpH.
            rewrite jval in H1.
            injection H1; intros; subst.
            split; eauto.
          Qed.

        End shared_mem_init_inner_loop_proof.

        Lemma shared_mem_init_inner_loop_correct: forall m d d' le i,
                                       pg d = true ->
                                       ihost d = true ->
                                       ikern d = true ->
                                       ipt d = true ->
                                       0 <= i < num_proc ->
                                       PTree.get _j le = Some (Vint Int.zero) ->
                                       PTree.get _i le = Some (Vint (Int.repr i)) ->
                                       d' = shared_mem_init_inner_mk_rdata i (num_proc - 1) d ->
                                       exists le',
                                         (exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile shared_mem_init_inner_while_condition shared_mem_init_inner_while_body) E0 le' (m, d') Out_normal /\ PTree.get _i le' = Some (Vint (Int.repr i))).
        Proof.
          intros.
          generalize (shared_mem_init_inner_loop_correct_aux m d i H H0 H1 H2 H3).
          unfold shared_mem_init_inner_loop_body_P.
          unfold shared_mem_init_inner_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp tmppre].
          destruct tmppre as [m''val tpile'].
          exists le'.
          subst.
          repeat vcgen.
          repeat vcgen.
        Qed.


        Definition shared_mem_init_mk_rdata (i: Z) (adt: RData) := adt {smspool: Calculate_smsp (Z.to_nat i) (smspool adt)}.


        Section shared_mem_init_loop_proof.

          Variable minit: memb.
          Variable adt: RData.

          Hypothesis pg : pg adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ipt: ipt adt = true.

          Definition shared_mem_init_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get _i le = Some (Vint Int.zero) /\
            m = (minit, adt).

          Definition shared_mem_init_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            m = (minit, shared_mem_init_mk_rdata (num_proc - 1) adt).

          Lemma shared_mem_init_loop_correct_aux : LoopProofSimpleWhile.t shared_mem_init_outter_while_condition shared_mem_init_outter_while_body ge (PTree.empty _) (shared_mem_init_loop_body_P) (shared_mem_init_loop_body_Q).
          Proof.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get _i le = Some (Vint i) /\
                                    0 <= Int.unsigned i <= num_proc /\ 
                                    (Int.unsigned i = 0 /\ m = (minit, adt) \/ 0 < Int.unsigned i /\ m = (minit, shared_mem_init_mk_rdata (Int.unsigned i - 1) adt)) /\
                                    w = num_proc - Int.unsigned i
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold shared_mem_init_loop_body_P in H.
            destruct H as [tile msubst].
            subst.
            esplit. esplit.
            repeat vcgen.

            intros.
            unfold shared_mem_init_outter_while_condition.
            unfold shared_mem_init_outter_while_body.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [icase nval].
            subst.
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.
            destruct m.

            Caseeq ihigh.
            intro ihigh.

            Caseeq icase.
            (* i = 0 *)
            intro tmpH; destruct tmpH as [ival msubst].
            injection msubst; intros; subst.

            exploit (shared_mem_init_inner_loop_correct minit adt (shared_mem_init_inner_mk_rdata 0 (num_proc - 1) adt) (PTree.set _j (Vint (Int.repr 0)) (set_opttemp None Vundef le)) (Int.unsigned i)); repeat vcgen; try rewrite ival; try reflexivity.
            destruct H as [le' stmt].
            destruct stmt as [stmt tmp].

            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            exists (num_proc - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold shared_mem_init_mk_rdata.
            rewrite ival; simpl.
            unfold Calculate_smsp_at_i.
            unfold shared_mem_init_inner_mk_rdata.
            reflexivity.

            (* i > 0 *)
            intro tmpH.
            destruct tmpH as [igt0 mval].
            injection mval; intros; subst.

            exploit (shared_mem_init_inner_loop_correct minit (shared_mem_init_mk_rdata (Int.unsigned i - 1) adt) (shared_mem_init_inner_mk_rdata (Int.unsigned i) (num_proc - 1) (shared_mem_init_mk_rdata (Int.unsigned i - 1) adt)) (PTree.set _j (Vint (Int.repr 0)) (set_opttemp None Vundef le)) (Int.unsigned i)); repeat vcgen.
            destruct H as [le' stmt].
            destruct stmt as [stmt tmp].

            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            exists (num_proc - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold shared_mem_init_mk_rdata.
            f_equal.
            replace (Int.unsigned i + 1 - 1) with (Int.unsigned i - 1 + 1) by omega.
            change (Int.unsigned i - 1 + 1) with (Z.succ (Int.unsigned i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(Int.unsigned i - 1)).
            Opaque Z.to_nat Z.of_nat.
            simpl.
            rewrite Nat2Z.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            replace (Int.unsigned i - 1 + 1) with (Int.unsigned i) by omega.
            unfold Calculate_smsp_at_i.
            unfold shared_mem_init_inner_mk_rdata.
            symmetry.
            reflexivity.
            omega.
            omega.

            (* i = num_proc *)
            intro ival.
            subst.
            esplit. esplit.
            repeat vcgen.
            unfold shared_mem_init_loop_body_Q.
            Caseeq icase.
            intro tmpH; destruct tmpH.
            rewrite ival in H0.
            discriminate H0.
            intro tmpH; destruct tmpH.
            rewrite ival in H1.
            injection H1; intros; subst.
            split; eauto.
          Qed.

        End shared_mem_init_loop_proof.

        Lemma shared_mem_init_loop_correct: forall m d d' le,
                                       pg d = true ->
                                       ihost d = true ->
                                       ikern d = true ->
                                       ipt d = true ->
                                       PTree.get _i le = Some (Vint Int.zero) ->
                                       d' = shared_mem_init_mk_rdata (num_proc - 1) d ->
                                       exists le',
                                         exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile shared_mem_init_outter_while_condition shared_mem_init_outter_while_body) E0 le' (m, d') Out_normal.
        Proof.
          intros.
          generalize (shared_mem_init_loop_correct_aux m d H H0 H1 H2).
          unfold shared_mem_init_loop_body_P.
          unfold shared_mem_init_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp m''val].
          exists le'.
          subst.
          repeat vcgen.
          repeat vcgen.
        Qed.

        Lemma shared_mem_init_body_correct: forall m d d' env le mbi_adr,
                                      env = PTree.empty _ ->
                                      PTree.get _mbi_adr le = Some (Vint mbi_adr) ->
                                      sharedmem_init_spec (Int.unsigned mbi_adr) d = Some d' ->
                                      high_level_invariant d ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) shared_mem_init_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold shared_mem_init_body.
          functional inversion H1; subst.

          set (initd := ((((((((d {vmxinfo : real_vmxinfo}) {pg : true}) {LAT
           : real_LAT (LAT d)}) {nps : real_nps} {AC: real_AC}) {init : true}) {PT : 0})
       {ptpool : CalRealPT.real_pt (ptpool d)}) {idpde
      : CalRealIDPDE.real_idpde (idpde d)})).
          exploit (shared_mem_init_loop_correct m initd (shared_mem_init_mk_rdata (num_proc - 1) initd) (PTree.set _i (Vint (Int.repr 0))
        (set_opttemp None Vundef (set_opttemp None Vundef le)))); unfold initd; simpl; try reflexivity; try assumption; repeat ptreesolve.
          unfold real_smspool, CalRealIDPDE.real_idpde.
          unfold shared_mem_init_mk_rdata.
          Opaque Z.to_nat Z.of_nat Calculate_smsp.
          simpl.
          generalize (Calculate_smsp (Z.to_nat 63) (smspool d)).
          generalize (CalRealIDPDE.real_idpde (idpde d)).
          intros real_smspool' real_idpde' stmt.
          destruct stmt as [le' stmt].
          esplit.
          repeat vcgen.
        Qed.
       
      End SharedMemInitBody.

      Theorem shared_mem_init_code_correct:
        spec_le (shared_mem_init ↦ shared_mem_init_spec_low) (〚shared_mem_init ↦ f_shared_mem_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (shared_mem_init_body_correct s (Genv.globalenv p) makeglobalenv b1 Hb1fs Hb1fp b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_shared_mem_init)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_shared_mem_init)))) H0. 
      Qed.


    End SharedMemInit.

  End WithPrimitives.

End MSHAREINTROCODESHAREDMEMINIT.
