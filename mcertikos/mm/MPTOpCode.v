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
(*          for the C functions implemented in the MPTOp layer         *)
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
Require Import MPTIntro.
Require Import MPTOp.
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
Require Import PTCommGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CalRealPTPool.
Require Import CalRealInitPTE.
Require Import XOmega.
Require Import AbstractDataType.
Require Import MPTOpCSource.
Require Import CommonTactic.

Module MPTOPCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.




    Section PTALLOCPDE.

      Let L: compatlayer (cdata RData) := container_alloc ↦ gensem container_alloc_spec
                                                  ⊕ pt_insert_pde ↦ gensem ptInsertPDE_spec
                                                  ⊕ rmv_PTE ↦ gensem rmvPTE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTAllocPDEBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** container_alloc *)

        Variable balloc: block.

        Hypothesis halloc1 : Genv.find_symbol ge container_alloc = Some balloc. 
        
        Hypothesis halloc2 : Genv.find_funct_ptr ge balloc = Some (External (EF_external container_alloc (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** pt_insert_pde *)

        Variable bpt_insert_pde: block.

        Hypothesis hpt_insert_pde1 : Genv.find_symbol ge pt_insert_pde = Some bpt_insert_pde. 
        
        Hypothesis hpt_insert_pde2 : Genv.find_funct_ptr ge bpt_insert_pde = Some (External (EF_external pt_insert_pde (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        (** rmv_PTE *)

        Variable brmv_PTE: block.

        Hypothesis hrmv_PTE1 : Genv.find_symbol ge rmv_PTE = Some brmv_PTE. 
        
        Hypothesis hrmv_PTE2 : Genv.find_funct_ptr ge brmv_PTE = Some (External (EF_external rmv_PTE (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        Definition pt_alloc_pde_mk_rdata (i proc_index pdi pi: Z) (adt: RData) := adt {ptpool: (ZMap.set proc_index (ZMap.set pdi (PDEValid pi (Calculate_init_pte (Z.to_nat i))) 
                                                            (ZMap.get proc_index (ptpool adt))) (ptpool adt))}.


        Section pt_alloc_pde_loop_proof.

          Variable minit: memb.
          Variable adt: RData.
          Variable proc_index: Z.
          Variable pdi: Z.
          Variable pi: Z.

          Hypothesis ipt : ipt adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis init: init adt = true.
          Hypothesis procindexrange: 0 <= proc_index < num_proc.
          Hypothesis procindexneqpt: proc_index <> (PT adt).
          Hypothesis pdirange: 0 <= pdi < 1024.

          Definition pt_alloc_pde_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get ti le = Some (Vint Int.zero) /\
            PTree.get tproc_index le = Some (Vint (Int.repr proc_index)) /\
            PTree.get tpde_index le = Some (Vint (Int.repr pdi)) /\
            PTree.get tpi le = Some (Vint (Int.repr pi)) /\
            ZMap.get pdi (ZMap.get proc_index (ptpool adt)) = PDEValid pi (ZMap.init PTEUndef) /\
            m = (minit, adt).

          Definition pt_alloc_pde_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            m = (minit, pt_alloc_pde_mk_rdata (one_k - 1) proc_index pdi pi adt) /\ PTree.get tpi le = Some (Vint (Int.repr pi)).

          Lemma pt_alloc_pde_loop_correct_aux : LoopProofSimpleWhile.t pt_alloc_pde_while_condition pt_alloc_pde_while_body ge (PTree.empty _) (pt_alloc_pde_loop_body_P) (pt_alloc_pde_loop_body_Q).
          Proof.
            generalize one_k_minus1; intro onekminus1.
            generalize one_k_minus1'; intro onekminus1'.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get ti le = Some (Vint i) /\
                                    PTree.get tproc_index le = Some (Vint (Int.repr proc_index)) /\
                                    PTree.get tpde_index le = Some (Vint (Int.repr pdi)) /\
                                    PTree.get tpi le = Some (Vint (Int.repr pi)) /\
                                    0 <= Int.unsigned i <= one_k /\ 
                                    ZMap.get pdi (ZMap.get proc_index (ptpool adt)) = PDEValid pi (ZMap.init PTEUndef) /\
                                    (Int.unsigned i = 0 /\ m = (minit, adt) \/ 0 < Int.unsigned i /\ m = (minit, pt_alloc_pde_mk_rdata (Int.unsigned i - 1) proc_index pdi pi adt)) /\
                                    w = one_k - Int.unsigned i
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold pt_alloc_pde_loop_body_P in H.
            destruct H as [tile tmpH].
            destruct tmpH as [tproc_indexle tmpH].
            destruct tmpH as [tpde_indexle tmpH].
            destruct tmpH as [tpile tmpH].
            destruct tmpH as [initpte msubst].
            subst.
            esplit. esplit.
            repeat vcgen.

            intros.
            unfold pt_alloc_pde_while_condition.
            unfold pt_alloc_pde_while_body.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tproc_indexle tmpH].
            destruct tmpH as [tpde_indexle tmpH].
            destruct tmpH as [tpile tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [initpde tmpH].
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
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold rmvPTE_spec.
            rewrite ikern, ihost, ipt, init, initpde.
            unfold PTE_Arg.
            unfold PDE_Arg.
            rewrite zle_lt_true.
            rewrite zle_le_true.
            rewrite zle_le_true.
            repeat zdestruct.
            omega.
            omega.
            omega.
            exists (one_k - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold pt_alloc_pde_mk_rdata.
            rewrite ival; simpl.
            reflexivity.

            (* i > 0 *)
            intro tmpH.
            destruct tmpH as [igt0 mval].
            injection mval; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold rmvPTE_spec.
            simpl.
            rewrite ZMap.gss.
            rewrite ZMap.gss.
            rewrite ikern, ihost, ipt, init.
            unfold PTE_Arg.
            unfold PDE_Arg.
            rewrite zle_lt_true.
            rewrite zle_le_true.
            rewrite zle_le_true.
            repeat zdestruct.
            omega.
            omega.
            omega.
            exists (one_k - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold pt_alloc_pde_mk_rdata.
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
            rewrite ZMap.set2.
            rewrite ZMap.set2.
            symmetry.
            reflexivity.
            omega.
            omega.

            (* i = one_k *)
            intro ival.
            subst.
            esplit. esplit.
            repeat vcgen.
            unfold pt_alloc_pde_loop_body_Q.
            Caseeq icase.
            intro tmpH; destruct tmpH.
            rewrite ival in H0.
            discriminate H0.
            intro tmpH; destruct tmpH.
            rewrite ival in H1.
            injection H1; intros; subst.
            split; eauto.
          Qed.

        End pt_alloc_pde_loop_proof.

        Lemma pt_alloc_pde_loop_correct: forall m d d' le proc_index pdi pi,
                                       ipt d = true ->
                                       ihost d = true ->
                                       ikern d = true ->
                                       init d = true ->
                                       0 <= proc_index < num_proc ->
                                       proc_index <> (PT d) ->
                                       0 <= pdi < 1024 ->
                                       ZMap.get pdi (ZMap.get proc_index (ptpool d)) = PDEValid pi (ZMap.init PTEUndef) ->
                                       PTree.get ti le = Some (Vint Int.zero) ->
                                       PTree.get tproc_index le = Some (Vint (Int.repr proc_index)) ->
                                       PTree.get tpde_index le = Some (Vint (Int.repr pdi)) ->
                                       PTree.get tpi le = Some (Vint (Int.repr pi)) ->
                                       d' = pt_alloc_pde_mk_rdata (one_k - 1) proc_index pdi pi d ->
                                       exists le',
                                         (exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile pt_alloc_pde_while_condition pt_alloc_pde_while_body) E0 le' (m, d') Out_normal /\ PTree.get tpi le' = Some (Vint (Int.repr pi))).
        Proof.
          intros.
          generalize (pt_alloc_pde_loop_correct_aux m d proc_index pdi pi H H0 H1 H2 H3 H4 H5).
          unfold pt_alloc_pde_loop_body_P.
          unfold pt_alloc_pde_loop_body_Q.
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

        Lemma pt_alloc_pde_body_correct: forall m d d' env le proc_index vadr padr,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      ptAllocPDE_spec (Int.unsigned proc_index) (Int.unsigned vadr) d = Some (d', Int.unsigned padr) ->
                                      high_level_invariant d ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_alloc_pde_body E0 le' (m, d') (Out_return (Some (Vint padr, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize one_k_minus1; intro onekminus1.
          generalize one_k_minus1'; intro onekminus1'.
          intros.
          subst.
          unfold pt_alloc_pde_body.
          functional inversion H2; subst.
          unfold pdi in *.
          functional inversion H5.
          destruct _x0.
          destruct a0.

          set (initd:= ((((d {AT : ZMap.set (Int.unsigned padr) (ATValid true ATNorm 0) (AT d)})
                            {pperm : ZMap.set (Int.unsigned padr) PGAlloc (pperm d)})
                           {HP : FlatMemory.FlatMem.free_page (Int.unsigned padr) (HP d)})
                          {pperm : ZMap.set (Int.unsigned padr)
                                            (PGHide
                                               (PGPMap (Int.unsigned proc_index) (PDX (Int.unsigned vadr))))
                                            (ZMap.set (Int.unsigned padr) PGAlloc (pperm d))}) 
                         {ptpool: ZMap.set (Int.unsigned proc_index)
                                     (ZMap.set (PDX (Int.unsigned vadr))
                                               (PDEValid (Int.unsigned padr) (ZMap.init PTEUndef))
                                               (ZMap.get (Int.unsigned proc_index) (ptpool d))) 
                                     (ptpool d)}
                         {AC : ZMap.set (Int.unsigned proc_index) cur (AC d)}).
          set (lastd:= (((d {HP : FlatMemory.FlatMem.free_page (Int.unsigned padr) (HP d)}) 
                           {AT : ZMap.set (Int.unsigned padr) (ATValid true ATNorm 0) (AT d)}) 
                          {pperm : ZMap.set (Int.unsigned padr)
                                            (PGHide
                                               (PGPMap (Int.unsigned proc_index) (PDX (Int.unsigned vadr))))
                                            (pperm d)}) 
                         {ptpool
                          : ZMap.set (Int.unsigned proc_index)
                                     (ZMap.set (PDX (Int.unsigned vadr))
                                               (PDEValid (Int.unsigned padr) real_init_PTE)
                                               (ZMap.get (Int.unsigned proc_index) (ptpool d))) 
                                     (ptpool d)}
                         {AC : ZMap.set (Int.unsigned proc_index) cur (AC d)}).
          exploit (pt_alloc_pde_loop_correct m initd lastd (PTree.set ti (Vint (Int.repr 0)) (PTree.set tpde_index (Vint (Int.divu vadr (Int.repr (4096 * 1024)))) (set_opttemp None Vundef (set_opttemp (Some tpi) (Vint padr) le)))) (Int.unsigned proc_index) pdi (Int.unsigned padr)); unfold initd, lastd, pdi; repeat vcgen.
          unfold PDX; xomega.
          unfold PDX; xomega.
          simpl.
          rewrite ZMap.gss.
          rewrite ZMap.gss.
          reflexivity.
          unfold real_init_PTE.
          unfold pt_alloc_pde_mk_rdata.
          repeat rewrite ZMap.set2.
          assert (Heq: forall h a p pt p1 pt0 pt' ac,
                         pt = pt' ->
                         d {HP: h} {AT: a} {pperm: p} {ptpool: pt} {AC: ac}
                         = d {AT: a} {pperm: p1} {HP: h} {pperm: p} {ptpool: pt0} {AC: ac} {ptpool: pt'}) 
            by (intros; subst; reflexivity). 
          apply Heq.
          Opaque Z.of_nat Z.to_nat.
          simpl.
          rewrite ZMap.gss.
          rewrite ZMap.set2.
          rewrite ZMap.set2.
          reflexivity.
          
          destruct H15 as [le' stmt].
          destruct stmt as [stmt tpile'].
          unfold cur, c in *.
          esplit.

          d3 vcgen.
          repeat vcgen.

          d2 vcgen.
          repeat vcgen.
          simpl.
          unfold ptInsertPDE_spec.
          unfold setPDEU_spec.
          simpl.
          rewrite H10, H7, H8, H9.
          unfold PDE_Arg.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          rewrite zlt_lt_true.
          rewrite ZMap.gss.
          repeat zdestruct.
          rewrite H6.
          symmetry.
          reflexivity.
          omega.
          unfold PDX.
          xomega.
          omega.
          repeat vcgen.

          (* usage = quota, so container_alloc returns 0 *)
          esplit; repeat vcgen.
          unfold container_alloc_spec; subst c; rewrites.
          rewrite H4; reflexivity.
          cases; try omega; repeat vcgen.
          simpl; repeat vcgen.
          repeat vcgen.
        Qed.

      End PTAllocPDEBody.


      Theorem pt_alloc_pde_code_correct:
        spec_le (pt_alloc_pde ↦ ptAllocPDE_spec_low) (〚pt_alloc_pde ↦ f_pt_alloc_pde 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_alloc_pde_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_alloc_pde)
                                                               (Vint n::Vint vadr::nil)
                                                               (create_undef_temps (fn_temps f_pt_alloc_pde)))) H0. 
      Qed.


    End PTALLOCPDE.



    Section PTINITCOMM.

      Let L: compatlayer (cdata RData) := set_PDE ↦ gensem setPDE_spec
                                                  ⊕ rmv_PDE ↦ gensem rmvPDE_spec
                                                  ⊕ idpde_init ↦ gensem idpde_init_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTInitCommBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_PDE *)

        Variable bset_PDE: block.

        Hypothesis hset_PDE1 : Genv.find_symbol ge set_PDE = Some bset_PDE. 
        
        Hypothesis hset_PDE2 : Genv.find_funct_ptr ge bset_PDE = Some (External (EF_external set_PDE (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** rmv_PDE *)

        Variable brmv_PDE: block.

        Hypothesis hrmv_PDE1 : Genv.find_symbol ge rmv_PDE = Some brmv_PDE. 
        
        Hypothesis hrmv_PDE2 : Genv.find_funct_ptr ge brmv_PDE = Some (External (EF_external rmv_PDE (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).


        (** idpde_init *)

        Variable bidpde_init: block.

        Hypothesis hidpde_init1 : Genv.find_symbol ge idpde_init = Some bidpde_init. 
        
        Hypothesis hidpde_init2 : Genv.find_funct_ptr ge bidpde_init = Some (External (EF_external idpde_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).


        Local Open Scope Z_scope.

        Definition pt_init_comm_pd_mk_rdata (i: Z) (index: Z) (adt: RData) := adt {ptpool: Calculate_PDE (Z.to_nat i) index (ptpool adt)}.

        Definition pt_init_comm_mk_rdata (i: Z) (adt: RData) := adt {ptpool: Calculate_pt_comm (Z.to_nat i) (ptpool adt)}.


        Section pd_inner_loop_proof.

          Variable minit: memb.
          Variable i: int.
          Variable adt: RData.

          Hypothesis ipt : ipt adt = true.
          Hypothesis pg : pg adt = false.
          Hypothesis ihost: ihost adt = true.
          Hypothesis irange: 0 <= Int.unsigned i < num_proc.
          Hypothesis ikern: ikern adt = true.
          Hypothesis init: init adt = true.

          Definition pd_inner_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get ti le = Some (Vint i) /\
            PTree.get tj le = Some (Vint Int.zero) /\
            (forall j0 pi pdt, ZMap.get (Int.unsigned j0) (ZMap.get (Int.unsigned i) (ptpool adt)) <> PDEValid pi pdt) /\
            m = (minit, adt).

          Definition pd_inner_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            m = (minit, pt_init_comm_pd_mk_rdata (one_k - 1) (Int.unsigned i) adt) /\
            PTree.get ti le = Some (Vint i).

          Lemma pd_inner_loop_correct_aux : LoopProofSimpleWhile.t pd_inner_while_condition pd_inner_while_body ge (PTree.empty _) (pd_inner_loop_body_P) (pd_inner_loop_body_Q).
          Proof.
            generalize one_k_minus1; intro onekminus1.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists j,
                                    PTree.get ti le = Some (Vint i) /\
                                    PTree.get tj le = Some (Vint j) /\
                                    0 <= Int.unsigned j <= one_k /\ 
                                    (Int.unsigned j = 0 /\ m = (minit, adt) \/ 0 < Int.unsigned j /\ m = (minit, pt_init_comm_pd_mk_rdata (Int.unsigned j - 1) (Int.unsigned i) adt)) /\
                                    (forall j0 pi pdt, Int.unsigned j0 >= Int.unsigned j -> ZMap.get (Int.unsigned j0) (ZMap.get (Int.unsigned i) (ptpool (snd m))) <> PDEValid pi pdt) /\
                                    w = one_k - Int.unsigned j 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold pd_inner_loop_body_P in H.
            destruct H as [tile tmpH].
            destruct tmpH as [tjle tmpH].
            destruct tmpH as [nonvalidpde msubst].
            subst.
            esplit. esplit.
            repeat vcgen.

            intros.
            unfold pd_inner_while_condition.
            unfold pd_inner_while_body.
            destruct H as [j tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tjle tmpH].
            destruct tmpH as [jrange tmpH].
            destruct tmpH as [jcase tmpH].
            destruct tmpH as [nonvalidpde nval].
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
            unfold setPDE_spec.
            rewrite ikern, pg, ihost, ipt, init.
            unfold PDE_Arg.
            rewrite zle_lt_true.
            rewrite zle_le_true.
            reflexivity.
            omega.
            omega.
            exists (one_k - Int.unsigned j - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold pt_init_comm_pd_mk_rdata.
            rewrite jval; simpl.
            unfold Calculate_PDE_at_i.
            reflexivity.
            simpl.
            rewrite ZMap.gss.
            rewrite ZMap.gso.
            apply nonvalidpde; eauto.
            omega.
            intro.
            rewrite H1 in H0.
            omega.

            (* j > 0 *)
            intro tmpH.
            destruct tmpH as [jgt0 mval].
            injection mval; intros; subst.
            assert (jcase: 0 < Int.unsigned j < 256 \/ 960 <= Int.unsigned j < 1024 \/ 256 <= Int.unsigned j < 960) by omega.
            Caseeq jcase.
            {
              intro jrange.
              esplit. esplit.
              repeat vcgen.
              esplit. esplit.
              repeat vcgen.
              unfold setPDE_spec.
              simpl.
              rewrite ikern, pg, ihost, ipt, init.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              reflexivity.
              omega.
              omega.
              exists (one_k - Int.unsigned j - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
              right.
              split.
              omega.
              unfold pt_init_comm_pd_mk_rdata.
              f_equal.
              replace (Int.unsigned j + 1 - 1) with (Int.unsigned j - 1 + 1) by omega.
              change (Int.unsigned j - 1 + 1) with (Z.succ (Int.unsigned j - 1)).
              rewrite Z2Nat.inj_succ with (n:=(Int.unsigned j - 1)).
              Opaque Z.to_nat Z.of_nat.
              simpl.
              unfold Calculate_PDE_at_i.
              rewrite Nat2Z.inj_succ.
              rewrite Z2Nat.id.
              unfold Z.succ.
              replace (Int.unsigned j - 1 + 1) with (Int.unsigned j) by omega.
              change (262144 / 1024) with 256.
              change (983040 / 1024) with 960.
              repeat zdestruct.
              omega.
              omega.
              simpl.
              rewrite ZMap.gss.
              rewrite ZMap.gso.
              simpl in nonvalidpde.
              apply nonvalidpde; eauto.
              omega.
              intro.
              rewrite H1 in H0.
              omega.
            }
            intro jcase.
            Caseeq jcase.
            {
              intro jrange.
              esplit. esplit.
              repeat vcgen.
              esplit. esplit.
              repeat vcgen.
              unfold setPDE_spec.
              simpl.
              rewrite ikern, pg, ihost, ipt, init.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              reflexivity.
              omega.
              omega.
              exists (one_k - Int.unsigned j - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
              right.
              split.
              omega.
              unfold pt_init_comm_pd_mk_rdata.
              f_equal.
              replace (Int.unsigned j + 1 - 1) with (Int.unsigned j - 1 + 1) by omega.
              change (Int.unsigned j - 1 + 1) with (Z.succ (Int.unsigned j - 1)).
              rewrite Z2Nat.inj_succ with (n:=(Int.unsigned j - 1)).
              Opaque Z.to_nat Z.of_nat.
              simpl.
              unfold Calculate_PDE_at_i.
              rewrite Nat2Z.inj_succ.
              rewrite Z2Nat.id.
              unfold Z.succ.
              replace (Int.unsigned j - 1 + 1) with (Int.unsigned j) by omega.
              change (262144 / 1024) with 256.
              change (983040 / 1024) with 960.
              repeat zdestruct.
              omega.
              omega.
              simpl.
              rewrite ZMap.gss.
              rewrite ZMap.gso.
              simpl in nonvalidpde.
              apply nonvalidpde; eauto.
              omega.
              intro.
              rewrite H1 in H0.
              omega.
            }
            {
              intro jrange.
              esplit. esplit.
              repeat vcgen.
              esplit. esplit.
              repeat vcgen.
              unfold rmvPDE_spec.
              simpl.
              rewrite ikern, ihost, ipt, init, pg.
              simpl in nonvalidpde.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              assert(tmp: (if zeq (Int.unsigned i) (PT adt) then false else false) = false).
              {
                destruct (zeq (Int.unsigned i) (PT adt)); reflexivity.
              }
              rewrite tmp; clear tmp.
              case_eq (ZMap.get (Int.unsigned j)
                                 (ZMap.get (Int.unsigned i)
                                           (Calculate_PDE (Z.to_nat (Int.unsigned j - 1)) 
                                                          (Int.unsigned i) (ptpool adt)))); intros.
              assert (tmp: Int.unsigned j >= Int.unsigned j) by omega.
              generalize (nonvalidpde j pi pte tmp); intro.
              congruence.
              reflexivity.
              reflexivity.
              reflexivity.
              unfold PDX.
              xomega.
              omega.
              exists (one_k - Int.unsigned j - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
              right.
              split.
              omega.
              unfold pt_init_comm_pd_mk_rdata.
              f_equal.
              replace (Int.unsigned j + 1 - 1) with (Int.unsigned j - 1 + 1) by omega.
              change (Int.unsigned j - 1 + 1) with (Z.succ (Int.unsigned j - 1)).
              rewrite Z2Nat.inj_succ with (n:=(Int.unsigned j - 1)).
              Opaque Z.to_nat Z.of_nat.
              simpl.
              unfold Calculate_PDE_at_i.
              rewrite Nat2Z.inj_succ.
              rewrite Z2Nat.id.
              unfold Z.succ.
              replace (Int.unsigned j - 1 + 1) with (Int.unsigned j) by omega.
              change (262144 / 1024) with 256.
              change (983040 / 1024) with 960.
              repeat zdestruct.
              omega.
              omega.
              simpl.
              rewrite ZMap.gss.
              rewrite ZMap.gso.
              simpl in nonvalidpde.
              apply nonvalidpde; eauto.
              omega.
              intro.
              rewrite H1 in H0.
              omega.
            }

            (* j = one_k *)
            intro jval.
            subst.
            esplit. esplit.
            repeat vcgen.
            unfold pd_inner_loop_body_Q.
            Caseeq jcase.
            intro tmpH; destruct tmpH.
            rewrite jval in H0.
            discriminate H0.
            intro tmpH; destruct tmpH.
            rewrite jval in H1.
            injection H1; intros; subst.
            split.
            assumption.
            assumption.
          Qed.

        End pd_inner_loop_proof.

        Lemma pd_inner_loop_correct: forall m d d' le i,
                                       ipt d = true ->
                                       pg d = false ->
                                       ihost d = true ->
                                       ikern d = true ->
                                       init d = true ->
                                       0 <= Int.unsigned i < num_proc ->
                                       PTree.get ti le = Some (Vint i) ->
                                       PTree.get tj le = Some (Vint Int.zero) ->
                                       (forall j0 pi pdt, ZMap.get (Int.unsigned j0) (ZMap.get (Int.unsigned i) (ptpool d)) <> PDEValid pi pdt) ->
                                       d' = pt_init_comm_pd_mk_rdata (one_k - 1) (Int.unsigned i) d ->
                                       exists le',
                                         exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile pd_inner_while_condition pd_inner_while_body) E0 le' (m, d') Out_normal /\
                                         PTree.get ti le' = Some (Vint i).
        Proof.
          intros.
          generalize (pd_inner_loop_correct_aux m i d H H0 H1 H4 H2 H3).
          unfold pd_inner_loop_body_P.
          unfold pd_inner_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp tmppre].
          destruct tmppre as [m''val tile'].
          exists le'.
          subst.
          repeat vcgen.
          repeat vcgen.
        Qed.



        Section pt_init_comm_outter_loop_proof.

          Variable minit: memb.
          Variable adt: RData.

          Hypothesis ipt : ipt adt = true.
          Hypothesis pg : pg adt = false.
          Hypothesis ihost : ihost adt = true.
          Hypothesis ikern : ikern adt = true.
          Hypothesis init: init adt = true.
          Hypothesis nonvalidpde: forall i j pi pdt, ZMap.get (Int.unsigned j) (ZMap.get (Int.unsigned i) (ptpool adt)) <> PDEValid pi pdt.

          Definition pt_init_comm_outter_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get ti le = Some (Vint Int.zero) /\ 
            m = (minit, adt).

          Definition pt_init_comm_outter_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            m = (minit, pt_init_comm_mk_rdata (num_proc - 1) adt).

          Lemma nonpdevalid_pt_init_comm: forall i j pi pdt, Int.unsigned i > 0 -> ZMap.get (Int.unsigned j) (ZMap.get (Int.unsigned i) (ptpool (pt_init_comm_mk_rdata (Int.unsigned i - 1) adt))) <> PDEValid pi pdt.
          Proof.
            intros.
            rewrite <- Z2Nat.id with (Int.unsigned i - 1).
            set(n:= Z.to_nat(Int.unsigned i - 1)).
            induction n.
            {
              simpl.
              unfold Calculate_pt_comm_at_i.
              set (n1:= (Z.to_nat (1048576 / 1024) - 1)%nat).
              induction n1.
              {
                simpl.
                unfold Calculate_PDE_at_i.
                change (262144 / 1024) with 256.
                change (983040 / 1024) with 960.
                repeat zdestruct.
                rewrite ZMap.gso.
                eapply nonvalidpde; eauto.
                intro.
                rewrite H0 in H; omega.
              }
              {
                Opaque Z.of_nat.
                simpl.
                unfold Calculate_PDE_at_i.
                change (262144 / 1024) with 256.
                change (983040 / 1024) with 960.
                repeat zdestruct.
                rewrite ZMap.gso.
                assumption.
                intro.
                rewrite H0 in H; omega.
                rewrite ZMap.gso.
                assumption.
                intro.
                rewrite H0 in H; omega.
                rewrite ZMap.gso.
                assumption.
                intro.
                rewrite H0 in H; omega.
              }
            }
            {
              simpl.
              rewrite Nat2Z.id.
              simpl.
              unfold Calculate_pt_comm_at_i.
              unfold pt_init_comm_mk_rdata in *.
              simpl in IHn.
              rewrite Nat2Z.id in IHn.
              set (n1:= (Z.to_nat (1048576 / 1024) - 1)%nat).
              induction n1.
              {
                simpl.
                unfold Calculate_PDE_at_i.
                change (262144 / 1024) with 256.
                change (983040 / 1024) with 960.
                repeat zdestruct.
                assert(icase: Int.unsigned i = Z.of_nat (S n) \/ Int.unsigned i <> Z.of_nat (S n)) by omega.
                Caseeq icase; intro.
                {
                  rewrite H0.
                  rewrite ZMap.gss.
                  assert(jcase: Int.unsigned j = 0 \/ Int.unsigned j <> 0) by omega.
                  Caseeq jcase; intro.
                  {
                    rewrite H1.
                    rewrite ZMap.gss.
                    intro contra; discriminate contra.
                  }
                  {
                    rewrite ZMap.gso.
                    rewrite <- H0.
                    assumption.
                    assumption.
                  }
                }
                {
                  rewrite ZMap.gso.
                  assumption.
                  assumption.
                }
              }
              {
                Opaque Z.of_nat.
                simpl.
                unfold Calculate_PDE_at_i.
                change (262144 / 1024) with 256.
                change (983040 / 1024) with 960.
                repeat zdestruct.
                assert(icase: Int.unsigned i = Z.of_nat (S n) \/ Int.unsigned i <> Z.of_nat (S n)) by omega.
                Caseeq icase; intro.
                {
                  rewrite H0.
                  rewrite ZMap.gss.
                  assert(jcase: Int.unsigned j = (Z.of_nat (S n1)) \/ Int.unsigned j <> (Z.of_nat (S n1))) by omega.
                  Caseeq jcase; intro.
                  {
                    rewrite H1.
                    rewrite ZMap.gss.
                    intro contra; discriminate contra.
                  }
                  {
                    rewrite ZMap.gso.
                    rewrite <- H0 in *.
                    assumption.
                    assumption.
                  }
                }
                {
                  rewrite ZMap.gso.
                  assumption.
                  assumption.
                }
                assert(icase: Int.unsigned i = Z.of_nat (S n) \/ Int.unsigned i <> Z.of_nat (S n)) by omega.
                Caseeq icase; intro.
                {
                  rewrite H0.
                  rewrite ZMap.gss.
                  assert(jcase: Int.unsigned j = (Z.of_nat (S n1)) \/ Int.unsigned j <> (Z.of_nat (S n1))) by omega.
                  Caseeq jcase; intro.
                  {
                    rewrite H1.
                    rewrite ZMap.gss.
                    intro contra; discriminate contra.
                  }
                  {
                    rewrite ZMap.gso.
                    rewrite <- H0 in *.
                    assumption.
                    assumption.
                  }
                }
                {
                  rewrite ZMap.gso.
                  assumption.
                  assumption.
                }
                assert(icase: Int.unsigned i = Z.of_nat (S n) \/ Int.unsigned i <> Z.of_nat (S n)) by omega.
                Caseeq icase; intro.
                {
                  rewrite H0.
                  rewrite ZMap.gss.
                  assert(jcase: Int.unsigned j = (Z.of_nat (S n1)) \/ Int.unsigned j <> (Z.of_nat (S n1))) by omega.
                  Caseeq jcase; intro.
                  {
                    rewrite H1.
                    rewrite ZMap.gss.
                    intro contra; discriminate contra.
                  }
                  {
                    rewrite ZMap.gso.
                    rewrite <- H0 in *.
                    assumption.
                    assumption.
                  }
                }
                {
                  rewrite ZMap.gso.
                  assumption.
                  assumption.
                }
              }
            }
            omega.
          Qed.


          Lemma pt_init_comm_outter_loop_correct_aux : LoopProofSimpleWhile.t pt_init_comm_outter_while_condition pt_init_comm_outter_while_body ge (PTree.empty _) (pt_init_comm_outter_loop_body_P) (pt_init_comm_outter_loop_body_Q).
          Proof.
            Opaque Z.to_nat.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get ti le = Some (Vint i) /\
                                    0 <= Int.unsigned i <= num_proc /\ 
                                    (Int.unsigned i = 0 /\ m = (minit, adt) \/ 0 < Int.unsigned i /\ m = (minit, pt_init_comm_mk_rdata (Int.unsigned i - 1) adt)) /\
                                    (forall i j pi pdt, Int.unsigned i > 0 -> ZMap.get (Int.unsigned j) (ZMap.get (Int.unsigned i) (ptpool (pt_init_comm_mk_rdata (Int.unsigned i - 1) adt))) <> PDEValid pi pdt) /\
                                    w = num_proc - Int.unsigned i 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold pt_init_comm_outter_loop_body_P in H.
            destruct H as [tile tmpH].
            destruct tmpH as [nonvalidpde msubst].
            subst.
            esplit. esplit.
            repeat vcgen.
            eapply nonpdevalid_pt_init_comm; eauto.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [icase tmpH].
            destruct tmpH as [nonvalidpdem nval].
            subst.
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.
            unfold pt_init_comm_outter_while_condition, pt_init_comm_outter_while_body.
            destruct m.

            Caseeq ihigh.

            (* i < num_proc *)
            intro ihigh.

            Caseeq icase.
            (* i = 0 *)
            intro tmpH.
            destruct tmpH as [ival msubst].
            injection msubst; intros; subst.

            exploit (pd_inner_loop_correct minit adt (pt_init_comm_pd_mk_rdata (one_k - 1) (Int.unsigned i) adt) (PTree.set tj (Vint (Int.repr 0)) le) i); repeat vcgen.
            destruct H as [pdxle tmpH].
            destruct tmpH as [stmp tix].

            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            exists (64 - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold pt_init_comm_mk_rdata.
            rewrite ival in *.
            simpl in *.
            change (Z.to_nat 0) with 0%nat.
            simpl.
            unfold Calculate_pt_comm_at_i.
            unfold pt_init_comm_pd_mk_rdata.
            reflexivity.

            (* i > 0 *)
            intro tmpH.
            destruct tmpH as [ival msubst].
            injection msubst; intros; subst.

            exploit (pd_inner_loop_correct minit (pt_init_comm_mk_rdata (Int.unsigned i - 1) adt) (pt_init_comm_pd_mk_rdata (one_k - 1) (Int.unsigned i) (pt_init_comm_mk_rdata (Int.unsigned i - 1) adt)) (PTree.set tj (Vint (Int.repr 0)) le) i); repeat vcgen.
            eapply nonvalidpdem; eauto.
            omega.
            destruct H as [pdxle tmpH].
            destruct tmpH as [stmp tix].
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
            unfold pt_init_comm_mk_rdata.
            unfold pt_init_comm_pd_mk_rdata.
            replace (Int.unsigned i + 1 - 1) with (Z.succ (Int.unsigned i - 1)) by omega.
            rewrite Z2Nat.inj_succ with (n:= Int.unsigned i - 1).
            Opaque Z.of_nat.
            simpl.
            rewrite Nat2Z.inj_succ with (n:= Z.to_nat (Int.unsigned i - 1)).
            rewrite Z2Nat.id with (n:= Int.unsigned i - 1).
            unfold Z.succ.
            replace (Int.unsigned i - 1 + 1) with (Int.unsigned i) by omega.
            unfold Calculate_pt_comm_at_i.
            reflexivity.
            omega.
            omega.

            (* i = num_proc *)
            intro ival.
            esplit. esplit.
            repeat vcgen.
            unfold pt_init_comm_outter_loop_body_Q.
            Caseeq icase.
            intro tmpH; destruct tmpH; omega.
            intro tmpH; destruct tmpH.
            rewrite ival in H1.
            assumption.
          Qed.

        End pt_init_comm_outter_loop_proof.

        Lemma pt_init_comm_outter_loop_correct: forall m d d' le,
                                                  PTree.get ti le = Some (Vint Int.zero) -> 
                                                  ipt d = true ->
                                                  pg d = false ->
                                                  ihost d = true ->
                                                  ikern d = true ->
                                                  init d = true ->
                                                  (forall i j pi pdt, ZMap.get (Int.unsigned j) (ZMap.get (Int.unsigned i) (ptpool d)) <> PDEValid pi pdt) ->
                                                  d' = pt_init_comm_mk_rdata (num_proc - 1) d ->
                                                  exists le',
                                                    exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile pt_init_comm_outter_while_condition pt_init_comm_outter_while_body) E0 le' (m, d') Out_normal.
        Proof.
          intros m d d' le tile ipt pe ihost ikern init nonpdevalid m'val.
          generalize (pt_init_comm_outter_loop_correct_aux m d ipt pe ihost ikern init nonpdevalid).
          unfold pt_init_comm_outter_loop_body_P.
          unfold pt_init_comm_outter_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le'' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp m''val].
          exists le''.
          subst.
          repeat vcgen.
          repeat vcgen.
        Qed.

        Lemma pt_init_comm_body_correct: forall m d d' env le mbi_adr,
                                           env = PTree.empty _ ->
                                           PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                           pt_init_comm_spec (Int.unsigned mbi_adr) d = Some d' ->
                                           high_level_invariant d ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) pt_init_comm_body E0 le' (m, d') Out_normal.
        Proof.
          intros.
          subst.
          unfold pt_init_comm_body.
          functional inversion H1.
          inversion H2.
          unfold PMap_uninitialized in valid_uninitialized.
          generalize (valid_uninitialized H7); intro pdenonvalid.
          subst.
          simpl in *.

          Opaque Z.of_nat Z.to_nat.
          exploit (pt_init_comm_outter_loop_correct m (((((d {vmxinfo : real_vmxinfo}) {AT : real_AT (AT d)}) {nps : real_nps} {AC: real_AC})
      {init : true}) {idpde : CalRealIDPDE.real_idpde (idpde d)}) ((((((d {vmxinfo : real_vmxinfo}) {AT : real_AT (AT d)}) {nps : real_nps} {AC: real_AC})
       {init : true}) {ptpool : real_ptp (ptpool d)}) {idpde
     : CalRealIDPDE.real_idpde (idpde d)}) (PTree.set ti (Vint (Int.repr 0)) (set_opttemp None Vundef le))); repeat vcgen.
          destruct H as [le' stmt].
          exists le'.
          repeat vcgen.
        Qed.

      End PTInitCommBody.


      Theorem pt_init_comm_code_correct:
        spec_le (pt_init_comm ↦ pt_init_comm_spec_low) (〚pt_init_comm ↦ f_pt_init_comm 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_init_comm_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_init_comm)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_pt_init_comm)))) H0. 
      Qed.

    End PTINITCOMM.




    Section PTFREEPDE.

      Let L: compatlayer (cdata RData) := pt_read_pde ↦ gensem ptReadPDE_spec
                                                  ⊕ pfree ↦ gensem pfree'_spec
                                                  ⊕ pt_rmv_pde ↦ gensem ptRmvPDE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTFreePDEBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** pt_read_pde *)

        Variable bpt_read_pde: block.

        Hypothesis hpt_read_pde1 : Genv.find_symbol ge pt_read_pde = Some bpt_read_pde. 
        
        Hypothesis hpt_read_pde2 : Genv.find_funct_ptr ge bpt_read_pde = Some (External (EF_external pt_read_pde (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (** pfree *)

        Variable bpfree: block.

        Hypothesis hpfree1 : Genv.find_symbol ge pfree = Some bpfree. 
        
        Hypothesis hpfree2 : Genv.find_funct_ptr ge bpfree = Some (External (EF_external pfree (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** pt_rmv_pde *)

        Variable bpt_rmv_pde: block.

        Hypothesis hpt_rmv_pde1 : Genv.find_symbol ge pt_rmv_pde = Some bpt_rmv_pde. 
        
        Hypothesis hpt_rmv_pde2 : Genv.find_funct_ptr ge bpt_rmv_pde = Some (External (EF_external pt_rmv_pde (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).


        Lemma pt_free_pde_body_correct: forall m d d' env le proc_index vadr,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      ptFreePDE_spec (Int.unsigned proc_index) (Int.unsigned vadr) d = Some d' ->
                                      high_level_invariant d ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_free_pde_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold pt_free_pde_body.
          functional inversion H2; subst.
          unfold pdi, pt' in *.
          functional inversion H4.
          esplit.
          repeat vcgen.
          unfold ptReadPDE_spec.
          unfold getPDE_spec.
          rewrite H5, H6, H7, H8, H10.
          unfold PDE_Arg.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          instantiate (1:= Int.repr pi).
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          unfold PDX.
          xomega.
          omega.
          unfold ptRmvPDE_spec.
          unfold rmvPDE_spec.
          rewrite H5, H6, H7, H8, H9, H10, H12.
          unfold PDE_Arg.
          rewrite zle_lt_true.
          rewrite zle_le_true.
          reflexivity.
          unfold PDX.
          xomega.
          omega.
          unfold pfree'_spec.
          simpl.
          repeat vcgen.
          rewrite ZMap.gss.
          rewrite ZMap.set2.
          reflexivity.
        Qed.

      End PTFreePDEBody.


      Theorem pt_free_pde_code_correct:
        spec_le (pt_free_pde ↦ ptFreePDE_spec_low) (〚pt_free_pde ↦ f_pt_free_pde 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_free_pde_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_free_pde)
                                                               (Vint n::Vint vadr::nil)
                                                               (create_undef_temps (fn_temps f_pt_free_pde)))) H0. 
      Qed.


    End PTFREEPDE.


  End WithPrimitives.

End MPTOPCODE.
