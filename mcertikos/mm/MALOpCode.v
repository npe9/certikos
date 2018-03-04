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
(*          for the C functions implemented in the MALOp layer         *)
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
Require Import MALOp.
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
Require Import ALGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import MALOpCSource.
Require Import AbstractDataType.
Require Import CommonTactic.
Require Import TacticsForTesting.

Module MALOPCODE.

  Section With_primitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.

    Section PFree.

      Let L: compatlayer (cdata RData) := at_set ↦ gensem set_at_u_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PFreeBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** at_set *)

        Variable batset: block.

        Hypothesis hat_set1 : Genv.find_symbol ge at_set = Some batset. 
        
        Hypothesis hat_set2 : Genv.find_funct_ptr ge batset = Some (External (EF_external at_set (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Lemma pfree_body_correct: forall m d d' env le index,
                                    env = PTree.empty _ ->
                                    PTree.get tpfree_index le = Some (Vint index)->
                                    MALOp.pfree_spec (Int.unsigned index) d = Some d' ->
                                    exists le',
                                      (exec_stmt ge env le ((m, d): mem) pfree_body E0 le' (m, d') Out_normal).
        Proof.
          generalize max_unsigned_val; intro.
          intros.
          subst.
          unfold pfree_body in *.
          functional inversion H2; subst.
          esplit.
          repeat vcgen.
        Qed. 

      End PFreeBody.

      Theorem pfree_code_correct:
        spec_le (pfree ↦ pfree_spec_low) (〚pfree ↦ f_pfree 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pfree_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                     (bind_parameter_temps' (fn_params f_pfree)
                                                            (Vint n::nil)
                                                            (create_undef_temps (fn_temps f_pfree)))) H0.
      Qed.

    End PFree.


    Section PAlloc.

      Let L: compatlayer (cdata RData) := get_nps ↦ gensem get_nps_spec
           ⊕ is_norm ↦ gensem is_at_norm_spec
           ⊕ at_get ↦ gensem get_at_u_spec
           ⊕ at_set ↦ gensem set_at_u_spec
           ⊕ at_set_c ↦ gensem set_at_c_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PallocBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_nps *)

        Variable bgetnps: block.
        
        Hypothesis hget_nps1 : Genv.find_symbol ge get_nps = Some bgetnps.
        
        Hypothesis hget_nps2 : Genv.find_funct_ptr ge bgetnps = Some (External (EF_external get_nps (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).
        
        (** is_norm *)

        Variable bisnorm: block.

        Hypothesis hat_isnorm1 : Genv.find_symbol ge is_norm = Some bisnorm.
        
        Hypothesis hat_isnorm2 : Genv.find_funct_ptr ge bisnorm = Some (External (EF_external is_norm (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** at_get *)

        Variable batget: block.

        Hypothesis hat_get1 : Genv.find_symbol ge at_get = Some batget.
        
        Hypothesis hat_get2 : Genv.find_funct_ptr ge batget = Some (External (EF_external at_get (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** at_set *)

        Variable batset: block.

        Hypothesis hat_set1 : Genv.find_symbol ge at_set = Some batset.
        
        Hypothesis hat_set2 : Genv.find_funct_ptr ge batset = Some (External (EF_external at_set (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** at_set_c *)

        Variable batset_c: block.

        Hypothesis hat_set_c1 : Genv.find_symbol ge at_set_c = Some batset_c.
        
        Hypothesis hat_set_c2 : Genv.find_funct_ptr ge batset_c = Some (External (EF_external at_set_c (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Lemma nps_range : forall d, high_level_invariant d -> init d = true -> kern_low <= nps d <= maxpage.
        Proof.
          intros.
          inv H.
          generalize (valid_nps H0); intro.
          repeat autounfold; simpl.
          repeat autounfold in *.
          omega.
        Qed.
        
        Lemma nps_representable : forall d, high_level_invariant d -> init d = true -> Int.unsigned (Int.repr (nps d)) = nps d.
        Proof.
          intros.
          apply Int.unsigned_repr. 
          generalize (nps_range d H H0).
          repeat autounfold; simpl.
          omega.
        Qed.

        Section Palloc_loop_proof.

          Variable minit: memb.
          Variable adt : RData.
          Notation nps := (AbstractDataType.nps adt).

          Variable n: int.
          Hypothesis inv: high_level_invariant adt.
          Hypothesis n_property: 0 < Int.unsigned n < nps /\ (exists n0, ZMap.get (Int.unsigned n) (AT adt) = ATValid false ATNorm n0) \/ Int.unsigned n = nps.
          Hypothesis lt_n_not_free: (forall x n0: Z, ((0 < x < Int.unsigned n)%Z ->
                                                    ZMap.get x (AT adt) <> ATValid false ATNorm n0)).
          Hypothesis initialized : init adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ihost: ihost adt = true.

          Lemma permission_valid : forall index, 0 < Int.unsigned index < nps -> exists t1 t2 n, ZMap.get (Int.unsigned index) (AT adt) = ATValid t1 t2 n.
          Proof.
            intros.
            generalize nps_range; intro nps_range.
            inv inv.
            simpl. 
            unfold AT_kern in valid_AT_kern.
            unfold AT_usr in valid_AT_usr.
            simpl in *.

            assert(0 <= Int.unsigned index < kern_low \/ kern_high <= Int.unsigned index < AbstractDataType.nps adt \/ kern_low <= Int.unsigned index < Z.min kern_high (AbstractDataType.nps adt)).
            destruct (Zmin.Zmin_spec kern_high (AbstractDataType.nps adt)).
            destruct H0.
            rewrite H1.
            omega.
            destruct H0.
            rewrite H1.
            omega.
            destruct H0.
            exists false.
            exists ATKern.
            exists 0.
            apply valid_AT_kern.
            assumption.
            trivial.
            left.
            assumption.
            destruct H0.
            exists false.
            exists ATKern.
            exists 0.
            apply valid_AT_kern.
            trivial.
            right.
            trivial.
            apply valid_AT_usr in H0.
            destruct H0 as [b].
            exists b.
            destruct H0.
            eauto.
            eauto.
            trivial.
          Qed.                                 

          Lemma permission_norm : forall index, (0 < Int.unsigned index < nps) -> is_at_norm_spec (Int.unsigned index) adt = Some 0 \/ is_at_norm_spec (Int.unsigned index) adt = Some 1.
          Proof.
            intros.
            generalize (nps_range adt inv initialized); intro.
            unfold is_at_norm_spec.
            generalize(permission_valid index H); intro.
            destruct H1 as [t1].
            destruct H1 as [t2].
            rewrite ikern, ihost.
            unfold zle_lt.
            destruct H1.
            destruct t2.
            autounfold in *; rewrite H1; auto.
            repeat zdestruct.
            destruct (ATType_dec ATKern ATNorm); eauto.
            autounfold in *; rewrite H1; auto.      
            repeat zdestruct.
            destruct (ATType_dec ATResv ATNorm); eauto.
            autounfold in *; rewrite H1; auto.   
            repeat zdestruct.
            destruct (ATType_dec ATNorm ATNorm); eauto.
          Qed.

          Lemma get_at_u_valid : forall index,  is_at_norm_spec (Int.unsigned index) adt = Some 1 ->  (get_at_u_spec (Int.unsigned index) adt = Some 0 \/ get_at_u_spec (Int.unsigned index) adt = Some 1).
          Proof.
            intros.
            unfold is_at_norm_spec in H.
            unfold get_at_u_spec.
            unfold zle_lt in *.
            autounfold in *.
            rewrite ikern, ihost in *.
            destruct (ZMap.get (Int.unsigned index) (AT adt)).
            destruct b; auto.
            repeat zdestruct.
            repeat zdestruct.
            repeat zdestruct.
          Qed.

          Definition palloc_index_valid (index: int): Prop := (exists n1, (ZMap.get (Int.unsigned index) (AT adt) = ATValid false ATNorm n1)) /\ forall x n, 0 < x < (Int.unsigned index) -> ZMap.get x (AT adt) <> ATValid false ATNorm n.

          Lemma get_and_norm : forall index, 0 < Int.unsigned index < nps -> (forall x n1: Z, 0 < x < Int.unsigned index -> ZMap.get x (AT adt) <> ATValid false ATNorm n1) ->  is_at_norm_spec (Int.unsigned index) adt = Some 1 -> get_at_u_spec (Int.unsigned index) adt = Some 0 -> palloc_index_valid index.
          Proof.
            intros index indexrange indvalid isnorm atget.
            generalize (nps_range adt inv initialized); intro.
            unfold is_at_norm_spec in isnorm.
            unfold get_at_u_spec in atget.
            unfold palloc_index_valid.
            unfold zle_lt in *.
            autounfold in *.
            rewrite ikern, ihost in *.
            repeat zdestruct.
            destruct (ZMap.get (Int.unsigned index) (AT adt)).
            destruct b.
            inversion atget.
            destruct (ATType_dec t ATNorm); eauto.
            destruct t.
            discriminate e.
            discriminate e.
            split.
            esplit.
            trivial.
            intros.
            apply (indvalid x n1).
            assumption.
            assumption.
            inversion isnorm.
            discriminate isnorm.
          Qed.

          Lemma palloc_index_unique : forall index1 index2, palloc_index_valid index1 -> palloc_index_valid index2 -> Int.unsigned index1 > 0 -> Int.unsigned index2 > 0 -> index1 = index2.
          Proof.
            intros index1 index2 valid1 valid2.
            unfold palloc_index_valid in *.
            destruct valid1 as [valid1a valid1b].
            destruct valid2 as [valid2a valid2b].
            destruct valid1a as [n1 valid1a].
            destruct valid2a as [n2 valid2a].
            case_eq (Int.unsigned index1).
            (* index1 = 0 *)
            intros.
            omega.
            (* index1 > 0 *)
            intro.
            case_eq (Int.unsigned index2).
            (* index2 = 0 *)
            intros.
            omega.
            (* index2 > 0 *)
            intros.
            rewrite H in *.
            rewrite H0 in *.
            generalize (Zgt_pos_0 p); intro ppos.
            generalize (Zgt_pos_0 p0); intro p0pos.
            assert(Z.pos p0 < Z.pos p -> False).
            intro.
            assert(forall n0, ZMap.get (Z.pos p0) (AT adt) <> ATValid false ATNorm n0).
            {
              intro.
              apply valid1b.
              split.
              omega.
              assumption.
            }
            generalize (H4 n2); intro.
            contradiction.
            assert(Z.pos p < Z.pos p0 -> False).
            {
              intro.
              assert(forall n0, ZMap.get (Z.pos p) (AT adt) <> ATValid false ATNorm n0).
              {
                intro.
                apply valid2b.
                split.
                omega.
                assumption.
              }
              generalize (H5 n1); intro.
              contradiction.
            }
            assert(Z.pos p = Z.pos p0) by omega.
            assert(Int.unsigned index1 = Int.unsigned index2).
            {
              rewrite H.
              rewrite H0.
              rewrite H5.
              trivial.
            }
            apply unsigned_inj.
            assumption.
            (* index2 < 0 *)
            intros.
            generalize (Zlt_neg_0 p0).
            omega.
            (* index1 < 0 *)
            intros.
            generalize (Zlt_neg_0 p).
            omega.
          Qed.

          Lemma palloc_index_invalid_norm : forall index n, is_at_norm_spec (Int.unsigned index) adt = Some 0 -> ZMap.get (Int.unsigned index) (AT adt) <> ATValid false ATNorm n.
          Proof.
            intros.
            intro.
            unfold is_at_norm_spec in H.
            unfold zle_lt in *.
            rewrite ikern, ihost in *.
            repeat zdestruct.
            autounfold in *.
            rewrite H0 in H.
            inversion H.
            destruct (ATType_dec ATNorm ATNorm); eauto.
            discriminate H2.
          Qed.

          Lemma palloc_index_invalid_atget : forall index n, get_at_u_spec (Int.unsigned index) adt = Some 1 -> ZMap.get (Int.unsigned index) (AT adt) <> ATValid false ATNorm n.
          Proof.
            intros.
            intro.
            autounfold in *.
            unfold get_at_u_spec in H.
            unfold zle_lt in *.
            rewrite ikern, ihost in *.
            repeat zdestruct.
            rewrite H0 in H.
            inversion H.
          Qed.

          Definition palloc_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get tnps le = Some (Vint (Int.repr nps)) /\ 
            PTree.get tpalloc_index le = Some (Vint (Int.repr 1)) /\ 
            PTree.get tpalloc_free_index le = Some (Vint (Int.repr nps)) /\
            m = (minit, adt).

          Definition palloc_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            PTree.get tpalloc_free_index le = Some (Vint n) /\   
            PTree.get tnps le = Some (Vint (Int.repr nps)) /\
            m = (minit, adt).

          Lemma palloc_loop_correct_aux : LoopProofSimpleWhile.t palloc_while_condition palloc_while_body ge (PTree.empty _) (palloc_loop_body_P) (palloc_loop_body_Q).
          Proof.
            generalize nps_range; intro nps_range.
            generalize max_unsigned_val; intro max_unsignedval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists index, 
                                    PTree.get tpalloc_index le = Some (Vint index) /\
                                    PTree.get tnps le = Some (Vint (Int.repr nps)) /\
                                    (0 < Int.unsigned index <= nps) /\ 
                                    m = (minit, adt) /\ 
                                    w = nps - Int.unsigned index /\ 
                                    (PTree.get tpalloc_free_index le = Some (Vint n) \/
                                     PTree.get tpalloc_free_index le = Some (Vint (Int.repr nps)) /\ (Int.unsigned index <= Int.unsigned n) /\ (forall x n: Z, (0 < x < Int.unsigned index) ->  ZMap.get x (AT adt) <> ATValid false ATNorm n)) 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold palloc_loop_body_P in H.
            destruct H.
            destruct H0.
            destruct H1.
            destruct H2.
            subst.

            generalize (nps_range adt inv initialized); intro npsrange.
            Caseeq n_property.
            intro tmpn.
            destruct tmpn as [tmpn1 tmpn2].
            esplit. esplit.
            repeat vcgen.
            right.
            split; auto.
            split; auto.
            omega.
            intros.
            apply lt_n_not_free; eauto.
            omega.
            intro tmpn.
            subst.
            esplit. esplit.
            repeat vcgen.
            left.
            rewrite <- tmpn in H1.
            rewrite Int.repr_unsigned in H1.
            assumption.

            intros.
            unfold palloc_while_condition.
            unfold palloc_while_body.
            unfold palloc_loop_body_Q.
            destruct H as [index]. destruct H. destruct H0. 
            destruct H1. destruct H2.
            destruct H3 as [n0val casefreeindex].
            destruct H1 as [indexge0 caseindexnps].
            apply Zle_lt_or_eq in caseindexnps.
            subst.
            generalize (nps_range adt inv initialized); intro npsrange.

            Caseeq caseindexnps.
            (* x < nps *)
            intros.

            Caseeq casefreeindex.
            (* free_index = n *)
            intros.

            Caseeq n_property.
            Require Import CLemmas.
            Case "0 < n < nps".
            intros.
            destruct H3.
            esplit. esplit.
            repeat vcgen.
            Case "n = nps".
            intros.
            assert(normcase: is_at_norm_spec (Int.unsigned index) adt = Some 0 \/
                             is_at_norm_spec (Int.unsigned index) adt = Some 1).
            apply permission_norm.
            omega.
            esplit. esplit.
            repeat vcgen.

            Caseeq normcase.

            (* is_at_norm adt (Int.unsigned index) = Some 0%Z *)
            intro.
            esplit. esplit.
            change 0 with (Int.unsigned Int.zero) in H5.
            repeat vcgen.

            (* Proof for I *)
            exists (nps - Int.unsigned index - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            left.
            rewrite PTree.gso.
            rewrite PTree.gso.
            assumption.
            vcgen.
            vcgen.

            (* is_at_norm adt (Int.unsigned index) = Some 1 *)
            intro.
            generalize (get_at_u_valid index H5).
            intro get_at_u_case.

            Caseeq get_at_u_case.

            (* get_at_u adt (Int.unsigned index) = Some 0 *)
            intro.
            unfold is_at_norm_spec in H5.
            rewrite ikern, ihost in H5.
            unfold get_at_u_spec in H6.
            rewrite ikern, ihost in H6.
            unfold zle_lt in *.
            repeat zdestruct.
            case_eq (ZMap.get (Int.unsigned index) (AT adt)); intros.
            rewrite H7 in H5, H6.
            destruct b.
            discriminate H6.
            destruct (ATType_dec t ATNorm).
            subst.
            assert(0 < Int.unsigned index < Int.unsigned n) by omega.
            generalize (lt_n_not_free (Int.unsigned index) n0 H8); intro.
            contradiction.
            discriminate H5.
            rewrite H7 in H5; discriminate H5.

            (* get_at_u adt (Int.unsigned index) = Some 1 *)
            intros.
            esplit. esplit.
            replace 1 with (Int.unsigned Int.one) in H5, H6.
            repeat vcgen.

            (* Proof for I *)
            exists (nps - Int.unsigned index - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            left.
            rewrite PTree.gso; repeat vcgen.
            reflexivity.


            (* free_index = nps *)
            intro tcond.
            destruct tcond as [freeind tcond].
            destruct tcond as [indleqn leind].

            Caseeq n_property.
            Case "0 < n < nps".
            intro tmpn.
            destruct tmpn as [tmpn1 tmpn2].
            esplit. esplit.
            repeat vcgen.
            assert(normcase: is_at_norm_spec (Int.unsigned index) adt = Some 0 \/
                             is_at_norm_spec (Int.unsigned index) adt = Some 1).
            apply permission_norm.
            omega.
            Caseeq normcase.

            (* is_at_norm adt (Int.unsigned index) = Some 0%Z *)
            intro.
            esplit. esplit.
            change 0 with (Int.unsigned Int.zero) in H3.
            repeat vcgen.

            (* Proof for I *)
            exists (nps - Int.unsigned index - 1).
            repeat vcgen.
            destruct tmpn2 as [n0 tmpn2].
            esplit.
            repeat vcgen.
            right.
            repeat vcgen.
            assert(Int.unsigned index <> Int.unsigned n).    
              intro.
              apply (palloc_index_invalid_norm _ n0) in H3.
              rewrite H4 in *.
              contradiction.
            omega.
            assert(LessOrEqual: 0<= x< Int.unsigned index \/ x = Int.unsigned index) by omega.
            Caseeq LessOrEqual.
            (* 0 <= x < Int.unsigned index *)
            intros.
            apply lt_n_not_free.
            omega.
            (* x = Int.unsigned index *)
            intros.
            subst x.
            apply (palloc_index_invalid_norm _ n1) in H3.
            assumption.

            (* is_at_norm adt (Int.unsigned index) = Some 1 *)
            intro.
            generalize (get_at_u_valid index H3).
            intro get_at_u_case.

            Caseeq get_at_u_case.

            (* get_at_u adt (Int.unsigned index) = Some 0 *)
            intro.
            assert(n = index).
            {
              destruct tmpn2.
              apply palloc_index_unique.
              unfold palloc_index_valid.
              split.
              esplit; eauto.
              eauto.
              apply get_and_norm; eauto.
              omega.
              omega.
            }
            subst.

            esplit. esplit.
            change 0 with (Int.unsigned Int.zero) in H4.
            change 1 with (Int.unsigned Int.one) in H3.
            repeat vcgen.

            (* Proof of I *)
            exists (nps - Int.unsigned index - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            left.
            rewrite PTree.gso; repeat vcgen.

            (* get_at_u adt (Int.unsigned index) = Some 1 *)
            intro.
            esplit. esplit. 
            change 1 with (Int.unsigned Int.one) in H3, H4.
            repeat vcgen.

            (* Proof for I *)
            exists (nps - Int.unsigned index - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            repeat vcgen.
            assert(Int.unsigned index <> Int.unsigned n).
            {
              destruct tmpn2.
              intro equal.
              rewrite <- equal in H5.
              apply (palloc_index_invalid_atget _ x) in H4.
              contradiction.
            }
            omega.
            assert(LessOrEqual: 0< x< Int.unsigned index \/ x = Int.unsigned index) by omega.
            Caseeq LessOrEqual.
            (* 0 <= x < Int.unsigned index *)
            intros.
            apply leind.
            assumption.
            (* x = Int.unsigned index *)
            intros.
            subst x.
            apply (palloc_index_invalid_atget _ n0) in H4.
            assumption.

            Case "n = nps".
            intros.

            esplit. esplit.
            repeat vcgen.
            assert(normcase: is_at_norm_spec (Int.unsigned index) adt = Some 0 \/
                             is_at_norm_spec (Int.unsigned index) adt = Some 1).
            apply permission_norm.
            omega.
            Caseeq normcase.

            (* is_at_norm adt (Int.unsigned index) = Some 0%Z *)
            intro.
            esplit. esplit.
            change 0 with (Int.unsigned Int.zero) in H4.
            repeat vcgen.

            (* Proof for I *)
            exists (nps - Int.unsigned index - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            left.
            rewrite PTree.gso; repeat vcgen.
            rewrite <- H2 in freeind.
            rewrite Int.repr_unsigned in freeind.
            assumption.

            (* is_at_norm adt (Int.unsigned index) = Some 1 *)
            intro.
            generalize (get_at_u_valid index H4).
            intro get_at_u_case.

            Caseeq get_at_u_case.

            (* get_at_u adt (Int.unsigned index) = Some 0 *)
            intro.
            unfold is_at_norm_spec in H4.
            rewrite ikern, ihost in H4.
            unfold get_at_u_spec in H5.
            rewrite ikern, ihost in H5.
            unfold zle_lt in *.
            repeat zdestruct.
            case_eq (ZMap.get (Int.unsigned index) (AT adt)); intros.
            rewrite H6 in H4, H5.
            destruct b.
            discriminate H5.
            destruct (ATType_dec t ATNorm).
            subst.
            assert(0 < Int.unsigned index < Int.unsigned n) by omega.
            generalize (lt_n_not_free (Int.unsigned index) n0 H7); intro.
            contradiction.
            discriminate H4.
            rewrite H6 in H4; discriminate H4.

            (* get_at_u adt (Int.unsigned index) = Some 1 *)
            intros.
            esplit. esplit.
            replace 1 with (Int.unsigned Int.one) in H4, H5.
            repeat vcgen.

            (* Proof for I *)
            exists (nps - Int.unsigned index - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            left.
            rewrite PTree.gso; repeat vcgen.
            rewrite <- H2 in freeind.
            rewrite Int.repr_unsigned in freeind.
            assumption.
            reflexivity.

            (* index = nps *)
            intros.
            Caseeq n_property.

            Case "0 < n < nps".
            intro tmpH.
            destruct tmpH as [nrange zget].
            esplit. esplit.
            repeat vcgen.
            destruct casefreeindex.
            eassumption.
            destruct H2.
            destruct H3.
            omega.
            discharge_cmp.
            discharge_cmp.
            discharge_cmp.
            destruct casefreeindex.
            assumption.
            destruct H3.
            destruct H4.
            rewrite H3.
            f_equal.
            f_equal.
            omega.
            discriminate H2.

            Case "n = nps".
            intro nval.
            esplit. esplit.
            repeat vcgen.
            destruct casefreeindex.
            eassumption.
            destruct H2.
            destruct H3.
            rewrite <- nval in H2.
            rewrite Int.repr_unsigned in H2.
            assumption.
            discharge_cmp.
            discharge_cmp.
            discharge_cmp.
            destruct casefreeindex.
            assumption.
            destruct H3.
            destruct H4.
            rewrite H3.
            f_equal.
            f_equal.
            rewrite <- nval.
            rewrite Int.repr_unsigned.
            reflexivity.
            discriminate H2.
          Qed.

        End Palloc_loop_proof.

        Lemma palloc_loop_correct: forall m d le n,
                                     high_level_invariant d ->
                                     init d = true ->
                                     ikern d = true ->
                                     ihost d = true ->
                                     (0 < Int.unsigned n < nps d /\ (exists n0, ZMap.get (Int.unsigned n) (AT d) = ATValid false ATNorm n0) \/ Int.unsigned n = nps d) ->
                                     (forall x n0: Z, ((0 < x < Int.unsigned n)%Z ->
                                                    ZMap.get x (AT d) <> ATValid false ATNorm n0)) ->
                                     PTree.get tnps le = Some (Vint (Int.repr(nps d))) ->
                                     PTree.get tpalloc_index le = Some (Vint (Int.repr 1)) ->
                                     PTree.get tpalloc_free_index le = Some (Vint (Int.repr(nps d))) ->
                                     exists le', exec_stmt ge (PTree.empty _) le ((m, d) : mem) (Swhile palloc_while_condition palloc_while_body) E0 le' (m, d) Out_normal /\ PTree.get tpalloc_free_index le'= Some (Vint n) /\ PTree.get tnps le' = Some (Vint (Int.repr (nps d))).
        Proof.
          intros m d le n inv init kern host nrange indvalid letnps leindex lefreeindex.
          generalize (palloc_loop_correct_aux m d n inv nrange indvalid init kern host).
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le' pre].
          destruct pre as [m' pre].
          destruct pre as [pre1 pre2].
          exists le'.
          unfold palloc_loop_body_Q in pre2.
          destruct pre2; subst.
          destruct H0.
          subst.
          auto.
          unfold palloc_loop_body_P.
          eauto.
        Qed.

        Lemma get_nps_valid: forall (m:mem) (d:RData), 
                               high_level_invariant d ->
                               init d = true ->
                               ikern d = true ->
                               ihost d = true ->
                               get_nps_spec d = Some (Int.unsigned (Int.repr (nps d))).
        Proof.
          intros.
          inv H.
          simpl in *.
          generalize (valid_nps H0); intro nps_range.
          unfold get_nps_spec.
          simpl.
          rewrite H1, H2.
          f_equal.
          rewrite Int.unsigned_repr.
          trivial.
          generalize max_unsigned_val.
          omega.
        Qed.

        Lemma palloc_body_correct: forall m d d' env le index,
                                     env = PTree.empty _ ->
                                     init d = true ->
                                     palloc_spec d = Some (d', Int.unsigned index) ->
                                     high_level_invariant d ->
                                     exists le',
                                       (exec_stmt ge env le ((m, d): mem) palloc_body E0 le' (m, d') (Out_return (Some (Vint index, tint)))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize get_nps_valid; intro npsvalid.
          intros.
          subst.
          unfold palloc_body.
          functional inversion H1; subst.
          destruct _x.
          destruct a0.

          (* destruct on palloc_loop_correct *)
          edestruct palloc_loop_correct.
          eassumption.
          eassumption.
          eassumption.
          eassumption.
          left.
          split.
          eassumption.
          assumption.
          intros.
          unfold not in *.
          intro.
          eapply n.
          eassumption.
          esplit; eassumption.
          instantiate (1 :=
            PTree.set tpalloc_free_index (Vint (Int.repr (nps d)))
              (PTree.set tpalloc_index (Vint (Int.repr 1))
                (PTree.set tnps (Vint (Int.repr (nps d)))
                  le))).
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          destruct H.
          destruct H3.
          generalize (nps_range _ H2 H0); intro.
          destruct e.
          destruct H9.

          esplit.
          repeat vcgen.
          { unfold get_nps_spec.
            rewrites.
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
          }
          { unfold set_at_u_spec; simpl.
            rewrites.
            unfold zle_lt.
            repeat zdestruct.
          }
          { unfold set_at_c_spec; simpl.
            rewrite ZMap.gss; rewrites.
            unfold zle_lt.
            repeat zdestruct.
            rewrite ZMap.set2.
            reflexivity.
          }

          destruct (first_free (AT d') (nps d')).
          destruct s; contradiction.
          generalize (nps_range d' H2 H0); intro.

          (* destruct on palloc_loop_correct *)
          edestruct palloc_loop_correct.
          eassumption.
          eassumption.
          eassumption.
          eassumption.
          right.
          erewrite <- nps_representable; eauto.
          intros.
          unfold not in *.
          intro.
          erewrite nps_representable in H7.
          eapply n; eauto.
          assumption.
          assumption.
          instantiate (1 :=
            PTree.set tpalloc_free_index (Vint (Int.repr (nps d')))
              (PTree.set tpalloc_index (Vint (Int.repr 1))
                (PTree.set tnps (Vint (Int.repr (nps d')))
                  le))).
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.

          repeat vcgen.
          destruct H7.
          destruct H9.
          esplit.
          d3 vcgen.
          repeat vcgen.
          unfold get_nps_spec; simpl; rewrites.
          erewrite <- nps_representable; eauto.

          d9 vcgen.
          repeat vcgen.
          discharge_cmp.
          repeat vcgen.
          vcgen.
          rewrite PTree.gss.
          f_equal.
          f_equal.
          rewrite H3.
          rewrite Int.repr_unsigned.
          reflexivity.
        Qed.

      End PallocBody.

      Theorem palloc_code_correct:
        spec_le (palloc ↦ palloc_spec_low) (〚palloc ↦ f_palloc 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigsteptest (palloc_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp 
                                          b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp 
                                          m'0 labd labd' (PTree.empty _)
                                          (create_undef_temps (fn_temps f_palloc))) H0.
        functional inversion H; auto.
        intro.
        destruct H3.
        repeat fbigstep_post.
      Qed.

    End PAlloc.

  End With_primitives.

End MALOPCODE.


