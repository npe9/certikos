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
(*          for the C functions implemented in the MALInit layer       *)
(*                                                                     *)
(*                        Xiongnan (Newman) Wu                         *)
(*                                                                     *)
(*                          Yale University                            *)
(*                                                                     *)
(* *********************************************************************)
Require Import TacticsForTesting.
Require Import VCGen.
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
Require Import MALInit.
Require Import ZArith.Zwf.
Require Import LoopProof.
Require Import RealParams.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import ALOpGenSpec.

Require Import AbstractDataType.
Require Import MALInitCSource.

Module MALINITCODE.

  Section With_primitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Opaque PTree.get PTree.set.

    Section Meminit.
      
      Let L: compatlayer (cdata RData) := (get_size ↦ gensem MMSize
          ⊕ is_usable ↦ gensem is_mm_usable_spec
          ⊕ get_mms ↦ gensem get_mm_s_spec
          ⊕ get_mml ↦ gensem get_mm_l_spec
          ⊕ boot_loader ↦ gensem bootloader0_spec
          ⊕ is_norm ↦ gensem is_at_norm_spec
          ⊕ set_norm ↦ gensem set_at_norm_spec
          ⊕ set_nps ↦ gensem set_nps_spec).

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Lemma size_range_valid d :  high_level_invariant d -> init d = true -> 0 < MMSize d <= Int.max_unsigned.
      Proof.
        intros.
        inv H.
        apply valid_mm_size.
        assumption.
      Qed.

      Lemma MM_s_l_valid_Z d : forall i s l, high_level_invariant d -> init d = true -> ikern d = true -> ihost d = true -> 0<= i < (MMSize d) -> get_mm_s_spec i d = Some  s -> get_mm_l_spec i d = Some l -> s >=0 /\ l > 0 /\ s + l < Int.max_unsigned.
      Proof.
        intros i s l inv initialized kern ihost sizerange getmms getmml.
        inv inv.
        unfold MM_valid in valid_mm.
        unfold MM_range in *.
        unfold get_mm_s_spec in *.
        unfold get_mm_l_spec in *.
        rewrite kern, ihost in *.
        simpl in *.
        generalize (valid_mm initialized i sizerange); intro validmm.
        destruct validmm as [s' validmm].
        destruct validmm as [l' validmm].
        destruct validmm as [p' validmm].
        destruct validmm as [zget validmm].
        destruct validmm as [sge0 validmm].
        destruct validmm as [lgt0 slrange'].
        rewrite zget in *.
        injection getmms; injection getmml; intros; subst.
        omega.
      Qed.

      Lemma MM_s_l_valid d : forall i s l, high_level_invariant d -> init d = true -> ikern d = true -> ihost d = true -> 0<= i < (MMSize d) -> get_mm_s_spec i d = Some (Int.unsigned s) -> get_mm_l_spec i d = Some (Int.unsigned l) -> Int.unsigned s + Int.unsigned l < Int.max_unsigned.
      Proof.
        intros.
        apply (MM_s_l_valid_Z d i (Int.unsigned s) (Int.unsigned l) H H0 H1 H2 H3 H4 H5).
      Qed.

      Lemma mm_valid d : forall i, high_level_invariant d -> init d = true -> ikern d = true -> ihost d = true -> 0<= i< (MMSize d) -> exists s l, get_mm_s_spec i d = Some (Int.unsigned s) /\ get_mm_l_spec i d = Some (Int.unsigned l) /\ Int.unsigned s >= 0 /\ Int.unsigned l > 0 /\ Int.unsigned s + Int.unsigned l < Int.max_unsigned.
      Proof.
        intros i inv.
        intros.
        simpl. 
        generalize inv; intro inv'.
        inv inv'.    
        unfold MM_valid in valid_mm.
        unfold MM_range in *.
        intros.
        unfold get_mm_s_spec.
        unfold get_mm_l_spec.
        simpl in *.
        generalize(valid_mm H i H2); intro.
        destruct H3 as [s tmpH].
        destruct tmpH as [l tmpH].
        destruct tmpH as [p tmpH].
        destruct tmpH as [slvalid tmpH].
        destruct tmpH as [sge0 tmpH].
        destruct tmpH as [lgt0 slrange].
        rewrite H0, H1.
        assert(getmms': get_mm_s_spec i d = Some s).
        unfold get_mm_s_spec.
        rewrite H0, H1.
        rewrite slvalid.
        trivial.
        assert(getmml': get_mm_l_spec i d = Some l).
        unfold get_mm_l_spec.
        rewrite H0, H1.
        rewrite slvalid.
        trivial.
        generalize (MM_s_l_valid_Z d i s l inv H H0 H1 H2 getmms' getmml').
        intro slmaxrange.
        exists (Int.repr s), (Int.repr l).
        rewrite Int.unsigned_repr.
        destruct (ZMap.get i (MM d)).
        injection slvalid; intros; subst.
        rewrite Int.unsigned_repr.
        auto.
        omega.
        inversion slvalid.
        omega.
      Qed.

      Lemma mm_usable_valid d : forall i, high_level_invariant d -> init d = true -> ikern d = true -> ihost d = true -> 0<= i< (MMSize d) -> exists v, is_mm_usable_spec i d = Some (Int.unsigned v) /\ (v = Int.zero \/ v = Int.one).
      Proof.
        intros i hinv.
        intros.
        generalize hinv; intro inv.
        inv inv.
        unfold MM_valid in valid_mm.
        unfold MM_range in *.
        unfold is_mm_usable_spec.
        simpl in *.
        rewrite H0, H1.
        generalize (valid_mm H i H2); intro.
        destruct H3 as [s tmpH].
        destruct tmpH as [l tmpH].
        destruct tmpH as [p tmpH].
        destruct tmpH as [valid tmpH].
        destruct tmpH.
        destruct p.
        exists Int.one.
        rewrite valid.
        auto.
        exists Int.zero.
        rewrite valid.
        auto.
      Qed.

      Lemma MM_match d : forall i j s l isnorm, 
                           high_level_invariant d -> 
                           init d = true ->
                           ikern d = true ->
                           ihost d = true ->
                           0<= j < (MMSize d) ->
                           get_mm_s_spec j d = Some (Int.unsigned s) ->
                           get_mm_l_spec j d = Some (Int.unsigned l) ->
                           kern_low <= i < kern_high ->
                           Int.unsigned s <= i * 4096 -> 
                           Int.unsigned l + Int.unsigned s >= (i + 1) * 4096 ->
                           is_mm_usable_spec j d = Some (Int.unsigned isnorm) ->
                           (Int.unsigned isnorm = 1 /\ MM_kern_valid ((MM d)) i ((MMSize d)) \/
                                                       Int.unsigned isnorm = 0 /\ ~ MM_kern_valid ((MM d)) i ((MMSize d))).
      Proof.
        intros i j s l isnorm inv.
        intros.
        generalize (mm_usable_valid d j inv H H0 H1 H2); intro.
        destruct H9 as [isnorm' tmpH].
        destruct tmpH as [H8' isnormcase].
        rewrite H8 in H8'.
        injection H8'; intro isnormeq.
        assert(isnorm = isnorm').
        rewrite <- Int.repr_unsigned.
        rewrite <- Int.repr_unsigned at 1.
        rewrite isnormeq.
        trivial.
        subst.
        unfold get_mm_s_spec in H3.
        unfold get_mm_l_spec in H4.
        unfold is_mm_usable_spec in H8.
        Caseeq isnormcase.

        (* isnorm = 0 *)
        intro.
        subst.
        right.
        repeat vcgen.
        intro.
        unfold MM_kern_valid in H9.
        destruct H9 as [i' tmpH].
        destruct tmpH as [s' tmpH].
        destruct tmpH as [l' tmpH].
        destruct tmpH as [i'range tmpH].
        destruct tmpH as [i'get tmpH].
        destruct tmpH as [s'range s'l'range].
        rewrite H0, H1 in *.
        assert(ZMap.get j ((MM d)) = MMValid (Int.unsigned s) (Int.unsigned l) MMResv).
        destruct (ZMap.get j ((MM d))).
        injection H3; injection H4; intros; subst.
        destruct p.
        inversion H8.
        trivial.
        inversion H8.
        rewrite H9 in *.
        inv inv.
        simpl in *.
        generalize (correct_mm H); intro.
        unfold MM_correct in H10.
        generalize (H10 j i' (Int.unsigned s) s' (Int.unsigned l) l' MMResv MMUsable H2 i'range H9 i'get); intro.
        unfold perm_consist in H11.
        assert(MMResv = MMUsable).
        apply H11.
        omega.
        omega.
        inversion H12.

        (* isnorm = 1 *)
        intro.
        subst.
        left.
        repeat vcgen.
        unfold MM_kern_valid.
        exists j, (Int.unsigned s), (Int.unsigned l).
        repeat vcgen.
        rewrite H0, H1 in *.
        destruct (ZMap.get j ((MM d))).
        injection H3; injection H4; intros; subst.
        destruct p.
        trivial.
        inversion H8.
        inversion H8.
      Qed.

      Lemma nps_range d : forall i, high_level_invariant d -> init d = true -> ikern d = true -> ihost d = true -> 0 <= (Z.of_nat i) < (MMSize d) -> 0 < Calculate_nps i (MM d) (MMSize d) <= maxpage.
      Proof.
        intros i inv initialized kern ihost sr.
        generalize (size_range_valid d inv initialized); intro sizerange.
        generalize (mm_valid d (Z.of_nat i) inv initialized kern ihost sr).
        induction i as [| i' IH].
        intros.
        unfold Calculate_nps.
        unfold maxs_at_i.
        change (Z.of_nat 0) with 0 in *.
        destruct H as [s tmpH].
        destruct tmpH as [l tmpH].
        destruct tmpH as [getmms tmpH].
        destruct tmpH as [getmml tmpH].
        destruct tmpH as [sge0 tmpH].
        destruct tmpH as [lgt0 slrange].
        unfold get_mm_s_spec in getmms.
        unfold get_mm_l_spec in getmml.
        rewrite kern, ihost in *.
        destruct (ZMap.get 0 ((MM d))).
        injection getmms; injection getmml; intros; subst.
        split.
        assert((Int.unsigned s + Int.unsigned l) / 4096 >= 0).
        apply Z_div_ge0.
        omega.
        omega.
        omega.
        assert((Int.unsigned s + Int.unsigned l) / 4096 < maxpage).
        apply Zdiv_lt_upper_bound.
        omega.
        assert(1048576 * 4096 > Int.max_unsigned).
        repeat autounfold; simpl.
        omega.
        omega.
        omega.
        inversion getmms.

        intros.
        unfold Calculate_nps.
        fold Calculate_nps.
        destruct H as [s tmpH].
        destruct tmpH as [l tmpH].
        destruct tmpH as [getmms tmpH].
        destruct tmpH as [getmml tmpH].
        destruct tmpH as [sge0 tmpH].
        destruct tmpH as [lgt0 slrange].
        unfold get_mm_s_spec in getmms.
        unfold get_mm_l_spec in getmml.
        rewrite kern, ihost in *.
        destruct (Z_lt_dec
                    (Calculate_nps i'
                                   ((MM d))
                                   ((MMSize d)))
                    (maxs_at_i (Z.of_nat (S i'))
                               ((MM d)))).
        unfold maxs_at_i.
        destruct (ZMap.get (Z.of_nat (S i'))).
        injection getmms; injection getmml; intros; subst.
        split.
        assert((Int.unsigned s + Int.unsigned l) / 4096 >= 0).
        apply Z_div_ge0.
        omega.
        omega.
        omega.
        assert((Int.unsigned s + Int.unsigned l) / 4096 < maxpage).
        apply Zdiv_lt_upper_bound.
        omega.
        assert(1048576 * 4096 > Int.max_unsigned).
        repeat autounfold; simpl.
        omega.
        omega.
        omega.
        inversion getmms.
        apply IH.
        split.
        apply Nat2Z.is_nonneg.
        rewrite Nat2Z.inj_succ in sr.
        unfold Z.succ in sr.
        omega.
        apply (mm_valid d (Z.of_nat i') inv initialized).
        assumption.
        assumption.
        split.
        apply Nat2Z.is_nonneg.
        rewrite Nat2Z.inj_succ in sr.
        unfold Z.succ in sr.
        omega.
      Qed.

      Local Open Scope Z_scope.

      Section MemInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (* boot_loader *)

        Variable bbootloader: block.

        Hypothesis hbootloader1 : Genv.find_symbol ge boot_loader = Some bbootloader.
        Hypothesis hbootloader2 : Genv.find_funct_ptr ge bbootloader = Some (External (EF_external boot_loader (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).
        
        (** get_mms *)

        Variable bgetmms: block.

        Hypothesis hget_mms1 : Genv.find_symbol ge get_mms = Some bgetmms. 
        
        Hypothesis hget_mms2 : Genv.find_funct_ptr ge bgetmms = Some (External (EF_external get_mms (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** get_mml *)

        Variable bgetmml: block.

        Hypothesis hget_mml1 : Genv.find_symbol ge get_mml = Some bgetmml. 
        
        Hypothesis hget_mml2 : Genv.find_funct_ptr ge bgetmml = Some (External (EF_external get_mml (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** is_usable *)

        Variable bisusable: block.

        Hypothesis his_usable1 : Genv.find_symbol ge is_usable = Some bisusable. 
        
        Hypothesis his_usable2 : Genv.find_funct_ptr ge bisusable = Some (External (EF_external is_usable (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** set_norm *)

        Variable batsetnorm: block.

        Hypothesis hset_norm1 : Genv.find_symbol ge set_norm = Some batsetnorm. 
        
        Hypothesis hset_norm2 : Genv.find_funct_ptr ge batsetnorm = Some (External (EF_external set_norm (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** set_nps *)

        Variable bsetnps: block.

        Hypothesis hset_nps1 : Genv.find_symbol ge set_nps = Some bsetnps. 
        
        Hypothesis hset_nps2 : Genv.find_funct_ptr ge bsetnps = Some (External (EF_external set_nps (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).


        (** get_size *)

        Variable bgetsize: block.

        Hypothesis hget_size1 : Genv.find_symbol ge get_size = Some bgetsize. 
        
        Hypothesis hget_size2 : Genv.find_funct_ptr ge bgetsize = Some (External (EF_external get_size (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).


        Section nps_loop_proof.

          Variable minit: memb.
          Variable adt: RData.
          Notation AT := (AT adt).
          Notation size := (MMSize adt).

          Hypothesis hinv: high_level_invariant adt. 
          Hypothesis initialized: init adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ihost: ihost adt = true.

          Definition nps_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get tsize le = Some (Vint (Int.repr size)) /\
            PTree.get ti le = Some (Vint (Int.zero)) /\
            PTree.get tnps le = Some (Vint (Int.zero)) /\
            m = (minit, adt).

          Definition nps_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            exists nps,
              PTree.get tsize le = Some (Vint (Int.repr size)) /\
              PTree.get tnps le = Some (Vint (Int.repr nps)) /\
              nps = Calculate_nps (Z.to_nat (size - 1)) (MM adt) size /\
              m = (minit, adt).

          Lemma nps_loop_correct_aux : LoopProofSimpleWhile.t nps_while_condition nps_while_body ge (PTree.empty _) (nps_loop_body_P) (nps_loop_body_Q).
          Proof.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i nps,
                                    PTree.get tsize le = Some (Vint (Int.repr size)) /\
                                    PTree.get ti le = Some (Vint i) /\
                                    PTree.get tnps le = Some (Vint nps) /\
                                    0 <= Int.unsigned i <= size /\
                                    (Int.unsigned i = 0 /\ Int.unsigned nps = 0 \/ Int.unsigned i > 0 /\ Int.unsigned nps = Calculate_nps (Z.to_nat (Int.unsigned i - 1)) (MM adt) size) /\ 
                                    w = size - Int.unsigned i /\
                                    0 < size <= Int.max_unsigned /\
                                    m = (minit, adt)
              )
            .
            apply Zwf_well_founded.
            unfold nps_loop_body_P.
            generalize (size_range_valid adt hinv initialized); intro sizerange.
            assert(0 < size <= Int.max_unsigned) by assumption.
            intros.
            destruct H0 as [tsizele tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tnpsle meqminit].
            subst.
            (* P => I *)
            esplit. esplit. esplit.
            repeat vcgen.
            autorewritearith.
            (* I => I *)
            generalize max_unsigned_val; intro muval.
            unfold nps_while_condition.
            unfold nps_while_body.
            unfold nps_loop_body_Q.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [nps tmpH].
            destruct tmpH as [tsizele tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tnpsle tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [npsval tmpH].
            destruct tmpH as [w tmpH].
            destruct tmpH as [sizerange meqminit].
            subst.
            assert(icase: Int.unsigned i < size \/ Int.unsigned i = size) by omega.
            Caseeq icase.

            (* i < size *)
            intro iltsize.
            exists (Vint Int.one), true.
            repeat vcgen.

            assert(ipre: 0<= Int.unsigned i< size) by omega.
            generalize(mm_valid adt (Int.unsigned i) hinv initialized ikern ihost ipre); intro tmpH.
            assert(ivalidu: 0 <= Int.unsigned i <= Int.max_unsigned) by omega.
            subst.
            destruct tmpH as [s0 tmpH].
            destruct tmpH as [l0 tmpH].
            destruct tmpH as [mmsvalid tmpH].
            destruct tmpH as [mmlvalid tmpH].
            destruct tmpH as [sgeq0 tmpH].
            destruct tmpH as [lgt0 slrange].
            generalize(MM_s_l_valid adt (Int.unsigned i) s0 l0 hinv initialized ikern ihost ipre mmsvalid mmlvalid).
            intro s_l_range.
            (* following asserts are mainly for optimization to save memory by not proving a new goal with omega everytime *)
            assert(svalidu: 0 <= Int.unsigned s0 <= Int.max_unsigned) by omega.
            assert(lvalidu: 0 <= Int.unsigned l0 <= Int.max_unsigned) by omega.
            assert(splvalidu: 0 <= Int.unsigned s0 + Int.unsigned l0 <= Int.max_unsigned) by omega.
            assert (uopt1: 0 <= (Int.unsigned s0 + Int.unsigned l0) / 4096) by (
                                                                                rewrite <- Int.unsigned_repr with (z:= (Int.unsigned s0 + Int.unsigned l0));
                                                                                solve_unsigned_range 4096 (Int.repr (Int.unsigned s0 + Int.unsigned l0));
                                                                                omega).
            assert (uopt2: (Int.unsigned s0 + Int.unsigned l0) / 4096 <= Int.max_unsigned) by (
                                                                                               rewrite <- Int.unsigned_repr with (z:= (Int.unsigned s0 + Int.unsigned l0));
                                                                                               solve_unsigned_range 4096 (Int.repr (Int.unsigned s0 + Int.unsigned l0));
                                                                                               omega).
            assert (uopt3: 0 <= (Int.unsigned s0 + Int.unsigned l0) / 4096 + 1) by omega.
            assert (uopt4: (Int.unsigned s0 + Int.unsigned l0) / 4096 + 1 <= Int.max_unsigned) by (solve_unsigned_range_lt 4096 (Int.unsigned s0 + Int.unsigned l0)).

            assert(maxscase: (Int.unsigned s0 + Int.unsigned l0) / PgSize + 1 > Int.unsigned nps \/ (Int.unsigned s0 + Int.unsigned l0) / PgSize + 1 <= Int.unsigned nps) by omega.

            Caseeq maxscase.
            (* maxs > nps *)
            intros maxscond.
            esplit. exists (minit, adt).
            repeat vcgen.

            (* proof for I *)
            exists (size - Int.unsigned i - 1).
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            Caseeq npsval.
            (* i = 0 *)
            intro npscond.
            destruct npscond as [ieq0 npseq0].
            right.
            rewrite ieq0 in *.
            split.
            omega.
            unfold get_mm_s_spec in mmsvalid.
            unfold get_mm_l_spec in mmlvalid.
            rewrite ikern, ihost in *.
            simpl in *.
            unfold maxs_at_i.
            destruct(ZMap.get 0 (MM adt)).
            injection mmsvalid.
            injection mmlvalid.
            intros.
            subst.
            trivial.
            inversion mmsvalid.
            (* i > 0 /\ nps = Calculate_nps i-1 mm size *)
            intro npscond.
            right.
            destruct npscond as [igt0 IH].
            split.
            omega.
            assert(tmpeq: Int.unsigned i + 1 - 1 = Int.unsigned i - 1 + 1) by omega.
            rewrite tmpeq; clear tmpeq.
            change (Int.unsigned i - 1 + 1) with (Z.succ (Int.unsigned i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(Int.unsigned i - 1)).
            unfold Calculate_nps.
            fold Calculate_nps.
            rewrite <- IH.
            rewrite <- Z2Nat.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            assert(tmpeq: Int.unsigned i - 1 + 1 = Int.unsigned i) by omega.
            rewrite tmpeq; clear tmpeq.
            unfold maxs_at_i.
            unfold get_mm_s_spec in mmsvalid.
            unfold get_mm_l_spec in mmlvalid.
            rewrite ikern, ihost in *.
            destruct(ZMap.get (Int.unsigned i) (MM adt)).
            injection mmsvalid; injection mmlvalid; intros; subst.
            destruct(Z_lt_dec (Int.unsigned nps) ((Int.unsigned s0 + Int.unsigned l0) / PgSize + 1)).
            trivial.
            omega.
            inversion mmsvalid.
            unfold Z.succ.
            omega.
            omega.
            omega.
            
            (* maxs <= nps *)
            intro maxscond.
            esplit. esplit.
            repeat vcgen.
            (* proof for I *)
            exists (size - Int.unsigned i - 1).
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            Caseeq npsval.
            (* i = 0 *)
            intros npscond.
            destruct npscond as [ieq0 npseq0].
            rewrite ieq0 in *.
            rewrite npseq0 in *.
            assert(divgeq0: (Int.unsigned s0 + Int.unsigned l0) / PgSize >= 0).
            apply Z_div_ge0.
            omega.
            omega.
            right.
            split.
            omega.
            simpl.
            unfold maxs_at_i.
            unfold get_mm_s_spec in mmsvalid.
            unfold get_mm_l_spec in mmlvalid.
            rewrite ikern, ihost in *.
            destruct (ZMap.get 0 (MM adt)).
            injection mmsvalid; injection mmlvalid; intros; subst.
            omega.
            trivial.
            (* i > 0 /\ nps = Calculate_nps (i - 1) mm size *)
            intros npscond.
            destruct npscond as [igt0 npspre].
            right.
            split.
            omega.
            assert(tmpeq: Int.unsigned i + 1 - 1 = Int.unsigned i - 1 + 1) by omega.
            rewrite tmpeq; clear tmpeq.
            change (Int.unsigned i - 1 + 1) with (Z.succ (Int.unsigned i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(Int.unsigned i - 1)).
            unfold Calculate_nps.
            fold Calculate_nps.
            rewrite <- npspre.
            rewrite <- Z2Nat.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            assert(tmpeq: Int.unsigned i - 1 + 1 = Int.unsigned i) by omega.
            rewrite tmpeq; clear tmpeq.
            unfold maxs_at_i.
            unfold get_mm_s_spec in mmsvalid.
            unfold get_mm_l_spec in mmlvalid.
            rewrite ikern, ihost in *.
            destruct(ZMap.get (Int.unsigned i) (MM adt)).
            injection mmsvalid; injection mmlvalid; intros; subst.
            destruct(Z_lt_dec (Int.unsigned nps) ((Int.unsigned s0 + Int.unsigned l0) / PgSize + 1)).
            omega.
            trivial.
            inversion mmsvalid.
            unfold Z.succ.
            omega.
            omega.
            omega.

            (* i = size *)
            intro sizecond.
            exists (Vint Int.zero), false.
            repeat vcgen.
            exists (Int.unsigned nps).
            Caseeq npsval.
            (* i = 0 /\ nps = 0*)
            intro npscond.
            destruct npscond as [ieq0 npseq0].
            repeat vcgen.
            (* i > 0 /\ nps = Calculate_nps (i - 1) mm size *)
            intro npscond.
            destruct npscond as [igt0 npspre].
            repeat vcgen.
            rewrite <- sizecond at 1.
            auto.
          Qed.

        End nps_loop_proof.

        Lemma nps_loop_correct: forall (m: memb) (d: RData) le size,
                                  high_level_invariant d ->
                                  init d = true ->
                                  ikern d = true ->
                                  ihost d = true ->
                                  size = (MMSize d) ->
                                  PTree.get tsize le = Some (Vint (Int.repr size)) ->
                                  PTree.get ti le = Some (Vint (Int.zero)) ->
                                  PTree.get tnps le = Some (Vint (Int.zero)) ->
                                  exists le' nps, 
                                    exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile nps_while_condition nps_while_body) E0 le' (m, d) Out_normal /\
                                    PTree.get tsize le' = Some (Vint (Int.repr size)) /\
                                    PTree.get tnps le' = Some (Vint (Int.repr nps)) /\
                                    nps = Calculate_nps (Z.to_nat (size - 1)) (MM d) size.
        Proof.
          intros m d le size hinv initialized kern ihost sizeeq tsizele tile tnpssle.
          generalize (nps_loop_correct_aux m d hinv initialized kern ihost).
          unfold nps_loop_body_P.
          unfold nps_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le' tmppre].
          destruct tmppre as [m' tmppre].
          destruct tmppre as [stmp tmppre].
          destruct tmppre as [nps tmppre].
          destruct tmppre as [tsizele' tmppre].
          destruct tmppre as [tnpsle' tmppre].
          destruct tmppre as [npsval msubst].
          exists le', nps.
          subst.
          repeat vcgen.
          subst.
          repeat vcgen.
        Qed.

        Section inner_loop_proof.

          Variable minit: memb.
          Variable adt: RData.
          Variable i: Z.
          Notation AT := (AT adt).
          Notation size := (MMSize adt).
          Notation nps := (nps adt).

          Hypothesis hinv: high_level_invariant adt.
          Hypothesis initialized: init adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ihost: ihost adt = true.

          Definition inner_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get ti le = Some (Vint (Int.repr i)) /\
            PTree.get tj le = Some (Vint (Int.zero)) /\
            PTree.get tflag le = Some (Vint (Int.zero)) /\
            PTree.get tisnorm le = Some (Vint (Int.zero)) /\
            PTree.get tsize le = Some (Vint (Int.repr size)) /\
            PTree.get tnps le = Some (Vint (Int.repr nps)) /\
            kern_low <= i < kern_high /\
            m = (minit, adt).

          Definition inner_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            exists flag isnorm,
              PTree.get ti le = Some (Vint (Int.repr i)) /\
              PTree.get tflag le = Some (Vint (Int.repr flag)) /\
              PTree.get tisnorm le = Some (Vint (Int.repr isnorm)) /\
              PTree.get tsize le = Some (Vint (Int.repr size)) /\
              PTree.get tnps le = Some (Vint (Int.repr nps)) /\
              ((flag = 1 /\ isnorm = 1 /\ MM_kern_valid (MM adt) i size) \/ ((flag = 1 /\ isnorm = 0 \/ flag = 0) /\ ~MM_kern_valid ((MM adt)) i ((MMSize adt)))) /\
              m = (minit, adt).


          Lemma inner_loop_correct_aux_j0_flag0: forall le j s0 l0 flag isnorm usable, 
                                                   j = 0 -> flag = 0 -> 
                                                   get_mm_s_spec j adt = Some (Int.unsigned s0) ->
                                                   get_mm_l_spec j adt = Some (Int.unsigned l0) ->
                                                   is_mm_usable_spec j adt = Some (Int.unsigned usable) ->
                                                   Int.unsigned s0 >= 0 ->
                                                   Int.unsigned l0 > 0 ->
                                                   Int.unsigned s0 + Int.unsigned l0 < Int.max_unsigned ->
                                                   Int.unsigned s0 <= i * PgSize \/ Int.unsigned s0 > i * PgSize ->
                                                   Int.unsigned l0 + Int.unsigned s0 >= (i + 1) * PgSize \/ Int.unsigned l0 + Int.unsigned s0 < (i + 1) * PgSize ->
                                                   kern_low <= i < kern_high ->
                                                   0 <= j < size ->
                                                   0 < size <= Int.max_unsigned ->
                                                   le ! ti = Some (Vint (Int.repr i)) ->
                                                   le ! tj = Some (Vint (Int.repr j)) ->
                                                   le ! tflag = Some (Vint (Int.repr flag)) ->
                                                   le ! tisnorm = Some (Vint isnorm) ->
                                                   le ! tsize = Some (Vint (Int.repr size)) ->
                                                   le ! tnps = Some (Vint (Int.repr nps)) ->
                                                   exists (le' : temp_env) (m' : mem),
                                                     exec_stmt ge (PTree.empty _) le ((minit, adt): mem) inner_while_body E0 le' m' Out_normal /\
                                                     (exists n' : Z,
                                                        (0 <= size - j /\ n' < size - j) /\
                                                        (exists (j0 flag0 : Z) (isnorm0 s1 l1 : int),
                                                           le' ! ti = Some (Vint (Int.repr i)) /\
                                                           le' ! tj = Some (Vint (Int.repr j0)) /\
                                                           le' ! tflag = Some (Vint (Int.repr flag0)) /\
                                                           le' ! tisnorm = Some (Vint isnorm0) /\
                                                           le' ! tsize = Some (Vint (Int.repr size)) /\
                                                           le' ! tnps = Some (Vint (Int.repr nps)) /\
                                                           0 <= j0 <= size /\
                                                           (j0 = 0 /\ flag0 = 0 \/
                                                                      j0 > 0 /\
                                                            le' ! ts = Some (Vint s1) /\
                                                            le' ! tl = Some (Vint l1) /\
                                                            get_mm_s_spec (j0 - 1) adt =
                                                            Some (Int.unsigned s1) /\
                                                            get_mm_l_spec (j0 - 1) adt =
                                                            Some (Int.unsigned l1) /\
                                                            is_mm_usable_spec (j0 - 1) adt =
                                                            Some (Int.unsigned isnorm0) /\
                                                            (flag0 = 0 /\
                                                             (Int.unsigned s1 > i * 4096 \/
                                                              Int.unsigned l1 + Int.unsigned s1 < (i + 1) * 4096) \/
                                                             flag0 = 1 /\
                                                             Int.unsigned s1 <= i * 4096 /\
                                                             Int.unsigned l1 + Int.unsigned s1 >= (i + 1) * 4096)) /\
                                                           (forall (j' : Z) (s' l' : int),
                                                              0 <= j' < j0 - 1 ->
                                                              get_mm_s_spec j' adt =
                                                              Some (Int.unsigned s') ->
                                                              get_mm_l_spec j' adt =
                                                              Some (Int.unsigned l') ->
                                                              Int.unsigned s' > i * 4096 \/
                                                              Int.unsigned l' + Int.unsigned s' < (i + 1) * 4096) /\
                                                           n' = size - j0 /\
                                                           kern_low <= i < kern_high /\ 0 < size <= Int.max_unsigned /\ m' = (minit, adt))).
          Proof.
            intros le j s0 l0 flag isnorm usable jeq0 flageq0 getmms getmml usablevalid s0ge0 l0gt0 slrange firstcondcase secondcondcase irange jrange sizerange.
            intros.
            generalize max_unsigned_val; intro muval.
            assert(svalidu: 0 <= Int.unsigned s0 <= Int.max_unsigned) by omega.
            assert(lvalidu: 0 <= Int.unsigned l0 <= Int.max_unsigned) by omega.
            assert(splvalidu: 0 <= Int.unsigned s0 + Int.unsigned l0 <= Int.max_unsigned) by omega.
            unfold inner_while_body.
            
            Caseeq firstcondcase.
            (* firstcondition = true *)
            intro firstcond.
            Caseeq secondcondcase.
            (* secondcondition = true *)
            intro secondcond.
            esplit. esplit.
            repeat vcgen.

            (* proof for I *)
            exists (size - j - 1).
            repeat vcgen.
            esplit. esplit. esplit. esplit. esplit. 
            repeat vcgen.
            right.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq; clear tmpeq.
            repeat vcgen.
            (* secondcondition = false *)
            intro secondcond.
            esplit. esplit.
            repeat vcgen.
            exists (size - j - 1).
            repeat vcgen.
            esplit. esplit. esplit. esplit. esplit. 
            repeat vcgen.
            right.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq; clear tmpeq.
            repeat vcgen.
            (* firstcondition = false *)
            intro fisrtcond.
            esplit. esplit.
            repeat vcgen.
            exists (size - j - 1).
            repeat vcgen.
            esplit. esplit. esplit. esplit. esplit.
            repeat vcgen.
            right.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq; clear tmpeq.
            repeat vcgen.
          Qed.

          Lemma inner_loop_correct_aux_jgt0_flag0: forall le j s0 l0 s l flag isnorm usable, 
                                                     j > 0 -> flag = 0 -> 
                                                     get_mm_s_spec j adt = Some (Int.unsigned s0) ->
                                                     get_mm_l_spec j adt = Some (Int.unsigned l0) ->
                                                     is_mm_usable_spec j adt = Some (Int.unsigned usable) ->
                                                     Int.unsigned s0 >= 0 ->
                                                     Int.unsigned l0 > 0 ->
                                                     Int.unsigned s0 + Int.unsigned l0 < Int.max_unsigned ->
                                                     Int.unsigned s0 <= i * PgSize \/ Int.unsigned s0 > i * PgSize ->
                                                     Int.unsigned l0 + Int.unsigned s0 >= (i + 1) * PgSize \/ Int.unsigned l0 + Int.unsigned s0 < (i + 1) * PgSize ->
                                                     kern_low <= i < kern_high ->
                                                     0 <= j < size ->
                                                     0 < size <= Int.max_unsigned ->
                                                     (forall (j' : Z) (s' l' : int),
                                                        0 <= j' < j - 1 ->
                                                        get_mm_s_spec j' adt =
                                                        Some (Int.unsigned s') ->
                                                        get_mm_l_spec j' adt =
                                                        Some (Int.unsigned l') ->
                                                        Int.unsigned s' > i * 4096 \/
                                                        Int.unsigned l' + Int.unsigned s' < (i + 1) * 4096) ->
                                                     get_mm_s_spec (j - 1) adt = Some (Int.unsigned s) ->
                                                     get_mm_l_spec (j - 1) adt = Some (Int.unsigned l) ->
                                                     is_mm_usable_spec (j - 1) adt = Some (Int.unsigned isnorm) ->
                                                     Int.unsigned s > i * 4096 \/ Int.unsigned l + Int.unsigned s < (i + 1) * 4096 ->
                                                     le ! ti = Some (Vint (Int.repr i)) ->
                                                     le ! tj = Some (Vint (Int.repr j)) ->
                                                     le ! tflag = Some (Vint (Int.repr flag)) ->
                                                     le ! tisnorm = Some (Vint isnorm) ->
                                                     le ! tsize = Some (Vint (Int.repr size)) ->
                                                     le ! tnps = Some (Vint (Int.repr nps)) ->
                                                     le ! ts = Some (Vint s) ->
                                                     le ! tl = Some (Vint l) ->
                                                     exists (le' : temp_env) (m' : mem),
                                                       exec_stmt ge (PTree.empty _) le ((minit, adt): mem) inner_while_body E0 le' m' Out_normal /\
                                                       (exists n' : Z,
                                                          (0 <= size - j /\ n' < size - j) /\
                                                          (exists (j0 flag0 : Z) (isnorm0 s1 l1 : int),
                                                             le' ! ti = Some (Vint (Int.repr i)) /\
                                                             le' ! tj = Some (Vint (Int.repr j0)) /\
                                                             le' ! tflag = Some (Vint (Int.repr flag0)) /\
                                                             le' ! tisnorm = Some (Vint isnorm0) /\
                                                             le' ! tsize = Some (Vint (Int.repr size)) /\
                                                             le' ! tnps = Some (Vint (Int.repr nps)) /\
                                                             0 <= j0 <= size /\
                                                             (j0 = 0 /\ flag0 = 0 \/
                                                                        j0 > 0 /\
                                                              le' ! ts = Some (Vint s1) /\
                                                              le' ! tl = Some (Vint l1) /\
                                                              get_mm_s_spec (j0 - 1) adt =
                                                              Some (Int.unsigned s1) /\
                                                              get_mm_l_spec (j0 - 1) adt =
                                                              Some (Int.unsigned l1) /\
                                                              is_mm_usable_spec (j0 - 1) adt =
                                                              Some (Int.unsigned isnorm0) /\
                                                              (flag0 = 0 /\
                                                               (Int.unsigned s1 > i * 4096 \/
                                                                Int.unsigned l1 + Int.unsigned s1 < (i + 1) * 4096) \/
                                                               flag0 = 1 /\
                                                               Int.unsigned s1 <= i * 4096 /\
                                                               Int.unsigned l1 + Int.unsigned s1 >= (i + 1) * 4096)) /\
                                                             (forall (j' : Z) (s' l' : int),
                                                                0 <= j' < j0 - 1 ->
                                                                get_mm_s_spec j' adt =
                                                                Some (Int.unsigned s') ->
                                                                get_mm_l_spec j' adt =
                                                                Some (Int.unsigned l') ->
                                                                Int.unsigned s' > i * 4096 \/
                                                                Int.unsigned l' + Int.unsigned s' < (i + 1) * 4096) /\
                                                             n' = size - j0 /\
                                                             kern_low <= i < kern_high /\ 0 < size <= Int.max_unsigned /\ m' = (minit, adt))).
          Proof.
            intros le j s0 l0 s l flag isnorm usable jgt0 flageq0 mmsvalid mmlvalid usablevalid s0ge0 l0gt0 slrange firstcondcase secondcondcase irange jrange sizerange jpre getmms getmml isuable slcase.
            intros.
            generalize max_unsigned_val; intro muval.
            assert(svalidu: 0 <= Int.unsigned s0 <= Int.max_unsigned) by omega.
            assert(lvalidu: 0 <= Int.unsigned l0 <= Int.max_unsigned) by omega.
            assert(splvalidu: 0 <= Int.unsigned s0 + Int.unsigned l0 <= Int.max_unsigned) by omega.
            unfold inner_while_body.

            Caseeq firstcondcase.
            (* firstcondition = true *)
            intro firstcond.
            Caseeq secondcondcase.
            (* secondcondition = true *)
            intro secondcond.
            esplit. esplit.
            repeat vcgen.
            (* proof for I *)
            exists (size - j - 1).
            repeat vcgen.
            esplit. esplit. esplit. esplit. esplit.
            repeat vcgen.
            right.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq; clear tmpeq.
            repeat vcgen.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq in H7; clear tmpeq.
            assert(j'case: 0 <= j' < j - 1 \/ j' = j - 1) by omega.
            Caseeq j'case.
            (* 0 <= j' < j - 1 *)
            intros.
            apply (jpre j' s' l'); try assumption.
            (* j' = j - 1 *)
            intros.
            subst.
            simpl in H8, H9.
            rewrite H8 in getmms.
            rewrite H9 in getmml.
            injection getmms; injection getmml; intros; subst.
            rewrite H10, H11.
            assumption.
            
            (* secondcondition = false *)
            intro secondcond.
            esplit. esplit.
            repeat vcgen.
            exists (size - j - 1).
            repeat vcgen.
            esplit. esplit. esplit. esplit. esplit.
            repeat vcgen.
            right.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq; clear tmpeq.
            repeat vcgen.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq in H7; clear tmpeq.
            assert(j'case: 0 <= j' < j - 1 \/ j' = j - 1) by omega.
            Caseeq j'case.
            (* 0 <= j' < j - 1 *)
            intros.
            apply (jpre j' s' l'); try assumption.
            (* j' = j - 1 *)
            intros.
            subst.
            simpl in H8, H9.
            rewrite H8 in getmms.
            rewrite H9 in getmml.
            injection getmms; injection getmml; intros; subst.
            rewrite H10, H11.
            assumption.
            
            (* firstcondition = false *)
            intro fisrtcond.
            esplit. esplit.
            repeat vcgen.
            exists (size - j - 1).
            repeat vcgen.
            esplit. esplit. esplit. esplit. esplit.
            repeat vcgen.
            right.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq; clear tmpeq.
            repeat vcgen.
            assert(tmpeq: j + 1 - 1 = j) by omega; rewrite tmpeq in H7; clear tmpeq.
            assert(j'case: 0 <= j' < j - 1 \/ j' = j - 1) by omega.
            Caseeq j'case.
            (* 0 <= j' < j - 1 *)
            intros.
            apply (jpre j' s' l'); try assumption.
            (* j' = j - 1 *)
            intros.
            subst.
            simpl in H8, H9.
            rewrite H8 in getmms.
            rewrite H9 in getmml.
            injection getmms; injection getmml; intros; subst.
            rewrite H10, H11.
            assumption.
          Qed.


          Lemma inner_loop_correct_aux : LoopProofSimpleWhile.t inner_while_condition inner_while_body ge (PTree.empty _) (inner_loop_body_P) (inner_loop_body_Q).
          Proof.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun (le: temp_env) (m: mem) (w: Z) => exists j flag isnorm s l,
                                                            PTree.get ti le = Some (Vint (Int.repr i)) /\
                                                            PTree.get tj le = Some (Vint (Int.repr j)) /\
                                                            PTree.get tflag le = Some (Vint (Int.repr flag)) /\
                                                            PTree.get tisnorm le = Some (Vint isnorm) /\
                                                            PTree.get tsize le = Some (Vint (Int.repr size)) /\
                                                            PTree.get tnps le = Some (Vint (Int.repr nps)) /\
                                                            0<= j <= size /\
                                                            (j = 0 /\ flag = 0 \/ (j > 0 /\
                                                                                   PTree.get ts le = Some (Vint s) /\
                                                                                   PTree.get tl le = Some (Vint l) /\
                                                                                   get_mm_s_spec (j - 1) adt = Some (Int.unsigned s) /\
                                                                                   get_mm_l_spec (j - 1) adt = Some (Int.unsigned l) /\
                                                                                   is_mm_usable_spec (j - 1) adt = Some (Int.unsigned isnorm) /\
                                                                                   (flag = 0 /\ (Int.unsigned s > i * PgSize \/ Int.unsigned l + Int.unsigned s < (i + 1) * PgSize) \/ flag = 1 /\ Int.unsigned s <= i * PgSize /\ Int.unsigned l + Int.unsigned s >= (i + 1) * PgSize)
                                                            )) /\
                                                            (forall j' s' l', 0 <= j' < j - 1 -> 
                                                                              get_mm_s_spec (j') adt = Some (Int.unsigned s') ->
                                                                              get_mm_l_spec (j') adt = Some (Int.unsigned l') ->
                                                                              (Int.unsigned s' > i * PgSize \/ Int.unsigned l' + Int.unsigned s' < (i + 1) * PgSize)) /\
                                                            w = size - j /\
                                                            kern_low <= i < kern_high /\
                                                            0 < size <= Int.max_unsigned /\
                                                            m = (minit, adt)
              )
            .
            apply Zwf_well_founded.
            unfold inner_loop_body_P.
            generalize(size_range_valid adt hinv initialized); intro tmpsr.
            assert(sizerange: 0 < size <= Int.max_unsigned) by assumption.
            intros.
            destruct H as [tile tmpH].
            destruct tmpH as [tjle tmpH].
            destruct tmpH as [tflagle tmpH].
            destruct tmpH as [tisnormle tmpH].
            destruct tmpH as [tsizele tmpH].
            destruct tmpH as [tnpsle tmpH].
            destruct tmpH as [irange msubst].
            subst.
            esplit. esplit. esplit. esplit. esplit. esplit. 
            (* P => I *)
            repeat vcgen.
            (* I=> I *)
            generalize max_unsigned_val; intro umval.
            unfold inner_loop_body_P.
            unfold inner_loop_body_Q.
            unfold inner_while_condition.
            unfold inner_while_body.
            intros.
            destruct H as [j tmpH].
            destruct tmpH as [flag tmpH].
            destruct tmpH as [isnorm tmpH].
            destruct tmpH as [s tmpH].
            destruct tmpH as [l tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tjle tmpH].
            destruct tmpH as [tflagle tmpH].
            destruct tmpH as [tisnormle tmpH].
            destruct tmpH as [tsizele tmpH].
            destruct tmpH as [tnpsle tmpH].
            destruct tmpH as [tmpjrange tmpH].
            destruct tmpH as [jrange tmpH].
            destruct tmpH as [jpre tmpH].
            destruct tmpH as [nval tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [sizerange msubst].
            destruct tmpjrange as [jge0 jlesize].
            subst.
            apply Zle_lt_or_eq in jlesize.
            
            Caseeq jlesize.

            (* j < size *)
            intro jltsize.
            assert(tmpjpre: 0 <= j < size) by omega.
            generalize(mm_usable_valid adt j hinv initialized ikern ihost tmpjpre); intro tmpH.
            assert(jvalidu: 0 <= j < Int.max_unsigned) by omega.
            destruct tmpH as [usable tmpH].
            destruct tmpH as [usablevalid usableval].
            generalize(mm_valid adt j hinv initialized ikern ihost tmpjpre); intro tmpH.
            destruct tmpH as [s0 tmpH].
            destruct tmpH as [l0 tmpH].
            destruct tmpH as [mmsvalid tmpH].
            destruct tmpH as [mmlvalid tmpH].
            destruct tmpH as [s0ge0 tmpH].
            destruct tmpH as [l0gt0 slrange].

            assert(firstcondcase: Int.unsigned s0 <= i * PgSize \/ Int.unsigned s0 > i * PgSize) by omega.
            assert(secondcondcase: Int.unsigned l0 + Int.unsigned s0 >= (i + 1) * PgSize \/ Int.unsigned l0 + Int.unsigned s0 < (i + 1) * PgSize) by omega. 
            Caseeq jrange.
            (* j = 0 /\ flag = 0*)
            intro jcond.
            destruct jcond as [jeq0 flageq0].
            exists (Vint (Int.one)), true.
            repeat vcgen.
            apply (inner_loop_correct_aux_j0_flag0 le j s0 l0 flag isnorm usable); try (assumption || omega).

            (* j > 0 *)
            intro jcond.
            destruct jcond as [jgt0 tmpcond].
            destruct tmpcond as [tsle tmpcond].
            destruct tmpcond as [tlle tmpcond].
            destruct tmpcond as [getmms tmpcond].
            destruct tmpcond as [getmml tmpcond].
            destruct tmpcond as [isusable flagcase].    
            Caseeq flagcase.
            (* flag = 0 *)
            intro flageq0.
            destruct flageq0 as [flageq0 sl].
            exists (Vint (Int.one)), true.
            repeat vcgen.
            idtac.
            apply (inner_loop_correct_aux_jgt0_flag0 le j s0 l0 s l flag isnorm usable); try (assumption || omega).

            (* flag = 1 /\ condition holds *)
            intro tmpcond.
            destruct tmpcond as [flageq1 tmpcond].
            destruct tmpcond as [firstcond secondcond].
            exists (Vint (Int.zero)), false.
            repeat vcgen.
            exists 1, (Int.unsigned isnorm).
            subst.
            repeat vcgen.
            assert(tmpjpre': 0 <= j - 1 < size) by omega.
            generalize (MM_match adt i (j - 1) s l isnorm hinv initialized ikern ihost tmpjpre' getmms getmml irange firstcond secondcond isusable).
            intro mmmatch.
            Caseeq mmmatch; intros.
            left; auto.
            right.
            destruct H0.
            split.
            left.
            split.
            trivial.
            assumption.
            assumption.

            (* j = size *)
            intro jeqsize.
            exists (Vint (Int.zero)), false.
            repeat vcgen.
            exists flag, (Int.unsigned isnorm).
            repeat vcgen.
            subst.
            destruct jrange.
            destruct H0.
            omega.
            destruct H0 as [sizegt0 tmpcond].
            destruct tmpcond as [tsle tmpcond].
            destruct tmpcond as [tlle tmpcond].
            destruct tmpcond as [getmms tmpcond].
            destruct tmpcond as [getmml tmpcond].
            destruct tmpcond as [isusable flagcase]. 
            destruct flagcase.
            (* flag = 0 *)
            destruct H0.
            subst.
            right.
            split.
            right.
            trivial.
            intro.
            unfold MM_kern_valid in H0.
            destruct H0 as [i' tmpH].
            destruct tmpH as [s' tmpH].
            destruct tmpH as [l' tmpH].
            destruct tmpH as [i'range tmpH].
            destruct tmpH as [i'get tmpH].
            destruct tmpH as [s'range s'l'range].
            assert(0 <= i' < MMSize adt - 1 \/ i' = MMSize adt - 1) by omega.
            destruct H0.
            assert(get_mm_s_spec i' adt = Some s' /\ get_mm_l_spec i' adt = Some l').
            unfold get_mm_s_spec.
            unfold get_mm_l_spec.
            rewrite ikern, ihost.
            rewrite i'get.
            auto.
            destruct H2 as [getmms' getmml'].
            generalize (MM_s_l_valid_Z adt i' s' l' hinv initialized ikern ihost i'range getmms' getmml').
            intro.
            destruct H2 as [s'ge0 tmpH].
            destruct tmpH as [l'gt0 s'l'ltmu].
            rewrite <- Int.unsigned_repr with (z:= s') in getmms'.
            rewrite <- Int.unsigned_repr with (z:= l') in getmml'.
            generalize (jpre i' (Int.repr s') (Int.repr l') H0 getmms' getmml').
            intro.
            rewrite Int.unsigned_repr in H2.
            rewrite Int.unsigned_repr in H2.
            omega.
            omega.
            omega.
            omega.
            omega.
            rewrite H0 in *.
            unfold get_mm_s_spec in getmms.
            unfold get_mm_l_spec in getmml.
            rewrite ikern, ihost in *.
            rewrite i'get in *.
            injection getmms; injection getmml; intros; subst.
            omega.
            (* flag = 1 *)
            destruct H0 as [flageq1 tmpcond].
            destruct tmpcond as [firstcond secondcond].
            subst.
            assert(tmpjpre': 0 <= size - 1 < size) by omega.
            generalize (MM_match adt i (size - 1) s l isnorm hinv initialized ikern ihost tmpjpre' getmms getmml irange firstcond secondcond isusable).
            intro mmmatch.
            Caseeq mmmatch; intros.
            left; auto.
            right.
            destruct H0.
            split.
            left.
            split.
            trivial.
            assumption.
            assumption.

            Grab Existential Variables.
            exists 0.
            repeat autounfold.
            unfold two_power_nat.
            unfold shift_nat.
            simpl.
            omega.
            exists 0.
            repeat autounfold.
            unfold two_power_nat.
            unfold shift_nat.
            simpl.
            omega.
          Qed.

        End inner_loop_proof.

        Lemma inner_loop_correct: forall m d le i,
                                    high_level_invariant d ->
                                    init d = true ->
                                    ikern d = true ->
                                    ihost d = true ->
                                    PTree.get ti le = Some (Vint (Int.repr i)) ->
                                    PTree.get tj le = Some (Vint (Int.zero)) ->
                                    PTree.get tflag le = Some (Vint (Int.zero)) ->
                                    PTree.get tisnorm le = Some (Vint (Int.zero)) ->
                                    PTree.get tsize le = Some (Vint (Int.repr ((MMSize d)))) ->
                                    PTree.get tnps le = Some (Vint (Int.repr (nps d))) ->
                                    kern_low <= i < kern_high ->
                                    exists le' flag isnorm, 
                                      exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile inner_while_condition inner_while_body) E0 le' (m, d) Out_normal /\
                                      PTree.get ti le' = Some (Vint (Int.repr i)) /\
                                      PTree.get tflag le' = Some (Vint (Int.repr flag)) /\
                                      PTree.get tisnorm le' = Some (Vint (Int.repr isnorm)) /\
                                      PTree.get tsize le' = Some (Vint (Int.repr ((MMSize d)))) /\
                                      PTree.get tnps le' = Some (Vint (Int.repr (nps d))) /\
                                      (flag = 1 /\ isnorm = 1 /\ MM_kern_valid ((MM d)) i ((MMSize d)) \/ (flag = 1 /\ isnorm = 0 \/ flag = 0) /\ ~MM_kern_valid ((MM d)) i ((MMSize d)))
        .
        Proof.
          intros m d le i hinv initialized kern ihost tile tjle tflagle tisnormle tsizele tnpsle pgaligned.
          generalize (inner_loop_correct_aux m d i hinv initialized kern ihost).
          unfold inner_loop_body_P.
          unfold inner_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le' tmppre].
          destruct tmppre as [m' tmppre].
          destruct tmppre as [stmp tmppre].
          destruct tmppre as [i' tmppre].
          destruct tmppre as [flag' tmppre].
          destruct tmppre as [isnorm' tmppre].
          destruct tmppre as [ti'le' tmppre].
          destruct tmppre as [tflag'le' tmppre].
          destruct tmppre as [tisnorm'le' tmppre].
          destruct tmppre as [tnps'le' tmppre].
          destruct tmppre as [post msubst].
          subst.
          exists le'.
          esplit. esplit.
          repeat vcgen.
          repeat vcgen.
        Qed.

        Definition mem_init_mk_rdata (adt: RData) (index: Z) := adt {AT: (Calculate_AT (Z.to_nat index) (nps adt) (MM adt) (MMSize adt) (AT adt))}.

        Section outter_loop_proof.

          Variable minit: memb.
          Variable adt : RData.
          Notation nps := (nps adt).
          Notation size := (MMSize adt).

          Opaque PTree.set PTree.get.

          Hypothesis hinv: high_level_invariant adt.
          Hypothesis initialized: init adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ihost: ihost adt = true.

          Definition outter_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get ti le = Some (Vint (Int.zero)) /\
            PTree.get tsize le = Some (Vint (Int.repr size)) /\
            PTree.get tnps le = Some (Vint (Int.repr nps)) /\
            0 < nps <= maxpage /\
            m = (minit, adt).

          Definition outter_loop_body_Q (le : temp_env) (m: mem): Prop := 
            m = (minit, (mem_init_mk_rdata adt (AbstractDataType.nps (snd m) - 1))).

          Lemma outter_loop_correct_aux : LoopProofSimpleWhile.t outter_while_condition outter_while_body ge (PTree.empty _) (outter_loop_body_P) (outter_loop_body_Q).
          Proof.
            generalize (size_range_valid adt hinv initialized); intro initsizerange.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get tsize le = Some (Vint (Int.repr ((MMSize (snd m))))) /\
                                    PTree.get ti le = Some (Vint (Int.repr i)) /\
                                    PTree.get tnps le = Some (Vint (Int.repr (AbstractDataType.nps (snd m)))) /\
                                    0 <= i <= AbstractDataType.nps (snd m) /\
                                    (i = 0 /\ m = (minit, adt) \/ i > 0 /\ m = (minit, (mem_init_mk_rdata adt (i - 1)))) /\
                                    w = AbstractDataType.nps (snd m) - i /\
                                    0 < (MMSize (snd m)) <= Int.max_unsigned /\
                                    0 < AbstractDataType.nps (snd m) <= maxpage /\
                                    init (snd m) = true /\
                                    AbstractDataType.ikern (snd m) = true /\
                                    AbstractDataType.ihost (snd m) = true /\
                                    high_level_invariant (snd m)
              )
            .
            apply Zwf_well_founded.
            unfold outter_loop_body_P.
            intros.
            destruct H as [tile tmpH].
            destruct tmpH as [tsizele tmpH].
            destruct tmpH as [tnpsle tmpH].
            destruct tmpH as [npsrange msubst].
            subst.
            (* I -> P *)
            unfold snd; simpl.
            esplit. esplit.
            repeat vcgen.
            
            (* I -> I *)
            generalize max_unsigned_val; intro muval.
            unfold outter_loop_body_Q.
            unfold outter_while_condition.
            unfold outter_while_body.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [tsizele tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tnpsle tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [icond tmpH].
            destruct tmpH as [wval tmpH].
            destruct tmpH as [sizerange tmpH].
            destruct tmpH as [npsrange tmpH].
            destruct tmpH as [minitialized tmpH].
            destruct tmpH as [kern tmpH].
            destruct tmpH as [host highinv].
            destruct irange as [ige0 icase].
            subst.

            assert(npslemaxu: AbstractDataType.nps (snd m) <= Int.max_unsigned) by (simpl; omega).
            apply Zle_lt_or_eq in icase.
            destruct m as [m d]; unfold snd in *; simpl in *.

            Caseeq icase.
            (* i < nps *)
            intro cond.
            exists (Vint (Int.one)), true.
            repeat vcgen.
            assert(icase1: i < kern_low \/ i >= kern_low) by omega.
            Caseeq icase1.

            (* i < kern_low *)
            intro cond'.
            assert(tmpi: 0 <= i < maxpage) by omega.
            assert(tmptype: ZtoATType 1 = Some ATKern) by reflexivity.
            esplit. esplit.
            repeat vcgen.
            unfold set_at_norm_spec.
            rewrite kern, host, tmptype.
            destruct (zle_lt 0 i 1048576); try omega.
            reflexivity.
            simpl.

            exists ((AbstractDataType.nps d) - i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold mem_init_mk_rdata in *.
            Caseeq icond.
            (* i = 0 *)
            intro acond.
            destruct acond as [ieq0 msubst].
            injection msubst; intros; subst.
            f_equal.
            (* i > 0 *)
            intro acond.
            destruct acond as [igt0 msubst].
            injection msubst; intros; subst.
            simpl in *.    
            assert(tmpeq: i + 1 - 1 = i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
            change (i - 1 + 1) with (Z.succ (i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(i - 1)).
            Opaque Z.of_nat.
            simpl.
            rewrite <- Z2Nat.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            replace (i - 1 + 1) with i by omega.
            destruct (Z_le_dec kern_low i).
            omega.
            reflexivity.
            omega.
            omega.
            omega.
            inv highinv.
            constructor; simpl; eauto.

            (* i >= kern_low *)
            intro cond'.
            assert(icase2: i >= kern_high \/ i < kern_high) by omega.
            Caseeq icase2.
            (* i >= kern_high *)
            intro cond''.
            assert(tmpi: 0 <= i < maxpage) by omega.
            assert(tmptype: ZtoATType 1 = Some ATKern) by reflexivity.
            esplit. esplit.
            repeat vcgen.
            simpl in *.
            unfold set_at_norm_spec.
            rewrite kern, host.
            destruct (zle_lt 0 i 1048576); try omega.
            reflexivity.
            simpl.

            exists (AbstractDataType.nps d - i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold mem_init_mk_rdata in *.
            Caseeq icond.
            (* i = 0 *)
            intro acond.
            destruct acond as [ieq0 msubst].
            injection msubst; intros; subst.
            f_equal.
            (* i > 0 *)
            intro acond.
            destruct acond as [igt0 msubst].
            injection msubst; intros; subst.
            simpl in *.    
            assert(tmpeq: i + 1 - 1 = i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
            change (i - 1 + 1) with (Z.succ (i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(i - 1)).
            Opaque Z.of_nat.
            simpl.
            rewrite <- Z2Nat.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            replace (i - 1 + 1) with i by omega.
            destruct (Z_le_dec kern_low i); try omega.
            destruct (Zmin.Zmin_spec kern_high nps) as [npscond|npscond].
            destruct npscond.
            rewrite H1.
            destruct (Z_lt_dec i kern_high); try omega.
            reflexivity.
            omega.
            omega.
            omega.
            omega.
            inv highinv.
            constructor; simpl; eauto.

            (* i < kern_high *)
            intro cond2.
            Definition newle (le: temp_env) := (PTree.set tisnorm (Vint (Int.repr 0)) (PTree.set tflag (Vint (Int.repr 0)) (PTree.set tj (Vint (Int.repr 0)) le))).
            assert(tmple: (newle le) ! ti = Some (Vint (Int.repr i)) /\ (newle le) ! tj = Some (Vint Int.zero) /\ (newle le) ! tflag = Some (Vint Int.zero) /\ (newle le) ! tisnorm = Some (Vint Int.zero) /\ (newle le) ! tsize = Some (Vint (Int.repr ((MMSize d)))) /\ (newle le) ! tnps = Some (Vint (Int.repr (AbstractDataType.nps d)))) by (unfold newle; repeat vcgen).
            destruct tmple as [tile' tmple].
            destruct tmple as [tjle' tmple].
            destruct tmple as [tflagle' tmple].
            destruct tmple as [tisnormle' tmple].
            destruct tmple as [tsizele' tnpsle'].
            assert(pgaligned: kern_low <= i < kern_high) by omega.
            generalize (inner_loop_correct m d (newle le) i highinv minitialized kern host tile' tjle' tflagle' tisnormle' tsizele' tnpsle' pgaligned).
            clear pgaligned.
            intro innerloop.
            clear tile' tjle' tflagle' tisnormle' tsizele' tnpsle'.
            destruct innerloop as [le' innerloop].
            destruct innerloop as [flag innerloop].
            destruct innerloop as [isnorm innerloop].
            destruct innerloop as [innerstmt innerloop].
            destruct innerloop as [tile' innerloop].
            destruct innerloop as [tflagle' innerloop].
            destruct innerloop as [tisnormle' innerloop].
            destruct innerloop as [tsizele' innerloop].
            destruct innerloop as [tnpsle' valcond].
            unfold newle in *.
            Caseeq valcond.

            (* flag = 1 /\ isnorm = 1 *)
            intro flagnormcond.
            assert(tmpi: 0 <= i < maxpage) by omega.
            assert(tmptype: ZtoATType 2 = Some ATNorm) by (unfold ZtoATType; repeat zdestruct; reflexivity).
            destruct flagnormcond as [flageq1 flagnormcond].
            destruct flagnormcond as [isnormeq1 valcond].
            esplit. esplit.
            repeat vcgen.
            simpl.
            unfold set_at_norm_spec.
            rewrite kern, host.
            destruct (zle_lt 0 i 1048576); try omega.
            reflexivity.
            simpl.
            exists (AbstractDataType.nps d - i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.

            (* post condition proof for the case norm *)
            Caseeq icond.
            (* i = 0 *)
            intro ieq0.
            destruct ieq0 as [ieq0 msubst].
            injection msubst; intros; subst.
            omega.
            (* i > 0 *)
            intro acond.
            destruct acond as [igt0 msubst].
            injection msubst; intros; subst.
            unfold mem_init_mk_rdata in *.
            simpl in *.
            assert(tmpeq: i + 1 - 1 = i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
            change (i - 1 + 1) with (Z.succ (i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(i - 1)).
            unfold Calculate_AT.
            fold Calculate_AT.
            rewrite <- Z2Nat.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            assert(tmpeq: i - 1 + 1 = i) by omega; rewrite tmpeq; clear tmpeq.
            destruct (Z_le_dec kern_low i); try (omega).
            destruct (Zmin.Zmin_spec kern_high nps) as [npscond|npscond].
            (* nps >= kern_high *)
            destruct npscond as [npsgekh zminsubst].
            rewrite zminsubst.
            destruct (Z_lt_dec i kern_high); try (omega).
            destruct (MM_kern_valid_dec (MM adt) i size); try contradiction.
            f_equal.
            (* nps < kern_high *)
            destruct npscond as [npsltkh zminsubst].
            rewrite zminsubst.
            destruct (Z_lt_dec i nps); try (omega).
            destruct (MM_kern_valid_dec (MM adt) i size); try contradiction.
            f_equal.
            unfold Z.succ.
            omega.
            omega.
            omega.
            inv highinv.
            constructor; simpl; eauto.

            intro flagnormcond.
            destruct flagnormcond as [flagnormcond invalcond].
            assert(tmpi: 0 <= i < maxpage) by omega.
            assert(tmptype: ZtoATType 0 = Some ATResv) by (unfold ZtoATType; repeat zdestruct; reflexivity).
            Caseeq flagnormcond.
            (* flag = 1 /\ isnorm = 0 *)
            intro flagnormcond.
            destruct flagnormcond as [flageq1 isnormeq0].
            esplit. esplit.
            repeat vcgen.
            unfold set_at_norm_spec.
            rewrite kern, host.
            destruct (zle_lt 0 i 1048576); try omega.
            reflexivity.
            simpl.
            exists (AbstractDataType.nps d - i - 1).
            repeat vcgen.
            simpl.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.

            (* post condition proof for the case resv *)
            Caseeq icond.
            (* i = 0 *)
            intro icond.
            destruct icond.
            subst.
            omega.
            (* i > 0 *)
            intro acond.
            destruct acond as [igt0 msubst].
            injection msubst; intros; subst.
            unfold mem_init_mk_rdata in *.
            simpl in *.
            assert(tmpeq: i + 1 - 1 = i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
            change (i - 1 + 1) with (Z.succ (i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(i - 1)).
            unfold Calculate_AT.
            fold Calculate_AT.
            rewrite <- Z2Nat.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            assert(tmpeq: i - 1 + 1 = i) by omega; rewrite tmpeq; clear tmpeq.
            destruct (Z_le_dec kern_low i); try (omega).
            destruct (Zmin.Zmin_spec kern_high nps) as [npscond|npscond].
            (* nps >= kern_high *)
            destruct npscond as [npsgekh zminsubst].
            rewrite zminsubst.
            destruct (Z_lt_dec i kern_high); try (omega).
            destruct (MM_kern_valid_dec (MM adt) i size); try (contradiction).
            reflexivity.
            (* nps < kern_high *)
            destruct npscond as [npsltkh zminsubst].
            rewrite zminsubst.
            destruct (Z_lt_dec i nps); try (omega).
            destruct (MM_kern_valid_dec (MM adt) i size); try (contradiction).
            reflexivity.
            unfold Z.succ.
            omega.
            omega.
            omega.
            inv highinv.
            constructor; simpl; eauto.

            (* flag = 0 *)
            intro flageq0.
            subst.
            esplit. esplit.
            repeat vcgen.
            unfold set_at_norm_spec.
            rewrite kern, host.
            destruct (zle_lt 0 i 1048576); try omega.
            reflexivity.
            simpl.
            exists (AbstractDataType.nps d - i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.

            (* post condition proof for the case resv *)
            Caseeq icond.
            (* i = 0 *)
            intro icond.
            destruct icond.
            subst.
            omega.
            (* i > 0 *)
            intro acond.
            destruct acond as [igt0 msubst].
            injection msubst; intros; subst.
            unfold mem_init_mk_rdata in *.
            simpl in *.
            assert(tmpeq: i + 1 - 1 = i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
            change (i - 1 + 1) with (Z.succ (i - 1)).
            rewrite Z2Nat.inj_succ with (n:=(i - 1)).
            unfold Calculate_AT.
            fold Calculate_AT.
            rewrite <- Z2Nat.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            assert(tmpeq: i - 1 + 1 = i) by omega; rewrite tmpeq; clear tmpeq.
            destruct (Z_le_dec kern_low i); try (omega).
            destruct (Zmin.Zmin_spec kern_high nps) as [npscond|npscond].
            (* nps >= kern_high *)
            destruct npscond as [npsgekh zminsubst].
            rewrite zminsubst.
            destruct (Z_lt_dec i kern_high); try (omega).
            destruct (MM_kern_valid_dec (MM adt) i size); try (contradiction).
            reflexivity.
            (* nps < kern_high *)
            destruct npscond as [npsltkh zminsubst].
            rewrite zminsubst.
            destruct (Z_lt_dec i nps); try (omega).
            destruct (MM_kern_valid_dec (MM adt) i size); try (contradiction).
            reflexivity.
            unfold Z.succ.
            omega.
            omega.
            omega.
            inv highinv.
            constructor; simpl; eauto.

            (* i = nps *)
            intro ieqnps.
            exists (Vint (Int.zero)), false.
            repeat vcgen.
            subst.
            Caseeq icond.
            intro.
            destruct H0.
            omega.
            intro.
            destruct H0.
            assumption.
          Qed.

        End outter_loop_proof.


        Lemma outter_loop_correct: forall m d d' le,
                                     high_level_invariant d ->
                                     init d = true ->
                                     ikern d = true ->
                                     ihost d = true ->
                                     PTree.get ti le = Some (Vint (Int.zero)) ->
                                     PTree.get tsize le = Some (Vint (Int.repr ((MMSize d)))) ->
                                     PTree.get tnps le = Some (Vint (Int.repr (nps d))) ->
                                     0 < nps d <= maxpage ->
                                     d' = mem_init_mk_rdata d (nps d - 1) ->
                                     exists le', exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile outter_while_condition outter_while_body) E0 le' (m, d') Out_normal
        .
        Proof.
          intros m d d' le hinv initialized kern host tile tsizele tnpsle sizerange newm.
          generalize (outter_loop_correct_aux m d hinv initialized kern host).
          unfold outter_loop_body_P.
          unfold outter_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le'' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp newm'].
          exists le''.
          rewrite newm.
          unfold mem_init_mk_rdata in *.
          simpl in *.
          assert(nps (snd m'') = nps d).
          rewrite newm'.
          reflexivity.
          rewrite newm' in stmp.
          unfold snd in *; simpl in *.
          rewrite H in stmp.
          assumption.
          repeat vcgen.
        Qed.

        Lemma mem_init_body_correct: forall m d d' env le mbi_adr,
                                       high_level_invariant d ->
                                       PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                       mem_init_spec (Int.unsigned mbi_adr) d = Some d' ->
                                       env = PTree.empty _ ->
                                       exists le',
                                         (exec_stmt ge env le ((m, d): mem) mem_init_body E0 le' (m, d') Out_normal).
        Proof.
          intros m d d' env le mbi_adr hinv tmbiadrle.
          intros.
          generalize max_unsigned_val; intro muval.
          generalize real_nps_range; unfold real_nps; intro rnps_range.
          unfold mem_init_body.
          functional inversion H.
          subst.
          
          inversion real_params.
          assert(bootloader: exists dbootloader, bootloader0_spec (Int.unsigned mbi_adr) d = ret dbootloader) by (esplit; repeat vcgen).
          destruct bootloader as [dbootloader bootloader].
          functional inversion bootloader.

          (* destruct on nps_loop_correct *)
          exploit (nps_loop_correct m dbootloader (PTree.set tnps (Vint (Int.repr 0))
                                      (set_opttemp (Some tsize) (Vint (Int.repr real_size))
                                                   (PTree.set ti (Vint (Int.repr 0)) (set_opttemp None Vundef le))))); try rewrite <- H0; simpl; eauto; ptreesolve.
          inversion hinv; constructor; eauto.
          intro npsloop.
          destruct npsloop as [npsloople' tmpH].
          destruct tmpH as [nps tmpH].
          destruct tmpH as [npsstmt tmpH].
          destruct tmpH as [tsizex tmpH].
          destruct tmpH as [tnpsx npsval].

          assert(setnps: exists dsetnps, set_nps_spec (Calculate_nps (Z.to_nat (real_size - 1)) real_mm real_size) dbootloader = ret dsetnps).
            esplit; rewrite <- H0; repeat vcgen.
            unfold set_nps_spec.
            simpl.
            rewrite H6, H7.
            reflexivity.
          destruct setnps as [dsetnps setnps].
          functional inversion setnps.

          (* destruct on outter_loop_correct *)
          exploit (outter_loop_correct m dsetnps (mem_init_mk_rdata dsetnps (AbstractDataType.nps dsetnps - 1)) (PTree.set ti (Vint (Int.repr 0)) (set_opttemp None Vundef npsloople'))); subst; simpl in *; eauto; ptreesolve.
          inversion hinv; constructor; eauto.
          omega.
          intro outterloop.
          destruct outterloop as [outterloople' outterloop].
          simpl in *.
          rewrite H2, H3, H4 in *.
          
          esplit.
          repeat vcgen.
          repeat vcgen.
        Qed.

      End MemInitBody.

      Theorem mem_init_code_correct:
        spec_le (mem_init ↦ mem_init_spec_low) (〚mem_init ↦ f_mem_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        exploit mem_init_body_correct; simpl; destruct H0; ptreesolve; eauto; autorewrite with lift_simpl lens_simpl; 
        repeat progress (unfold lift, set; simpl); eauto; repeat progress (try rewrite Int.unsigned_repr); 
        repeat progress discharge_unsigned_range; simpl in *.
        instantiate (1:= bind_parameter_temps' (fn_params f_mem_init)
                                               (Vint mbi_adr::nil)
                                               (create_undef_temps (fn_temps f_mem_init))).
        repeat progress match goal with
                          | [H: ?x = _ |- context[?x]] => try rewrite H
                        end; eauto.
        intro stmt; try (destruct stmt as [le' stmt]).
        repeat progress fbigstep_post.
      Qed.
                                                                              
      End Meminit.

    End With_primitives.

  End MALINITCODE.
