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
(*          for the C functions implemented in the MPTIntro layer      *)
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
Require Import PTOpGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import AbstractDataType.
Require Import MPTIntroCSource.
Require Import CalRealIDPDE.


Module MPTINTROCODE.

  Section WithPrimitives. 

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.
     

    Section IDPDEINIT.

      Let L: compatlayer (cdata RData) := container_init ↦ gensem container_init0_spec
           ⊕ set_IDPTE ↦ gensem setIDPTE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Section IDPDEInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_IDPTE *)

        Variable bsetidpte: block.

        Hypothesis hset_idpte1 : Genv.find_symbol ge set_IDPTE = Some bsetidpte. 
        
        Hypothesis hset_idpte2 : Genv.find_funct_ptr ge bsetidpte = Some (External (EF_external set_IDPTE (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).
        
        (** container_init *)

        Variable binit: block.

        Hypothesis hinit1 : Genv.find_symbol ge container_init = Some binit. 
        
        Hypothesis hinit2 : Genv.find_funct_ptr ge binit = Some (External (EF_external container_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        Definition idpte_init_mk_rdata (adt: RData) (pde_index: Z) (index: Z) := adt {idpde: (Calculate_idpte (Z.to_nat index) pde_index (idpde adt))}.

        Section idpte_loop_proof.

          Variable minit: memb.
          Variable adt : RData.
          Variable i : Z.
          Variable perm: Z.

          Opaque PTree.set PTree.get.

          Hypothesis initialized: init adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ipt: ipt adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis pg: pg adt = false.
          Hypothesis irange: 0 <= i < one_k.
          Hypothesis permval: (256 <= i < 960 /\ perm = 3) \/ ((i < 256 \/ i >= 960) /\ perm = 259).

          Definition idpte_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get tj le = Some (Vint (Int.zero)) /\
            PTree.get ti le = Some (Vint (Int.repr i)) /\
            PTree.get tperm le = Some (Vint (Int.repr perm)) /\
            m = (minit, adt).

          Definition idpte_loop_body_Q (le : temp_env) (m: mem): Prop := 
            m = (minit, (idpte_init_mk_rdata adt i (one_k - 1))) /\
            PTree.get ti le = Some (Vint (Int.repr i)).

          Lemma idpte_loop_correct_aux : LoopProofSimpleWhile.t idpde_init_inner_while_condition idpde_init_inner_while_body ge (PTree.empty _) (idpte_loop_body_P) (idpte_loop_body_Q).
          Proof.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists j,
                                    PTree.get tj le = Some (Vint (Int.repr j)) /\
                                    PTree.get ti le = Some (Vint (Int.repr i)) /\
                                    PTree.get tperm le = Some (Vint (Int.repr perm)) /\
                                    0 <= j <= one_k /\
                                    (j = 0 /\ m = (minit, adt) \/ j > 0 /\ m = (minit, (idpte_init_mk_rdata adt i (j - 1)))) /\
                                    w = one_k - j /\
                                    init (snd m) = true /\
                                    AbstractDataType.ikern (snd m) = true /\
                                    AbstractDataType.ihost (snd m) = true /\
                                    AbstractDataType.pg (snd m) = false /\
                                    AbstractDataType.ipt (snd m) = true
              )
            .
            apply Zwf_well_founded.
            unfold idpte_loop_body_P.
            intros.
            destruct H as [tjle tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tperm msubst].
            subst.
            (* I -> P *)
            esplit. esplit.
            repeat vcgen.
            
            (* I -> I *)
            generalize max_unsigned_val; intro muval.
            unfold idpte_loop_body_Q.
            unfold idpde_init_inner_while_condition.
            unfold idpde_init_inner_while_body.
            intros.
            destruct H as [j tmpH].
            destruct tmpH as [tjle tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tpermle tmpH].
            destruct tmpH as [jrange tmpH].
            destruct tmpH as [jcond tmpH].
            destruct tmpH as [wval tmpH].
            destruct tmpH as [minitialized tmpH].
            destruct tmpH as [kern tmpH].
            destruct tmpH as [host tmpH].
            destruct tmpH as [pgm iptm].
            destruct jrange as [jge0 jcase].
            subst.

            apply Zle_lt_or_eq in jcase.
            Caseeq jcase.
            {
              (* j < one_k *)
              intro cond.
              exists (Vint (Int.one)), true.
              repeat vcgen.
              destruct m.
              assert(exists p, ZtoPerm perm = Some p).
              {
                unfold ZtoPerm.
                destruct permval.
                destruct H0.
                subst.
                esplit; reflexivity.
                destruct H0.
                subst.
                esplit; reflexivity.
              }
              destruct H0.
              esplit. esplit.
              repeat vcgen.
              unfold setIDPTE_spec.
              simpl in *.
              rewrite kern, pgm, host, iptm, minitialized, H0.
              unfold IDPTE_Arg.
              rewrite one_k_minus1, one_k_minus1'.
              unfold zle_le.
              repeat zdestruct.
              exists (1024 - j - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
              right.
              split.
              omega.
              destruct jcond.
              {
                destruct H1.
                injection H2; intros; subst.
                unfold idpte_init_mk_rdata.
                simpl.
                unfold Calculate_idpte_at_i.
                destruct permval.
                {
                  destruct H1.
                  subst.
                  repeat zdestruct.
                  unfold ZtoPerm in H0; simpl in H0.
                  injection H0; intros; subst.
                  reflexivity.
                }
                {
                  destruct H1.
                  unfold ZtoPerm in H0; simpl in H0; subst; injection H0; intros; subst.
                  destruct H1; repeat zdestruct.
                }
              }
              {
                destruct H1.
                injection H2; intros; subst.
                unfold idpte_init_mk_rdata.
                simpl.
                assert(tmpeq: j + 1 - 1 = j - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
                change (j - 1 + 1) with (Z.succ (j - 1)).
                rewrite Z2Nat.inj_succ with (n:=(j - 1)).
                Opaque Z.of_nat.
                simpl.
                rewrite <- Z2Nat.inj_succ.
                rewrite Z2Nat.id.
                unfold Z.succ.
                assert(tmpeq: j - 1 + 1 = j) by omega; rewrite tmpeq; clear tmpeq.
                unfold Calculate_idpte_at_i.
                destruct permval.
                {
                  destruct H3.
                  subst.
                  repeat zdestruct.
                  unfold ZtoPerm in H0; simpl in H0.
                  injection H0; intros; subst.
                  reflexivity.
                }
                {
                  destruct H3.
                  unfold ZtoPerm in H0; simpl in H0; subst; injection H0; intros; subst.
                  destruct H3; repeat zdestruct.
                }
                unfold Z.succ.
                omega.
                omega.
                omega.
              }
            }
            {
              (* j = one_k *)
              intro; subst.
              destruct jcond.
              destruct H.
              omega.
              destruct H.
              destruct m.
              injection H0; intros; subst.
              esplit. esplit.
              repeat vcgen.
            }
          Qed.

        End idpte_loop_proof.


        Lemma idpte_loop_correct: forall m d d' le i perm,
                                     init d = true ->
                                     ikern d = true ->
                                     ihost d = true ->
                                     ipt d = true ->
                                     pg d = false ->
                                     0 <= i < one_k ->
                                     (256 <= i < 960 /\ perm = 3) \/ ((i < 256 \/ i >= 960) /\ perm = 259) ->
                                     PTree.get tj le = Some (Vint (Int.zero)) ->
                                     PTree.get ti le = Some (Vint (Int.repr i)) ->
                                     PTree.get tperm le = Some (Vint (Int.repr perm)) ->
                                     d' = idpte_init_mk_rdata d i (one_k - 1) ->
                                     exists le', exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile idpde_init_inner_while_condition idpde_init_inner_while_body) E0 le' (m, d') Out_normal /\ PTree.get ti le' = Some (Vint (Int.repr i))
        .
        Proof.
          intros m d d' le i perm initialized kern host ipt pg irange permval tjle tile tpermle newm.
          generalize (idpte_loop_correct_aux m d i perm initialized kern ipt host pg irange permval).
          unfold idpte_loop_body_P.
          unfold idpte_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le'' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp tmppre].
          destruct tmppre as [newm' lei].
          exists le''.
          rewrite newm in *.
          rewrite newm' in *.
          unfold idpte_init_mk_rdata in *.
          split.
          assumption.
          assumption.
          repeat vcgen.
        Qed.

        Definition idpde_init_mk_rdata (adt: RData) (index: Z) := adt {idpde: (Calculate_idpde (Z.to_nat index) (idpde adt))}.

        Section idpde_loop_proof.

          Variable minit: memb.
          Variable adt: RData.

          Hypothesis initialized: init adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ipt: ipt adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis pg: pg adt = false.

          Definition idpde_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get ti le = Some (Vint Int.zero) /\ 
            m = (minit, adt).

          Definition idpde_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            m = (minit, idpde_init_mk_rdata adt (one_k - 1)).

          Lemma idpde_loop_correct_aux : LoopProofSimpleWhile.t idpde_init_outter_while_condition idpde_init_outter_while_body ge (PTree.empty _) (idpde_loop_body_P) (idpde_loop_body_Q).
          Proof.
            Opaque Z.to_nat.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get ti le = Some (Vint i) /\
                                    0 <= Int.unsigned i <= one_k /\ 
                                    (Int.unsigned i = 0 /\ m = (minit, adt) \/ 0 < Int.unsigned i /\ m = (minit, idpde_init_mk_rdata adt (Int.unsigned i - 1))) /\
                                    w = one_k - Int.unsigned i 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold idpde_loop_body_P in H.
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
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.
            unfold idpde_init_outter_while_condition, idpde_init_outter_while_body.
            destruct m.

            Caseeq ihigh.

            (* i < one_k *)
            intro ihigh.
            assert(iintervals: Int.unsigned i = 0 \/ 0 < Int.unsigned i < 256 \/ Int.unsigned i >= 960 \/ 256 <= Int.unsigned i < 960) by omega.
            Caseeq iintervals.
            {
              intro irange.
              rewrite <- Int.repr_unsigned with i in tile.
              rewrite irange in *.
              destruct icase; try (destruct H; omega).
              destruct H.
              injection H0; intros; subst.
              exploit (idpte_loop_correct minit adt (idpte_init_mk_rdata adt 0 (one_k - 1)) (PTree.set tj (Vint (Int.repr 0)) (PTree.set tperm (Vint (Int.repr 259)) le)) 0 259); repeat vcgen.
              destruct H1 as [le' stmt].
              destruct stmt as [stmt tile'].
              esplit. esplit.
              repeat vcgen.
              esplit. esplit.
              repeat vcgen.
              exists (one_k - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
            }
            intro iinterval.
            Caseeq iinterval.
            {
              intro irange.
              destruct icase; try (destruct H; omega).
              destruct H.
              injection H0; intros; subst.
              exploit (idpte_loop_correct minit (idpde_init_mk_rdata adt (Int.unsigned i - 1)) (idpte_init_mk_rdata (idpde_init_mk_rdata adt (Int.unsigned i - 1)) (Int.unsigned i) (one_k - 1)) (PTree.set tj (Vint (Int.repr 0)) (PTree.set tperm (Vint (Int.repr 259)) le)) (Int.unsigned i) 259); repeat vcgen.
              destruct H1 as [le' stmt].
              destruct stmt as [stmt tile'].
              esplit. esplit.
              repeat vcgen.
              esplit. esplit.
              repeat vcgen.
              exists (one_k - Int.unsigned i - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
              right.
              split.
              omega.
              unfold idpde_init_mk_rdata, idpte_init_mk_rdata in *.
              simpl in *.
              assert(tmpeq: Int.unsigned i + 1 - 1 = Int.unsigned i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
              change (Int.unsigned i - 1 + 1) with (Z.succ (Int.unsigned i - 1)).
              rewrite Z2Nat.inj_succ with (n:=(Int.unsigned i - 1)).
              unfold Calculate_idpde.
              fold Calculate_idpde.
              rewrite <- Z2Nat.inj_succ.
              rewrite Z2Nat.id.
              unfold Z.succ.
              assert(tmpeq: Int.unsigned i - 1 + 1 = Int.unsigned i) by omega; rewrite tmpeq; clear tmpeq.
              reflexivity.
              unfold Z.succ; omega.
              omega.
              omega.
            }
            intro iinterval.
            Caseeq iinterval.
            {
              intro irange.
              destruct icase; try (destruct H; omega).
              destruct H.
              injection H0; intros; subst.
              exploit (idpte_loop_correct minit (idpde_init_mk_rdata adt (Int.unsigned i - 1)) (idpte_init_mk_rdata (idpde_init_mk_rdata adt (Int.unsigned i - 1)) (Int.unsigned i) (one_k - 1)) (PTree.set tj (Vint (Int.repr 0)) (PTree.set tperm (Vint (Int.repr 259)) le)) (Int.unsigned i) 259); repeat vcgen.
              destruct H1 as [le' stmt].
              destruct stmt as [stmt tile'].
              esplit. esplit.
              repeat vcgen.
              esplit. esplit.
              repeat vcgen.
              exists (one_k - Int.unsigned i - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
              right.
              split.
              omega.
              unfold idpde_init_mk_rdata, idpte_init_mk_rdata in *.
              simpl in *.
              assert(tmpeq: Int.unsigned i + 1 - 1 = Int.unsigned i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
              change (Int.unsigned i - 1 + 1) with (Z.succ (Int.unsigned i - 1)).
              rewrite Z2Nat.inj_succ with (n:=(Int.unsigned i - 1)).
              unfold Calculate_idpde.
              fold Calculate_idpde.
              rewrite <- Z2Nat.inj_succ.
              rewrite Z2Nat.id.
              unfold Z.succ.
              assert(tmpeq: Int.unsigned i - 1 + 1 = Int.unsigned i) by omega; rewrite tmpeq; clear tmpeq.
              reflexivity.
              unfold Z.succ; omega.
              omega.
              omega.
            }
            {
              intro irange.
              destruct icase; try (destruct H; omega).
              destruct H.
              injection H0; intros; subst.
              exploit (idpte_loop_correct minit (idpde_init_mk_rdata adt (Int.unsigned i - 1)) (idpte_init_mk_rdata (idpde_init_mk_rdata adt (Int.unsigned i - 1)) (Int.unsigned i) (one_k - 1)) (PTree.set tj (Vint (Int.repr 0)) (PTree.set tperm (Vint (Int.repr 3)) le)) (Int.unsigned i) 3); repeat vcgen.
              destruct H1 as [le' stmt].
              destruct stmt as [stmt tile'].
              esplit. esplit.
              repeat vcgen.
              esplit. esplit.
              repeat vcgen.
              exists (one_k - Int.unsigned i - 1).
              repeat vcgen.
              esplit.
              repeat vcgen.
              right.
              split.
              omega.
              unfold idpde_init_mk_rdata, idpte_init_mk_rdata in *.
              simpl in *.
              assert(tmpeq: Int.unsigned i + 1 - 1 = Int.unsigned i - 1 + 1) by omega; rewrite tmpeq; clear tmpeq.
              change (Int.unsigned i - 1 + 1) with (Z.succ (Int.unsigned i - 1)).
              rewrite Z2Nat.inj_succ with (n:=(Int.unsigned i - 1)).
              unfold Calculate_idpde.
              fold Calculate_idpde.
              rewrite <- Z2Nat.inj_succ.
              rewrite Z2Nat.id.
              unfold Z.succ.
              assert(tmpeq: Int.unsigned i - 1 + 1 = Int.unsigned i) by omega; rewrite tmpeq; clear tmpeq.
              reflexivity.
              unfold Z.succ; omega.
              omega.
              omega.
            }

            (* i = one_k *)
            intro ival.
            rewrite <- Int.repr_unsigned with i in tile.
            rewrite ival in *.
            esplit. esplit.
            repeat vcgen.
            unfold idpde_loop_body_Q.
            Caseeq icase.
            intro tmpH; destruct tmpH; omega.
            intro tmpH; destruct tmpH.
            assumption.
          Qed.

        End idpde_loop_proof.

        Lemma idpde_loop_correct:
          forall m d d' le,
            PTree.get ti le = Some (Vint Int.zero) -> 
            init d = true ->
            ikern d = true ->
            ihost d = true ->
            ipt d = true ->
            pg d = false ->
            d' = idpde_init_mk_rdata d (one_k - 1) ->
            exists le',
              exec_stmt ge (PTree.empty _) le ((m, d): mem)
                        (Swhile idpde_init_outter_while_condition idpde_init_outter_while_body) E0 le' (m, d') Out_normal.
        Proof.
          intros m d d' le tile init kern host ipt pg m'val.
          generalize (idpde_loop_correct_aux m d init kern ipt host pg).
          unfold idpde_loop_body_P.
          unfold idpde_loop_body_Q.
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

        Lemma Calculate_idpde_eq:
          forall d n,
            ((((d {vmxinfo : real_vmxinfo})
                 {AT : real_AT (AT d)}) {nps : real_nps} {AC : real_AC}) {init : true})
              {idpde: Calculate_idpde (Z.to_nat n) (idpde d)} =
            ((((d {vmxinfo : real_vmxinfo})
                 {AT : real_AT (AT d)}) {nps : real_nps} {AC : real_AC}) {init : true})
              {idpde: Calculate_idpde 
                        (Z.to_nat n)
                        (idpde (((d {vmxinfo: real_vmxinfo})
                                   {AT : real_AT (AT d)}) {nps : real_nps}) {init: true})}.
        Proof.
          intros. Opaque Calculate_idpde.
          reflexivity.
        Qed.
        
        Lemma idpde_init_mk_rdata_eq:
          forall d,
            (((((d {vmxinfo : real_vmxinfo})
                  {AT : real_AT (AT d)}) {nps : real_nps} {AC : real_AC}) {init : true}) {idpde: real_idpde (idpde d)})
            = (idpde_init_mk_rdata
                 (((d {vmxinfo: real_vmxinfo}) 
                     {AT : real_AT (AT d)}) {nps : real_nps} {AC : real_AC})
                 {init : true} (1024 -1)).
        Proof.
          intros. unfold idpde_init_mk_rdata,real_idpde.
          eapply Calculate_idpde_eq.
        Qed.

        Lemma idpde_init_body_correct: forall m d d' env le mbi_adr,
                                           env = PTree.empty _ ->
                                           PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                           idpde_init_low_spec (Int.unsigned mbi_adr) d = Some d' ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) idpde_init_body E0 le' (m, d') Out_normal.
        Proof.
          intros. subst.
          functional inversion H1; subst.
          unfold idpde_init_body.
          exploit (idpde_loop_correct 
                     m (d {vmxinfo: real_vmxinfo} {AT : real_AT (AT d)} 
                          {nps : real_nps} {AC: real_AC} {init : true})
                     (idpde_init_mk_rdata (d {vmxinfo: real_vmxinfo} {AT : real_AT (AT d)}
                                             {nps: real_nps} {AC: real_AC} {init : true}) (one_k - 1))
                     (PTree.set ti (Vint (Int.repr 0)) (set_opttemp None Vundef le)));
          try reflexivity; try assumption.
          repeat vcgen.
          intro.
          destruct H as [le' stmt].
          exists le'.
          change E0 with (E0 ** E0).
          econstructor.
          repeat vcgen.
          change E0 with (E0 ** E0).
          econstructor.
          repeat vcgen.
          rewrite idpde_init_mk_rdata_eq.
          assumption.
        Qed.

      End IDPDEInitBody.

      Theorem idpde_init_code_correct:
        spec_le (idpde_init ↦ idpde_init_spec_low) (〚idpde_init ↦ f_idpde_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (idpde_init_body_correct s (Genv.globalenv p) makeglobalenv b1 Hb1fs Hb1fp b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_idpde_init)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_idpde_init)))) H0. 
      Qed.

    End IDPDEINIT.

    Section PTREAD.

      Let L: compatlayer (cdata RData) := get_PTE ↦ gensem getPTE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PT_Read_Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bgetptx: block.

        Hypothesis hget_ptx1 : Genv.find_symbol ge get_PTE = Some bgetptx. 
        
        Hypothesis hget_ptx2 : Genv.find_funct_ptr ge bgetptx = Some (External (EF_external get_PTE (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default).

        Lemma pt_read_body_correct: forall m d env le proc_index vaddr paddr,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tvaddr le = Some (Vint vaddr) ->
                                      ptRead_spec (Int.unsigned proc_index)
                                                      (Int.unsigned vaddr) d = Some (Int.unsigned paddr) ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_read_body E0 le' (m, d) (Out_return (Some (Vint paddr, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          unfold pt_read_body.
          intros.
          subst.
          functional inversion H2.
          unfold pdi, pti in *.
          esplit.
          repeat vcgen.
          unfold PDX in H3.
          unfold PTX in H3.
          simpl in H3.
          rewrite H3.
          reflexivity.
          assert (0 < one_k) by omega.
          generalize (Z.mod_pos_bound (Int.unsigned vaddr / 4096) one_k H); intro.
          omega.
          assert (0 < one_k) by omega.
          generalize (Z.mod_pos_bound (Int.unsigned vaddr / 4096) one_k H); intro.
          omega.
        Qed.

      End PT_Read_Body.

      Theorem pt_read_code_correct:
        spec_le (pt_read ↦ ptRead_spec_low) (〚pt_read ↦ f_pt_read 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_read_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd (PTree.empty _) 
                                     (bind_parameter_temps' (fn_params f_pt_read)
                                                            (Vint n::Vint vadr::nil)
                                                            (create_undef_temps (fn_temps f_pt_read)))) H0.
      Qed.

    End PTREAD.



    Section PTREADPDE.

      Let L: compatlayer (cdata RData) := get_PDE ↦ gensem getPDE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section Pt_Read_Pde_Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bgetpde: block.

        Hypothesis hget_pde1 : Genv.find_symbol ge get_PDE = Some bgetpde. 
        
        Hypothesis hget_pde2 : Genv.find_funct_ptr ge bgetpde = Some (External (EF_external get_PDE (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma pt_read_pde_body_correct: forall m d env le proc_index vaddr paddr,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tvaddr le = Some (Vint vaddr) ->
                                      ptReadPDE_spec (Int.unsigned proc_index)
                                                      (Int.unsigned vaddr) d = Some (Int.unsigned paddr) ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_read_pde_body E0 le' (m, d) (Out_return (Some (Vint paddr, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          unfold pt_read_pde_body.
          intros.
          subst.
          functional inversion H2.
          unfold pdi in *.
          esplit.
          repeat vcgen.
          unfold PDX in H3.
          unfold PTX in H3.
          simpl in H3.
          rewrite H3.
          reflexivity.
        Qed.

      End Pt_Read_Pde_Body.

      Theorem pt_read_pde_code_correct:
        spec_le (pt_read_pde ↦ ptReadPDE_spec_low) (〚pt_read_pde ↦ f_pt_read_pde 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_read_pde_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd (PTree.empty _) 
                                     (bind_parameter_temps' (fn_params f_pt_read_pde)
                                                            (Vint n::Vint vadr::nil)
                                                            (create_undef_temps (fn_temps f_pt_read_pde)))) H0.
      Qed.

    End PTREADPDE.


    Section PTRMVAUX.

      Let L: compatlayer (cdata RData) := rmv_PTE ↦ gensem rmvPTE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section Pt_Rmv_Aux_Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable brmvptx: block.

        Hypothesis hrmv_ptx1 : Genv.find_symbol ge rmv_PTE = Some brmvptx. 
        
        Hypothesis hrmv_ptx2 : Genv.find_funct_ptr ge brmvptx = Some (External (EF_external rmv_PTE (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Lemma pt_rmv_aux_body_correct: forall m d d' env le proc_index vaddr,
                                     env = PTree.empty _ ->
                                     PTree.get tproc_index le = Some (Vint proc_index) ->
                                     PTree.get tvaddr le = Some (Vint vaddr) ->
                                     ptRmvAux_spec (Int.unsigned proc_index)
                                                    (Int.unsigned vaddr) d = Some d' ->
                                     exists le',
                                       exec_stmt ge env le ((m, d): mem) pt_rmv_aux_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          unfold pt_rmv_aux_body.
          intros.
          functional inversion H2.
          unfold pdi, pti in *.
          subst.
          esplit.
          repeat vcgen.
          unfold PDX, PTX in H4.
          simpl in H4.
          unfold Int.divu, Int.modu.
          repeat vcgen.
          assert (0 < one_k) by omega.
          generalize (Z.mod_pos_bound (Int.unsigned vaddr / 4096) one_k H); intro.
          omega.
          assert (0 < one_k) by omega.
          generalize (Z.mod_pos_bound (Int.unsigned vaddr / 4096) one_k H); intro.
          omega.
        Qed.

      End Pt_Rmv_Aux_Body.

      Theorem pt_rmv_aux_code_correct:
        spec_le (pt_rmv_aux ↦ ptRmvAux_spec_low) (〚pt_rmv_aux ↦ f_pt_rmv_aux 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_rmv_aux_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                     (bind_parameter_temps' (fn_params f_pt_rmv_aux)
                                                            (Vint n::Vint vadr::nil)
                                                            (create_undef_temps (fn_temps f_pt_rmv_aux)))) H0.
      Qed.

    End PTRMVAUX.


    Section PTRMVPDE.

      Let L: compatlayer (cdata RData) := rmv_PDE ↦ gensem rmvPDE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section Pt_Rmv_Pde_Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable brmvptx: block.

        Hypothesis hrmv_ptx1 : Genv.find_symbol ge rmv_PDE = Some brmvptx. 
        
        Hypothesis hrmv_ptx2 : Genv.find_funct_ptr ge brmvptx = Some (External (EF_external rmv_PDE (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Lemma pt_rmv_pde_body_correct: forall m d d' env le proc_index vaddr,
                                     env = PTree.empty _ ->
                                     PTree.get tproc_index le = Some (Vint proc_index) ->
                                     PTree.get tvaddr le = Some (Vint vaddr) ->
                                     ptRmvPDE_spec (Int.unsigned proc_index)
                                                    (Int.unsigned vaddr) d = Some d' ->
                                     exists le',
                                       exec_stmt ge env le ((m, d): mem) pt_rmv_pde_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          unfold pt_rmv_pde_body.
          intros.
          functional inversion H2.
          unfold pdi in *.
          subst.
          esplit.
          repeat vcgen.
          unfold PDX in H4.
          simpl in H4.
          unfold Int.divu.
          repeat vcgen.
        Qed.

      End Pt_Rmv_Pde_Body.

      Theorem pt_rmv_pde_code_correct:
        spec_le (pt_rmv_pde ↦ ptRmvPDE_spec_low) (〚pt_rmv_pde ↦ f_pt_rmv_pde 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_rmv_pde_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                     (bind_parameter_temps' (fn_params f_pt_rmv_pde)
                                                            (Vint n::Vint vadr::nil)
                                                            (create_undef_temps (fn_temps f_pt_rmv_pde)))) H0.
      Qed.

    End PTRMVPDE.


    Section PTINSERTAUX.

      Let L: compatlayer (cdata RData) := set_PTE ↦ gensem setPTE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTInsertAuxBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bsetptx: block.

        Hypothesis hset_ptx1 : Genv.find_symbol ge set_PTE = Some bsetptx. 
        
        Hypothesis hset_ptx2 : Genv.find_funct_ptr ge bsetptx = Some (External (EF_external set_PTE (signature_of_type (Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil))))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil))))) Tvoid cc_default).

        Lemma pt_insert_aux_body_correct: forall m d d' env le proc_index vaddr paddr perm,
                                        env = PTree.empty _ ->
                                        PTree.get tproc_index le = Some (Vint proc_index) ->
                                        PTree.get tvaddr le = Some (Vint vaddr) ->
                                        PTree.get tpaddr le = Some (Vint paddr) ->
                                        PTree.get tperm le = Some (Vint perm) ->
                                        ptInsertAux_spec (Int.unsigned proc_index)
                                                          (Int.unsigned vaddr) (Int.unsigned paddr) (Int.unsigned perm) d = Some d' ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) pt_insert_aux_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          unfold pt_insert_aux_body.
          intros.
          subst.
          functional inversion H4.
          unfold pdi, pti in *.
          esplit.
          repeat vcgen.
          unfold PDX, PTX in H5.
          simpl in H5.
          unfold Int.modu, Int.divu.
          repeat vcgen.
          assert (0 < one_k) by omega.
          generalize (Z.mod_pos_bound (Int.unsigned vaddr / 4096) one_k H); intro.
          omega.
          assert (0 < one_k) by omega.
          generalize (Z.mod_pos_bound (Int.unsigned vaddr / 4096) one_k H); intro.
          omega.
        Qed.

      End PTInsertAuxBody.

      Theorem pt_insert_aux_code_correct:
        spec_le (pt_insert_aux ↦ ptInsertAux_spec_low) (〚pt_insert_aux ↦ f_pt_insert_aux 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_insert_aux_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                     (bind_parameter_temps' (fn_params f_pt_insert_aux)
                                                            (Vint n::Vint vadr::Vint padr::Vint p0::nil)
                                                            (create_undef_temps (fn_temps f_pt_insert_aux)))) H0.
      Qed.

    End PTINSERTAUX.



    Section PTINSERTPDE.

      Let L: compatlayer (cdata RData) := set_PDEU ↦ gensem setPDEU_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTInsertPdeBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bsetptx: block.

        Hypothesis hset_ptx1 : Genv.find_symbol ge set_PDEU = Some bsetptx. 
        
        Hypothesis hset_ptx2 : Genv.find_funct_ptr ge bsetptx = Some (External (EF_external set_PDEU (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).

        Lemma pt_insert_pde_body_correct: forall m d d' env le proc_index vaddr pi,
                                        env = PTree.empty _ ->
                                        PTree.get tproc_index le = Some (Vint proc_index) ->
                                        PTree.get tvaddr le = Some (Vint vaddr) ->
                                        PTree.get tpi le = Some (Vint pi) ->
                                        ptInsertPDE_spec (Int.unsigned proc_index)
                                                          (Int.unsigned vaddr) (Int.unsigned pi) d = Some d' ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) pt_insert_pde_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          unfold pt_insert_pde_body.
          intros.
          subst.
          functional inversion H3.
          unfold pdi in *.
          esplit.
          repeat vcgen.
          unfold PDX in H4.
          simpl in H4.
          unfold Int.divu.
          repeat vcgen.
        Qed.

      End PTInsertPdeBody.

      Theorem pt_insert_pde_code_correct:
        spec_le (pt_insert_pde ↦ ptInsertPDE_spec_low) (〚pt_insert_pde ↦ f_pt_insert_pde 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_insert_pde_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                     (bind_parameter_temps' (fn_params f_pt_insert_pde)
                                                            (Vint n::Vint vadr::Vint padr::nil)
                                                            (create_undef_temps (fn_temps f_pt_insert_pde)))) H0.
      Qed.

    End PTINSERTPDE.


  End WithPrimitives.

End MPTINTROCODE.
