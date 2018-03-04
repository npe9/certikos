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
(*          for the C functions implemented in the MPTBit layer        *)
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
Require Import MPTInit.
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
Require Import MPTInitCSource.


Module MPTINITCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.
    


    Section PTRESV2.

      Let L: compatlayer (cdata RData) := container_alloc ↦ gensem alloc_spec
           ⊕ pt_insert ↦ gensem ptInsert0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTResv2Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** container_alloc *)

        Variable balloc: block.

        Hypothesis halloc1 : Genv.find_symbol ge container_alloc = Some balloc. 
        
        Hypothesis halloc2 : Genv.find_funct_ptr ge balloc = Some (External (EF_external container_alloc (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** pt_insert2 *)

        Variable bptinsert: block.

        Hypothesis hpt_insert1 : Genv.find_symbol ge pt_insert = Some bptinsert. 
        
        Hypothesis hpt_insert2 : Genv.find_funct_ptr ge bptinsert = Some (External (EF_external pt_insert (signature_of_type (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))) tint cc_default)) (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))) tint cc_default).

        Lemma pt_resv2_body_correct: forall m d d' env le proc_index vaddr perm proc_index2 vaddr2 perm2 v,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tvaddr le = Some (Vint vaddr) ->
                                      PTree.get tperm le = Some (Vint perm) ->
                                      PTree.get tproc_index2 le = Some (Vint proc_index2) ->
                                      PTree.get tvaddr2 le = Some (Vint vaddr2) ->
                                      PTree.get tperm2 le = Some (Vint perm2) ->
                                      ptResv2_spec (Int.unsigned proc_index) (Int.unsigned vaddr) (Int.unsigned perm) (Int.unsigned proc_index2) (Int.unsigned vaddr2) (Int.unsigned perm2) d = Some (d', Int.unsigned v) ->
                                      high_level_invariant d ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_resv2_body E0 le' (m, d') (Out_return (Some (Vint v, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold pt_resv2_body.
          inversion H7.
          functional inversion H6; subst.
          {
            rewrite <- Int.unsigned_repr with 1048577 in H8; try omega.
            apply unsigned_inj in H8.
            rewrite <- H8.
            functional inversion H9; subst.
            {
              destruct _x.
              omega.
            }
            {
              change 0 with (Int.unsigned Int.zero) in H9.
              esplit.
              repeat vcgen.
            }
          }
          {
            rewrite <- Int.unsigned_repr with 1048577 in H8; try omega.
            apply unsigned_inj in H8.
            rewrite <- H8.
            functional inversion H9;subst.
            {
              destruct _x0.
              destruct a0.
              generalize (valid_nps H17); intro npsrange.
              esplit.
              repeat vcgen.
            }
            {
              omega.
            }
          }
          {
            functional inversion H8; subst.
            {
              destruct _x1.
              destruct a0.
              generalize (valid_nps H17); intro npsrange.
              functional inversion H10; functional inversion H28; subst; esplit; repeat vcgen.
              destruct _x2.
              destruct a1.
              simpl in a0.
              instantiate (1:= v0).
              repeat vcgen.
              discharge_cmp.
              omega.
              destruct _x2.
              destruct a1.
              simpl in a0.
              omega.
              repeat vcgen.
              repeat vcgen.
            }
            {
              omega.
            }
          }
          Grab Existential Variables.
          apply le.
          apply le.
          apply le.
        Qed.

      End PTResv2Body.

      Theorem pt_resv2_code_correct:
        spec_le (pt_resv2 ↦ ptResv2_spec_low) (〚pt_resv2 ↦ f_pt_resv2 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_resv2_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_resv2)
                                                               (Vint n::Vint vadr::Vint p0::Vint n'::Vint vadr'::Vint p'::nil)
                                                               (create_undef_temps (fn_temps f_pt_resv2)))) H0. 
      Qed.

    End PTRESV2.



    Section PTNEW.

      Let L: compatlayer (cdata RData) := container_split ↦ gensem container_split_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.


      Section PTNewBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (* parameters *)
        Variables (id quota: int).

        (** container_split *)

        Variable bsplit: block.

        Hypothesis hsplit1 : Genv.find_symbol ge container_split = Some bsplit.

        Hypothesis hsplit2 : 
          Genv.find_funct_ptr ge bsplit = Some (External 
            (EF_external container_split (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) 
            (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma pt_new_body_correct: 
          forall m d d' env le n,
            env = PTree.empty _ ->
            pt_new_spec (Int.unsigned id) (Int.unsigned quota) d = Some (d', Int.unsigned n) ->            
            le ! tid = Some (Vint id) -> le ! tquota = Some (Vint quota) ->
            exists le',
              exec_stmt ge env le ((m, d): mem) pt_new_body E0 le' (m, d') (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold pt_new_body.
          functional inversion H0.
          unfold update_cusage, update_cchildren in *; rewrite ZMap.gss in *; simpl in *.          
          exists (PTree.set tchild (Vint n) le).
          repeat vcgen.
          subst; apply PTree.gempty.
          unfold container_split_spec, update_cusage, update_cchildren; subst child c i.
          repeat (match goal with
                  | [ H : ?a = _ |- context [if ?a then _ else _] ] => rewrite H
                  | [ |- context [if ?a then _ else _] ] => destruct a; try omega
                  end).
          rewrite ZMap.gss; subst.
          apply f_equal with (f:= Int.repr) in H4; rewrite Int.repr_unsigned in H4; subst.
          repeat vcgen.
        Qed.

      End PTNewBody.

      Theorem pt_new_code_correct:
        spec_le (pt_new ↦ pt_new_spec_low) (〚pt_new ↦ f_pt_new 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (pt_new_body_correct s (Genv.globalenv p) makeglobalenv id q b0 Hb0fs Hb0fp 
                                      m'0 labd labd' (PTree.empty _) 
                                      (bind_parameter_temps' (fn_params f_pt_new)
                                         (Vint id :: Vint q :: nil)
                                         (create_undef_temps (fn_temps f_pt_new)))) H0.
      Qed.

    End PTNEW.


    Section PTRESV.

      Let L: compatlayer (cdata RData) := container_alloc ↦ gensem alloc_spec
           ⊕ pt_insert ↦ gensem ptInsert0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTResvBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** container_alloc *)

        Variable balloc: block.

        Hypothesis halloc1 : Genv.find_symbol ge container_alloc = Some balloc. 
        
        Hypothesis halloc2 : Genv.find_funct_ptr ge balloc = Some (External (EF_external container_alloc (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** pt_insert2 *)

        Variable bptinsert: block.

        Hypothesis hpt_insert1 : Genv.find_symbol ge pt_insert = Some bptinsert. 
        
        Hypothesis hpt_insert2 : Genv.find_funct_ptr ge bptinsert = Some (External (EF_external pt_insert (signature_of_type (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))) tint cc_default)) (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))) tint cc_default).

        Lemma pt_resv_body_correct: forall m d d' env le proc_index vaddr perm v,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tvaddr le = Some (Vint vaddr) ->
                                      PTree.get tperm le = Some (Vint perm) ->
                                      ptResv_spec (Int.unsigned proc_index)
                                                    (Int.unsigned vaddr) (Int.unsigned perm) d = Some (d', Int.unsigned v) ->
                                      high_level_invariant d ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_resv_body E0 le' (m, d') (Out_return (Some (Vint v, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold pt_resv_body.
          inversion H4.
          functional inversion H3; subst.
          {
            rewrite <- Int.unsigned_repr with 1048577 in H5; try omega.
            apply unsigned_inj in H5.
            rewrite <- H5.
            functional inversion H6;subst.
            {
              destruct _x.
              destruct a0.
              generalize (valid_nps H12); intro npsrange.
              esplit.
              repeat vcgen.
            }
            {
              change 0 with (Int.unsigned Int.zero) in H6.
              esplit.
              repeat vcgen.
            }
          }
          {
            functional inversion H5; subst.
            {
              destruct _x0.
              destruct a0.
              generalize (valid_nps H12); intro npsrange.
              esplit.
              repeat vcgen.
            }
            {
              change 0 with (Int.unsigned Int.zero) in H5.
              esplit.
              repeat vcgen.
            }
          }
          Grab Existential Variables.
          apply le.
          apply le.
        Qed.

      End PTResvBody.

      Theorem pt_resv_code_correct:
        spec_le (pt_resv ↦ ptResv_spec_low) (〚pt_resv ↦ f_pt_resv 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_resv_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_resv)
                                                               (Vint n::Vint vadr::Vint p0::nil)
                                                               (create_undef_temps (fn_temps f_pt_resv)))) H0. 
      Qed.

    End PTRESV.


    Section PMAPINIT.

      Let L: compatlayer (cdata RData) := pt_init ↦ gensem pt_init_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Section PMapInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** pt_init *)

        Variable bptinit: block.

        Hypothesis hpt_init1 : Genv.find_symbol ge pt_init = Some bptinit. 
        
        Hypothesis hpt_init2 : Genv.find_funct_ptr ge bptinit = Some (External (EF_external pt_init (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        Lemma pmap_init_body_correct: 
          forall m d d' env le mbi_adr,
            env = PTree.empty _ ->
            PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
            pmap_init_spec (Int.unsigned mbi_adr) d = Some d' ->
            exec_stmt ge env le ((m, d): mem) pmap_init_body E0 le (m, d') Out_normal.
        Proof.
          intros; unfold pmap_init_body.
          functional inversion H1.
          change le with (set_opttemp None Vundef le); repeat vcgen.
          subst; apply PTree.gempty.
          unfold pt_init_spec.
          repeat (match goal with
                  | [ H : ?a = _ |- context[if ?a then _ else _] ] => rewrite H
                  end); auto.
        Qed.

      End PMapInitBody.

      Theorem pmap_init_code_correct:
        spec_le (pmap_init ↦ pmap_init_spec_low) (〚pmap_init ↦ f_pmap_init 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (pmap_init_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp 
                                         m'0 labd labd' (PTree.empty _) 
                                         (bind_parameter_temps' (fn_params f_pmap_init)
                                                                (Vint mbi_adr::nil)
                                                                (create_undef_temps (fn_temps f_pmap_init)))) H0. 
      Qed.

    End PMAPINIT.



(*
    Section PTFREE.

      Let L: compatlayer (cdata RData) := set_bit ↦ gensem (fun a b d => set_pt_bit_spec d a b)
           ⊕ pt_rmv ↦ gensem (fun a b d => ptRmv_spec d a b).

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PTFreeBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_bit *)

        Variable bsetbit: block.

        Hypothesis hset_bit1 : Genv.find_symbol ge set_bit = Some bsetbit. 
        
        Hypothesis hset_bit2 : Genv.find_funct_ptr ge bsetbit = Some (External (EF_external set_bit (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** pt_rmv *)

        Variable bptrmv: block.

        Hypothesis hpt_rmv1 : Genv.find_symbol ge pt_rmv = Some bptrmv. 
        
        Hypothesis hpt_rmv2 : Genv.find_funct_ptr ge bptrmv = Some (External (EF_external pt_rmv (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        Definition pt_free_mk_rdata adt (i: Z) (proc_index: Z) := (mkRData (HP adt) (ti adt) (pe adt) (ikern adt) (ihost adt) (AT adt) (nps adt) (PT adt) (ZMap.set proc_index (Calculate_free_pt (Z.to_nat ((i - (kern_low * PgSize)) / PgSize)) (ZMap.get proc_index (ptpool adt))) (ptpool adt)) (ipt adt) (pb adt)).

        Section pt_free_loop_proof.

          Variable minit: memb.
          Variable proc_index: int.
          Variable adt: RData.
          Hypothesis pe : pe adt = true.
          Hypothesis ipt : ipt adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis indexrange: 0 < Int.unsigned proc_index < num_proc.
          Hypothesis hinv: high_level_invariant adt.

          Lemma valid_PT_kern: forall m: mem, ipt adt = true -> pe adt = true -> PT adt = 0.
          Proof.
            intros.
            remember adt as ad.
            destruct ad.
            destruct hinv.
            rewrite Heqad in *.
            apply valid_PT_kern; auto.
          Qed.

          Definition pt_free_loop_body_P (le: temp_env) (m: mem): Prop := 
            PTree.get ti le = Some (Vint (Int.repr adr_low)) /\ 
            PTree.get tproc_index le = Some (Vint proc_index) /\ 
            (forall i, adr_low <= Int.unsigned i < adr_high -> 
                       exists pdt, ZMap.get (PDX (Int.unsigned i))
                                            (ZMap.get (Int.unsigned proc_index)
                                                      (ptpool adt)) = PDTValid pdt) /\
            m = (minit, adt).

          Definition pt_free_loop_body_Q (le : temp_env) (m: mem): Prop := 
            m = (minit, pt_free_mk_rdata adt (adr_high - PgSize) (Int.unsigned proc_index)).

          Lemma pt_free_loop_correct_aux : LoopProofSimpleWhile.t pt_free_while_condition pt_free_while_body ge (PTree.empty _) (pt_free_loop_body_P) (pt_free_loop_body_Q).
          Proof.
            generalize max_unsigned_val; intro muval.
            generalize adr_low_val; intro adrlowval.
            generalize adr_high_val; intro adrhighval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le (m: mem) w => exists i,
                                           PTree.get ti le = Some (Vint i) /\
                                           PTree.get tproc_index le = Some (Vint proc_index) /\
                                           ipt adt = true /\
                                           pe adt = true /\
                                           ihost adt = true /\
                                           (forall i, adr_low <= Int.unsigned i < adr_high -> 
                                                      exists pdt, ZMap.get (PDX (Int.unsigned i))
                                                                           (ZMap.get (Int.unsigned proc_index)
                                                                                     (ptpool adt)) = PDTValid pdt) /\
                                           (Int.unsigned i = adr_low /\ m = (minit, adt) \/ Int.unsigned i > adr_low /\ m = (minit, pt_free_mk_rdata adt (Int.unsigned i - PgSize) (Int.unsigned proc_index))) /\
                                           adr_low <= Int.unsigned i <= adr_high /\
                                           (PgSize | Int.unsigned i) /\
                                           w = adr_high - Int.unsigned i 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold pt_free_loop_body_P in H.
            destruct H as [tile tmpH].
            destruct tmpH as [tprocindexle tmpH].
            destruct tmpH as [pdtvalid msubst].
            subst.
            esplit. esplit. 
            repeat vcgen.
            unfold Z.divide.
            exists 262144.
            omega.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [tprocindexle tmpH].
            destruct tmpH as [nipt tmpH].
            destruct tmpH as [npe tmpH].
            destruct tmpH as [nihost tmpH].
            destruct tmpH as [pdtvalid tmpH].
            destruct tmpH as [mcase tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [idiv nval].
            subst.
            unfold pt_free_while_condition.
            unfold pt_free_while_body.
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.
            destruct m.
            Caseeq ihigh.

            (* i < adr_high *)
            intro ihigh.

            assert(icrange: adr_low <= Int.unsigned i < adr_high) by omega.
            generalize (pdtvalid i icrange); intro pdtvalidi.
            destruct pdtvalidi as [pdt pdtvalidi].
            generalize (valid_PT_kern (m, adt) nipt npe); intro pt.

            Caseeq mcase.

            (* i = adr_low *)
            intro tmpH.
            destruct tmpH as [jval msubst].
            rewrite jval.
            injection msubst; intros; subst.

            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold ptRmv_spec.
            rewrite ikern, pe, ihost, ipt, pdtvalidi.
            unfold ptRmv_Arg.
            repeat zdestruct.
            exists (adr_high - adr_low - PgSize).
            repeat vcgen.
            esplit. 
            Opaque Z.sub PTree.set "!".
            simpl.
            Transparent Z.sub.
            repeat vcgen.
            right.
            split.
            omega.
            assert(1073741824 <= Int.unsigned i + 4096 - 4096 < 4026531840) by omega.
            f_equal.
            unfold pt_free_mk_rdata.
            rewrite jval in *.
            simpl.
            unfold Calculate_free_pt_at_i.
            rewrite pdtvalidi.
            rewrite ipt, ihost, ikern, pe.
            reflexivity.
            unfold Z.divide in *.
            destruct idiv as [z idiv].
            exists (z + 1).
            omega.
            
            (* i > adr_low *)
            intro tmpH.
            destruct tmpH as [igt tmpH].
            injection tmpH; intros; subst.

            assert (exists pdt, ZMap.get (PDX (Int.unsigned i))
                                         (Calculate_free_pt
                                            (Z.to_nat ((Int.unsigned i - 4096 - 1073741824) / 4096))
                                            (ZMap.get (Int.unsigned proc_index) (ptpool adt))) = PDTValid pdt).
              set (ni:= Z.to_nat ((Int.unsigned i - 4096 - 1073741824) / 4096)).
              induction ni.
              (* ni = 0 *)
              simpl.
              unfold Calculate_free_pt_at_i.
              assert(exists pdt : PTE,
               ZMap.get (PDX 1073741824)
                 (ZMap.get (Int.unsigned proc_index) (ptpool adt)) =
               PDTValid pdt).
                rewrite <- Int.unsigned_repr with (1073741824); try omega.
                apply pdtvalid; auto.
                rewrite Int.unsigned_repr with (1073741824); try omega.
              destruct H.
              rewrite H.
              assert(icase: PDX (Int.unsigned i) = PDX 1073741824 \/ PDX (Int.unsigned i) <> PDX 1073741824) by omega.
              Caseeq icase.
              (* PDX i0 = PDX i *)
              intro ieqi.
              rewrite ieqi.
              rewrite ZMap.gss.
              esplit.
              reflexivity.
              (* PDX i0 <> PDX i *)
              intro ineqi.
              rewrite ZMap.gso.
              apply pdtvalid.
              assumption.
              assumption.
              (* ni = S ni' *)
              Opaque Z.of_nat.
              simpl.
              unfold Calculate_free_pt_at_i.
              destruct (ZMap.get (PDX (Z.of_nat (S ni) * 4096 + 1073741824))
           (Calculate_free_pt ni
              (ZMap.get (Int.unsigned proc_index) (ptpool adt)))).
              assert(icase: PDX (Int.unsigned i) = PDX (Z.of_nat (S ni) * 4096 + 1073741824) \/ PDX (Int.unsigned i) <> PDX (Z.of_nat (S ni) * 4096 + 1073741824)) by omega.
              Caseeq icase.
              (* PDX i0 = PDX i *)
              intro ieqi.
              rewrite ieqi.
              rewrite ZMap.gss.
              esplit.
              reflexivity.
              (* PDX i0 <> PDX i *)
              intro ineqi.
              rewrite ZMap.gso.
              assumption.
              assumption.
              assumption.
            destruct H.

            esplit. esplit.
            split.
            repeat vcgen.
            split.
            repeat vcgen.
            split.
            intro contra; discriminate contra.
            intro.
            esplit. esplit.
            repeat vcgen.
            unfold ptRmv_spec.
            simpl.
            rewrite ZMap.gss.
            rewrite ikern, pe, ihost, ipt.
            unfold ptRmv_Arg.
            repeat zdestruct.
            rewrite H.
            reflexivity.

            exists (adr_high - Int.unsigned i - PgSize).
            repeat vcgen.
            esplit. 
            repeat vcgen.
            right.
            split.
            omega.
            assert (irangenew: adr_low <= Int.unsigned i + 4096 - 4096 < adr_high) by omega.
            f_equal.
            unfold pt_free_mk_rdata.
            rewrite ZMap.set2.
            simpl.
            assert(tmp: ((Int.unsigned i + 4096 - 4096 - 1073741824) / 4096) = (Int.unsigned i - 4096 - 1073741824) / 4096 + 1).
            rewrite <- Z_div_plus_full.
            assert (tmp1: Int.unsigned i + 4096 - 4096 - 1073741824 = Int.unsigned i - 1073741824) by omega.
            assert (tmp2: Int.unsigned i - 4096 - 1073741824 + 1 * 4096 = Int.unsigned i - 1073741824) by omega.
            rewrite tmp1, tmp2.
            trivial.
            omega.
            rewrite tmp.
            change ((Int.unsigned i - 4096 - 1073741824) / 4096 + 1) with (Z.succ ((Int.unsigned i - 4096 - 1073741824) / 4096)).
            rewrite Z2Nat.inj_succ.
            Opaque Z.of_nat.
            simpl.
            rewrite Nat2Z.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            unfold Calculate_free_pt_at_i.
            assert(tmp2: (((Int.unsigned i - 4096 - 1073741824) / 4096 + 1) *
                          4096 + 1073741824) = Int.unsigned i).
            rewrite <- Z_div_plus_full.
            replace (Int.unsigned i - 4096 - 1073741824 + 1 * 4096) with (Int.unsigned i - 1073741824) by omega.
            destruct idiv as [z idiv].
            rewrite idiv.
            replace 1073741824 with (262144 * 4096) by omega. 
            rewrite <- Z.mul_sub_distr_r.
            rewrite Z_div_mult_full.
            rewrite <- Z.mul_add_distr_r.
            replace (z - 262144 + 262144) with z by omega.
            trivial.
            omega.
            omega.
            rewrite tmp2.
            simpl in H.
            rewrite H.
            rewrite pe, ikern, ihost, ipt.
            reflexivity.
            repeat discharge_unsigned_range.
            repeat discharge_unsigned_range.
            repeat discharge_unsigned_range.
            apply Z_div_pos; try omega.
            destruct idiv as [z idiv].
            rewrite idiv in *.
            omega.
            apply Z_div_pos; try omega.
            destruct idiv as [z idiv].
            rewrite idiv in *.
            omega.
            destruct idiv as [z idiv].
            rewrite idiv in *.
            omega.
            destruct idiv as [z idiv].
            rewrite idiv.
            unfold Z.divide.
            exists (z + 1).
            omega.

            (* j = adr_high *)
            intro jeqadrhigh.
            esplit. esplit.
            repeat vcgen.
            unfold pt_free_loop_body_Q.
            Caseeq mcase.
            intro tmpH.
            destruct tmpH.
            omega.
            intro tmpH.
            rewrite jeqadrhigh in tmpH.
            destruct tmpH as [ihigh' tmpH].
            assumption.
          Qed.

        End pt_free_loop_proof.

          Lemma pt_free_loop_correct: forall m d d' le proc_index,    
                                        pe d = true ->
                                        ipt d = true ->
                                        ikern d = true ->
                                        ihost d = true ->
                                        0 < Int.unsigned proc_index < num_proc ->
                                        high_level_invariant d ->
                                        PTree.get ti le = Some (Vint (Int.repr adr_low)) ->
                                        PTree.get tproc_index le = Some (Vint proc_index) ->  
                                        (forall i, adr_low <= Int.unsigned i < adr_high -> 
                                                   exists pdt, ZMap.get (PDX (Int.unsigned i))
                                                                        (ZMap.get (Int.unsigned proc_index)
                                                                                  (ptpool d)) = PDTValid pdt) ->
                                        d' = pt_free_mk_rdata d (adr_high - PgSize) (Int.unsigned proc_index) ->
                                        exists le', exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile pt_free_while_condition pt_free_while_body) E0 le' (m, d') Out_normal.
          Proof.
            intros m d d' le proc_index pe ipt ikern ihost indexrange hinv tile tindexle pdtvalid d'val.
            generalize (pt_free_loop_correct_aux m proc_index d pe ipt ikern ihost indexrange hinv).
            intro LP.
            refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
            intro pre.
            destruct pre as [le'' pre].
            destruct pre as [m'' pre].
            destruct pre as [pre1 pre2].
            unfold pt_free_loop_body_Q in pre2.
            subst.
            esplit.
            eassumption.
            unfold pt_free_loop_body_P.
            eauto.
          Qed.

        Lemma pt_free_body_correct: forall m d d' env le proc_index,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      pt_free_spec d (Int.unsigned proc_index) = Some d' ->
                                      high_level_invariant d ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_free_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold pt_free_body.
          functional inversion H1.
          subst.
          
          set (di:= {|
                     HP := HP d;
                     ti := ti d;
                     pe := pe d;
                     ikern := ikern d;
                     ihost := ihost d;
                     AT := AT d;
                     nps := nps d;
                     PT := PT d;
                     ptpool := ptpool d;
                     ipt := ipt d;
                     pb := ZMap.set (Int.unsigned proc_index) PTFalse (pb d) |}).
          exploit (pt_free_loop_correct m di (pt_free_mk_rdata di (4026531840 - 4096) (Int.unsigned proc_index)) (PTree.set ti (Vint (Int.repr adr_low)) (set_opttemp None Vundef le)) proc_index); repeat vcgen.
          generalize set_bit_inv; intro.
          inversion H.          
          eapply semprops_high_level_invariant; auto.
          instantiate  (2:= d).
          repeat econstructor.
          instantiate (2:= proc_index).
          instantiate (1:= (Int.repr 0)).
          unfold set_pt_bit_spec.
          unfold di.
          rewrite H3, H4, H5.
          unfold ZtoPTBit.
          repeat zdestruct.
          assumption.
          unfold di; simpl.
          destruct H2.
          rewrite H6 in valid_PT_common.
          exploit (valid_PT_common refl_equal (Int.unsigned proc_index)).
          omega.
          intro.
          destruct H2.
          unfold PDT_usr in H10.
          unfold PDT_valid in H10.
          unfold PDX in *.
          generalize (H10 (Int.unsigned i / 4096)); intro.
          rewrite <- Zdiv_Zdiv in H11; try omega.
          rewrite <- Zdiv_Zdiv; try omega.
          rewrite Z_div_mult_full in H11; try omega.
          apply H11.
          generalize H; clear; intro.
          xomega.
          destruct H as [le' stmt].

          esplit.
          repeat vcgen.
          unfold set_pt_bit_spec, di.
          rewrite H3, H4, H5.
          unfold ZtoPTBit.
          repeat zdestruct.
        Qed.

      End PTFreeBody.

      Theorem pt_free_code_correct:
        spec_le (pt_free ↦ pt_free_spec_low) (〚pt_free ↦ f_pt_free 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_free_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_free)
                                                               (Vint n::nil)
                                                               (create_undef_temps (fn_temps f_pt_free)))) H0. 
      Qed.

    End PTFREE.

*)


  End WithPrimitives.

End MPTINITCODE.
