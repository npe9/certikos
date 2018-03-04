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
(*          for the C functions implemented in the MALT layer          *)
(*                                                                     *)
(*                        David Costanzo                               *)
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
Require Import MemWithData.
Require Import EventsX.
Require Import Globalenvs.
Require Import Locations.
Require Import LAsm.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
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
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import ContainerGenSpec.
Require Import MALTCSource.
Require Import TacticsForTesting.
Require Import MALT.

Require Import AbstractDataType.
Require Import CommonTactic.

(*Global Opaque compatdata_layerdata ldata_type.*)

Module MALTCODE.

  (* Helper lemmas related to struct *)
  Open Scope Z_scope.

  Lemma convert_quota :  forall i, Int.unsigned i < num_id ->
    Int.unsigned (Int.mul i (Int.repr 20)) + Int.unsigned (Int.repr 0) = Int.unsigned i * CSIZE + QUOTA.
  Proof.
    intros i Hi.
    assert (Hrange:= Int.unsigned_range_2 i).
    rewrite Int.mul_signed.
    rewrite 2 Int.signed_eq_unsigned; try rewrite max_signed_val; try omega.
    rewrite 3 Int.unsigned_repr; eauto; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
  Qed.

  Lemma convert_usage :  forall i, Int.unsigned i < num_id ->
    Int.unsigned (Int.mul i (Int.repr 20)) + Int.unsigned (Int.repr 4) = Int.unsigned i * CSIZE + USAGE.
  Proof.
    intros i Hi.
    assert (Hrange:= Int.unsigned_range_2 i).
    rewrite Int.mul_signed.
    rewrite 2 Int.signed_eq_unsigned; try rewrite max_signed_val; try omega.
    rewrite 3 Int.unsigned_repr; eauto; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
  Qed.

  Lemma convert_parent :  forall i, Int.unsigned i < num_id ->
    Int.unsigned (Int.mul i (Int.repr 20)) + Int.unsigned (Int.repr 8) = Int.unsigned i * CSIZE + PARENT.
  Proof.
    intros i Hi.
    assert (Hrange:= Int.unsigned_range_2 i).
    rewrite Int.mul_signed.
    rewrite 2 Int.signed_eq_unsigned; try rewrite max_signed_val; try omega.
    rewrite 3 Int.unsigned_repr; eauto; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
  Qed.

  Lemma convert_nchildren :  forall i, Int.unsigned i < num_id ->
    Int.unsigned (Int.mul i (Int.repr 20)) + Int.unsigned (Int.repr 12) = Int.unsigned i * CSIZE + NCHILDREN.
  Proof.
    intros i Hi.
    assert (Hrange:= Int.unsigned_range_2 i).
    rewrite Int.mul_signed.
    rewrite 2 Int.signed_eq_unsigned; try rewrite max_signed_val; try omega.
    rewrite 3 Int.unsigned_repr; eauto; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
  Qed.

  Lemma convert_used :  forall i, Int.unsigned i < num_id ->
    Int.unsigned (Int.mul i (Int.repr 20)) + Int.unsigned (Int.repr 16) = Int.unsigned i * CSIZE + USED.
  Proof.
    intros i Hi.
    assert (Hrange:= Int.unsigned_range_2 i).
    rewrite Int.mul_signed.
    rewrite 2 Int.signed_eq_unsigned; try rewrite max_signed_val; try omega.
    rewrite 3 Int.unsigned_repr; eauto; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
    rewrite Int.unsigned_repr; try rewrite max_unsigned_val; try omega.
  Qed.

  Close Scope Z_scope.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Opaque PTree.get PTree.set.

    Local Open Scope Z_scope.

    (* Helpers for omega *)
    Let Hmax := max_unsigned_val.
    Let Hnps_range := real_nps_range.
    Let Hquota_range := real_quota_range.
    Let Hstruct_size : sizeof t_struct_AC = 20. Proof. auto. Qed.

    Section ContainerInit.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops) (cdata_prf:= malt_data_prf)) :=
        AC_LOC ↦ container_loc_type 
               ⊕ mem_init ↦ gensem mem_init_spec
               ⊕ get_nps ↦ gensem get_nps_spec
               ⊕ is_norm ↦ gensem is_at_norm_spec
               ⊕ at_get ↦ gensem get_at_u_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section InitBody.

        Context `{Hwb: WritableBlockOps}.
        Context `{Hwbg: WritableBlockAllowGlobals WB}.

        Variables (s: stencil) (ge: genv).
        Hypothesis Hstencil_matches: stencil_matches s ge.

        (* AC_LOC *)
        Variable b_ac: block.
        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        (* mem_init *)
        Variable b_mi : block.
        Hypothesis hmem_init1 : Genv.find_symbol ge mem_init = Some b_mi. 
        Hypothesis hmem_init2 : Genv.find_funct_ptr ge b_mi =
          Some (External (EF_external mem_init
            (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (* get_nps *)
        Variable b_nps : block.
        Hypothesis hnps1 : Genv.find_symbol ge get_nps = Some b_nps.
        Hypothesis hnps2 : Genv.find_funct_ptr ge b_nps =
          Some (External (EF_external get_nps
            (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

         (* is_norm *)
        Variable b_norm : block.
        Hypothesis hnorm1 : Genv.find_symbol ge is_norm = Some b_norm. 
        Hypothesis hnorm2 : Genv.find_funct_ptr ge b_norm =
          Some (External (EF_external is_norm
            (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (* at_get *)
        Variable b_atget : block.
        Hypothesis hatget1 : Genv.find_symbol ge at_get = Some b_atget.
        Hypothesis hatget2 : Genv.find_funct_ptr ge b_atget =
          Some (External (EF_external at_get
            (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        Section Container_init_loop_proof.

          Variables (minit : memb) (dinit dpreinit : RData).
          Hypothesis ATinit : AT dinit = real_AT (AT dpreinit).
          Hypotheses (ikerninit : ikern dinit = true) (ihostinit : ihost dinit = true).

          Definition init_loop_body_P (le: temp_env) (m : mem) : Prop := 
            le ! t_nps = Some (Vint (Int.repr real_nps)) /\
            le ! t_rq = Some (Vint (Int.repr 0)) /\
            le ! t_i = Some (Vint (Int.repr 1)) /\ m = (minit, dinit).

          Definition init_loop_body_Q (le : temp_env) (m : mem): Prop :=
            le ! t_rq = Some (Vint (Int.repr real_quota)) /\ m = (minit, dinit).

          Lemma container_init_loop_correct : 
            LoopProofSimpleWhile.t container_init_while_condition container_init_while_body 
                                   ge (PTree.empty _) init_loop_body_P init_loop_body_Q.
          Proof.
            apply LoopProofSimpleWhile.make with
              (W := Z) (lt := fun z1 z2 => 0 <= z2 /\  z1 < z2)
              (I := fun le m w => 
                      exists i,
                        0 < i <= real_nps /\
                        le ! t_i = Some (Vint (Int.repr i)) /\
                        le ! t_nps = Some (Vint (Int.repr real_nps)) /\
                        le ! t_rq = Some (Vint (Int.repr (unused_pages_AT (AT dinit) (Z.to_nat (i-1))))) /\
                        m = (minit, dinit) /\ w = real_nps - i).
            apply Zwf_well_founded.
            unfold init_loop_body_P; intros le m Hle; decompose [and] Hle; clear Hle; subst.
            exists (real_nps - 1), 1; repeat (apply conj; try omega; auto).
            intros le m w [i Hle]; decompose [and] Hle; clear Hle; subst.
            assert (Hcases: i = real_nps \/ i < real_nps) by omega; destruct Hcases; subst.
            {
              (* while condition is false *)
              eexists; exists false; repeat split; try discriminate.
              repeat vcgen.
              cases; simpl; auto; omega.
              subrewrite'; repeat f_equal.
              rewrite real_quota_convert; rewrite real_quota_unused_pages_AT; reflexivity.
            }
            {
              (* while condition is true *)
              assert (Hi_conv: i = Z.pos (Pos.of_succ_nat (Z.to_nat (i - 1)))).
              {
                change (Z.pos (Pos.of_succ_nat (Z.to_nat (i-1)))) with (Z.of_nat (S (Z.to_nat (i-1)))).
                rewrite Nat2Z.inj_succ; rewrite <- Z.add_1_r.
                rewrite Z2Nat.id; omega.
              }
              eexists; exists true; repeat split; intros; try discriminate.
              repeat vcgen.
              cases; simpl; auto.
              clear Hdestruct; rewrite 2 Int.unsigned_repr in *; omega.
              destruct (ZMap.get i (AT dinit)) as [[|] t v|] eqn:Hat;
                try (destruct (ATType_dec t ATNorm); try subst t).

              (* Case 1: u = true, t = ATNorm *)
              eexists; exists (minit, dinit); repeat split.
              unfold container_init_while_body; d3 vcgen.
              (* call is_norm *)
              repeat vcgen.
              unfold is_at_norm_spec; rewrites; cases; try omega; try congruence.
              change 1 with (Int.unsigned (Int.repr 1)); reflexivity.
              d2 vcgen.
              (* call at_get *)
              repeat vcgen.
              unfold get_at_u_spec; rewrites; cases; try omega.
              change 1 with (Int.unsigned (Int.repr 1)); reflexivity.
              d2 vcgen.
              (* if statement (false) *)
              repeat vcgen.
              (* increment i *)
              repeat vcgen.
              (* reestablish loop invariant *)
              exists (real_nps - i - 1); repeat vcgen.
              exists (i + 1); repeat vcgen.
              replace (Z.to_nat (i+1-1)) with (S (Z.to_nat (i-1))).
              simpl; rewrite <- Hi_conv; rewrites; auto.
              rewrite <- Z2Nat.inj_succ; f_equal; omega.

              (* Case 2: u = true, t <> ATNorm *)
              eexists; exists (minit, dinit); repeat split.
              unfold container_init_while_body; d3 vcgen.
              (* call is_norm *)
              repeat vcgen.
              unfold is_at_norm_spec; rewrites; cases; try omega; try congruence.
              change 0 with (Int.unsigned (Int.repr 0)); reflexivity.
              d2 vcgen.
              (* call at_get *)
              repeat vcgen.
              unfold get_at_u_spec; rewrites; cases; try omega.
              change 1 with (Int.unsigned (Int.repr 1)); reflexivity.
              d2 vcgen.
              (* if statement (false) *)
              repeat vcgen.
              (* increment i *)
              repeat vcgen.
              (* reestablish loop invariant *)
              exists (real_nps - i - 1); repeat vcgen.
              exists (i + 1); repeat vcgen.
              replace (Z.to_nat (i+1-1)) with (S (Z.to_nat (i-1))).
              simpl; rewrite <- Hi_conv; rewrites; auto.
              rewrite <- Z2Nat.inj_succ; f_equal; omega.

              (* Case 3: u = false, t = ATNorm *)
              eexists; exists (minit, dinit); repeat split.
              unfold container_init_while_body; d3 vcgen.
              (* call is_norm *)
              repeat vcgen.
              unfold is_at_norm_spec; rewrites; cases; try omega; try congruence.
              change 1 with (Int.unsigned (Int.repr 1)); reflexivity.
              d2 vcgen.
              (* call at_get *)
              repeat vcgen.
              unfold get_at_u_spec; rewrites; cases; try omega.
              change 0 with (Int.unsigned (Int.repr 0)); reflexivity.
              d2 vcgen.
              (* if statement (true) *)
              repeat vcgen.
              (* increment i *)
              assert (Hrange:= unused_pages_AT_range (Z.to_nat (i - 1)) (AT dinit)).
              rewrite Z2Nat.id in Hrange by omega; repeat vcgen.
              (* reestablish loop invariant *)
              exists (real_nps - i - 1); repeat vcgen.
              exists (i + 1); repeat split; try solve [repeat vcgen].
              ptreesolve; repeat f_equal.
              replace (Z.to_nat (i+1-1)) with (S (Z.to_nat (i-1))).
              simpl; rewrite <- Hi_conv; rewrites; auto; omega.
              rewrite <- Z2Nat.inj_succ; f_equal; omega.

              (* Case 4: u = false, t <> ATNorm *)
              eexists; exists (minit, dinit); repeat split.
              unfold container_init_while_body; d3 vcgen.
              (* call is_norm *)
              repeat vcgen.
              unfold is_at_norm_spec; rewrites; cases; try omega; try congruence.
              change 0 with (Int.unsigned (Int.repr 0)); reflexivity.
              d2 vcgen.
              (* call at_get *)
              repeat vcgen.
              unfold get_at_u_spec; rewrites; cases; try omega.
              change 0 with (Int.unsigned (Int.repr 0)); reflexivity.
              d2 vcgen.
              (* if statement (false) *)
              repeat vcgen.
              (* increment i *)
              repeat vcgen.
              (* reestablish loop invariant *)
              exists (real_nps - i - 1); repeat vcgen.
              exists (i + 1); repeat vcgen.
              replace (Z.to_nat (i+1-1)) with (S (Z.to_nat (i-1))).
              simpl; rewrite <- Hi_conv; rewrites; destruct t; try congruence; auto.
              rewrite <- Z2Nat.inj_succ; f_equal; omega.
              
              (* Case 5: ATUndef (impossible) *)
              assert (Hcases: (0 <= i < kern_low \/ kern_high <= i < real_nps) \/ 
                      kern_low <= i < Z.min kern_high real_nps) by (rewrite Zmin_spec; cases; omega).
              rewrite ATinit in Hat; destruct Hcases as [Hi|Hi].
              rewrite (real_at_kern_valid (AT dpreinit) _ Hi) in Hat; discriminate.
              destruct (real_at_usr_valid (AT dpreinit) _ Hi) as [? [[? ?]|?]]; rewrites; discriminate.
            }
          Qed.

        End Container_init_loop_proof.

        Lemma container_init_while_correct: 
          forall m d pre_d le,
            ikern d = true -> ihost d = true -> AT d = real_AT (AT pre_d) ->
            le ! t_nps = Some (Vint (Int.repr real_nps)) ->
            le ! t_rq = Some (Vint (Int.repr 0)) ->
            le ! t_i = Some (Vint (Int.repr 1)) ->
            exists le', 
              exec_stmt ge (PTree.empty _) le ((m, d) : mem) 
                (Swhile container_init_while_condition container_init_while_body) 
                E0 le' (m, d) Out_normal /\ le' ! t_rq = Some (Vint (Int.repr real_quota)).
        Proof.
          intros m d pre_d le Hkern Hhost Hat Hnps Hrq Hi.
          assert (Hloop:= container_init_loop_correct m _ _ Hat Hkern Hhost).
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ Hloop le (m, d) _)).
          intros [? [? [? [? ?]]]]; subst; eauto.
          repeat split; auto.
        Qed.

        Lemma container_init_body_correct: 
          forall m m' (d d' : cdata RData) (m1 m2 m3 m4 : memb) env le mbi,
            env = PTree.empty _ -> le ! _mbi = Some (Vint mbi) ->
            mem_init_spec (Int.unsigned mbi) d = Some d' ->
            Mem.store Mint32 (m,d') b_ac QUOTA (Vint (Int.repr real_quota)) = Some (m1,d') ->
            Mem.store Mint32 (m1,d') b_ac USAGE (Vint Int.zero) = Some (m2,d') ->
            Mem.store Mint32 (m2,d') b_ac PARENT (Vint Int.zero) = Some (m3,d') ->
            Mem.store Mint32 (m3,d') b_ac NCHILDREN (Vint Int.zero) = Some (m4,d') ->
            Mem.store Mint32 (m4,d') b_ac USED (Vint Int.one) = Some (m',d') ->
            exists le',
              exec_stmt ge env le (m, d) container_init_body E0 le' (m', d') Out_normal.
        Proof.
          intros; subst.
          functional inversion H1; subst d'.

          (* Obtain the final le from the while loop and instantiate based on that *)
          destruct (container_init_while_correct m 
                      (d {MM : real_mm} {MMSize : real_size} {vmxinfo : real_vmxinfo} 
                         {AT : real_AT (AT d)} {nps : real_nps} {init : true}) d
                      (PTree.set t_i (Vint (Int.repr 1))
                         (PTree.set t_rq (Vint (Int.repr 0))
                            (PTree.set t_nps (Vint (Int.repr real_nps)) le))))
             as [le' [Hexec ?]]; auto; simpl; ptreesolve; exists le'.

          unfold container_init_body; simpl; repeat vcgen.
          unfold get_nps_spec; simpl; rewrites.
          rewrite Int.unsigned_repr; try omega; reflexivity.
        Qed.

      End InitBody.

      Theorem container_init_code_correct: 
        spec_le (container_init ↦ container_init_spec_low) 
                (〚container_init ↦ f_container_init〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (container_init_body_correct _ _ makeglobalenv _ H0 _ Hb2fs Hb2fp 
                    _ Hb3fs Hb3fp _ Hb4fs Hb4fp _ Hb5fs Hb5fp
                    m0 m'0 labd labd' m1 m2 m3 m4 (PTree.empty _)
                   (bind_parameter_temps' (fn_params f_container_init) (Vint mbi :: nil)
                      (create_undef_temps (fn_temps f_container_init)))) tt.
      Qed.

    End ContainerInit.

    Section ContainerGetParent.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops)) := AC_LOC ↦ container_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetParentBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv) (b_ac: block).

        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        Lemma container_get_parent_body_correct: 
          forall m d env le v i,
            env = PTree.empty _ -> le ! _id = Some (Vint i) -> 0 <= Int.unsigned i < num_id ->
            Mem.load Mint32 (m, d) b_ac (Int.unsigned i * CSIZE + PARENT) = Some (Vint v) ->
            exec_stmt ge env le (m, d) container_get_parent_body E0 le (m, d) (Out_return (Some (Vint v, tint))).
        Proof.
          intros; subst; unfold PARENT in *.
          unfold container_get_parent_body; simpl; repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
        Qed.

      End GetParentBody.

      Theorem container_get_parent_code_correct: 
        spec_le (container_get_parent ↦ container_get_parent_spec_low) 
                (〚container_get_parent ↦ f_container_get_parent〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (container_get_parent_body_correct _ _ H (fst m') (snd m') (PTree.empty _) 
                   (bind_parameter_temps' (fn_params f_container_get_parent) (Vint i :: nil) (PTree.empty _))) m'.
      Qed.

    End ContainerGetParent.

    Section ContainerGetNchildren.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops)) := AC_LOC ↦ container_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetNchildrenBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv) (b_ac: block).

        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        Lemma container_get_nchildren_body_correct: 
          forall m d env le v i,
            env = PTree.empty _ -> le ! _id = Some (Vint i) -> 0 <= Int.unsigned i < num_id ->
            Mem.load Mint32 (m, d) b_ac (Int.unsigned i * CSIZE + NCHILDREN) = Some (Vint v) ->
            exec_stmt ge env le (m, d) container_get_nchildren_body E0 le (m, d) (Out_return (Some (Vint v, tint))).
        Proof.
          intros; subst; unfold NCHILDREN in *.
          unfold container_get_nchildren_body; simpl; repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
        Qed.

      End GetNchildrenBody.

      Theorem container_get_nchildren_code_correct: 
        spec_le (container_get_nchildren ↦ container_get_nchildren_spec_low) 
                (〚container_get_nchildren ↦ f_container_get_nchildren〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (container_get_nchildren_body_correct _ _ H (fst m') (snd m') (PTree.empty _) 
                   (bind_parameter_temps' (fn_params f_container_get_nchildren) (Vint i :: nil) (PTree.empty _))) m'.
      Qed.

    End ContainerGetNchildren.

    Section ContainerGetQuota.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops)) := AC_LOC ↦ container_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetQuotaBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv) (b_ac: block).

        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        Lemma container_get_quota_body_correct: 
          forall m d env le v i,
            env = PTree.empty _ -> le ! _id = Some (Vint i) -> 0 <= Int.unsigned i < num_id ->
            Mem.load Mint32 (m, d) b_ac (Int.unsigned i * CSIZE + QUOTA) = Some (Vint v) ->
            exec_stmt ge env le (m, d) container_get_quota_body E0 le (m, d) (Out_return (Some (Vint v, tint))).
        Proof.
          intros; subst; unfold QUOTA in *.
          unfold container_get_quota_body; simpl; repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
        Qed.

      End GetQuotaBody.

      Theorem container_get_quota_code_correct: 
        spec_le (container_get_quota ↦ container_get_quota_spec_low) 
                (〚container_get_quota ↦ f_container_get_quota〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (container_get_quota_body_correct _ _ H (fst m') (snd m') (PTree.empty _) 
                   (bind_parameter_temps' (fn_params f_container_get_quota) (Vint i :: nil) (PTree.empty _))) m'.
      Qed.

    End ContainerGetQuota.

    Section ContainerGetUsage.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops)) := AC_LOC ↦ container_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetUsageBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv) (b_ac: block).

        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        Lemma container_get_usage_body_correct: 
          forall m d env le v i,
            env = PTree.empty _ -> le ! _id = Some (Vint i) -> 0 <= Int.unsigned i < num_id ->
            Mem.load Mint32 (m, d) b_ac (Int.unsigned i * CSIZE + USAGE) = Some (Vint v) ->
            exec_stmt ge env le (m, d) container_get_usage_body E0 le (m, d) (Out_return (Some (Vint v, tint))).
        Proof.
          intros; subst; unfold USAGE in *.
          unfold container_get_usage_body; simpl; repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
        Qed.

      End GetUsageBody.

      Theorem container_get_usage_code_correct: 
        spec_le (container_get_usage ↦ container_get_usage_spec_low) 
                (〚container_get_usage ↦ f_container_get_usage〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (container_get_usage_body_correct _ _ H (fst m') (snd m') (PTree.empty _) 
                   (bind_parameter_temps' (fn_params f_container_get_usage) (Vint i :: nil) (PTree.empty _))) m'.
      Qed.

    End ContainerGetUsage.

    Section ContainerCanConsume.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops)) := AC_LOC ↦ container_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section CanConsumeBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv) (b_ac: block).

        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        Lemma container_can_consume_body_correct: 
          forall m d env le i n q u,
            env = PTree.empty _ -> le ! _id = Some (Vint i) -> le ! _n = Some (Vint n) ->
            0 <= Int.unsigned i < num_id ->
            Mem.load Mint32 (m, d) b_ac (Int.unsigned i * CSIZE + QUOTA) = Some (Vint q) ->
            Mem.load Mint32 (m, d) b_ac (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
            exec_stmt ge env le (m, d) container_can_consume_body E0 le (m, d) 
              (Out_return (Some (Vint 
                 (match (Int.unsigned n <=? Int.unsigned q, 
                         Int.unsigned u <=? Int.unsigned q - Int.unsigned n) with
                  | (true, true) => Int.one 
                  | _ => Int.zero end), tint))).
        Proof.
          intros; subst.

          assert (((Int.unsigned n <=? Int.unsigned q) = true /\ 
                   (Int.unsigned u <=? Int.unsigned q - Int.unsigned n) = true) \/
                  ((Int.unsigned n <=? Int.unsigned q) = true /\ 
                   (Int.unsigned u <=? Int.unsigned q - Int.unsigned n) = false) \/
                  (Int.unsigned n <=? Int.unsigned q) = false) as Hcases.
          destruct (Int.unsigned n <=? Int.unsigned q); auto.
          destruct (Int.unsigned u <=? Int.unsigned q - Int.unsigned n); auto.

          destruct Hcases as [Hcase1|Hcase2].
          (* Case 1: n <= q && u <= q - n *)
          destruct Hcase1 as [Hle1 Hle2].
          rewrite Hle1; rewrite Hle2.
          vcgen; vcgen; try discriminate.
          vcgen; simpl.
          {
            vcgen; vcgen; eauto.
            vcgen; vcgen.
            vcgen; vcgen; vcgen; vcgen; eauto.
            apply deref_loc_reference; auto.
            simpl; unfold sem_add; simpl; unfold align; simpl.
            rewrite Int.add_zero_l; rewrite Int.mul_commut; auto.
            apply deref_loc_copy; auto.
            apply deref_loc_value with (chunk := Mint32); auto.
            unfold Mem.loadv; unfold align; simpl; unfold lift; simpl.
            rewrite Int.add_unsigned.
            rewrite Int.unsigned_repr; rewrite convert_quota; try rewrite max_unsigned_val; eauto;
              unfold CSIZE; unfold QUOTA; omega.
            vcgen.
          }
          {
            vcgen; simpl; unfold bool_val; simpl.
            destruct (zlt (Int.unsigned q) (Int.unsigned n)); simpl; unfold Int.eq.
            rewrite Z.leb_le in Hle1; omega.
            destruct (zeq (Int.unsigned Int.one) (Int.unsigned Int.zero)); simpl.
            inv e.
            eauto.
          }
          {
            vcgen; simpl.
            vcgen.
            vcgen.
            vcgen.
            vcgen; vcgen.
            vcgen.
            vcgen.
            vcgen; eauto.
            apply deref_loc_reference; auto.
            vcgen; eauto.
            simpl; unfold sem_add; simpl; unfold align; simpl.
            rewrite Int.add_zero_l; rewrite Int.mul_commut; auto.
            apply deref_loc_copy; auto.
            vcgen.
            vcgen.
            apply deref_loc_value with (chunk := Mint32); auto.
            unfold Mem.loadv; unfold align; simpl; unfold lift; simpl.
            rewrite Int.add_unsigned.
            rewrite Int.unsigned_repr; rewrite convert_usage; try rewrite max_unsigned_val; eauto;
              unfold CSIZE; unfold USAGE; omega.
            vcgen.
            vcgen.
            vcgen.
            vcgen.
            vcgen; vcgen.
            vcgen.
            vcgen; eauto.
            apply deref_loc_reference; auto.
            vcgen; eauto.
            simpl; unfold sem_add; simpl; unfold align; simpl.
            rewrite Int.add_zero_l; rewrite Int.mul_commut; auto.
            apply deref_loc_copy; auto.
            vcgen.
            vcgen.
            apply deref_loc_value with (chunk := Mint32); auto.
            unfold Mem.loadv; unfold align; simpl; unfold lift; simpl.
            rewrite Int.add_unsigned.
            rewrite Int.unsigned_repr; rewrite convert_quota; try rewrite max_unsigned_val; eauto;
              unfold CSIZE; unfold QUOTA; omega.
            vcgen; eauto.
            vcgen.
            vcgen.
            simpl.
            rewrite Int.unsigned_repr.
            destruct (zlt (Int.unsigned q - Int.unsigned n) (Int.unsigned u)).
            rewrite Z.leb_le in Hle2; omega.
            vcgen.
            rewrite Z.leb_le in Hle1; assert (Hrange := Int.unsigned_range_2 q).
            rewrite max_unsigned_val in Hrange |- *.
            split; try omega.
            apply Z.le_trans with (m := Int.unsigned q); try omega.
            assert (Hrange' := Int.unsigned_range_2 n); omega.
            simpl; vcgen; vcgen.
          }

          (* Case 2: (n <= q && u > q - n) || n > q *)
          replace E0 with (E0 ** E0).
          vcgen; vcgen.
          {            
            destruct Hcase2 as [[Hle1 Hle2]|Hle].

            (* Case 2A: n <= q && u > q - n *)
            vcgen.
            {
              vcgen; vcgen; eauto.
              vcgen.
              vcgen.
              vcgen; vcgen.
              vcgen; vcgen; eauto.
              apply deref_loc_reference; auto.
              vcgen; eauto.
              simpl; unfold sem_add; simpl; unfold align; simpl.
              rewrite Int.add_zero_l; rewrite Int.mul_commut; auto.
              apply deref_loc_copy; auto.
              vcgen.
              vcgen.
              apply deref_loc_value with (chunk := Mint32); auto.
              unfold Mem.loadv; unfold align; simpl; unfold lift; simpl.
              rewrite Int.add_unsigned.
              rewrite Int.unsigned_repr; rewrite convert_quota; try rewrite max_unsigned_val; eauto;
                unfold CSIZE; unfold QUOTA; omega.
              vcgen; eauto.
            }
            {
              simpl; destruct (zlt (Int.unsigned q) (Int.unsigned n)).
              rewrite Z.leb_le in Hle1; omega.
              vcgen.
            }
            {
              vcgen.
              vcgen; vcgen; eauto.
              vcgen.
              vcgen.
              vcgen; vcgen.
              vcgen; vcgen; eauto.
              apply deref_loc_reference; auto.
              vcgen; eauto.
              simpl; unfold sem_add; simpl; unfold align; simpl.
              rewrite Int.add_zero_l; rewrite Int.mul_commut; auto.
              apply deref_loc_copy; auto.
              vcgen.
              vcgen.
              apply deref_loc_value with (chunk := Mint32); auto.
              unfold Mem.loadv; unfold align; simpl; unfold lift; simpl.
              rewrite Int.add_unsigned.
              rewrite Int.unsigned_repr; rewrite convert_usage; try rewrite max_unsigned_val; eauto;
                unfold CSIZE; unfold USAGE; omega.
              vcgen; eauto.
              vcgen.
              vcgen.
              vcgen.
              vcgen.
              vcgen; vcgen.
              vcgen.
              vcgen; eauto.
              apply deref_loc_reference; auto.
              vcgen; eauto.
              simpl; unfold sem_add; simpl; unfold align; simpl.
              rewrite Int.add_zero_l; rewrite Int.mul_commut; auto.
              apply deref_loc_copy; auto.
              vcgen.
              vcgen.
              apply deref_loc_value with (chunk := Mint32); auto.
              unfold Mem.loadv; unfold align; simpl; unfold lift; simpl.
              rewrite Int.add_unsigned.
              rewrite Int.unsigned_repr; rewrite convert_quota; try rewrite max_unsigned_val; eauto;
                unfold CSIZE; unfold QUOTA; omega.
              vcgen; eauto.
              vcgen.
              vcgen.
              simpl.
              rewrite Int.unsigned_repr.
              destruct (zlt (Int.unsigned q - Int.unsigned n) (Int.unsigned u)).
              vcgen.
              rewrite Z.leb_nle in Hle2; omega.
              rewrite Z.leb_le in Hle1; assert (Hrange := Int.unsigned_range_2 q).
              rewrite max_unsigned_val in Hrange |- *.
              split; try omega.
              apply Z.le_trans with (m := Int.unsigned q); try omega.
              assert (Hrange' := Int.unsigned_range_2 n); omega.
              simpl; vcgen.
            }

            (* Case 2B: n > q *)
            vcgen.
            vcgen; vcgen; eauto.
            vcgen.
            vcgen.
            vcgen; vcgen.
            vcgen; vcgen; eauto.
            apply deref_loc_reference; auto.
            vcgen; eauto.
            simpl; unfold sem_add; simpl; unfold align; simpl.
            rewrite Int.add_zero_l; rewrite Int.mul_commut; auto.
            apply deref_loc_copy; auto.
            vcgen.
            vcgen.
            apply deref_loc_value with (chunk := Mint32); auto.
            unfold Mem.loadv; unfold align; simpl; unfold lift; simpl.
            rewrite Int.add_unsigned.
            rewrite Int.unsigned_repr; rewrite convert_quota; try rewrite max_unsigned_val; eauto;
              unfold CSIZE; unfold QUOTA; omega.
            vcgen; eauto.
            simpl.
            destruct (zlt (Int.unsigned q) (Int.unsigned n)).            
            vcgen.
            rewrite Z.leb_nle in Hle; omega.
            simpl; vcgen.
          }
          {
            destruct Hcase2 as [[Hle1 Hle2]|Hle].
            rewrite Hle1; rewrite Hle2; vcgen; vcgen.
            rewrite Hle; vcgen; vcgen.
          }
          {
            simpl; auto.
          }
        Qed.

      End CanConsumeBody.

      Theorem container_can_consume_code_correct: 
        spec_le (container_can_consume ↦ container_can_consume_spec_low) 
                (〚container_can_consume ↦ f_container_can_consume〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (container_can_consume_body_correct _ _ H (fst m') (snd m') (PTree.empty _) 
                   (bind_parameter_temps' (fn_params f_container_can_consume) 
                   (Vint i :: Vint n :: nil) (PTree.empty _))) m'.
      Qed.

    End ContainerCanConsume.

    Section ContainerSplit.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops)) :=
        AC_LOC ↦ container_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SplitBody.

        Context `{Hwb: WritableBlockOps}.
        Context `{Hwbg: WritableBlockAllowGlobals WB}.

        Variable (s: stencil).

        Variables (ge: genv) (b_ac b_bl: block).

        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        (* Parameters *)
        Variables (i q : int).

        Lemma container_split_body_correct: 
          forall m m' (d : cdata RData) env j u nc (m1 m2 m3 m4 m5 m6: memb),
            env = PTree.empty _ -> 0 <= Int.unsigned i < num_id -> 0 <= Int.unsigned j < num_id ->
            Int.unsigned j = Int.unsigned i * max_children + 1 + Int.unsigned nc -> 
            Mem.load Mint32 (m,d) b_ac (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
            Mem.load Mint32 (m,d) b_ac (Int.unsigned i * CSIZE + NCHILDREN) = Some (Vint nc) ->
            Mem.store Mint32 (m,d) b_ac (Int.unsigned j * CSIZE + USED) (Vint Int.one) = Some (m1,d) ->
            Mem.store Mint32 (m1,d) b_ac (Int.unsigned j * CSIZE + QUOTA) (Vint q) = Some (m2,d) ->
            Mem.store Mint32 (m2,d) b_ac (Int.unsigned j * CSIZE + USAGE) (Vint Int.zero) = Some (m3,d) ->
            Mem.store Mint32 (m3,d) b_ac (Int.unsigned j * CSIZE + PARENT) (Vint i) = Some (m4,d) ->
            Mem.store Mint32 (m4,d) b_ac (Int.unsigned j * CSIZE + NCHILDREN) (Vint Int.zero) = Some (m5,d) ->
            Mem.store Mint32 (m5,d) b_ac (Int.unsigned i * CSIZE + USAGE) (Vint (Int.add u q)) = Some (m6,d) ->
            Mem.store Mint32 (m6,d) b_ac (Int.unsigned i * CSIZE + NCHILDREN) (Vint (Int.add nc Int.one)) = Some (m',d) ->
            exists le,
              exec_stmt ge env (PTree.set _n (Vint q) (PTree.set _id (Vint i) (create_undef_temps (fn_temps f_container_split)))) 
                      (m, d) container_split_body E0 le (m', d) (Out_return (Some (Vint j, tint))).
        Proof.
          intros; subst.
          rename H2 into Hj, H5 into Hs1, H6 into Hs2, H7 into Hs3, H8 into Hs4, H9 into Hs5,
                 H10 into Hs6, H11 into Hs7.

          assert (Hsep: forall m k1 k2 a b : Z, a <> b -> 0 <= m ->
                      0 <= k1 -> k1 + size_chunk Mint32 <= m -> 0 <= k2 -> k2 + size_chunk Mint32 <= m -> 
                      a * m + k1 + size_chunk Mint32 <= b * m + k2 \/ b * m + k2 + size_chunk Mint32 <= a * m + k1).
          intros m0 k1 k2 a1 a2 Ha_neq Hm_0 Hk1_0 Hle1 Hk2_0 Hle2.
          assert (a1 < a2 \/ a2 < a1) as Ha; try omega.
          destruct Ha; [left | right].
          apply Z.le_trans with (m := a1 * m0 + m0); try omega.
          replace (a1 * m0 + m0) with ((a1 + 1) * m0).
          assert (a1 + 1 <= a2) as Hle_a; try omega.
          apply Z.mul_le_mono_nonneg_r with (p := m0) in Hle_a; auto; omega.
          rewrite Z.mul_add_distr_r; omega.
          apply Z.le_trans with (m := a2 * m0 + m0); try omega.
          replace (a2 * m0 + m0) with ((a2 + 1) * m0).
          assert (a2 + 1 <= a1) as Hle_a; try omega.
          apply Z.mul_le_mono_nonneg_r with (p := m0) in Hle_a; auto; omega.
          rewrite Z.mul_add_distr_r; omega.
          unfold CSIZE, QUOTA, USAGE, PARENT, NCHILDREN, USED in *.
          unfold size_chunk in Hsep.

          assert (Hneq: Int.unsigned i <> Int.unsigned j)
            by (assert (Hrange:= Int.unsigned_range nc); omega).

          exists ((PTree.set t_child (Vint j) (PTree.set t_nc (Vint nc) 
                  (PTree.set _n (Vint q) (PTree.set _id (Vint i)
                     (create_undef_temps (fn_temps f_container_split))))))).
          unfold container_split_body; simpl; d3 vcgen.
          (* set t_nc *)
          repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
          d2 vcgen.
          (* set t_child *)
          repeat vcgen.
          d3 vcgen.
          (* set child's USED *)
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; rewrite Hj in *; repeat vcgen.
          d2 vcgen.
          (* set child's QUOTA *)
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; rewrite Hj in *; repeat vcgen.
          d2 vcgen.
          (* set child's USAGE *)
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; rewrite Hj in *; repeat vcgen.
          d2 vcgen.
          (* set child's PARENT *)
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; rewrite Hj in *; repeat vcgen.
          d2 vcgen.
          (* set child's NCHILDREN *)
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; rewrite Hj in *; repeat vcgen.
          d2 vcgen.
          (* increase parent's USAGE *)
          repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
          rewrite (Mem.load_store_other _ _ _ _ _ _ Hs5); try solve [right; apply Hsep; auto; try omega].
          rewrite (Mem.load_store_other _ _ _ _ _ _ Hs4); try solve [right; apply Hsep; auto; try omega].
          rewrite (Mem.load_store_other _ _ _ _ _ _ Hs3); try solve [right; apply Hsep; auto; try omega].
          rewrite (Mem.load_store_other _ _ _ _ _ _ Hs2); try solve [right; apply Hsep; auto; try omega].
          rewrite (Mem.load_store_other _ _ _ _ _ _ Hs1); try solve [right; apply Hsep; auto; try omega]; eauto.
          repeat vcgen.
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; repeat vcgen.
          d2 vcgen.
          (* increment parent's NCHILDREN *)
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; repeat vcgen.
          replace j with (Int.repr (Int.unsigned i * 3 + 1 + Int.unsigned nc)).
          repeat vcgen.
          apply f_equal with (f:= Int.repr) in Hj.
          rewrite Int.repr_unsigned in Hj; congruence.
        Qed.

      End SplitBody.

      Theorem container_split_code_correct: 
        spec_le (container_split ↦ container_split_spec_low) 
                (〚container_split ↦ f_container_split〛 L).
      Proof.
        fbigstep_pre L.
        repeat (match goal with
                | [ H : _ = _ /\ _ = _ |- _ ] => destruct H
                end).

        fbigstep (container_split_body_correct _ _ H i n (fst m) (fst m') (snd m) (PTree.empty _)
                     j u nc (fst m1) (fst m2) (fst m3) (fst m4) (fst m5) (fst m6)) m.
        rewrite <- H22 in H24; rewrite <- H23 in H24; inv H24.
        rewrite <- H22 in H24; rewrite <- H23 in H24; inv H24.
        destruct m'; auto.
      Qed.

    End ContainerSplit.

    Section ContainerAlloc.

      Let L: compatlayer (cdata RData (cdata_ops:= malt_data_ops)) := 
        AC_LOC ↦ container_loc_type ⊕ palloc ↦ gensem palloc'_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section AllocBody.

        Context `{Hwb: WritableBlockOps}.
        Context `{Hwbg: WritableBlockAllowGlobals WB}.

        Variables (s: stencil) (ge: genv).
        Hypothesis Hstencil_matches: stencil_matches s ge.
        
        Variable b_ac: block.
        Hypothesis hac_loc1 : Genv.find_symbol ge AC_LOC = Some b_ac.

        (* palloc *)
        Variable b_palloc : block.
        Hypothesis hpalloc1 : Genv.find_symbol ge palloc = Some b_palloc.
        Hypothesis hpalloc2 : Genv.find_funct_ptr ge b_palloc =
          Some (External (EF_external palloc
            (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        Lemma container_alloc_body_correct0: 
          forall m d env le i u,
            env = PTree.empty _ -> le ! _id = Some (Vint i) ->
            0 <= Int.unsigned i < num_id -> 
            Mem.load Mint32 (m,d) b_ac (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
            Mem.load Mint32 (m,d) b_ac (Int.unsigned i * CSIZE + QUOTA) = Some (Vint u) ->  
            exec_stmt ge env le (m,d) container_alloc_body E0 
                      (PTree.set t_q (Vint u) (PTree.set t_u (Vint u) le))
                      (m,d) (Out_return (Some (Vzero,tint))).
        Proof.
          intros; subst.
          unfold container_alloc_body; simpl.
          d3 vcgen.     
          (* load usage into u *)
          repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
          d2 vcgen.
          (* load quota into q *)
          repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
          (* evaluate if statement to true and return 0 *)
          apply exec_Sseq_2; try discriminate; repeat vcgen.
        Qed.

        Lemma container_alloc_body_correct1: 
          forall m m' (d d' : cdata RData) env le i u q pi,
            env = PTree.empty _ -> le ! _id = Some (Vint i) ->
            0 <= Int.unsigned i < num_id -> Int.unsigned u < Int.unsigned q ->
            0 <= pi <= Int.max_unsigned -> palloc'_spec d = Some (d', pi) ->
            Mem.load Mint32 (m,d) b_ac (Int.unsigned i * CSIZE + USAGE) = Some (Vint u) ->
            Mem.load Mint32 (m,d) b_ac (Int.unsigned i * CSIZE + QUOTA) = Some (Vint q) ->
            Mem.store Mint32 (m,d) b_ac (Int.unsigned i * CSIZE + USAGE) (Vint (Int.add u Int.one)) = Some (m',d) ->
            exec_stmt ge env le (m,d) container_alloc_body E0
                      (PTree.set t_i (Vint (Int.repr pi)) 
                         (PTree.set t_q (Vint q) 
                            (PTree.set t_u (Vint u) le)))
                      (m',d') (Out_return (Some (Vint (Int.repr pi), tint))).
        Proof.
          intros; subst.
          unfold container_alloc_body; simpl.
          d3 vcgen.
          (* load usage into u *)
          repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
          d2 vcgen.
          (* load quota into q *)
          repeat vcgen.
          unfold Mem.loadv; rewrite Z.mul_comm; repeat vcgen.
          d2 vcgen.
          (* evaluate if statement to false and skip over it *)
          repeat vcgen.
          d2 vcgen.
          (* increment usage *)
          repeat vcgen.
          unfold Mem.storev; rewrite Z.mul_comm; repeat vcgen.
          d2 vcgen.
          (* call palloc *)
          repeat vcgen.
          (* return pi *)
          repeat vcgen.
        Qed.

      End AllocBody.

      Theorem container_alloc_code_correct: 
        spec_le (container_alloc ↦ container_alloc_spec_low) 
                (〚container_alloc ↦ f_container_alloc〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (container_alloc_body_correct0 _ _ H (fst m') (snd m') (PTree.empty _) 
                   (bind_parameter_temps' (fn_params f_container_alloc) (Vint i :: nil)
                      (create_undef_temps (fn_temps f_container_alloc)))) m'.
        fbigstep (container_alloc_body_correct1 _ _ makeglobalenv _ H0 _ Hb2fs Hb2fp 
                    m0 m'0 d d' (PTree.empty _) 
                    (bind_parameter_temps' (fn_params f_container_alloc) (Vint i :: nil)
                      (create_undef_temps (fn_temps f_container_alloc)))) tt.
      Qed.

    End ContainerAlloc.

  End WithPrimitives.

End MALTCODE.
