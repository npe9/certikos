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
(*          for the C functions implemented in the MBoot layer         *)
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
Require Import MemWithData.
Require Import EventsX.
Require Import Globalenvs.
Require Import LAsm.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import MBoot.
Require Import ZArith.Zwf.
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
Require Import ALInitGenSpec.
Require Import MBootCSource.
Require Import TacticsForTesting.

Require Import AbstractDataType.

Global Opaque compatdata_layerdata ldata_type.

Module MBOOTCODE.

  Section WithPrimitives.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Opaque PTree.get PTree.set.

    Local Open Scope Z_scope.

    Section GetNps.

      Let L: compatlayer (cdata RData) := NPS_LOC ↦ nps_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetNpsBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv) (bnps_loc: block).

        Hypothesis hnps_loc1 : Genv.find_symbol ge NPS_LOC = Some bnps_loc.

        Lemma get_nps_body_correct: forall m d env le nps,
                                      env = PTree.empty _ ->
                                      Mem.loadv Mint32 (m, d) (Vptr bnps_loc Int.zero) = Some (Vint nps) ->
                                      exec_stmt ge env le (m, d) get_nps_body E0 le (m, d) (Out_return (Some (Vint nps, tint))).
        Proof.
          intros; subst.
          repeat vcgen.
        Qed.

      End GetNpsBody.

      Theorem get_nps_code_correct: 
        spec_le (get_nps ↦ get_nps_spec_low) (〚get_nps ↦ f_get_nps〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_nps_body_correct (Genv.globalenv p) b0 H (fst m') (snd m')) m'.
      Qed.    

    End GetNps.

    Section SetNps.

      Let L: compatlayer (cdata RData) := NPS_LOC ↦ nps_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetNpsBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv) (bnps_loc: block).

        Hypothesis hnps_loc1 : Genv.find_symbol ge NPS_LOC = Some bnps_loc.

        Lemma set_nps_body_correct: forall m m' d env le nps,
                                      env = PTree.empty _ ->
                                      PTree.get tnewnps le = Some (Vint nps) ->
                                      Mem.store Mint32 (m, d) bnps_loc 0 (Vint nps) = Some (m', d) ->
                                      exec_stmt ge env le (m, d) set_nps_body E0 le (m', d) Out_normal
        .
        Proof.
          intros; subst.
          repeat vcgen.
        Qed.

      End SetNpsBody.

      Theorem set_nps_correct: 
        spec_le (set_nps ↦ set_nps_spec_low) (〚set_nps ↦ f_set_nps 〛L).
      Proof.
        fbigstep_pre L. destruct H0 as [H0 Heq].
        fbigstep (set_nps_body_correct (Genv.globalenv p) b0 H (fst m) (fst m') (snd m) (PTree.empty _) 
                                       (bind_parameter_temps' (fn_params f_set_nps)
                                                              (Vint n::nil)
                                                              (create_undef_temps (fn_temps f_set_nps)))) m.
        destruct m'; simpl in *. congruence.
      Qed.

    End SetNps.


    Section IsNorm.

      Lemma structsize: sizeof t_struct_A = 12.
      Proof.
        generalize max_unsigned_val; intro muval.
        simpl.
        unfold align; simpl.
        trivial.
      Qed.

      Let L: compatlayer (cdata RData) := AT_LOC ↦ at_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section IsNormBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches s ge).

        Variable (bat_loc: block).

        Hypothesis hat_loc : Genv.find_symbol ge AT_LOC = Some bat_loc.

        Lemma is_norm_body_correct: forall m d env le index isnorm isnorm',
                                      env = PTree.empty _ ->
                                      0 <= (Int.unsigned index) < maxpage ->
                                      Mem.load Mint32 m bat_loc (Int.unsigned index * 12) = Some (Vint isnorm) ->
                                      Int.unsigned isnorm' = ZToATTypeZ (Int.unsigned isnorm) ->
                                      PTree.get tisnorm le = Some Vundef ->
                                      PTree.get tis_norm_index le = Some (Vint index) ->
                                      exists le',
                                        exec_stmt ge env le (m, d) is_norm_body E0 le' (m, d) (Out_return (Some (Vint isnorm', tint)))
        .
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          intros.
          unfold is_norm_body.
          subst.
          unfold ZToATTypeZ in H2.

          assert(isnormcase: Int.unsigned isnorm = 0 \/ Int.unsigned isnorm <> 0) by omega.
          Caseeq isnormcase.

          (* isnorm = 0 *)
          intro veq0.
          destruct (zeq (Int.unsigned isnorm) 0); try omega.
          change 0 with (Int.unsigned Int.zero) in e.
          change 0 with (Int.unsigned Int.zero) in H2.
          apply unsigned_inj in H2.
          apply unsigned_inj in e.
          subst.
          esplit.
          clear H3.
          repeat vcgen.
          unfold Mem.loadv.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite stsize.
          rewrite Z.add_0_l.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          discharge_cmp.
          discharge_cmp.
          repeat vcgen.
          rewrite PTree.gss; reflexivity.

          (* isnorm <> 0 *)
          intro vneq0.
          destruct (zeq (Int.unsigned isnorm) 0); try omega.
          assert(isnormcase2: Int.unsigned isnorm = 1 \/ Int.unsigned isnorm <> 1) by omega.
          Caseeq isnormcase2.

          (* isnorm = 1 *)
          intro veq1.
          destruct (zeq (Int.unsigned isnorm) 1); try omega.
          change 0 with (Int.unsigned Int.zero) in H2.
          apply unsigned_inj in H2.
          subst.
          esplit.
          repeat vcgen.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite stsize.
          rewrite Z.add_0_l.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          discharge_cmp.
          discharge_cmp.
          repeat vcgen.
          rewrite PTree.gss; reflexivity.
          (* isnorm <> 1 *)
          intro vneq1.
          destruct (zeq (Int.unsigned isnorm) 1); try omega.
          change 1 with (Int.unsigned Int.one) in H2.
          apply unsigned_inj in H2.
          subst.
          esplit.
          repeat vcgen.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite stsize.
          rewrite Z.add_0_l.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          discharge_cmp.
          discharge_cmp.
          repeat vcgen.
          rewrite PTree.gss; reflexivity.
        Qed.

      End IsNormBody.

      Theorem is_norm_code_correct:
        spec_le (is_norm ↦ is_norm_spec_low) (〚is_norm ↦ f_is_norm 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (is_norm_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_is_norm)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_is_norm)))) m'.
      Qed.

    End IsNorm.

    Section SetNorm.

      Let L: compatlayer (cdata RData) := AT_LOC ↦ at_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetNormBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variable (s: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches s ge).

        Variable (bat_loc: block).

        Hypothesis hat_loc : Genv.find_symbol ge AT_LOC = Some bat_loc.

        Lemma set_norm_body_correct: forall m m' m'' m''' d env le index normval,
                                       env = PTree.empty _ ->
                                       0 <= (Int.unsigned index) < maxpage ->
                                       PTree.get tset_norm_index le = Some (Vint index) ->
                                       PTree.get tnorm_val le = Some (Vint normval) ->
                                       Mem.store Mint32 (m, d) bat_loc (Int.unsigned (Int.repr (Int.unsigned index * 12))) (Vint normval) = Some (m', d) ->
                                       Mem.store Mint32 (m', d) bat_loc (Int.unsigned (Int.repr (Int.unsigned index * 12 + 4))) (Vint (Int.zero)) = Some (m'', d) ->
                                       Mem.store Mint32 (m'', d) bat_loc (Int.unsigned (Int.repr (Int.unsigned index * 12 + 8))) (Vint (Int.zero)) = Some (m''', d) ->
                                       exec_stmt ge env le (m, d) set_norm_body E0 le (m''', d) Out_normal
        .
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          intros.
          subst.
          unfold set_norm_body.
          repeat vcgen.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          eassumption.
          rewrite Z.mul_comm.
          eassumption.
          rewrite Z.mul_comm.
          eassumption.
        Qed.

      End SetNormBody.

      Theorem set_norm_correct: 
        spec_le (set_norm ↦ set_norm_spec_low) (〚set_norm ↦ f_set_norm 〛L).
      Proof.
        fbigstep_pre L. destruct H0 as [H0 Heq0]. destruct H1 as [H1 Heq1].
        destruct H2.
        fbigstep (set_norm_body_correct (Genv.globalenv p) b0 H (fst m) (fst m0) (fst m1) (fst m')
                                        (snd m) (PTree.empty _) (bind_parameter_temps' (fn_params f_set_norm)
                                                                                       (Vint n::Vint v::nil)
                                                                                       (create_undef_temps (fn_temps f_set_norm)))) m; eauto.
        destruct m'; simpl in *. congruence.    
      Qed.

    End SetNorm.


    Section AtGet.

      Let L: compatlayer (cdata RData) := AT_LOC ↦ at_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ATGetBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches s ge).

        Variable (bat_loc: block).

        Hypothesis hat_loc : Genv.find_symbol ge AT_LOC = Some bat_loc.

        Lemma at_get_body_correct: forall m d env le index allocated v,
                                     env = PTree.empty _ ->
                                     0 <= (Int.unsigned index) < maxpage ->
                                     Mem.loadv Mint32 (m, d) (Vptr bat_loc (Int.repr ((Int.unsigned index) * 12 + 4))) = Some (Vint v) ->
                                     Int.unsigned allocated = IntToBoolZ v ->
                                     PTree.get tallocated le = Some Vundef ->
                                     PTree.get tat_get_index le = Some (Vint index) ->
                                     exists le',
                                       exec_stmt ge env le (m, d) at_get_body E0 le' (m, d) (Out_return (Some (Vint allocated, tint)))
        .
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          intros.
          unfold at_get_body.
          subst.
          unfold IntToBoolZ in H2.
          unfold Int.eq in H2.
          change (Int.unsigned Int.zero) with 0 in H2.

          assert(isnormcase: Int.unsigned v = 0 \/ Int.unsigned v <> 0) by omega.
          Caseeq isnormcase.

          (* isnorm = 0 *)
          intro veq0.
          destruct (zeq (Int.unsigned v) 0); try omega.
          change 0 with (Int.unsigned Int.zero) in H2, e.
          apply unsigned_inj in H2.
          apply unsigned_inj in e.
          subst.
          esplit.
          repeat vcgen.
          rewrite Z.mul_comm.
          eassumption.
          discharge_cmp.
          discharge_cmp.
          repeat vcgen.
          rewrite PTree.gss; reflexivity.

          (* isnorm <> 0 *)
          intro vneq0.
          destruct (zeq (Int.unsigned v) 0); try omega.
          change 1 with (Int.unsigned Int.one) in H2.
          apply unsigned_inj in H2.
          subst.
          esplit.
          repeat vcgen.
          rewrite Z.mul_comm.
          eassumption.
          discharge_cmp.
          discharge_cmp.
          repeat vcgen.
          rewrite PTree.gss; reflexivity.
        Qed.

      End ATGetBody.

      Theorem at_get_code_correct:
        spec_le (at_get ↦ at_get_spec_low) (〚at_get ↦ f_at_get 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (at_get_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_at_get)
                                                                                                                       (Vint n::nil)
                                                                                                                       (create_undef_temps (fn_temps f_at_get)))) m'.
      Qed.

    End AtGet.

    Section AtSet.

      Let L: compatlayer (cdata RData) := AT_LOC ↦ at_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ATSetBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variable (s: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches s ge).

        Variable (bat_loc: block).

        Hypothesis hat_loc : Genv.find_symbol ge AT_LOC = Some bat_loc.

        Lemma at_set_body_correct: forall m m' d env le index allocatedval,
                                     env = PTree.empty _ ->
                                     0 <= (Int.unsigned index) < maxpage ->
                                     PTree.get tat_set_index le = Some (Vint index) ->
                                     PTree.get tallocated_val le = Some (Vint allocatedval) ->
                                     Mem.store Mint32 (m, d) bat_loc (Int.unsigned (Int.repr (Int.unsigned index * 12 + 4))) (Vint allocatedval) = Some (m', d) ->
                                     exec_stmt ge env le (m, d) at_set_body E0 le (m', d) Out_normal
        .
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          intros; subst.
          repeat vcgen.
          rewrite Z.mul_comm.
          eassumption.
        Qed.

      End ATSetBody.

      Theorem at_set_code_correct:
        spec_le (at_set ↦ at_set_spec_low) (〚at_set ↦ f_at_set 〛L).
      Proof.
        fbigstep_pre L. destruct H0 as [H0 Heq].
        fbigstep (at_set_body_correct (Genv.globalenv p) b0 H (fst m) (fst m') (snd m) (PTree.empty _) (bind_parameter_temps' (fn_params f_at_set)
                                                                                                                              (Vint n::Vint v::nil)
                                                                                                                              (create_undef_temps (fn_temps f_at_set)))) m.
        destruct m'; simpl in *. congruence.
      Qed.

    End AtSet.


    Section AtGetC.

      Let L: compatlayer (cdata RData) := AT_LOC ↦ at_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ATGetCBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches s ge).

        Variable (bat_loc: block).

        Hypothesis hat_loc : Genv.find_symbol ge AT_LOC = Some bat_loc.

        Lemma at_get_c_body_correct: forall m d env le index c,
                                     env = PTree.empty _ ->
                                     0 <= (Int.unsigned index) < maxpage ->
                                     Mem.loadv Mint32 (m, d) (Vptr bat_loc (Int.repr ((Int.unsigned index) * 12 + 8))) = Some (Vint c) ->
                                     PTree.get tat_get_c_index le = Some (Vint index) ->
                                     exists le',
                                       exec_stmt ge env le (m, d) at_get_c_body E0 le' (m, d) (Out_return (Some (Vint c, tint)))
        .
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          intros.
          unfold at_get_c_body.
          subst.
          unfold IntToBoolZ in H2.
          unfold Int.eq in H2.
          change (Int.unsigned Int.zero) with 0 in H2.
          esplit.
          repeat vcgen.
          rewrite stsize.
          rewrite Z.mul_comm.
          assumption.
        Qed.

      End ATGetCBody.

      Theorem at_get_c_code_correct:
        spec_le (at_get_c ↦ at_get_c_spec_low) (〚at_get_c ↦ f_at_get_c 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (at_get_c_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_at_get_c)
                                                                                                                       (Vint n::nil)
                                                                                                                       (create_undef_temps (fn_temps f_at_get_c)))) m'.
      Qed.

    End AtGetC.

    Section AtSetC.

      Let L: compatlayer (cdata RData) := AT_LOC ↦ at_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ATSetCBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variable (s: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches s ge).

        Variable (bat_loc: block).

        Hypothesis hat_loc : Genv.find_symbol ge AT_LOC = Some bat_loc.

        Lemma at_set_c_body_correct: forall m m' d env le index cval,
                                     env = PTree.empty _ ->
                                     0 <= (Int.unsigned index) < maxpage ->
                                     PTree.get tat_set_c_index le = Some (Vint index) ->
                                     PTree.get tc_val le = Some (Vint cval) ->
                                     Mem.store Mint32 (m, d) bat_loc (Int.unsigned (Int.repr (Int.unsigned index * 12 + 8))) (Vint cval) = Some (m', d) ->
                                     exec_stmt ge env le (m, d) at_set_c_body E0 le (m', d) Out_normal
        .
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          intros; subst.
          repeat vcgen.
          rewrite Z.mul_comm.
          eassumption.
        Qed.

      End ATSetCBody.

      Theorem at_set_c_code_correct:
        spec_le (at_set_c ↦ at_set_c_spec_low) (〚at_set_c ↦ f_at_set_c 〛L).
      Proof.
        fbigstep_pre L. destruct H0 as [H0 Heq].
        fbigstep (at_set_c_body_correct (Genv.globalenv p) b0 H (fst m) (fst m') (snd m) (PTree.empty _) (bind_parameter_temps' (fn_params f_at_set_c)
                                                                                                                              (Vint n::Vint v::nil)
                                                                                                                              (create_undef_temps (fn_temps f_at_set_c)))) m.
        destruct m'; simpl in *. congruence.
      Qed.

    End AtSetC.


  End WithPrimitives.

End MBOOTCODE.