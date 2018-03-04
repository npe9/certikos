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
(*          for the C functions implemented in the MPTNew layer        *)
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
Require Import MPTNew.
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
Require Import KContextGenSpec.
Require Import TacticsForTesting.
Require Import MShareCSource.
Require Import AbstractDataType.

Module MPTNEWCODE.

  Section WithPrimitives.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.

    Section SETRA.

      Let L: compatlayer (cdata RData) := KCtxtPool_LOC ↦ kctxtpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetRABody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bkctxtpool_loc: block.
        Hypothesis hbkctxtpool_loc: Genv.find_symbol ge KCtxtPool_LOC = Some bkctxtpool_loc.

        Lemma set_RA_body_correct: forall m m' d env le proc_index b ofs,
                                     env = PTree.empty _ ->
                                     PTree.get tproc_index le = Some (Vint proc_index) ->
                                     PTree.get tentry le = Some (Vptr b ofs) ->
                                     Mem.store Mint32 (m, d) bkctxtpool_loc (Int.unsigned proc_index * 24 + 5 * 4) (Vptr b ofs) = Some (m', d) ->
                                     0 <= (Int.unsigned proc_index) < num_proc ->
                                     exec_stmt ge env le ((m, d): mem) set_RA_body E0 le (m', d) Out_normal.
        Proof.
          generalize t_struct_KCtxt_size.
          generalize max_unsigned_val.
          intros.
          unfold set_RA_body.
          subst.
          repeat vcgen.
          rewrite H0.
          Opaque Z.mul.
          simpl.
          change (5*4) with 20 in H4.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr.
          assumption.
          omega.
        Qed.

      End SetRABody.

      Theorem set_RA_code_correct:
        spec_le (set_RA ↦ kctxt_ra_spec_low) (〚set_RA ↦ f_set_RA 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_RA_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_RA)
                                                          (Vint n::Vptr bf ofs::nil)
                                                          (create_undef_temps (fn_temps f_set_RA)))) H0.
      Qed.

    End SETRA.


    Section SETSP.

      Let L: compatlayer (cdata RData) := KCtxtPool_LOC ↦ kctxtpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetSPBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bkctxtpool_loc: block.
        Hypothesis hbkctxtpool_loc: Genv.find_symbol ge KCtxtPool_LOC = Some bkctxtpool_loc.

        Lemma set_SP_body_correct: forall m m' d env le proc_index b ofs,
                                     env = PTree.empty _ ->
                                     PTree.get tproc_index le = Some (Vint proc_index) ->
                                     PTree.get tesp le = Some (Vptr b ofs) ->
                                     Mem.store Mint32 (m, d) bkctxtpool_loc (Int.unsigned proc_index * 24) (Vptr b ofs) = Some (m', d) ->
                                     0 <= (Int.unsigned proc_index) < num_proc ->
                                     exec_stmt ge env le ((m, d): mem) set_SP_body E0 le (m', d) Out_normal.
        Proof.
          generalize t_struct_KCtxt_size.
          generalize max_unsigned_val.
          intros.
          unfold set_SP_body.
          subst.
          repeat vcgen.
          rewrite H0.
          Opaque Z.mul.
          simpl.
          rewrite Z.mul_comm.
          rewrite Z.add_0_r.
          rewrite Int.unsigned_repr.
          assumption.
          omega.
        Qed.

      End SetSPBody.

      Theorem set_SP_code_correct:
        spec_le (set_SP ↦ kctxt_sp_spec_low) (〚set_SP ↦ f_set_SP 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_SP_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_SP)
                                                          (Vint n::Vptr bf ofs::nil)
                                                          (create_undef_temps (fn_temps f_set_SP)))) H0.
      Qed.

    End SETSP.

  End WithPrimitives.

End MPTNEWCODE.
