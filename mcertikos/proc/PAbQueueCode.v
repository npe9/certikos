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
(*         for the C functions implemented in the PAbQueue layer       *)
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
Require Import PAbQueue.
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
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CurIDGenSpec.
Require Import TacticsForTesting.
Require Import PAbQueueCSource.
Require Import AbstractDataType.


Module PABQUEUECODE.

  Section WithPrimitives.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.


    Section GETCURID.

      Let L: compatlayer (cdata RData) := CURID_LOC ↦ curid_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetCurIDBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable bcurid_loc: block.
        Hypothesis hcurid_loc : Genv.find_symbol ge CURID_LOC = Some bcurid_loc.

        Lemma get_curid_body_correct: forall m d env le curid,
                                        env = PTree.empty _ ->
                                        Mem.loadv Mint32 (m, d) (Vptr bcurid_loc Int.zero) = Some (Vint curid) ->
                                        exec_stmt ge env le ((m, d): mem) get_curid_body E0 le (m, d) (Out_return (Some (Vint curid, tint)))
        .
        Proof.
          intros.
          subst.
          unfold get_curid_body.
          repeat vcgen.
        Qed.

      End GetCurIDBody.

      Theorem get_curid_code_correct:
        spec_le (get_curid ↦ get_curid_spec_low) (〚get_curid ↦ f_get_curid 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_curid_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_curid)
                                                                                                                        nil
                                                                                                                        (create_undef_temps (fn_temps f_get_curid)))) m'.
      Qed.
      
    End GETCURID.


    Section SETCURID.

      Let L: compatlayer (cdata RData) := CURID_LOC ↦ curid_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetCurIDBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bcurid_loc: block.
        Hypothesis hcurid_loc : Genv.find_symbol ge CURID_LOC = Some bcurid_loc.

        Lemma set_curid_body_correct: forall m m' d env le curid,
                                        env = PTree.empty _ ->
                                        PTree.get tcurid le = Some (Vint curid) ->
                                        Mem.store Mint32 (m, d) bcurid_loc 0 (Vint curid) = Some (m', d) ->
                                        exec_stmt ge env le ((m, d): mem) set_curid_body E0 le (m', d) Out_normal
        .
        Proof.
          intros.
          unfold set_curid_body.
          rewrite H.
          repeat vcgen.
        Qed.

      End SetCurIDBody.

      Theorem set_curid_code_correct:
        spec_le (set_curid ↦ set_curid_spec_low) (〚set_curid ↦ f_set_curid 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_curid_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_curid)
                                                          (Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_curid)))) H0.
      Qed.
      
    End SETCURID.

  End WithPrimitives.

End PABQUEUECODE.
