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
(*         for the C functions implemented in the PreInit layer        *)
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
Require Import PreInit.
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
Require Import BootGenSpec.
Require Import PreInitCSource.
Require Import TacticsForTesting.

Require Import AbstractDataType.

Global Opaque compatdata_layerdata ldata_type.

Module PREINITCODE.

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

    Section Fload.

      Let L: compatlayer (cdata RData) := FlatMem_LOC ↦ flatmem_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section FloadBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (s: stencil).

        Variables (ge: genv) (bflatmem_loc: block).

        Hypothesis hflatmem_loc1 : Genv.find_symbol ge FlatMem_LOC = Some bflatmem_loc.

        Lemma fload_body_correct: forall m d env le addr val,
                                      env = PTree.empty _ ->
                                      PTree.get taddr le = Some (Vint addr) ->
                                      0 <= Int.unsigned addr < adr_low ->
                                      Mem.load Mint32 (m, d) bflatmem_loc (Int.unsigned addr * 4) = Some (Vint val) ->
                                      exec_stmt ge env le (m, d) fload_body E0 le (m, d) (Out_return (Some (Vint val, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize tintsize; intro tintsize.
          intros; subst.
          unfold fload_body.
          repeat vcgen.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; try omega.
          assumption.
        Qed.

      End FloadBody.

      Theorem fload_code_correct: 
        spec_le (fload ↦ fload_spec_low) (〚fload ↦ f_fload〛 L).
      Proof.
        fbigstep_pre L.
        fbigstep (fload_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_fload)
                                                                                                                        (Vint addr::nil)
                                                                                                                        (create_undef_temps (fn_temps f_fload)))) m'.
      Qed.    

    End Fload.


    Section Fstore.

      Let L: compatlayer (cdata RData) := FlatMem_LOC ↦ flatmem_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section FstoreBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variable (s: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches s ge).

        Variable (bflatmem_loc: block).

        Hypothesis hflatmem_loc1 : Genv.find_symbol ge FlatMem_LOC = Some bflatmem_loc.

        Lemma fstore_body_correct: forall m m' d env le addr val,
                                       env = PTree.empty _ ->
                                       PTree.get taddr le = Some (Vint addr) ->
                                       PTree.get tval le = Some (Vint val) ->
                                       0 <= Int.unsigned addr < adr_low ->
                                       Mem.store Mint32 (m, d) bflatmem_loc (Int.unsigned addr * 4) (Vint val) = Some (m', d) ->
                                       exec_stmt ge env le ((m, d): mem) fstore_body E0 le (m', d) Out_normal
        .
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize tintsize; intro tintsize.
          intros.
          subst.
          unfold fstore_body.
          repeat vcgen.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          destruct H3.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; try omega.
          rewrite H.
          reflexivity.
        Qed.

      End FstoreBody.

      Theorem fstore_correct: 
        spec_le (fstore ↦ fstore_spec_low) (〚fstore ↦ f_fstore 〛L).
      Proof.
        fbigstep_pre L. destruct H1 as [H1 Heq1].
        destruct H2.
        fbigstep (fstore_body_correct (Genv.globalenv p) b0 H (fst m) (fst m')
                                        (snd m) (PTree.empty _) (bind_parameter_temps' (fn_params f_fstore)
                                                                                       (Vint addr::Vint n::nil)
                                                                                       (create_undef_temps (fn_temps f_fstore)))) m; eauto.
        destruct m'; simpl in *. congruence.    
      Qed.

    End Fstore.

  End WithPrimitives.

End PREINITCODE.