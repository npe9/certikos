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
(*         for the C functions implemented in the PThreadInit layer    *)
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
Require Import PThreadInit.
Require Import ZArith.Zwf.
Require Import RealParams.
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
Require Import QueueIntroGenSpec.
Require Import TacticsForTesting.
Require Import PThreadInitCSource.
Require Import AbstractDataType.


Module PTHREADINITCODE.

  Section WithPrimitives.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.

    Section GETHEAD.

      Let L: compatlayer (cdata RData) := TDQPool_LOC ↦ tdqpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetHeadBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable btdqpool_loc: block.
        Hypothesis hbtdqpool_loc: Genv.find_symbol ge TDQPool_LOC = Some btdqpool_loc.

        Lemma get_head_body_correct: forall m d env le chan_index head,
                                       env = PTree.empty _ ->
                                       PTree.get tchan_index le = Some (Vint chan_index) ->
                                       Mem.load Mint32 (m, d) btdqpool_loc (Int.unsigned chan_index * 8) = Some (Vint head) ->
                                       0 <= (Int.unsigned chan_index) <= num_chan ->
                                       exec_stmt ge env le ((m, d): mem) get_head_body E0 le (m, d) (Out_return (Some (Vint head, tint))).
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TDQ_size.
          intros.
          subst.
          unfold get_head_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End GetHeadBody.

      Theorem get_head_code_correct:
        spec_le (get_head ↦ get_head_spec_low) (〚get_head ↦ f_get_head 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_head_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_head)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_get_head)))) m'.
      Qed.

    End GETHEAD.


    Section GETTAIL.

      Let L: compatlayer (cdata RData) := TDQPool_LOC ↦ tdqpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetTailBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable btdqpool_loc: block.
        Hypothesis hbtdqpool_loc: Genv.find_symbol ge TDQPool_LOC = Some btdqpool_loc.

        Lemma get_tail_body_correct: forall m d env le chan_index tail,
                                       env = PTree.empty _ ->
                                       PTree.get tchan_index le = Some (Vint chan_index) ->
                                       Mem.load Mint32 (m, d) btdqpool_loc (Int.unsigned chan_index * 8 + 4) = Some (Vint tail) ->
                                       0 <= (Int.unsigned chan_index) <= num_chan ->
                                       exec_stmt ge env le ((m, d): mem) get_tail_body E0 le (m, d) (Out_return (Some (Vint tail, tint))).
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TDQ_size.
          intros.
          subst.
          unfold get_tail_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End GetTailBody.

      Theorem get_tail_code_correct:
        spec_le (get_tail ↦ get_tail_spec_low) (〚get_tail ↦ f_get_tail 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_tail_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_tail)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_get_tail)))) m'.
      Qed.

    End GETTAIL.


    Section SETHEAD.

      Let L: compatlayer (cdata RData) := TDQPool_LOC ↦ tdqpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetHeadBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable btdqpool_loc: block.
        Hypothesis hbtdqpool_loc: Genv.find_symbol ge TDQPool_LOC = Some btdqpool_loc.

        Lemma set_head_body_correct: forall m m' d env le chan_index head,
                                       env = PTree.empty _ ->
                                       PTree.get tchan_index le = Some (Vint chan_index) ->
                                       PTree.get thead le = Some (Vint head) ->
                                       Mem.store Mint32 (m, d) btdqpool_loc (Int.unsigned chan_index * 8) (Vint head) = Some (m', d) ->
                                       0 <= (Int.unsigned chan_index) <= num_chan ->
                                       exec_stmt ge env le ((m, d): mem) set_head_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TDQ_size.
          intros.
          subst.
          unfold set_head_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End SetHeadBody.

      Theorem set_head_code_correct:
        spec_le (set_head ↦ set_head_spec_low) (〚set_head ↦ f_set_head 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_head_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_head)
                                                          (Vint n::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_head)))) H0.
      Qed.

    End SETHEAD.


    Section SETTAIL.

      Let L: compatlayer (cdata RData) := TDQPool_LOC ↦ tdqpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetTailBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable btdqpool_loc: block.
        Hypothesis hbtdqpool_loc: Genv.find_symbol ge TDQPool_LOC = Some btdqpool_loc.

        Lemma set_tail_body_correct: forall m m' d env le chan_index tail,
                                       env = PTree.empty _ ->
                                       PTree.get tchan_index le = Some (Vint chan_index) ->
                                       PTree.get ttail le = Some (Vint tail) ->
                                       Mem.store Mint32 (m, d) btdqpool_loc (Int.unsigned chan_index * 8 + 4) (Vint tail) = Some (m', d) ->
                                       0 <= (Int.unsigned chan_index) <= num_chan ->
                                       exec_stmt ge env le ((m, d): mem) set_tail_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TDQ_size.
          intros.
          subst.
          unfold set_tail_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End SetTailBody.

      Theorem set_tail_code_correct:
        spec_le (set_tail ↦ set_tail_spec_low) (〚set_tail ↦ f_set_tail 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_tail_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_tail)
                                                          (Vint n::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_tail)))) H0.
      Qed.

    End SETTAIL.


    Section TDQINIT.

      Let L: compatlayer (cdata RData) := TDQPool_LOC ↦ tdqpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section TDQInitBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable btdqpool_loc: block.
        Hypothesis hbtdqpool_loc: Genv.find_symbol ge TDQPool_LOC = Some btdqpool_loc.

        Lemma tdq_init_body_correct: forall m m1 m' d env le chan_index,
                                       env = PTree.empty _ ->
                                       PTree.get tchan_index le = Some (Vint chan_index) ->
                                       Mem.store Mint32 (m, d) btdqpool_loc (Int.unsigned chan_index * 8) (Vint (Int.repr num_proc)) = Some (m1, d) ->
                                       Mem.store Mint32 (m1, d) btdqpool_loc (Int.unsigned chan_index * 8 + 4) (Vint (Int.repr num_proc)) = Some (m', d) ->
                                       0 <= (Int.unsigned chan_index) <= num_chan ->
                                       exec_stmt ge env le ((m, d): mem) tdq_init_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TDQ_size.
          intros.
          subst.
          unfold tdq_init_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [eassumption | omega].
          rewrite H.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [eassumption | omega].
        Qed.

      End TDQInitBody.

      Theorem tdq_init_code_correct:
        spec_le (tdq_init ↦ tdq_init_spec_low) (〚tdq_init ↦ f_tdq_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m, m', m1, H1.
        fbigstep (tdq_init_body_correct (Genv.globalenv p) b0 H m m1 m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_tdq_init)
                                                          (Vint n::nil)
                                                          (create_undef_temps (fn_temps f_tdq_init)))) H0.
      Qed.

    End TDQINIT.

  End WithPrimitives.

End PTHREADINITCODE.
