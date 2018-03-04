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
(*         for the C functions implemented in the PKContextNew layer   *)
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
Require Import PKContextNew.
Require Import PKContext.
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
Require Import ThreadIntroGenSpec.
Require Import PKContextNewCSource.
Require Import AbstractDataType.


Module PKCONTEXTNEWCODE.

  Section WithPrimitives.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.

    Section GETSTATE.

      Let L: compatlayer (cdata RData) := TCBPool_LOC ↦ tcbpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetStateBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable btcbpool_loc: block.
        Hypothesis htcbpool_loc: Genv.find_symbol ge TCBPool_LOC = Some btcbpool_loc.

        Lemma get_state_body_correct: forall m d env le proc_index state,
                                        env = PTree.empty _ ->
                                        PTree.get tproc_index le = Some (Vint proc_index) ->
                                        Mem.load Mint32 (m, d) btcbpool_loc (Int.unsigned proc_index * 12) = Some (Vint state) ->
                                        0 <= (Int.unsigned proc_index) < num_proc ->
                                        exec_stmt ge env le ((m, d): mem) get_state_body E0 le (m, d) (Out_return (Some (Vint state, tint))).
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TCB_size.
          intros.
          subst.
          unfold get_state_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End GetStateBody.

      Theorem get_state_code_correct:
        spec_le (get_state ↦ get_state_spec_low) (〚get_state ↦ f_get_state 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_state_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_state)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_get_state)))) m'.
      Qed.

    End GETSTATE.


    Section GETPREV.

      Let L: compatlayer (cdata RData) := TCBPool_LOC ↦ tcbpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetPrevBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable btcbpool_loc: block.
        Hypothesis htcbpool_loc: Genv.find_symbol ge TCBPool_LOC = Some btcbpool_loc.

        Lemma get_prev_body_correct: forall m d env le proc_index prev,
                                       env = PTree.empty _ ->
                                       PTree.get tproc_index le = Some (Vint proc_index) ->
                                       Mem.load Mint32 (m, d) btcbpool_loc (Int.unsigned proc_index * 12 + 4) = Some (Vint prev) ->
                                       0 <= (Int.unsigned proc_index) < num_proc ->
                                       exec_stmt ge env le ((m, d): mem) get_prev_body E0 le (m, d) (Out_return (Some (Vint prev, tint))).
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TCB_size.
          intros.
          subst.
          unfold get_prev_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End GetPrevBody.

      Theorem get_prev_code_correct:
        spec_le (get_prev ↦ get_prev_spec_low) (〚get_prev ↦ f_get_prev 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_prev_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_prev)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_get_prev)))) m'.
      Qed.

    End GETPREV.


    Section GETNEXT.

      Let L: compatlayer (cdata RData) := TCBPool_LOC ↦ tcbpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetNextBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable btcbpool_loc: block.
        Hypothesis htcbpool_loc: Genv.find_symbol ge TCBPool_LOC = Some btcbpool_loc.


        Lemma get_next_body_correct: forall m d env le proc_index next,
                                       env = PTree.empty _ ->
                                       PTree.get tproc_index le = Some (Vint proc_index) ->
                                       Mem.load Mint32 (m, d) btcbpool_loc (Int.unsigned proc_index * 12 + 8) = Some (Vint next) ->
                                       0 <= (Int.unsigned proc_index) < num_proc ->
                                       exec_stmt ge env le ((m, d): mem) get_next_body E0 le (m, d) (Out_return (Some (Vint next, tint))).
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TCB_size.
          intros.
          subst.
          unfold get_next_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End GetNextBody.

      Theorem get_next_code_correct:
        spec_le (get_next ↦ get_next_spec_low) (〚get_next ↦ f_get_next 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_next_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_next)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_get_next)))) m'.
      Qed.

    End GETNEXT.


    Section SETSTATE.

      Let L: compatlayer (cdata RData) := TCBPool_LOC ↦ tcbpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetStateBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable btcbpool_loc: block.
        Hypothesis htcbpool_loc: Genv.find_symbol ge TCBPool_LOC = Some btcbpool_loc.


        Lemma set_state_body_correct: forall m m' d env le proc_index state,
                                        env = PTree.empty _ ->
                                        PTree.get tproc_index le = Some (Vint proc_index) ->
                                        PTree.get tstate le = Some (Vint state) ->
                                        Mem.store Mint32 (m, d) btcbpool_loc (Int.unsigned proc_index * 12) (Vint state) = Some (m', d) ->
                                        0 <= (Int.unsigned proc_index) < num_proc ->
                                        exec_stmt ge env le ((m, d): mem) set_state_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TCB_size.
          intros.
          subst.
          unfold set_state_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.add_0_r.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End SetStateBody.

      Theorem set_state_code_correct:
        spec_le (set_state ↦ set_state_spec_low) (〚set_state ↦ f_set_state 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_state_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_state)
                                                          (Vint n::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_state)))) H0.
      Qed.

    End SETSTATE.


    Section SETPREV.

      Let L: compatlayer (cdata RData) := TCBPool_LOC ↦ tcbpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetPrevBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable btcbpool_loc: block.
        Hypothesis htcbpool_loc: Genv.find_symbol ge TCBPool_LOC = Some btcbpool_loc.


        Lemma set_prev_body_correct: forall m m' d env le proc_index prev,
                                       env = PTree.empty _ ->
                                       PTree.get tproc_index le = Some (Vint proc_index) ->
                                       PTree.get tprev le = Some (Vint prev) ->
                                       Mem.store Mint32 (m, d) btcbpool_loc (Int.unsigned proc_index * 12 + 4) (Vint prev) = Some (m', d) ->
                                       0 <= (Int.unsigned proc_index) < num_proc ->
                                       exec_stmt ge env le ((m, d): mem) set_prev_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TCB_size.
          intros.
          subst.
          unfold set_prev_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End SetPrevBody.

      Theorem set_prev_code_correct:
        spec_le (set_prev ↦ set_prev_spec_low) (〚set_prev ↦ f_set_prev 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_prev_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_prev)
                                                          (Vint n::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_prev)))) H0.
      Qed.

    End SETPREV.


    Section SETNEXT.

      Let L: compatlayer (cdata RData) := TCBPool_LOC ↦ tcbpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetNextBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable btcbpool_loc: block.
        Hypothesis htcbpool_loc: Genv.find_symbol ge TCBPool_LOC = Some btcbpool_loc.

        Lemma set_next_body_correct: forall m m' d env le proc_index next,
                                       env = PTree.empty _ ->
                                       PTree.get tproc_index le = Some (Vint proc_index) ->
                                       PTree.get tnext le = Some (Vint next) ->
                                       Mem.store Mint32 (m, d) btcbpool_loc (Int.unsigned proc_index * 12 + 8) (Vint next) = Some (m', d) ->
                                       0 <= (Int.unsigned proc_index) < num_proc ->
                                       exec_stmt ge env le ((m, d): mem) set_next_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TCB_size.
          intros.
          subst.
          unfold set_next_body.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End SetNextBody.

      Theorem set_next_code_correct:
        spec_le (set_next ↦ set_next_spec_low) (〚set_next ↦ f_set_next 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_next_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_next)
                                                          (Vint n::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_next)))) H0.
      Qed.

    End SETNEXT.


    Section TCBINIT.

      Let L: compatlayer (cdata RData) := TCBPool_LOC ↦ tcbpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section TCBInitBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable btcbpool_loc: block.
        Hypothesis htcbpool_loc: Genv.find_symbol ge TCBPool_LOC = Some btcbpool_loc.

        Lemma tcb_init_body_correct: forall m m1 m2 m' d env le proc_index,
                                       env = PTree.empty _ ->
                                       PTree.get tproc_index le = Some (Vint proc_index) ->
                                       Mem.store Mint32 (m, d) btcbpool_loc (Int.unsigned proc_index * 12) (Vint (Int.repr 3)) = Some (m1, d) ->
                                       Mem.store Mint32 (m1, d) btcbpool_loc (Int.unsigned proc_index * 12 + 4) (Vint (Int.repr num_proc)) = Some (m2, d) ->
                                       Mem.store Mint32 (m2, d) btcbpool_loc (Int.unsigned proc_index * 12 + 8) (Vint (Int.repr num_proc)) = Some (m', d) ->
                                       0 <= (Int.unsigned proc_index) < num_proc ->
                                       exec_stmt ge env le ((m, d): mem) tcb_init_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val.
          generalize t_struct_TCB_size.
          intros.
          subst.
          unfold tcb_init_body.
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
          repeat vcgen.
          rewrite H.
          simpl.
          rewrite Z.mul_comm.
          rewrite Int.unsigned_repr; [assumption | omega].
        Qed.

      End TCBInitBody.

      Theorem tcb_init_code_correct:
        spec_le (tcb_init ↦ tcb_init_spec_low) (〚tcb_init ↦ f_tcb_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m, m', m0, m1, H1, H2.
        fbigstep (tcb_init_body_correct (Genv.globalenv p) b0 H m m0 m1 m2 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_tcb_init)
                                                          (Vint n::nil)
                                                          (create_undef_temps (fn_temps f_tcb_init)))) H0.
      Qed.

    End TCBINIT.

  End WithPrimitives.

End PKCONTEXTNEWCODE.
