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
(*          for the C functions implemented in the PIPC layer          *)
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
Require Import Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import PIPC.
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
Require Import UCtxtIntroGenSpec.
Require Import TacticsForTesting.
Require Import PIPCCSource.
Require Import AbstractDataType.


Module PIPCCODE.

  Section WithPrimitives.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.

    Lemma tarrsize: sizeof (tarray tint 17) = 68.
    Proof. reflexivity. Qed.

    Section UCTXGET.

      Let L: compatlayer (cdata RData) := UCTX_LOC ↦ uctx_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UCTXGetBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable buctx_loc: block.
        Hypothesis hbuctx_loc: Genv.find_symbol ge UCTX_LOC = Some buctx_loc.

        Lemma uctx_get_body_correct: forall m d env le proc_index ofs uctx,
                                       env = PTree.empty _ ->
                                       PTree.get tproc_index le = Some (Vint proc_index) ->
                                       PTree.get tofs le = Some (Vint ofs) ->
                                       Mem.load Mint32 (m, d) buctx_loc (Int.unsigned proc_index * UCTXT_SIZE * 4 + Int.unsigned ofs * 4) = Some (Vint uctx) ->
                                       0 <= Int.unsigned proc_index < num_proc ->
                                       is_UCTXT_ptr (Int.unsigned ofs) = false ->
                                       exec_stmt ge env le ((m, d): mem) uctx_get_body E0 le (m, d) (Out_return (Some (Vint uctx, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize tarrsize; intro tarrsize.
          generalize tintsize; intro tintsize.
          intros.
          assert(0 <= Int.unsigned ofs < UCTXT_SIZE).
            functional inversion H4; subst; omega.
          subst.
          unfold uctx_get_body.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.loadv.
          replace (0 + 68 * Int.unsigned proc_index + 4 * Int.unsigned ofs) with (Int.unsigned proc_index * 17 * 4 + Int.unsigned ofs * 4) by omega.
          rewrite Int.unsigned_repr; try omega.
          assumption.
        Qed.

      End UCTXGetBody.

      Theorem uctx_get_code_correct:
        spec_le (uctx_get ↦ uctx_get_spec_low) (〚uctx_get ↦ f_uctx_get 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (uctx_get_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_uctx_get)
                                                                                                                        (Vint n::Vint ofs::nil)
                                                                                                                        (create_undef_temps (fn_temps f_uctx_get)))) m'.
      Qed.

    End UCTXGET.


    Section UCTXSET.

      Let L: compatlayer (cdata RData) := UCTX_LOC ↦ uctx_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UCTXSetBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable buctx_loc: block.
        Hypothesis hbuctx_loc: Genv.find_symbol ge UCTX_LOC = Some buctx_loc.

        Lemma uctx_set_body_correct: forall m m' d env le proc_index ofs val,
                                       env = PTree.empty _ ->
                                       PTree.get tproc_index le = Some (Vint proc_index) ->
                                       PTree.get tofs le = Some (Vint ofs) ->
                                       PTree.get tval le = Some (Vint val) ->
                                       Mem.store Mint32 (m, d) buctx_loc (Int.unsigned proc_index * UCTXT_SIZE * 4 + Int.unsigned ofs * 4) (Vint val) = Some (m', d) ->
                                       0 <= Int.unsigned proc_index < num_proc ->
                                       is_UCTXT_ptr (Int.unsigned ofs) = false ->
                                       exec_stmt ge env le ((m, d): mem) uctx_set_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize tarrsize; intro tarrsize.
          generalize tintsize; intro tintsize.
          intros.
          assert(0 <= Int.unsigned ofs < UCTXT_SIZE).
            functional inversion H5; subst; omega.
          subst.
          unfold uctx_set_body.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          replace (0 + 68 * Int.unsigned proc_index + 4 * Int.unsigned ofs) with (Int.unsigned proc_index * 17 * 4 + Int.unsigned ofs * 4) by omega.
          rewrite Int.unsigned_repr; try omega.
          assumption.
        Qed.

      End UCTXSetBody.

      Theorem uctx_set_code_correct:
        spec_le (uctx_set ↦ uctx_set_spec_low) (〚uctx_set ↦ f_uctx_set 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (uctx_set_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_uctx_set)
                                                          (Vint n::Vint ofs::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_uctx_set)))) H0.
      Qed.

    End UCTXSET.


    Section UCTXSETEIP.

      Let L: compatlayer (cdata RData) := UCTX_LOC ↦ uctx_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UCTXSetEIPBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable buctx_loc: block.
        Hypothesis hbuctx_loc: Genv.find_symbol ge UCTX_LOC = Some buctx_loc.

        Lemma uctx_set_eip_body_correct: forall m m' d env le proc_index bf ofs,
                                           env = PTree.empty _ ->
                                           PTree.get tproc_index le = Some (Vint proc_index) ->
                                           PTree.get tval le = Some (Vptr bf ofs) ->
                                           Mem.store Mint32 (m, d) buctx_loc (Int.unsigned proc_index * UCTXT_SIZE * 4 + U_EIP * 4) (Vptr bf ofs) = Some (m', d) ->
                                           0 <= Int.unsigned proc_index < num_proc ->
                                           exec_stmt ge env le ((m, d): mem) uctx_set_eip_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize tarrsize; intro tarrsize.
          generalize tintsize; intro tintsize.
          intros.
          subst.
          unfold uctx_set_eip_body.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          replace (0 + 68 * Int.unsigned proc_index + 4 * U_EIP) with (Int.unsigned proc_index * 68 + U_EIP * 4) by omega.
          rewrite Int.unsigned_repr; try omega.
          replace (Int.unsigned proc_index * 68) with (Int.unsigned proc_index * 17 * 4) by omega.
          assumption.
        Qed.

      End UCTXSetEIPBody.

      Theorem uctx_set_eip_code_correct:
        spec_le (uctx_set_eip ↦ uctx_set_eip_spec_low) (〚uctx_set_eip ↦ f_uctx_set_eip 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (uctx_set_eip_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_uctx_set_eip)
                                                          (Vint n::Vptr bf ofs::nil)
                                                          (create_undef_temps (fn_temps f_uctx_set_eip)))) H0.
      Qed.

    End UCTXSETEIP.


    Section SAVEUCTX.

      Let L: compatlayer (cdata RData) := UCTX_LOC ↦ uctx_loc_type
           ⊕ get_curid ↦ gensem get_curid_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SaveUCTXBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable buctx_loc: block.
        Hypothesis hbuctx_loc: Genv.find_symbol ge UCTX_LOC = Some buctx_loc.

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        Lemma save_uctx_body_correct: forall m m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m' d env le n u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16,
                                        env = PTree.empty _ ->
                                        high_level_invariant d ->
                                        PTree.get tu0 le = Some (Vint u0) ->
                                        PTree.get tu1 le = Some (Vint u1) ->
                                        PTree.get tu2 le = Some (Vint u2) ->
                                        PTree.get tu3 le = Some (Vint u3) ->
                                        PTree.get tu4 le = Some (Vint u4) ->
                                        PTree.get tu5 le = Some (Vint u5) ->
                                        PTree.get tu6 le = Some (Vint u6) ->
                                        PTree.get tu7 le = Some (Vint u7) ->
                                        PTree.get tu8 le = Some (Vint u8) ->
                                        PTree.get tu9 le = Some (Vint u9) ->
                                        PTree.get tu10 le = Some (Vint u10) ->
                                        PTree.get tu11 le = Some (Vint u11) ->
                                        PTree.get tu12 le = Some (Vint u12) ->
                                        PTree.get tu13 le = Some (Vint u13) ->
                                        PTree.get tu14 le = Some (Vint u14) ->
                                        PTree.get tu15 le = Some (Vint u15) ->
                                        PTree.get tu16 le = Some (Vint u16) ->
                                        cid d = n ->
                                        kernel_mode d ->
                                        
                                        pg d = true ->
                                        Mem.store Mint32 ((m, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 0) (Vint u0) = Some (m1, d) ->
                                        Mem.store Mint32 ((m1, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 1) (Vint u1) = Some (m2, d) ->
                                        Mem.store Mint32 ((m2, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 2) (Vint u2) = Some (m3, d) ->
                                        Mem.store Mint32 ((m3, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 3) (Vint u3) = Some (m4, d) ->
                                        Mem.store Mint32 ((m4, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 4) (Vint u4) = Some (m5, d) ->
                                        Mem.store Mint32 ((m5, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 5) (Vint u5) = Some (m6, d) ->
                                        Mem.store Mint32 ((m6, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 6) (Vint u6) = Some (m7, d) ->
                                        Mem.store Mint32 ((m7, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 7) (Vint u7) = Some (m8, d) ->
                                        Mem.store Mint32 ((m8, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 8) (Vint u8) = Some (m9, d) ->
                                        Mem.store Mint32 ((m9, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 9) (Vint u9) = Some (m10, d) ->
                                        Mem.store Mint32 ((m10, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 10) (Vint u10) = Some (m11, d) ->
                                        Mem.store Mint32 ((m11, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 11) (Vint u11) = Some (m12, d) ->
                                        Mem.store Mint32 ((m12, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 12) (Vint u12) = Some (m13, d) ->
                                        Mem.store Mint32 ((m13, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 13) (Vint u13) = Some (m14, d) ->
                                        Mem.store Mint32 ((m14, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 14) (Vint u14) = Some (m15, d) ->
                                        Mem.store Mint32 ((m15, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 15) (Vint u15) = Some (m16, d) ->
                                        Mem.store Mint32 ((m16, d): mem) buctx_loc (UCTXT_SIZE * 4 * n + 4 * 16) (Vint u16) = Some (m', d) ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) save_uctx_body E0 le' (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize tarrsize; intro tarrsize.
          generalize tintsize; intro tintsize.
          intros.
          subst.
          inversion H19.
          unfold save_uctx_body.
          assert(0 <= cid d < 64).
            destruct H0; assumption.
          assert(get_curid_spec d = Some (cid d)).
            unfold get_curid_spec.
            rewrite H, H18, H20.
            reflexivity.
          esplit.
          repeat vcgen; repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          rewrite tarrsize, tintsize.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
        Qed.

      End SaveUCTXBody.

      Theorem save_uctx_code_correct:
        spec_le (save_uctx ↦ save_uctx_spec_low) (〚save_uctx ↦ f_save_uctx 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        Opaque Z.mul.
        fbigstep_pre L'.
        destruct m, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m'.
        destruct H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16.
        simpl in *.
        subst.
        fbigstep (save_uctx_body_correct s (Genv.globalenv p) makeglobalenv b1 H b2 Hb2fs Hb2fp m m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 l16 (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_save_uctx)
                                                          (Vint u0::Vint u1::Vint u2::Vint u3::Vint u4::Vint u5::Vint u6::Vint u7::Vint u8::Vint u9::Vint u10::Vint u11::Vint u12::Vint u13::Vint u14::Vint u15::Vint u16::nil)
                                                          (create_undef_temps (fn_temps f_save_uctx)))) H18; repeat progress match goal with
                    | [H: ?x = _ |- context[?x]] => rewrite H; reflexivity
  end; ptreesolve.
        rewrite H15; reflexivity.
        rewrite H16; reflexivity.
      Qed.

    End SAVEUCTX.

  End WithPrimitives.

End PIPCCODE.