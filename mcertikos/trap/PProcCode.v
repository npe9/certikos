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
(*        for the C functions implemented in the VVMXInit layer        *)
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
Require Import Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Ctypes.
Require Import Cop.
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
Require Import TrapArgGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import XOmega.
Require Import PProcCSource.
Require Import AbstractDataType.
Require Import ObjThread.
Require Import ObjProc.
Require Import ObjArg.


Module PPROCCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

(*
    Section LA2PARESV.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem (fun d => get_curid_spec d)
           ⊕ pt_read ↦ gensem (fun a b d => ptRead_spec d a b)
           ⊕ pt_resv ↦ gensem (fun a b c d => ptResv_spec d a b c).

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section La2paResvBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** pt_resv *)

        Variable bpt_resv: block.

        Hypothesis hpt_resv1 : Genv.find_symbol ge pt_resv = Some bpt_resv. 
        
        Hypothesis hpt_resv2 : Genv.find_funct_ptr ge bpt_resv = Some (External (EF_external pt_resv (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default).

        (** pt_read *)

        Variable bpt_read: block.

        Hypothesis hpt_read : Genv.find_symbol ge pt_read = Some bpt_read. 
        
        Hypothesis hpt_read2 : Genv.find_funct_ptr ge bpt_read = Some (External (EF_external pt_read (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma la2pa_resv_body_correct: forall m d d' env le va pa,
                                         env = PTree.empty _ ->
                                         PTree.get tva le = Some (Vint va) ->
                                         la2pa_resv_spec d (Int.unsigned va) = Some (d', Int.unsigned pa) ->
                                         high_level_invariant d ->
                                         exists le',
                                           exec_stmt ge env le ((m, d): mem) la2pa_resv_body E0 le' (m, d') (Out_return (Some (Vint pa, tint))).
        Proof.   
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H2; assumption).
          subst.
          unfold la2pa_resv_body.
          functional inversion H1; subst.

          generalize H4; intro tmpinv;
          unfold ptRead_spec in tmpinv;
          case_eq (ikern d); intro ikern; rewrite ikern in tmpinv; try discriminate tmpinv;
          case_eq (ihost d); intro ihost; rewrite ihost in tmpinv; try discriminate tmpinv;
          clear tmpinv.
          rewrite <- Int.unsigned_repr with (cid d) in H4.
          esplit.
          repeat vcgenfull.
          unfold get_curid_spec.
          rewrite ikern, ihost, H5.
          rewrite <- Int.unsigned_repr with (cid d).
          reflexivity.
          omega.
          rewrite H4.
          change 0 with (Int.unsigned Int.zero).
          reflexivity.
          discharge_cmp.
          repeat vcgenfull.
          instantiate (1:= (Int.repr padr')).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.
          repeat vcgen.
          reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          unfold Int.modu.
          rewrite Int.unsigned_repr; try omega.
          simpl.
          assert(Int.repr (padr' / 4096 * 4096 + Int.unsigned va mod 4096) = pa).
            erewrite <- unsigned_inj.
            reflexivity.
            rewrite Int.unsigned_repr.
            assumption.
            xomega.
          rewrite <- H.
          simpl.
          unfold sem_add.
          simpl.
          unfold sem_binarith.
          simpl.
          repeat vcgenfull.
          xomega.
          xomega.
          xomega.
          xomega.
          omega.

          generalize H4; intro tmpinv;
          unfold ptRead_spec in tmpinv;
          case_eq (ikern d'); intro ikern; rewrite ikern in tmpinv; try discriminate tmpinv;
          case_eq (ihost d'); intro ihost; rewrite ihost in tmpinv; try discriminate tmpinv;
          clear tmpinv.
          rewrite <- Int.unsigned_repr with (cid d') in H4.
          esplit.
          repeat vcgenfull.
          unfold get_curid_spec.
          rewrite ikern, ihost, H5.
          rewrite <- Int.unsigned_repr with (cid d').
          reflexivity.
          omega.
          rewrite H4.
          instantiate (1:= (Int.repr padr)).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.
          discharge_cmp.
          repeat vcgenfull.
          repeat vcgen.
          reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          unfold Int.modu.
          rewrite Int.unsigned_repr; try omega.
          simpl.
          assert(Int.repr (padr / 4096 * 4096 + Int.unsigned va mod 4096) = pa).
            erewrite <- unsigned_inj.
            reflexivity.
            rewrite Int.unsigned_repr.
            assumption.
            xomega.
          rewrite <- H.
          unfold sem_add.
          simpl.
          unfold sem_binarith.
          simpl.
          repeat vcgenfull.
          xomega.
          xomega.
          xomega.
          xomega.
          omega.
        Qed.

      End La2paResvBody.

      Theorem la2pa_resv_code_correct:
        spec_le (la2pa_resv ↦ la2pa_resv_spec_low) (〚la2pa_resv ↦ f_la2pa_resv 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (la2pa_resv_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_la2pa_resv)
                                                               (Vint va::nil)
                                                               (create_undef_temps (fn_temps f_la2pa_resv)))) H0. 
      Qed.

    End LA2PARESV.
*)

    Section UCTXARG1.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_get ↦ gensem uctx_get_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxArg1Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_get *)

        Variable buctx_get: block.

        Hypothesis huctx_get1 : Genv.find_symbol ge uctx_get = Some buctx_get. 
        
        Hypothesis huctx_get2 : Genv.find_funct_ptr ge buctx_get = Some (External (EF_external uctx_get (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma uctx_arg1_body_correct: forall m d env le arg,
                                        env = PTree.empty _ ->
                                        uctx_arg1_spec d = Some (Int.unsigned arg) ->
                                        high_level_invariant d ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) uctx_arg1_body E0 le' (m, d) (Out_return (Some (Vint arg, tint))).
        Proof.   
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H1; assumption).
          unfold uctx_arg1_body.
          functional inversion H0; subst.
          assert(ipt: ipt d = true).
            destruct H1. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.  
          rewrite H3, H4, H5.
          rewrite Int.unsigned_repr.
          reflexivity.   
          omega.
          unfold uctx_get_spec.   
          rewrite H3, H4, H5, ipt, H6.
          unfold is_UCTXT_ptr.
          repeat zdestruct.   
          rewrite H2.
          rewrite zle_lt_true.
          reflexivity.
          omega.   
          omega.
          omega.
        Qed.

      End UctxArg1Body.

      Theorem uctx_arg1_code_correct:
        spec_le (uctx_arg1 ↦ uctx_arg1_spec_low) (〚uctx_arg1 ↦ f_uctx_arg1 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_arg1_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_arg1)
                                                               nil
                                                               (create_undef_temps (fn_temps f_uctx_arg1)))) H0. 
      Qed.

    End UCTXARG1.


    Section UCTXARG2.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_get ↦ gensem uctx_get_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxArg2Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_get *)

        Variable buctx_get: block.

        Hypothesis huctx_get1 : Genv.find_symbol ge uctx_get = Some buctx_get. 
        
        Hypothesis huctx_get2 : Genv.find_funct_ptr ge buctx_get = Some (External (EF_external uctx_get (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma uctx_arg2_body_correct: forall m d env le arg,
                                        env = PTree.empty _ ->
                                        uctx_arg2_spec d = Some (Int.unsigned arg) ->
                                        high_level_invariant d ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) uctx_arg2_body E0 le' (m, d) (Out_return (Some (Vint arg, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H1; assumption).
          unfold uctx_arg2_body.
          functional inversion H0; subst.
          assert(ipt: ipt d = true).
            destruct H1. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.  
          rewrite H3, H4, H5.
          rewrite Int.unsigned_repr.
          reflexivity.   
          omega.
          unfold uctx_get_spec.   
          rewrite H3, H4, H5, ipt, H6.
          unfold is_UCTXT_ptr.
          repeat zdestruct.   
          rewrite H2.
          rewrite zle_lt_true.
          reflexivity.
          omega.   
          omega.
          omega.
        Qed.

      End UctxArg2Body.

      Theorem uctx_arg2_code_correct:
        spec_le (uctx_arg2 ↦ uctx_arg2_spec_low) (〚uctx_arg2 ↦ f_uctx_arg2 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_arg2_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_arg2)
                                                               nil
                                                               (create_undef_temps (fn_temps f_uctx_arg2)))) H0. 
      Qed.

    End UCTXARG2.


    Section UCTXARG3.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_get ↦ gensem uctx_get_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxArg3Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_get *)

        Variable buctx_get: block.

        Hypothesis huctx_get1 : Genv.find_symbol ge uctx_get = Some buctx_get. 
        
        Hypothesis huctx_get2 : Genv.find_funct_ptr ge buctx_get = Some (External (EF_external uctx_get (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma uctx_arg3_body_correct: forall m d env le arg,
                                        env = PTree.empty _ ->
                                        uctx_arg3_spec d = Some (Int.unsigned arg) ->
                                        high_level_invariant d ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) uctx_arg3_body E0 le' (m, d) (Out_return (Some (Vint arg, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H1; assumption).
          unfold uctx_arg3_body.
          functional inversion H0; subst.
          assert(ipt: ipt d = true).
            destruct H1. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.  
          rewrite H3, H4, H5.
          rewrite Int.unsigned_repr.
          reflexivity.   
          omega.
          unfold uctx_get_spec.   
          rewrite H3, H4, H5, ipt, H6.
          unfold is_UCTXT_ptr.
          repeat zdestruct.   
          rewrite H2.
          rewrite zle_lt_true.
          reflexivity.
          omega.   
          omega.
          omega.
        Qed.

      End UctxArg3Body.

      Theorem uctx_arg3_code_correct:
        spec_le (uctx_arg3 ↦ uctx_arg3_spec_low) (〚uctx_arg3 ↦ f_uctx_arg3 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_arg3_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_arg3)
                                                               nil
                                                               (create_undef_temps (fn_temps f_uctx_arg3)))) H0. 
      Qed.

    End UCTXARG3.


    Section UCTXARG4.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_get ↦ gensem uctx_get_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxArg4Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_get *)

        Variable buctx_get: block.

        Hypothesis huctx_get1 : Genv.find_symbol ge uctx_get = Some buctx_get. 
        
        Hypothesis huctx_get2 : Genv.find_funct_ptr ge buctx_get = Some (External (EF_external uctx_get (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma uctx_arg4_body_correct: forall m d env le arg,
                                        env = PTree.empty _ ->
                                        uctx_arg4_spec d = Some (Int.unsigned arg) ->
                                        high_level_invariant d ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) uctx_arg4_body E0 le' (m, d) (Out_return (Some (Vint arg, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H1; assumption).
          unfold uctx_arg4_body.
          functional inversion H0; subst.
          assert(ipt: ipt d = true).
            destruct H1. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.  
          rewrite H3, H4, H5.
          rewrite Int.unsigned_repr.
          reflexivity.   
          omega.
          unfold uctx_get_spec.   
          rewrite H3, H4, H5, ipt, H6.
          unfold is_UCTXT_ptr.
          repeat zdestruct.   
          rewrite H2.
          rewrite zle_lt_true.
          reflexivity.
          omega.   
          omega.
          omega.
        Qed.

      End UctxArg4Body.

      Theorem uctx_arg4_code_correct:
        spec_le (uctx_arg4 ↦ uctx_arg4_spec_low) (〚uctx_arg4 ↦ f_uctx_arg4 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_arg4_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_arg4)
                                                               nil
                                                               (create_undef_temps (fn_temps f_uctx_arg4)))) H0. 
      Qed.

    End UCTXARG4.


    Section UCTXARG5.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_get ↦ gensem uctx_get_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxArg5Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_get *)

        Variable buctx_get: block.

        Hypothesis huctx_get1 : Genv.find_symbol ge uctx_get = Some buctx_get. 
        
        Hypothesis huctx_get2 : Genv.find_funct_ptr ge buctx_get = Some (External (EF_external uctx_get (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma uctx_arg5_body_correct: forall m d env le arg,
                                        env = PTree.empty _ ->
                                        uctx_arg5_spec d = Some (Int.unsigned arg) ->
                                        high_level_invariant d ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) uctx_arg5_body E0 le' (m, d) (Out_return (Some (Vint arg, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H1; assumption).
          unfold uctx_arg5_body.
          functional inversion H0; subst.
          assert(ipt: ipt d = true).
            destruct H1. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.  
          rewrite H3, H4, H5.
          rewrite Int.unsigned_repr.
          reflexivity.   
          omega.
          unfold uctx_get_spec.   
          rewrite Int.unsigned_repr.
          rewrite H3, H4, H5, ipt, H6.
          unfold is_UCTXT_ptr.
          repeat zdestruct.   
          rewrite H2.
          rewrite zle_lt_true.
          reflexivity.
          omega.   
          omega.
        Qed.

      End UctxArg5Body.

      Theorem uctx_arg5_code_correct:
        spec_le (uctx_arg5 ↦ uctx_arg5_spec_low) (〚uctx_arg5 ↦ f_uctx_arg5 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_arg5_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_arg5)
                                                               nil
                                                               (create_undef_temps (fn_temps f_uctx_arg5)))) H0. 
      Qed.

    End UCTXARG5.

    Section UCTXARG6.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_get ↦ gensem uctx_get_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxArg6Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_get *)

        Variable buctx_get: block.

        Hypothesis huctx_get1 : Genv.find_symbol ge uctx_get = Some buctx_get. 
        
        Hypothesis huctx_get2 : Genv.find_funct_ptr ge buctx_get = Some (External (EF_external uctx_get (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma uctx_arg6_body_correct: forall m d env le arg,
                                        env = PTree.empty _ ->
                                        uctx_arg6_spec d = Some (Int.unsigned arg) ->
                                        high_level_invariant d ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) uctx_arg6_body E0 le' (m, d) (Out_return (Some (Vint arg, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H1; assumption).
          unfold uctx_arg6_body.
          functional inversion H0; subst.
          assert(ipt: ipt d = true).
            destruct H1. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.  
          rewrite H3, H4, H5.
          rewrite Int.unsigned_repr.
          reflexivity.   
          omega.
          rewrite Int.unsigned_repr.
          unfold uctx_get_spec.   
          rewrite H3, H4, H5, ipt, H6.
          unfold is_UCTXT_ptr.
          rewrite H2.
          rewrite zle_lt_true.
          reflexivity.
          omega.   
          omega.
       Qed.

      End UctxArg6Body.

      Theorem uctx_arg6_code_correct:
        spec_le (uctx_arg6 ↦ uctx_arg6_spec_low) (〚uctx_arg6 ↦ f_uctx_arg6 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_arg6_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_arg6)
                                                               nil
                                                               (create_undef_temps (fn_temps f_uctx_arg6)))) H0. 
      Qed.

    End UCTXARG6.

    Section UCTXSETERRNO.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_set ↦ gensem uctx_set_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxSetErronoBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_set *)

        Variable buctx_set: block.

        Hypothesis huctx_set1 : Genv.find_symbol ge uctx_set = Some buctx_set. 
        
        Hypothesis huctx_set2 : Genv.find_funct_ptr ge buctx_set = Some (External (EF_external uctx_set (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        Lemma uctx_set_errno_body_correct: forall m d d' env le errno,
                                             env = PTree.empty _ ->
                                             PTree.get terrno le = Some (Vint errno) ->
                                             uctx_set_errno_spec (Int.unsigned errno) d = Some d' ->
                                             high_level_invariant d ->
                                             exists le',
                                               exec_stmt ge env le ((m, d): mem) uctx_set_errno_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H2; assumption).
          unfold uctx_set_errno_body.
          functional inversion H1; subst.
          assert(ipt: ipt d = true).
            destruct H2. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H4, H5, H6.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          unfold uctx_set_spec.
          rewrite H4, H5, H6, ipt.
          unfold is_UCTXT_ptr.
          rewrite zle_lt_true.
          reflexivity.
          omega.
          omega.
          omega.
        Qed.

      End UctxSetErronoBody.

      Theorem uctx_set_errno_code_correct:
        spec_le (uctx_set_errno ↦ uctx_set_errno_spec_low) (〚uctx_set_errno ↦ f_uctx_set_errno 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_set_errno_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_set_errno)
                                                               (Vint arg::nil)
                                                               (create_undef_temps (fn_temps f_uctx_set_errno)))) H0. 
      Qed.

    End UCTXSETERRNO.


    Section UCTXSETRETVAL1.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_set ↦ gensem uctx_set_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxSetRetval1Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_set *)

        Variable buctx_set: block.

        Hypothesis huctx_set1 : Genv.find_symbol ge uctx_set = Some buctx_set. 
        
        Hypothesis huctx_set2 : Genv.find_funct_ptr ge buctx_set = Some (External (EF_external uctx_set (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        Lemma uctx_set_retval1_body_correct: forall m d d' env le retval,
                                               env = PTree.empty _ ->
                                               PTree.get tretval le = Some (Vint retval) ->
                                               uctx_set_retval1_spec (Int.unsigned retval) d = Some d' ->
                                               high_level_invariant d ->
                                               exists le',
                                                 exec_stmt ge env le ((m, d): mem) uctx_set_retval1_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H2; assumption).
          unfold uctx_set_retval1_body.
          functional inversion H1; subst.
          assert(ipt: ipt d = true).
            destruct H2. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H4, H5, H6.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          unfold uctx_set_spec.
          rewrite H4, H5, H6, ipt.
          unfold is_UCTXT_ptr.
          rewrite zle_lt_true.
          reflexivity.
          omega.
          omega.
          omega.
        Qed.

      End UctxSetRetval1Body.

      Theorem uctx_set_retval1_code_correct:
        spec_le (uctx_set_retval1 ↦ uctx_set_retval1_spec_low) (〚uctx_set_retval1 ↦ f_uctx_set_retval1 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_set_retval1_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_set_retval1)
                                                               (Vint arg::nil)
                                                               (create_undef_temps (fn_temps f_uctx_set_retval1)))) H0. 
      Qed.

    End UCTXSETRETVAL1.

    Section UCTXSETRETVAL2.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_set ↦ gensem uctx_set_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxSetRetval2Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_set *)

        Variable buctx_set: block.

        Hypothesis huctx_set1 : Genv.find_symbol ge uctx_set = Some buctx_set. 
        
        Hypothesis huctx_set2 : Genv.find_funct_ptr ge buctx_set = Some (External (EF_external uctx_set (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        Lemma uctx_set_retval2_body_correct: forall m d d' env le retval,
                                               env = PTree.empty _ ->
                                               PTree.get tretval le = Some (Vint retval) ->
                                               uctx_set_retval2_spec (Int.unsigned retval) d = Some d' ->
                                               high_level_invariant d ->
                                               exists le',
                                                 exec_stmt ge env le ((m, d): mem) uctx_set_retval2_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H2; assumption).
          unfold uctx_set_retval2_body.
          functional inversion H1; subst.
          assert(ipt: ipt d = true).
            destruct H2. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H4, H5, H6.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          unfold uctx_set_spec.
          rewrite H4, H5, H6, ipt.
          unfold is_UCTXT_ptr.
          rewrite zle_lt_true.
          reflexivity.
          omega.
          omega.
          omega.
        Qed.

      End UctxSetRetval2Body.

      Theorem uctx_set_retval2_code_correct:
        spec_le (uctx_set_retval2 ↦ uctx_set_retval2_spec_low) (〚uctx_set_retval2 ↦ f_uctx_set_retval2 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_set_retval2_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_set_retval1)
                                                               (Vint arg::nil)
                                                               (create_undef_temps (fn_temps f_uctx_set_retval2)))) H0. 
      Qed.

    End UCTXSETRETVAL2.

    Section UCTXSETRETVAL3.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_set ↦ gensem uctx_set_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxSetRetval3Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_set *)

        Variable buctx_set: block.

        Hypothesis huctx_set1 : Genv.find_symbol ge uctx_set = Some buctx_set. 
        
        Hypothesis huctx_set2 : Genv.find_funct_ptr ge buctx_set = Some (External (EF_external uctx_set (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        Lemma uctx_set_retval3_body_correct: forall m d d' env le retval,
                                               env = PTree.empty _ ->
                                               PTree.get tretval le = Some (Vint retval) ->
                                               uctx_set_retval3_spec (Int.unsigned retval) d = Some d' ->
                                               high_level_invariant d ->
                                               exists le',
                                                 exec_stmt ge env le ((m, d): mem) uctx_set_retval3_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H2; assumption).
          unfold uctx_set_retval3_body.
          functional inversion H1; subst.
          assert(ipt: ipt d = true).
            destruct H2. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H4, H5, H6.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          unfold uctx_set_spec.
          rewrite H4, H5, H6, ipt.
          unfold is_UCTXT_ptr.
          rewrite zle_lt_true.
          reflexivity.
          omega.
          omega.
          omega.
        Qed.

      End UctxSetRetval3Body.

      Theorem uctx_set_retval3_code_correct:
        spec_le (uctx_set_retval3 ↦ uctx_set_retval3_spec_low) (〚uctx_set_retval3 ↦ f_uctx_set_retval3 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_set_retval3_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_set_retval1)
                                                               (Vint arg::nil)
                                                               (create_undef_temps (fn_temps f_uctx_set_retval3)))) H0. 
      Qed.

    End UCTXSETRETVAL3.

    Section UCTXSETRETVAL4.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ uctx_set ↦ gensem uctx_set_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section UctxSetRetval4Body.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_set *)

        Variable buctx_set: block.

        Hypothesis huctx_set1 : Genv.find_symbol ge uctx_set = Some buctx_set. 
        
        Hypothesis huctx_set2 : Genv.find_funct_ptr ge buctx_set = Some (External (EF_external uctx_set (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).


        Lemma uctx_set_retval4_body_correct: forall m d d' env le retval,
                                               env = PTree.empty _ ->
                                               PTree.get tretval le = Some (Vint retval) ->
                                               uctx_set_retval4_spec (Int.unsigned retval) d = Some d' ->
                                               high_level_invariant d ->
                                               exists le',
                                                 exec_stmt ge env le ((m, d): mem) uctx_set_retval4_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(cid_range: 0 <= cid d < 64) by (destruct H2; assumption).
          unfold uctx_set_retval4_body.
          functional inversion H1; subst.
          assert(ipt: ipt d = true).
            destruct H2. 
            rewrite <- valid_ikern_ipt.
            assumption.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H4, H5, H6.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          unfold uctx_set_spec.
          rewrite H4, H5, H6, ipt.
          unfold is_UCTXT_ptr.
          rewrite zle_lt_true.
          unfold uctx'.
          unfold uctx.
          repeat rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          rewrite Int.unsigned_repr.
          omega.
          omega.
        Qed.

      End UctxSetRetval4Body.

      Theorem uctx_set_retval4_code_correct:
        spec_le (uctx_set_retval4 ↦ uctx_set_retval4_spec_low) (〚uctx_set_retval4 ↦ f_uctx_set_retval4 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (uctx_set_retval4_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_uctx_set_retval1)
                                                               (Vint arg::nil)
                                                               (create_undef_temps (fn_temps f_uctx_set_retval4)))) H0. 
      Qed.

    End UCTXSETRETVAL4.


  End WithPrimitives.

End PPROCCODE.
