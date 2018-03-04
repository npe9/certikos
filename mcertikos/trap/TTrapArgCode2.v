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
(*         for the C functions implemented in the TTrapArg layer       *)
(*                                                                     *)
(*                        Xiongnan (Newman) Wu                         *)
(*                       Hao Chen (hao.chen@yale.edu)                  *)
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
Require Import compcert.lib.Integers.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import VCGen.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import TacticsForTesting.
Require Import XOmega.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import AbstractDataType.
Require Import TTrapArg.
Require Import TrapGenSpec.
Require Import TTrapArgCSource.
Require Import ObjTrap.
Require Import CommonTactic.

Module TTRAPARGCODE2.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.




    (*Section SYSMMAP.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
                                                    ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
                                                    ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
                                                    ⊕ uctx_arg4  ↦ gensem uctx_arg4_spec
                                                    ⊕ pt_read ↦ gensem ptRead_spec
                                                    ⊕ pt_resv ↦ gensem ptResv_spec
                                                    ⊕ vmx_set_mmap ↦ gensem vmx_set_mmap_spec
                                                    ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysMMapBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_arg2 *)

        Variable buctx_arg2: block.

        Hypothesis huctx_arg21 : Genv.find_symbol ge uctx_arg2 = Some buctx_arg2.

        Hypothesis huctx_arg22 : Genv.find_funct_ptr ge buctx_arg2 = Some (External (EF_external uctx_arg2 (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_arg3 *)

        Variable buctx_arg3: block.

        Hypothesis huctx_arg31 : Genv.find_symbol ge uctx_arg3 = Some buctx_arg3.

        Hypothesis huctx_arg32 : Genv.find_funct_ptr ge buctx_arg3 = Some (External (EF_external uctx_arg3 (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_arg4 *)

        Variable buctx_arg4: block.

        Hypothesis huctx_arg41 : Genv.find_symbol ge uctx_arg4 = Some buctx_arg4.

        Hypothesis huctx_arg42 : Genv.find_funct_ptr ge buctx_arg4 = Some (External (EF_external uctx_arg4 (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** pt_read *)

        Variable bpt_read: block.

        Hypothesis hpt_read1 : Genv.find_symbol ge pt_read = Some bpt_read.

        Hypothesis hpt_read2 : Genv.find_funct_ptr ge bpt_read = Some (External (EF_external pt_read (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (** pt_resv *)

        Variable bpt_resv: block.

        Hypothesis hpt_resv1 : Genv.find_symbol ge pt_resv = Some bpt_resv.

        Hypothesis hpt_resv2 : Genv.find_funct_ptr ge bpt_resv = Some (External (EF_external pt_resv (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default).

        (** vmx_set_mmap *)

        Variable bvmx_set_mmap: block.

        Hypothesis hvmx_set_mmap1 : Genv.find_symbol ge vmx_set_mmap = Some bvmx_set_mmap.

        Hypothesis hvmx_set_mmap2 : Genv.find_funct_ptr ge bvmx_set_mmap = Some (External (EF_external vmx_set_mmap (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default).

        (** uctx_set_errno *)

        Variable buctx_set_errno: block.

        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.

        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno = Some (External (EF_external uctx_set_errno (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).


        Lemma sys_mmap_body_correct: forall m d d' env le,
                                       env = PTree.empty _ ->
                                       trap_mmap_spec d = Some d' ->
                                       high_level_invariant d ->
                                       exists le',
                                         exec_stmt ge env le ((m, d): mem) sys_mmap_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(iflags: ikern d = true /\ pg d = true /\ ihost d = true).
          {
            functional inversion H0; subst.
            functional inversion H3; auto.
            functional inversion H3; auto.
            functional inversion H3; auto.
          }
          destruct iflags as [ikern iflags].
          destruct iflags as [pg ihost].
          destruct H1.
          assert(negval: Int.repr (-4096) = Int.repr (4294963200)).
          {
            apply Int.eqm_samerepr.
            unfold Int.eqm.
            unfold Int.eqmod.
            exists (-1).
            repeat autounfold.
            unfold two_power_nat, shift_nat.
            simpl.
            reflexivity.
          }

          functional inversion H0; subst.

          unfold hpa0 in *.
          functional inversion H2; subst.
          functional inversion H3; subst.
          functional inversion H4; subst.
          unfold andb in H5.
          subdestruct.
          destruct (Zdivide_dec 4096 (Int.unsigned n0) AuxStateDataType.HPS).
          destruct (Zdivide_dec 4096 (Int.unsigned n) AuxStateDataType.HPS).
          unfold Z.divide in *.
          destruct d0.
          destruct d1.
          Focus 2.
          simpl in *.
          discriminate Hdestruct0.
          Focus 2.
          simpl in *.
          discriminate Hdestruct.
          exploit (Z.mod_unique_pos (Int.unsigned n0) 4096 x 0).
          omega.
          omega.
          intro n0modval.
          exploit (Z.mod_unique_pos (Int.unsigned n) 4096 x0 0).
          omega.
          omega.
          intro nmodval.
          destruct (zle_le 1073741824 (Int.unsigned n0) 4026527744).
          Focus 2.
          simpl in *.
          discriminate H5.
          unfold sys_mmap_body.
          rewrite negval.
          assert(0 <= _x1 <= Int.max_unsigned).
          {
            functional inversion H9; try omega.
            functional inversion H; try omega.
            subst.
            functional inversion H36; try omega.
            destruct _x6.
            generalize (valid_nps pg); intro.
            functional inversion H25.
            clear H47.
            rewrite <- H49 in a0.
            simpl in a0.
            omega.
            omega.
            omega.
          }
          assert(0 <= _x3 <= Int.max_unsigned).
          {
            functional inversion H12; try omega.
            functional inversion H31; try omega.
          }

          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite ikern, pg, ihost.
          instantiate (1:= (Int.repr (cid d))).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          discharge_cmp.
          discharge_unsigned_range.
          discharge_unsigned_range.
          repeat vcgen.
          discharge_cmp.
          discharge_cmp.
          ptreesolve.
          discharge_cmp.
          repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          discharge_cmp.
          econstructor.
          ptreesolve.
          discharge_cmp.
          repeat vcgen.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat vcgen.
          discharge_cmp.
          omega.
          omega.
          omega.
          repeat vcgenfull.
          change (Z.lor (Z.lor 1 4) 2) with 7.
          instantiate (1:= (Int.repr _x1)).
          rewrite Int.unsigned_repr; try omega.
          eassumption.
          repeat vcgen.
          instantiate (1:= (Int.repr hpa')).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.
          repeat ptreesolve.
          discharge_cmp.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          simpl.
          unfold sem_mod, sem_binarith.
          simpl.
          discharge_cmp.
          discharge_cmp.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat vcgen.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat vcgenfull.
          rewrite <- n0modval.
          rewrite Z.add_0_r.
          repeat discharge_unsigned_range.
          rewrite <- n0modval.
          rewrite Z.add_0_r.
          repeat discharge_unsigned_range.


          unfold hpa0 in *.
          functional inversion H2; subst.
          functional inversion H3; subst.
          functional inversion H4; subst.
          unfold andb in H5.
          subdestruct.
          destruct (Zdivide_dec 4096 (Int.unsigned n0) AuxStateDataType.HPS).
          destruct (Zdivide_dec 4096 (Int.unsigned n) AuxStateDataType.HPS).
          unfold Z.divide in *.
          destruct d0.
          destruct d1.
          Focus 2.
          simpl in *.
          discriminate Hdestruct0.
          Focus 2.
          simpl in *.
          discriminate Hdestruct.
          exploit (Z.mod_unique_pos (Int.unsigned n0) 4096 x 0).
          omega.
          omega.
          intro n0modval.
          exploit (Z.mod_unique_pos (Int.unsigned n) 4096 x0 0).
          omega.
          omega.
          intro nmodval.
          destruct (zle_le 1073741824 (Int.unsigned n0) 4026527744).
          Focus 2.
          simpl in *.
          discriminate H5.
          unfold sys_mmap_body.
          rewrite negval.
          assert(0 <= _x1 <= Int.max_unsigned).
          {
            functional inversion H9; try omega.
            functional inversion H27; try omega.
          }
          subst.

          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite ikern, pg, ihost.
          instantiate (1:= (Int.repr (cid d))).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          discharge_cmp.
          discharge_unsigned_range.
          discharge_unsigned_range.
          repeat vcgen.
          discharge_cmp.
          discharge_cmp.
          ptreesolve.
          discharge_cmp.
          repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          discharge_cmp.
          econstructor.
          ptreesolve.
          discharge_cmp.
          repeat vcgen.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat vcgen.
          discharge_cmp.
          discharge_unsigned_range.
          omega.
          omega.
          repeat vcgenfull.
          repeat ptreesolve.
          discharge_cmp.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          simpl.
          unfold sem_mod, sem_binarith.
          simpl.
          discharge_cmp.
          discharge_cmp.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat vcgen.
          repeat ptreesolve.
          simpl.
          repeat ptreesolve.
          repeat vcgen.
          repeat vcgenfull.
          rewrite <- n0modval.
          rewrite Z.add_0_r.
          repeat discharge_unsigned_range.
          rewrite <- n0modval.
          rewrite Z.add_0_r.
          repeat discharge_unsigned_range.


          functional inversion H2; subst.
          functional inversion H3; subst.
          functional inversion H4; subst.
          unfold andb in H5.
          subdestruct.
          destruct (Zdivide_dec 4096 (Int.unsigned n0) AuxStateDataType.HPS).
          destruct (Zdivide_dec 4096 (Int.unsigned n) AuxStateDataType.HPS).
          unfold Z.divide in *.
          destruct d0.
          destruct d1.
          Focus 2.
          simpl in *.
          discriminate Hdestruct0.
          Focus 2.
          simpl in *.
          discriminate Hdestruct.
          exploit (Z.mod_unique_pos (Int.unsigned n0) 4096 x 0).
          omega.
          omega.
          intro n0modval.
          exploit (Z.mod_unique_pos (Int.unsigned n) 4096 x0 0).
          omega.
          omega.
          intro nmodval.
          destruct (zle_le 1073741824 (Int.unsigned n0) 4026527744).
          simpl in *.
          discriminate H5.
          unfold sys_mmap_body.
          rewrite negval.
          destruct o.

          {
            esplit.
            repeat vcgen.
            unfold get_curid_spec.
            rewrite ikern, pg, ihost.
            instantiate (1:= (Int.repr (cid d))).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            discharge_unsigned_range.
            discharge_unsigned_range.
            repeat vcgen.
            discharge_cmp.
            discharge_cmp.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            discharge_cmp.
            repeat ptreesolve.
            discharge_cmp.
            repeat vcgen.
          }
          {
            esplit.
            repeat vcgen.
            unfold get_curid_spec.
            rewrite ikern, pg, ihost.
            instantiate (1:= (Int.repr (cid d))).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            discharge_unsigned_range.
            discharge_unsigned_range.
            repeat vcgen.
            discharge_cmp.
            discharge_cmp.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            discharge_cmp.
            repeat ptreesolve.
            discharge_cmp.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat ptreesolve.
            discharge_cmp.
            repeat vcgen.
          }
          {
            destruct (Zdivide_dec 4096 (Int.unsigned n0) AuxStateDataType.HPS).
            destruct (Zdivide_dec 4096 (Int.unsigned n) AuxStateDataType.HPS).
            simpl in *.
            discriminate Hdestruct0.
            Focus 2.
            simpl in *.
            discriminate Hdestruct.
            unfold Z.divide in d0.
            destruct d0.
            exploit (Z.mod_unique_pos (Int.unsigned n0) 4096 x 0).
            omega.
            omega.
            intro n0modval.
            assert(nmodneq0: 0 <> Int.unsigned n mod 4096).
            {
              intro.
              symmetry in H.
              eapply Z.mod_divide in H.
              contradiction.
              omega.
            }
            assert(0 <= Int.unsigned n mod 4096 < 4096).
            {
                apply Z.mod_bound_pos.
                discharge_unsigned_range.
                omega.
            }
            unfold sys_mmap_body.
            esplit.
            repeat vcgen.
            unfold get_curid_spec.
            rewrite ikern, pg, ihost.
            instantiate (1:= (Int.repr (cid d))).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            discharge_unsigned_range.
            discharge_unsigned_range.
            repeat vcgen.
            discharge_cmp.
            discharge_cmp.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            discharge_cmp.
            repeat ptreesolve.
            discharge_cmp.
            repeat vcgen.
          }
          {
            destruct (Zdivide_dec 4096 (Int.unsigned n0) AuxStateDataType.HPS).
            simpl in *.
            discriminate Hdestruct.
            assert(nmodneq0: 0 <> Int.unsigned n0 mod 4096).
            {
              intro.
              symmetry in H.
              eapply Z.mod_divide in H.
              contradiction.
              omega.
            }
            assert(0 <= Int.unsigned n0 mod 4096 < 4096).
            {
                apply Z.mod_bound_pos.
                discharge_unsigned_range.
                omega.
            }
            unfold sys_mmap_body.
            esplit.
            repeat vcgen.
            unfold get_curid_spec.
            rewrite ikern, pg, ihost.
            instantiate (1:= (Int.repr (cid d))).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            discharge_unsigned_range.
            discharge_unsigned_range.
            repeat vcgen.
            discharge_cmp.
            discharge_cmp.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            discharge_cmp.
            repeat ptreesolve.
            discharge_cmp.
            repeat vcgen.
          }
        Qed.

      End SysMMapBody.

      Theorem sys_mmap_code_correct:
        spec_le (sys_mmap ↦ trap_mmap_spec_low) (〚sys_mmap ↦ f_sys_mmap 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (sys_mmap_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp b7 Hb7fs Hb7fp m'0 labd labd0 (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_sys_mmap)
                                                               nil
                                                               (create_undef_temps (fn_temps f_sys_mmap)))) H1. 
      Qed.

    End SYSMMAP.*)


    Section PTFRESV.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ pt_resv ↦ gensem ptResv_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PtfResvBody.

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

        Hypothesis hpt_resv2 : Genv.find_funct_ptr ge bpt_resv = Some (External (EF_external pt_resv (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default).

        Lemma high_inv_curid:
          forall d,
            high_level_invariant d ->
            ikern d = true ->
            ihost d = true ->
            pg d = true ->
            get_curid_spec d = Some (cid d)
            /\ 0 <= (cid d) <= Int.max_unsigned.
        Proof.
          unfold get_curid_spec. intros.
          subrewrite'. split; trivial.
          destruct H.
          generalize max_unsigned_val; intro muval.
          omega.
        Qed.

        Require Import AuxLemma.

        Lemma ptInsert0_range:
          forall p1 p2 v d d' re n,
            ptInsert0_spec p1 p2 v n d = Some (d', re) ->
            262144 <= nps d <= 1048576 ->
            0 <= re <= Int.max_unsigned.
        Proof.
          intros. rewrite_omega.
          functional inversion H; subst; try omega.
          functional inversion H10; try subst; try omega.
        Qed.

        Lemma ptResv_range:
          forall v1 v2 v3 d d' r,
            ptResv_spec v1 v2 v3 d = Some (d', r) ->
            262144 <= nps d <= 1048576 ->
            0 <= r <= Int.max_unsigned.
        Proof.
          intros. rewrite_omega.
          functional inversion H; clear H; [omega|].
          eapply ptInsert0_range; eauto.
          functional inversion H2; subst; trivial.
        Qed.

        Lemma ptResv_range':
          forall v1 v2 v3 d d' r,
            ptResv_spec v1 v2 v3 d = Some (d', r) ->
            high_level_invariant d ->
            pg d = true ->
            0 <= r <= Int.max_unsigned.
        Proof.
          intros.
          eapply ptResv_range; eauto.
          inv H0.
          eauto.
        Qed.            
                                                            
        Lemma ptfault_resv_body_correct:
          forall m d d' env le vaddr,
            env = PTree.empty _ ->
            PTree.get _vaddr le = Some (Vint vaddr) ->
            ptfault_resv_spec (Int.unsigned vaddr) d = Some d' ->
            high_level_invariant d ->
            exists le',
              exec_stmt ge env le ((m, d): mem) ptfault_resv_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold ptfault_resv_body.
          functional inversion H1; subst.
          {
            exploit high_inv_curid; eauto.
            intros (Hget & Hrange).
            exploit ptResv_range'; eauto. intros Hrange'.
            esplit.
            repeat vcgen.
            - rewrite <- (Int.unsigned_repr (cid d)).
              reflexivity.
              assumption.
            - rewrite <- (Int.unsigned_repr (_x0)) in H8;
              eassumption.
            - apply Hrange.
            - apply Hrange.
          }
          {
            exploit high_inv_curid; eauto.
            intros (Hget & Hrange).
            esplit.
            repeat vcgen.
            rewrite <- (Int.unsigned_repr (cid d')).
            reflexivity.
            assumption.
          }
        Qed.

      End PtfResvBody.

      Theorem ptfault_resv_code_correct:
        spec_le (ptfault_resv ↦ ptf_resv_spec_low) (〚ptfault_resv ↦ f_ptfault_resv 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (ptfault_resv_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp
                                            m'0 labd labd0 (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_ptfault_resv)
                                                               (Vint i::nil)
                                                               (create_undef_temps (fn_temps f_ptfault_resv)))) H1. 
      Qed.

    End PTFRESV.


    Section SYSPROCCREATE.

      Let L: compatlayer (cdata RData) := uctx_arg2  ↦ gensem uctx_arg2_spec
               ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
               ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec
               ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
               ⊕ get_curid ↦ gensem get_curid_spec
               ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
               ⊕ container_can_consume ↦ gensem container_can_consume_spec
               ⊕ proc_create ↦ proc_create_compatsem proc_create_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysProcCreateBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** uctx_arg2 *)

        Variable buctx_arg2: block.

        Hypothesis huctx_arg21 : Genv.find_symbol ge uctx_arg2 = Some buctx_arg2.

        Hypothesis huctx_arg22 : Genv.find_funct_ptr ge buctx_arg2 = Some (External (EF_external uctx_arg2 (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_arg3 *)

        Variable buctx_arg3: block.

        Hypothesis huctx_arg31 : Genv.find_symbol ge uctx_arg3 = Some buctx_arg3.

        Hypothesis huctx_arg32 : Genv.find_funct_ptr ge buctx_arg3 = Some (External (EF_external uctx_arg3 (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_set_errno *)

        Variable buctx_set_errno: block.

        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.

        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno = Some (External (EF_external uctx_set_errno (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** uctx_set_retval1 *)

        Variable buctx_set_retval1: block.

        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.

        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 = Some (External (EF_external uctx_set_retval1 (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid.

        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** get_nchildren *)

        Variable bget_nchildren: block.

        Hypothesis hget_nchildren1 : Genv.find_symbol ge container_get_nchildren = Some bget_nchildren.

        Hypothesis hget_nchildren2 : 
          Genv.find_funct_ptr ge bget_nchildren = 
          Some (External (EF_external container_get_nchildren 
                                      (signature_of_type (Tcons tint Tnil) tint cc_default)) 
                         (Tcons tint Tnil) tint cc_default).

        (** container_can_consume *)

        Variable bcan_consume: block.

        Hypothesis hcan_consume1 : Genv.find_symbol ge container_can_consume = Some bcan_consume.

        Hypothesis hcan_consume2 : Genv.find_funct_ptr ge bcan_consume = Some (External (EF_external container_can_consume (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (** proc_create *)

        Variable bproc_create: block.

        Hypothesis hproc_create1 : Genv.find_symbol ge proc_create = Some bproc_create.

        Hypothesis hproc_create2 : Genv.find_funct_ptr ge bproc_create = Some (External (EF_external proc_create (signature_of_type (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tint Tnil))) tint cc_default)) (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tint Tnil))) tint cc_default).


        Ltac if_simpl :=
          repeat match goal with
                 | [ H : ?a = _ |- context [if ?a then _ else _] ] => rewrite H
                 | [ H : _ = ?a |- context [if ?a then _ else _] ] => rewrite <- H
                 end.

        Lemma sys_proc_create_body_correct: 
          forall m d d' env le,
            env = PTree.empty _ ->
            trap_proc_create_spec sc m d = Some d' ->
            high_level_invariant d ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_proc_create_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize (tptrsize tvoid).
          intros.
          subst.
          destruct H2.
          destruct valid_container.
          
          rename H1 into Hspec; unfold trap_proc_create_spec in Hspec.
          destruct (uctx_arg3_spec d) eqn:Harg3; try discriminate Hspec.
          assert (Herrno: uctx_set_errno_spec 1 d = Some d' \/ 
                          exists abd', uctx_set_errno_spec 0 abd' = Some d') 
            by (subdestruct; eauto); destruct Herrno as [Herrno|Herrno].

          (* Case 1: one of the if conditions fails; return error code *)
          functional inversion Herrno; subst.
          functional inversion Harg3; subst.
          specialize (cvalid_max_children _ (proj1 (correct_curid H2))).
          unfold sys_proc_create_body.

          destruct (zle_le 0 (Int.unsigned n)
                           (cquota (ZMap.get (cid d) (AC d)) -
                            cusage (ZMap.get (cid d) (AC d)))) eqn:Hquota.
          {
            esplit.
            d3 vcgen.
            repeat vcgen.
            unfold get_curid_spec; rewrites.
            rewrite Int.unsigned_repr; eauto; omega.

            d2 vcgen.
            repeat vcgen.

            d2 vcgen.
            repeat vcgen.
            unfold container_can_consume_spec; rewrites.
            erewrite (proj1 (correct_curid _)); rewrite Int.unsigned_repr; eauto; omega.

            d2 vcgen.
            repeat vcgen.
            unfold container_get_nchildren_spec; rewrites.
            erewrite (proj1 (correct_curid _)); rewrite Int.unsigned_repr; eauto; omega.

            destruct (zle_le 0 (cid d * max_children + 1 + max_children) num_id) eqn:Hchild.
            {
              destruct (zlt (Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d))))) max_children) eqn:Hnc.
              {
                subdestruct.
                rewrite <- Herrno in Hspec.
                unfold uctx_set_errno_spec in Hspec; subdestruct.
                inv Hspec.
                rename H37 into Hspec.
                apply f_equal with (f:= PTree.get (ZIndexed.index (cid r0))) in Hspec.
                rewrite 2 PTree.gss in Hspec.
                inv Hspec.
                rename H41 into Hspec.
                apply f_equal with (f:= PTree.get 14) in Hspec.
                rewrite 2 PTree.gss in Hspec; inv Hspec.
              }
              {
                vcgen.
                repeat vcgen.
                cases; try omega; vcgen.
                repeat vcgen.
              }
            }
            {
              vcgen.
              repeat vcgen.
              cases; try omega; vcgen.
              repeat vcgen.
            }
          }
          {
            esplit.
            d3 vcgen.
            repeat vcgen.
            unfold get_curid_spec; if_simpl.
            rewrite Int.unsigned_repr; eauto; omega.

            d2 vcgen.
            repeat vcgen.

            d2 vcgen.
            repeat vcgen.
            unfold container_can_consume_spec; rewrites.
            erewrite (proj1 (correct_curid _)); rewrite Int.unsigned_repr; eauto; omega.

            d2 vcgen.
            repeat vcgen.
            unfold container_get_nchildren_spec; rewrites.
            erewrite (proj1 (correct_curid _)); rewrite Int.unsigned_repr; eauto; omega.

            destruct (zle_le 0 (cid d * max_children + 1 + max_children) num_id) eqn:Hchild.
            {
              destruct (zlt (Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d))))) max_children);
              repeat vcgen.
            }
            {
              repeat vcgen.
            }
          } 
      
          (* Case 2: requester has enough available quota to spawn child, and has not exceeded
             its maximum number of allowed children *)
          destruct Herrno as [d'' Herrno].
          assert (Hcon: uctx_set_errno_spec 0 d'' <> uctx_set_errno_spec 1 d).
          {
            unfold uctx_set_errno_spec.
            functional inversion Herrno; functional inversion Harg3; rewrites.
            intro Hcon; inv Hcon.
            rename H38 into Hcon.
            apply f_equal with (f:= PTree.get (ZIndexed.index (cid d''))) in Hcon.
            rewrite 2 PTree.gss in Hcon; inv Hcon.
            rename H42 into Hcon.
            apply f_equal with (f:= PTree.get 14) in Hcon.
            rewrite 2 PTree.gss in Hcon; inv Hcon.
          }
          subdestruct; try solve [contradiction Hcon; rewrite Herrno, Hspec; reflexivity].
          unfold ELF_ident in Hdestruct5.
          unfold Int.eq in Hdestruct13; subdestruct.
          injection Hdestruct5; intros; subst.
          rewrite Hdestruct7 in Hdestruct9.
          injection Hdestruct9; intros; subst.
          clear Hdestruct17.
          apply unsigned_inj in e0.
          generalize Hdestruct14; intro proc_create_inv.
          unfold proc_create_spec in proc_create_inv.
          subdestruct.
          subst.
          destruct a0.
          injection proc_create_inv; intros; subst.
          unfold sys_proc_create_body.
          destruct (correct_curid eq_refl) as [Hused _].
          specialize (cvalid_quota _ Hused); specialize (cvalid_usage _ Hused).
          esplit.

          d3 vcgen.
          repeat vcgen.
          unfold get_curid_spec; if_simpl.
          rewrite Int.unsigned_repr; eauto; omega.

          d4 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          
          repeat vcgen.
          unfold container_can_consume_spec; if_simpl.
          rewrite Int.unsigned_repr; eauto; omega.

          d2 vcgen.
          repeat vcgen.
          unfold container_get_nchildren_spec; if_simpl.
          rewrite Int.unsigned_repr; eauto; omega.
          
          vcgen.
          repeat vcgen.
          repeat vcgen.

          d2 vcgen.
          repeat vcgen.

          d2 vcgen.
          d4 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          erewrite stencil_matches_symbols; eauto.
          repeat vcgen.
          erewrite stencil_matches_symbols; eauto.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          unfold proc_create_spec; if_simpl.
          rewrite Hdestruct22; rewrite Int.unsigned_repr; eauto; omega.

          repeat vcgen.
          Grab Existential Variables.
          assumption.
          assumption.
          assumption.
          assumption.
        Qed.

      End SysProcCreateBody.

      Theorem sys_proc_create_code_correct:
        spec_le (sys_proc_create ↦ trap_proc_create_spec_low) (〚sys_proc_create ↦ f_sys_proc_create 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (sys_proc_create_body_correct 
                    s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp 
                    b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp
                    b6 Hb6fs Hb6fp b7 Hb7fs Hb7fp m'0 labd labd0 (PTree.empty _) 
                    (bind_parameter_temps' (fn_params f_sys_proc_create) nil
                       (create_undef_temps (fn_temps f_sys_proc_create)))) H0. 
      Qed.

    End SYSPROCCREATE.


  End WithPrimitives.

End TTRAPARGCODE2.