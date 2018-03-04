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
(*          for the C functions implemented in the TTrap layer         *)
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
Require Import DispatchGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import XOmega.
Require Import TTrapCSource.
Require Import AbstractDataType.
Require Import ObjArg.
Require Import ObjTrap.
Require Import ObjSyncIPC.
Require Export TrapPrimSemantics.
Require Import CommonTactic.


Module TTRAPCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.


    Section TRAPSENDTOCHANPRE.

      Let L: compatlayer (cdata RData) :=
                    uctx_arg2  ↦ gensem uctx_arg2_spec
                    ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
                    ⊕ uctx_arg4  ↦ gensem uctx_arg4_spec
                    ⊕ syncsendto_chan_pre ↦ gensem syncsendto_chan_pre_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section TrapSenToChanBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** uctx_arg2 *)
        Variable buctx_arg2: block.
        Hypothesis huctx_arg21 : Genv.find_symbol ge uctx_arg2 = Some buctx_arg2.
        Hypothesis huctx_arg22 : Genv.find_funct_ptr ge buctx_arg2 =
                                 Some (External (EF_external uctx_arg2 (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** uctx_arg3 *)
        Variable buctx_arg3: block.
        Hypothesis huctx_arg31 : Genv.find_symbol ge uctx_arg3 = Some buctx_arg3.
        Hypothesis huctx_arg32 : Genv.find_funct_ptr ge buctx_arg3 = 
                                 Some (External (EF_external uctx_arg3 (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** uctx_arg4 *)
        Variable buctx_arg4: block.
        Hypothesis huctx_arg41 : Genv.find_symbol ge uctx_arg4 = Some buctx_arg4.
        Hypothesis huctx_arg42 : Genv.find_funct_ptr ge buctx_arg4 = 
                                 Some (External (EF_external uctx_arg4 (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** syncsendto_chan_pre *)
        Variable bsyncsendto_chan_pre: block.
        Hypothesis hsyncsendto_chan_pre1 : Genv.find_symbol ge syncsendto_chan_pre = Some bsyncsendto_chan_pre.
        Hypothesis hsyncsendto_chan_pre2 : Genv.find_funct_ptr ge bsyncsendto_chan_pre =
                                    Some (External (EF_external syncsendto_chan_pre
                                                                (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default))
                                                   (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default).


        Lemma trap_sendtochan_pre_body_correct: forall m d d' env le val,
            env = PTree.empty _ ->
            trap_sendtochan_pre_spec d = Some (d', Int.unsigned val) ->
            exists le',
              exec_stmt ge env le ((m, d): mem) trap_sendtochan_pre_body E0 le' (m, d') (Out_return (Some (Vint val, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; try subst;
          functional inversion H2; try subst;
          functional inversion H3; try subst;
          unfold trap_sendtochan_pre_body;
          esplit;
          repeat vcgen.
        Qed.

      End TrapSenToChanBody.

      Theorem trap_sendtochan_pre_code_correct:
        spec_le
          (trap_sendtochan_pre ↦ trap_sendtochan_pre_spec_low)
          (〚trap_sendtochan_pre ↦ f_trap_sendtochan_pre 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (trap_sendtochan_pre_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_trap_sendtochan_pre)
                                    nil
                                    (create_undef_temps (fn_temps f_trap_sendtochan_pre)))) H0.
      Qed.

    End TRAPSENDTOCHANPRE.



    Section TRAPSENDTOCHANPOST.

      Let L: compatlayer (cdata RData) :=
                    uctx_set_errno  ↦ gensem  uctx_set_errno_spec
                    ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                    ⊕ syncsendto_chan_post ↦ gensem syncsendto_chan_post_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section TrapSenToChanPostBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        (** uctx_set_retval1 *)
        Variable buctx_set_retval1: block.
        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.
        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 =
                                        Some (External (EF_external uctx_set_retval1
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).

        (** syncsendto_chan_post *)
        Variable bsyncsendto_chan_post: block.
        Hypothesis hsyncsendto_chan_post1 : Genv.find_symbol ge syncsendto_chan_post = Some bsyncsendto_chan_post.
        Hypothesis hsyncsendto_chan_post2 : Genv.find_funct_ptr ge bsyncsendto_chan_post =
                                    Some (External (EF_external syncsendto_chan_post
                                                                (signature_of_type Tnil tint cc_default))
                                                   Tnil tint cc_default).


        Lemma trap_sendtochan_post_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_sendtochan_post_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) trap_sendtochan_post_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          assert(rrange: 0 <= r <= Int.max_unsigned).
          {
            functional inversion H1; try omega.
            apply Int.unsigned_range_2.
          }
          unfold trap_sendtochan_post_body;
          esplit;
          repeat vcgen.
        Qed.

      End TrapSenToChanPostBody.

      Theorem trap_sendtochan_post_code_correct:
        spec_le
          (trap_sendtochan_post ↦ trap_sendtochan_post_spec_low)
          (〚trap_sendtochan_post ↦ f_trap_sendtochan_post 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (trap_sendtochan_post_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_trap_sendtochan_post)
                                    nil
                                    (create_undef_temps (fn_temps f_trap_sendtochan_post)))) H0.
      Qed.

    End TRAPSENDTOCHANPOST.


    Section SYSCALLDISPATCHC.

      Let L: compatlayer (cdata RData) := sys_proc_create  ↦ trap_proccreate_compatsem trap_proc_create_spec
                  ⊕ sys_get_quota  ↦ gensem trap_get_quota_spec
                  ⊕ sys_offer_shared_mem  ↦ gensem trap_offer_shared_mem_spec
                  ⊕ print ↦ gensem print_spec
                  ⊕ uctx_arg1  ↦ gensem uctx_arg1_spec
                  ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SyscallDispatchCBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** sys_proc_create *)

        Variable bsys_proc_create: block.

        Hypothesis hsys_proc_create1 : Genv.find_symbol ge sys_proc_create = Some bsys_proc_create. 
        
        Hypothesis hsys_proc_create2 : Genv.find_funct_ptr ge bsys_proc_create = Some (External (EF_external sys_proc_create (signature_of_type Tnil tvoid cc_default)) Tnil tvoid cc_default).

        (** sys_get_quota *)

        Variable bsys_get_quota: block.

        Hypothesis hsys_get_quota1 : Genv.find_symbol ge sys_get_quota = Some bsys_get_quota.

        Hypothesis hsys_get_quota2 : Genv.find_funct_ptr ge bsys_get_quota = Some (External (EF_external sys_get_quota (signature_of_type Tnil tvoid cc_default)) Tnil tvoid cc_default).

        (** sys_offer_shared_mem *)

        Variable bsys_offer_shared_mem: block.

        Hypothesis hsys_offer_shared_mem1 : Genv.find_symbol ge sys_offer_shared_mem = Some bsys_offer_shared_mem.

        Hypothesis hsys_offer_shared_mem2 : 
          Genv.find_funct_ptr ge bsys_offer_shared_mem = 
          Some (External (EF_external sys_offer_shared_mem (signature_of_type Tnil tvoid cc_default)) Tnil tvoid cc_default).

        Variable bprint: block.

        Hypothesis hprint1 : Genv.find_symbol ge print = Some bprint.

        Hypothesis hprint2 : 
          Genv.find_funct_ptr ge bprint = 
          Some (External (EF_external print (signature_of_type Tnil tvoid cc_default)) Tnil tvoid cc_default).

        (** sys_receive_chan *)

        Variable bsys_receive_chan: block.

        Hypothesis hsys_receive_chan1 : Genv.find_symbol ge sys_receive_chan = Some bsys_receive_chan. 
        
        Hypothesis hsys_receive_chan2 : Genv.find_funct_ptr ge bsys_receive_chan = Some (External (EF_external sys_receive_chan (signature_of_type Tnil tvoid cc_default)) Tnil tvoid cc_default).

        (** uctx_arg1 *)

        Variable buctx_arg1: block.

        Hypothesis huctx_arg11 : Genv.find_symbol ge uctx_arg1 = Some buctx_arg1. 
        
        Hypothesis huctx_arg12 : Genv.find_funct_ptr ge buctx_arg1 = Some (External (EF_external uctx_arg1 (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** uctx_set_errno *)

        Variable buctx_set_errno: block.

        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno. 
        
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno = Some (External (EF_external uctx_set_errno (signature_of_type (Tcons tint Tnil) tvoid cc_default)) (Tcons tint Tnil) tvoid cc_default).


        Lemma NSYS_NR_correct: forall m d d' le z,
                                   uctx_set_errno_spec 3 d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   0 <= z <= Int.max_unsigned ->
                                   Syscall_Z2Num z = NSYS_NR ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H2.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          assumption.
        Qed.

        Lemma NSYS_PUTS_correct: forall m d d' le z,
                                   uctx_set_errno_spec 3 d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_PUTS ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_RING0_SPAWN_correct: forall m d d' le z,
                                   uctx_set_errno_spec 3 d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_RING0_SPAWN ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_SPAWN_correct: forall m d d' le z,
                                   trap_proc_create_spec sc m d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_SPAWN ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_YIELD_correct: forall m d d' le z,
                                   uctx_set_errno_spec 3 d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_YIELD ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_DISK_OP_correct: forall m d d' le z,
                                   uctx_set_errno_spec 3 d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_DISK_OP ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_DISK_CAP_correct: forall m d d' le z,
                                   uctx_set_errno_spec 3 d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_DISK_CAP ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_GET_QUOTA_correct: forall m d d' le z,
                                   trap_get_quota_spec d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_GET_QUOTA ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_RECV_correct: forall m d d' le z,
                                   uctx_set_errno_spec 3 d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_RECV ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NSYS_OFFER_SHARED_MEM_correct: forall m d d' le z,
                                   trap_offer_shared_mem_spec d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_SHARE ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma NPRINT_correct: forall m d d' le z,
                                   print_spec d = Some d' ->
                                   uctx_arg1_spec d = Some z ->
                                   Syscall_Z2Num z = NSYS_PRINT ->
                                   exists le',
                                     exec_stmt ge (PTree.empty _) le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syscall_dispatch_c_body.
          subst.
          unfold Syscall_Z2Num in H1.
          subdestruct.
          rewrite <- Int.unsigned_repr in H0 at 1.
          esplit.
          repeat vcgen.
          omega.
        Qed.

        Lemma syscall_dispatch_c_body_correct: forall m d d' env le,
                                        env = PTree.empty _ ->
                                        sys_dispatch_c_spec sc m d = Some d' ->
                                        high_level_invariant d ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) syscall_dispatch_c_body E0 le' (m, d') Out_normal.
        Proof.   
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold sys_dispatch_c_spec in H0.
          case_eq (uctx_arg1_spec d); intros; rewrite H in H0; try discriminate H0.
          case_eq (zle_le 0 z Int.max_unsigned); intros; rewrite H2 in H0; try discriminate H0.
          case_eq (Syscall_Z2Num z); intros; rewrite H3 in H0.
          eapply NSYS_PUTS_correct; eauto.
          eapply NSYS_RING0_SPAWN_correct; eauto.
          eapply NSYS_SPAWN_correct; eauto.
          eapply NSYS_YIELD_correct; eauto.
          eapply NSYS_DISK_OP_correct; eauto.
          eapply NSYS_DISK_CAP_correct; eauto.
          eapply NSYS_GET_QUOTA_correct; eauto.
          eapply NSYS_RECV_correct; eauto.
          eapply NSYS_OFFER_SHARED_MEM_correct; eauto.
          eapply NPRINT_correct; eauto.
          eapply NSYS_NR_correct; eauto.
        Qed.

      End SyscallDispatchCBody.

      Theorem syscall_dispatch_c_code_correct:
        spec_le (syscall_dispatch_C ↦ sys_dispatch_c_spec_low) (〚syscall_dispatch_C ↦ f_syscall_dispatch_c 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (syscall_dispatch_c_body_correct 
                    s (Genv.globalenv p) makeglobalenv b0
                    Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp
                    m'0 labd labd0 (PTree.empty _)
                    (bind_parameter_temps' (fn_params f_syscall_dispatch_c)
                                           nil (create_undef_temps (fn_temps f_syscall_dispatch_c)))) H0. 
      Qed.

    End SYSCALLDISPATCHC.

  End WithPrimitives.

End TTRAPCODE.