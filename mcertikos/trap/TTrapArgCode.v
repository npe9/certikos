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

Lemma int_wrap:
  Int.repr (-1) = Int.repr (Int.max_unsigned).
Proof.
  apply Int.eqm_samerepr.
  unfold Int.eqm.
  unfold Int.eqmod.
  exists (-1).
  reflexivity.
Qed.

Lemma unsigned_int_range:
  forall x: int,
    0 <= Int.unsigned x <= Int64.max_unsigned.
Proof.
  split.
  apply Int.unsigned_range.
  apply Z.le_trans with (m:=Int.max_unsigned);
    ( apply Int.unsigned_range_2 ||
            unfold Int.max_unsigned, Int64.max_unsigned;
      simpl; omega).
Qed.

Lemma cat_unsigned64_lor_range:
  forall lo hi,
    0 <= Z.lor (Z.shiftl (Int.unsigned hi) 32) (Int.unsigned lo) <= Int64.max_unsigned.
Proof.
  intros lo hi.
  apply Z64_lor_range.
  apply Z_shiftl_32_range.
  apply Int.unsigned_range_2.
  apply unsigned_int_range.
Qed.

Lemma unsigned_div_2pow32_eq_0:
  forall x, Int.unsigned x / 2 ^ 32 = 0.
Proof.
  intro.
  generalize (Int.unsigned_range x); intro.
  repeat autounfold in H.
  unfold two_power_nat, shift_nat in H.
  simpl in H.
  change (2 ^ 32) with 4294967296.
  xomega.
Qed.

Lemma unsigned_shiftl_lor_shiftr_range:
  forall x y n,
    0 <= n ->
    0 <= Z.shiftr (Z.lor (Z.shiftl (Int.unsigned x) n) (Int.unsigned y)) n <= Int.max_unsigned.
Proof.
  split.
  - apply Z.shiftr_nonneg.
    apply Z_lor_range_lo.
    + apply Z.shiftl_nonneg.
      apply Int.unsigned_range.
    + apply Int.unsigned_range.
  - rewrite Z.shiftr_lor.
    rewrite Z.shiftr_shiftl_r.
    + rewrite Z.sub_diag with (n:=n).
      rewrite Z.shiftr_0_r.
      rewrite Z.shiftr_div_pow2.
      apply Z_lor_range.
      apply Int.unsigned_range_2.
      split.
      * change 0 with (0 / 2 ^ n).
        apply Z_div_le.
        apply Z.lt_gt.
        apply Z.pow_pos_nonneg; omega.
        apply Int.unsigned_range.
      * rewrite <- Z_div_mult_full with (a:=Int.max_unsigned)(b:=2^n).
        {
          apply Z_div_le.
          - apply Z.lt_gt.
            apply Z.pow_pos_nonneg; omega.
          - apply Z.le_trans with (m:=Int.max_unsigned).
            + apply Int.unsigned_range_2.
            + apply Z.le_mul_diag_r with (n:=Int.max_unsigned)(m:=2^n).
              * repeat autounfold.
                unfold two_power_nat, shift_nat.
                simpl.
                omega.
              * apply Zle_lt_or_eq in H.
                destruct H.
                {
                  generalize (Z.pow_gt_1 2 n).
                  intro Hr.
                  destruct Hr.
                  - omega.
                  - apply H0 in H.
                    omega.
                }
                rewrite <- H.
                simpl.
                omega.
        }
        apply Z.pow_nonzero.
        omega.
        assumption.
      * assumption.
    + assumption.
Qed.

Lemma unsigned_shiftl_lor_shiftr_32_range:
  forall x y,
    0 <= Z.shiftr (Z.lor (Z.shiftl (Int.unsigned x) 32) (Int.unsigned y)) 32 <= Int.max_unsigned.
Proof.
  intros.
  apply unsigned_shiftl_lor_shiftr_range with (n:=32).
  omega.
Qed.

Lemma Z_mod_range:
  forall x n,
    n > 0 ->
    0 <= x mod n <= n - 1.
Proof.
  intros.
  assert(0 <= x mod n < n).
  apply Z_mod_lt.
  omega.
  omega.
Qed.

Ltac intomega :=
  repeat autounfold; unfold two_power_nat, shift_nat; simpl; omega.

Hint Resolve Z_lor_range_lo.
Hint Resolve Z_land_range_lo.
Hint Resolve Z_shiftl_32_range.
Hint Resolve Int.unsigned_range_2.
Hint Resolve cat_unsigned64_lor_range.
Hint Resolve Z.shiftr_nonneg.
Hint Resolve unsigned_shiftl_lor_shiftr_range.
Hint Resolve unsigned_shiftl_lor_shiftr_32_range.

Module TTRAPARGCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Section SYS_PRINT.

(**
(*

extern unsigned int get_curid(void);
extern unsigned int uctx_arg2(void);
extern unsigned int device_output(unsigned int, unsigned int, unsigned int);
extern void uctx_set_errno(unsigned int);

      void print () {
          unsigned int curid;
          curid = get_curid();
          out = uctx_arg2();
          device_output (curid, curid, out);          
          uctx_set_errno(0); 

      }

*)
*)

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
                      ⊕ uctx_arg2 ↦ gensem uctx_arg2_spec
                      ⊕ device_output ↦ gensem device_output_spec
                      ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section PrintBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)
        Variable bget_curid: block.
        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid.
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid =
                                 Some (External (EF_external get_curid (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** uctx_arg2 *)
        Variable buctx_arg2: block.
        Hypothesis huctx_arg21 : Genv.find_symbol ge uctx_arg2 = Some buctx_arg2.
        Hypothesis huctx_arg22 : Genv.find_funct_ptr ge buctx_arg2 =
                                 Some (External (EF_external uctx_arg2
                                                             (signature_of_type Tnil tint cc_default))
                                                Tnil tint cc_default).

        (** device_output *)
        Variable bdevice_output: block.
        Hypothesis hdevice_output1 : Genv.find_symbol ge device_output = Some bdevice_output.
        Hypothesis hdevice_output2 : Genv.find_funct_ptr ge bdevice_output =
                                     Some (External (EF_external device_output
                                                                 (signature_of_type (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))
                                                                                    tvoid cc_default))
                                                    (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default).

        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).


        Require Import AuxLemma.
        Require Import CommonTactic.

        Lemma print_correct:
          forall m d d' env le,
            env = PTree.empty _ ->
            print_spec d = Some d' ->
            high_level_invariant d ->
            exists le',
              exec_stmt ge env le ((m, d): mem) print_body E0 le' (m, d') Out_normal.
        Proof.
          (*generalize max_unsigned_val; intro muval.*)
          intros; subst.
          unfold print_body.
          functional inversion H0. 
          esplit.

          assert (0 <= cid d <= Int.max_unsigned) as curid_range.
          { pose proof (valid_curid _ H1) as valid_curid.
            rewrite_omega.
          }

          d3 vcgen.
          { repeat vcgen.
            unfold get_curid_spec.
            functional inversion H2; subst. subrewrite'.
            instantiate (1 := Int.repr (cid d)).
            rewrite Int.unsigned_repr; auto.
          }

          assert (0 <= content <= Int.max_unsigned)
            as (content_range).
          { functional inversion H2; subst.
            repeat discharge_unsigned_range.
          }

          repeat vcgen.
          {
            instantiate (1 := Int.repr content).
            rewrite Int.unsigned_repr; auto.
          }          
          rewrite Int.unsigned_repr; auto.          
        Qed.

      End PrintBody.

      Theorem print_code_correct:
        spec_le (print ↦ print_spec_low)
                (〚print ↦ f_print 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (print_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             m'0 labd labd'
             (PTree.empty _)
             (bind_parameter_temps' (fn_params f_print)
                                    nil
                                    (create_undef_temps (fn_temps f_print)))) H.
      Qed.

    End SYS_PRINT.

    Section SYSGETQUOTA.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
                      ⊕ container_get_quota ↦ gensem container_get_quota_spec
                      ⊕ container_get_usage ↦ gensem container_get_usage_spec
                      ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec
                      ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysGetQuotaBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)
        Variable bget_curid: block.
        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid.
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid =
                                 Some (External (EF_external get_curid (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** container_get_quota *)
        Variable bcontainer_get_quota: block.
        Hypothesis hcontainer_get_quota1 : Genv.find_symbol ge container_get_quota = Some bcontainer_get_quota.
        Hypothesis hcontainer_get_quota2 : Genv.find_funct_ptr ge bcontainer_get_quota =
                                   Some (External (EF_external container_get_quota
                                                               (signature_of_type (Tcons tint Tnil) tint cc_default))
                                                  (Tcons tint Tnil) tint cc_default).

        (** container_get_usage *)
        Variable bcontainer_get_usage: block.
        Hypothesis hcontainer_get_usage1 : Genv.find_symbol ge container_get_usage = Some bcontainer_get_usage.
        Hypothesis hcontainer_get_usage2 : Genv.find_funct_ptr ge bcontainer_get_usage =
                                   Some (External (EF_external container_get_usage
                                                               (signature_of_type (Tcons tint Tnil) tint cc_default))
                                                  (Tcons tint Tnil) tint cc_default).

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


        Lemma sys_get_quota_body_correct:
          forall m d d' env le,
            env = PTree.empty _ ->
            trap_get_quota_spec d = Some d' ->
            high_level_invariant d ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_get_quota_body E0 le' (m, d') Out_normal.
        Proof.
          (*generalize max_unsigned_val; intro muval.*)
          intros; subst.
          unfold sys_get_quota_body.
          functional inversion H0.

          assert (0 <= curid <= Int.max_unsigned) as curid_range.
          { functional inversion H2.
            pose proof (valid_curid _ H1) as valid_curid.
            intomega.
          }

          assert (0 <= quota <= Int.max_unsigned /\
                  0 <= usage <= Int.max_unsigned /\
                  0 <= quota - usage <= Int.max_unsigned)
              as (quota_range & usage_range & remaining_quota_range).
          { functional inversion H3; subst.
            functional inversion H4; subst.
            pose proof (cvalid_quota _ (valid_container _ H1) _ H7) as valid_quota.
            pose proof (cvalid_usage _ (valid_container _ H1) _ H7) as valid_usage.
            unfold c, c0; omega.
          }

          esplit.
          d3 vcgen.
          { repeat vcgen.
            instantiate (1 := Int.repr curid).
            rewrite Int.unsigned_repr; auto.
          }
          d3 vcgen; [ repeat vcgen.. |].
          { instantiate (1 := Int.repr quota).
            rewrite Int.unsigned_repr; auto.
          }
          vcgen.
          { repeat vcgen.
            instantiate (1 := Int.repr usage).
            rewrite Int.unsigned_repr; auto.
          }
          repeat vcgen.
        Qed.

      End SysGetQuotaBody.

      Theorem sys_get_quota_code_correct:
        spec_le (sys_get_quota ↦ trap_get_quota_spec_low)
                (〚sys_get_quota ↦ f_sys_get_quota 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_get_quota_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             m'0 labd labd0
             (PTree.empty _)
             (bind_parameter_temps' (fn_params f_sys_get_quota)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_get_quota)))) H.
      Qed.

    End SYSGETQUOTA.


    Section SYSOFFER_SHARED_MEM.

(**
<<
extern unsigned int get_curid(void);
extern unsigned int uctx_arg2(void);
extern unsigned int offer_shared_mem(unsigned int, unsigned int, unsigned int);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);

void sys_offer_shared_mem()
{
    unsigned int curid;
    unsigned int vadr;
    unsigned int res;
    curid = get_curid();
    if (curid == 1) {
       vadr = uctx_arg2();
       res = offer_shared_mem (1, 2, vadr);
       uctx_set_retval1(res);
       uctx_set_errno(0);       
    } {
       uctx_set_errno(0);             
    }
}
>>
*)

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
                      ⊕ uctx_arg2 ↦ gensem uctx_arg2_spec
                      ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec
                      ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec
                      ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysShareBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)
        Variable bget_curid: block.
        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid.
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid =
                                 Some (External (EF_external get_curid (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** uctx_arg2 *)
        Variable buctx_arg2: block.
        Hypothesis huctx_arg21 : Genv.find_symbol ge uctx_arg2 = Some buctx_arg2.
        Hypothesis huctx_arg22 : Genv.find_funct_ptr ge buctx_arg2 =
                                 Some (External (EF_external uctx_arg2
                                                             (signature_of_type Tnil tint cc_default))
                                                Tnil tint cc_default).

        (** offer_shared_mem *)
        Variable boffer_shared_mem: block.
        Hypothesis hoffer_shared_mem1 : Genv.find_symbol ge offer_shared_mem = Some boffer_shared_mem.
        Hypothesis hoffer_shared_mem2 : Genv.find_funct_ptr ge boffer_shared_mem =
                                        Some (External (EF_external offer_shared_mem
                                                                    (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                                                                       tint cc_default))
                                                       (Tcons tint(Tcons tint(Tcons tint Tnil))) tint cc_default).

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


        Require Import AuxLemma.

        Lemma sys_offer_shared_mem_correct:
          forall m d d' env le,
            env = PTree.empty _ ->
            trap_offer_shared_mem_spec d = Some d' ->
            high_level_invariant d ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_offer_shared_mem_body E0 le' (m, d') Out_normal.
        Proof.
          (*generalize max_unsigned_val; intro muval.*)
          intros; subst.
          unfold sys_offer_shared_mem_body.
          functional inversion H0. 
          - esplit.
            assert (0 <= vadr <= Int.max_unsigned /\
                    0 <= res <= Int.max_unsigned)
              as (vadr_range & res_range).
            { functional inversion H3; subst.
              split. 
              repeat discharge_unsigned_range.
              functional inversion H5; subst; rewrite_omega.
            }

            d3 vcgen.
            { repeat vcgen.
              unfold get_curid_spec.
              functional inversion H3; subst. subrewrite'.
              instantiate (1 := Int.repr 1).
              rewrite Int.unsigned_repr; auto.
              rewrite_omega.
            }

            repeat vcgen.

            {
              rewrite Int.unsigned_repr; auto.
            }
            {
              instantiate (1 := Int.repr res).
              rewrite Int.unsigned_repr; auto.
              rewrite Int.unsigned_repr; eauto.              
            }
            {
              rewrite_omega.
            }
            {
              rewrite Int.unsigned_repr; eauto.
            }
          - esplit.
            assert (0 <= n <= Int.max_unsigned) as curid_range.
            { pose proof (valid_curid _ H1) as valid_curid.
              intomega.
            }

            d3 vcgen.
            { repeat vcgen.
              unfold get_curid_spec.
              functional inversion H3; subst. subrewrite'.
              instantiate (1 := Int.repr n).
              rewrite Int.unsigned_repr; auto.
            }

            repeat vcgen.
        Qed.

      End SysShareBody.

      Theorem sys_offer_shared_mem_code_correct:
        spec_le (sys_offer_shared_mem ↦ trap_offer_shared_mem_spec_low)
                (〚sys_offer_shared_mem ↦ f_sys_offer_shared_mem 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_offer_shared_mem_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             m'0 labd labd0
             (PTree.empty _)
             (bind_parameter_temps' (fn_params f_sys_offer_shared_mem)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_offer_shared_mem)))) H.
      Qed.

    End SYSOFFER_SHARED_MEM.

    Section SYSRECEIVECHAN.

      Let L: compatlayer (cdata RData) :=
                    uctx_arg2  ↦ gensem uctx_arg2_spec
                    ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
                    ⊕ uctx_arg4  ↦ gensem uctx_arg4_spec
                    ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec
                    ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                    ⊕ syncreceive_chan ↦ gensem syncreceive_chan_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysReceiveChanBody.

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

        (** syncreceive_chan *)
        Variable bsyncreceive_chan: block.
        Hypothesis hsyncreceive_chan1 : Genv.find_symbol ge syncreceive_chan = Some bsyncreceive_chan.
        Hypothesis hsyncreceive_chan2 : Genv.find_funct_ptr ge bsyncreceive_chan =
                                    Some (External (EF_external syncreceive_chan
                                                                (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default))
                                                   (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default).


        Lemma sys_receive_chan_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_receivechan_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_receive_chan_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          assert(rrange: 0 <= r <= Int.max_unsigned).
          {
            functional inversion H4; try omega.
            unfold arecvcount.
            functional inversion H3.
            rewrite <- H20 in *.
            generalize (Z.min_spec (Int.unsigned scount) (Int.unsigned n)).
            intro tmp.
            destruct tmp; destruct H25; rewrite H26;
            apply Int.unsigned_range_2.
          }
          rewrite <- Int.unsigned_repr with r in H4; try omega.
          functional inversion H1; try subst;
          functional inversion H2; try subst;
          functional inversion H3; try subst;
          unfold sys_receive_chan_body;
          esplit;
          repeat vcgen.
        Qed.

      End SysReceiveChanBody.

      Theorem sys_receive_chan_code_correct:
        spec_le
          (sys_receive_chan ↦ trap_receivechan_spec_low)
          (〚sys_receive_chan ↦ f_sys_receive_chan 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_receive_chan_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             b5 Hb5fs Hb5fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_receive_chan)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_receive_chan)))) H0.
      Qed.

    End SYSRECEIVECHAN.


    (*Section SYSGETEXITINFO.

      Let L: compatlayer (cdata RData) :=
        vmx_get_exit_reason ↦ gensem vmx_get_exit_reason_spec
                            ⊕ vmx_get_exit_io_port ↦ gensem vmx_get_exit_io_port_spec
                            ⊕ vmx_get_io_width ↦ gensem vmx_get_io_width_spec
                            ⊕ vmx_get_io_write ↦ gensem vmx_get_io_write_spec
                            ⊕ vmx_get_exit_io_rep ↦ gensem vmx_get_exit_io_rep_spec
                            ⊕ vmx_get_exit_io_str ↦ gensem vmx_get_exit_io_str_spec
                            ⊕ vmx_get_exit_fault_addr ↦ gensem vmx_get_exit_fault_addr_spec
                            ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                            ⊕ uctx_set_retval2  ↦ gensem uctx_set_retval2_spec
                            ⊕ uctx_set_retval3  ↦ gensem uctx_set_retval3_spec
                            ⊕ uctx_set_retval4  ↦ gensem uctx_set_retval4_spec
                            ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysGetExitinfoBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_get_exit_reason *)
        Variable bvmx_get_exit_reason: block.
        Hypothesis hvmx_get_exit_reason1 : Genv.find_symbol ge vmx_get_exit_reason = Some bvmx_get_exit_reason.
        Hypothesis hvmx_get_exit_reason2 : Genv.find_funct_ptr ge bvmx_get_exit_reason =
                                           let arg_type := Tnil in
                                           let ret_type := tuint in
                                           let cal_conv := cc_default in
                                           let prim := vmx_get_exit_reason in
                                           Some (External (EF_external prim
                                                                       (signature_of_type arg_type ret_type cal_conv))
                                                          arg_type ret_type cal_conv).


        (** vmx_get_exit_io_port *)
        Variable bvmx_get_exit_io_port: block.
        Hypothesis hvmx_get_exit_io_port1 : Genv.find_symbol ge vmx_get_exit_io_port = Some bvmx_get_exit_io_port.
        Hypothesis hvmx_get_exit_io_port2 : Genv.find_funct_ptr ge bvmx_get_exit_io_port =
                                            let arg_type := Tnil in
                                            let ret_type := tuint in
                                            let cal_conv := cc_default in
                                            let prim := vmx_get_exit_io_port in
                                            Some (External (EF_external prim
                                                                        (signature_of_type arg_type ret_type cal_conv))
                                                           arg_type ret_type cal_conv).


        (** vmx_get_io_width *)
        Variable bvmx_get_io_width: block.
        Hypothesis hvmx_get_io_width1 : Genv.find_symbol ge vmx_get_io_width = Some bvmx_get_io_width.
        Hypothesis hvmx_get_io_width2 : Genv.find_funct_ptr ge bvmx_get_io_width =
                                        let arg_type := Tnil in
                                        let ret_type := tuint in
                                        let cal_conv := cc_default in
                                        let prim := vmx_get_io_width in
                                        Some (External (EF_external prim
                                                                    (signature_of_type arg_type ret_type cal_conv))
                                                       arg_type ret_type cal_conv).

        (** vmx_get_io_write *)
        Variable bvmx_get_io_write: block.
        Hypothesis hvmx_get_io_write1 : Genv.find_symbol ge vmx_get_io_write = Some bvmx_get_io_write.
        Hypothesis hvmx_get_io_write2 : Genv.find_funct_ptr ge bvmx_get_io_write =
                                        let arg_type := Tnil in
                                        let ret_type := tuint in
                                        let cal_conv := cc_default in
                                        let prim := vmx_get_io_write in
                                        Some (External (EF_external prim
                                                                    (signature_of_type arg_type ret_type cal_conv))
                                                       arg_type ret_type cal_conv).

        (** vmx_get_exit_io_rep *)
        Variable bvmx_get_exit_io_rep: block.
        Hypothesis hvmx_get_exit_io_rep1 : Genv.find_symbol ge vmx_get_exit_io_rep = Some bvmx_get_exit_io_rep.
        Hypothesis hvmx_get_exit_io_rep2 : Genv.find_funct_ptr ge bvmx_get_exit_io_rep =
                                           let arg_type := Tnil in
                                           let ret_type := tuint in
                                           let cal_conv := cc_default in
                                           let prim := vmx_get_exit_io_rep in
                                           Some (External (EF_external prim
                                                                       (signature_of_type arg_type ret_type cal_conv))
                                                          arg_type ret_type cal_conv).
        (** vmx_get_exit_io_str *)
        Variable bvmx_get_exit_io_str: block.
        Hypothesis hvmx_get_exit_io_str1 : Genv.find_symbol ge vmx_get_exit_io_str = Some bvmx_get_exit_io_str.
        Hypothesis hvmx_get_exit_io_str2 : Genv.find_funct_ptr ge bvmx_get_exit_io_str =
                                           let arg_type := Tnil in
                                           let ret_type := tuint in
                                           let cal_conv := cc_default in
                                           let prim := vmx_get_exit_io_str in
                                           Some (External (EF_external prim
                                                                       (signature_of_type arg_type ret_type cal_conv))
                                                          arg_type ret_type cal_conv).
        (** vmx_get_exit_fault_addr *)
        Variable bvmx_get_exit_fault_addr: block.
        Hypothesis hvmx_get_exit_fault_addr1 : Genv.find_symbol ge vmx_get_exit_fault_addr = Some bvmx_get_exit_fault_addr.
        Hypothesis hvmx_get_exit_fault_addr2 : Genv.find_funct_ptr ge bvmx_get_exit_fault_addr =
                                               let arg_type := Tnil in
                                               let ret_type := tuint in
                                               let cal_conv := cc_default in
                                               let prim := vmx_get_exit_fault_addr in
                                               Some (External (EF_external prim
                                                                           (signature_of_type arg_type ret_type cal_conv))
                                                              arg_type ret_type cal_conv).
        
        (** uctx_set_retval1 *)
        Variable buctx_set_retval1: block.
        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.
        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 =
                                        Some (External (EF_external uctx_set_retval1
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).

        (** uctx_set_retval2 *)
        Variable buctx_set_retval2: block.
        Hypothesis huctx_set_retval21 : Genv.find_symbol ge uctx_set_retval2 = Some buctx_set_retval2.
        Hypothesis huctx_set_retval22 : Genv.find_funct_ptr ge buctx_set_retval2 =
                                        Some (External (EF_external uctx_set_retval2
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).
        (** uctx_set_retval3 *)
        Variable buctx_set_retval3: block.
        Hypothesis huctx_set_retval31 : Genv.find_symbol ge uctx_set_retval3 = Some buctx_set_retval3.
        Hypothesis huctx_set_retval32 : Genv.find_funct_ptr ge buctx_set_retval3 =
                                        Some (External (EF_external uctx_set_retval3
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).

        (** uctx_set_retval4 *)
        Variable buctx_set_retval4: block.
        Hypothesis huctx_set_retval41 : Genv.find_symbol ge uctx_set_retval4 = Some buctx_set_retval4.
        Hypothesis huctx_set_retval42 : Genv.find_funct_ptr ge buctx_set_retval4 =
                                        Some (External (EF_external uctx_set_retval4
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).
        
        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_get_exitinfo_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_get_exitinfo_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_get_exitinfo_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.

          assert(0 <= port <= Int.max_unsigned).
          {
            functional inversion H2.
            repeat discharge_unsigned_range.
          }

          assert(0 <= width <= Int.max_unsigned).
          {
            functional inversion H3;
            intomega.
          }

          assert(0 <= write <= Int.max_unsigned).
          {
            functional inversion H4;
            intomega.
          }

          assert(0 <= rep <= Int.max_unsigned).
          {
            functional inversion H5; subst.
            apply Z_land_range.
            split.
            apply Z.shiftr_nonneg.
            discharge_unsigned_range.
            rewrite Z.shiftr_div_pow2.
            change (2 ^ 5) with 32.
            generalize (Int.unsigned_range_2 v); intro.
            xomega.
            omega.
            omega.
          }
          assert(0 <= str <= Int.max_unsigned).
          {
            functional inversion H6; subst.
            apply Z_land_range.
            split.
            apply Z.shiftr_nonneg.
            discharge_unsigned_range.
            rewrite Z.shiftr_div_pow2.
            change (2 ^ 4) with 16.
            generalize (Int.unsigned_range_2 v); intro.
            xomega.
            omega.
            omega.
          }
          assert(0 <= fault_addr <= Int.max_unsigned).
          {
            functional inversion H7; subst.
            repeat discharge_unsigned_range.
          }
          rewrite <- Int.unsigned_repr in H2 at 1; try omega.
          rewrite <- Int.unsigned_repr in H3 at 1; try omega.
          rewrite <- Int.unsigned_repr in H4 at 1; try omega.
          rewrite <- Int.unsigned_repr in H5 at 1; try omega.
          rewrite <- Int.unsigned_repr in H6 at 1; try omega.
          rewrite <- Int.unsigned_repr in H7 at 1; try omega.
          unfold flags in *.
          unfold get_flags in H12.
          subdestruct; subst.

          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
          }
          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            change (Z.lor 0 1) with 1 in H12.
            change (Int.unsigned Int.one) with 1.
            assumption.
          }
          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            change (Z.lor 0 2) with 2 in *.
            repeat vcgen.
          }
          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            change (Z.lor 1 2) with 3 in *.
            repeat vcgen.
          }
          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            change (Z.lor 0 4) with 4 in *.
            repeat vcgen.
          }
          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            change (Z.lor 1 4) with 5 in *.
            repeat vcgen.
          }
          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            change (Z.lor (Z.lor 0 2) 4) with 6 in *.
            repeat vcgen.
          }
          {
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 30)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            discharge_cmp.
            repeat vcgen.
            ptreesolve.
            discharge_cmp.
            change (Z.lor (Z.lor 1 2) 4) with 7 in *.
            repeat vcgen.
          }
          {
            assert(0 <= port <= Int.max_unsigned).
            {
              functional inversion H2.
              repeat discharge_unsigned_range.
            }

            assert(0 <= width <= Int.max_unsigned).
            {
              functional inversion H3;
              intomega.
            }

            assert(0 <= write <= Int.max_unsigned).
            {
              functional inversion H4;
              intomega.
            }

            assert(0 <= rep <= Int.max_unsigned).
            {
              functional inversion H5; subst.
              apply Z_land_range.
              split.
              apply Z.shiftr_nonneg.
              discharge_unsigned_range.
              rewrite Z.shiftr_div_pow2.
              change (2 ^ 5) with 32.
              generalize (Int.unsigned_range_2 v); intro.
              xomega.
              omega.
              omega.
            }
            assert(0 <= str <= Int.max_unsigned).
            {
              functional inversion H6; subst.
              apply Z_land_range.
              split.
              apply Z.shiftr_nonneg.
              discharge_unsigned_range.
              rewrite Z.shiftr_div_pow2.
              change (2 ^ 4) with 16.
              generalize (Int.unsigned_range_2 v); intro.
              xomega.
              omega.
              omega.
            }
            assert(0 <= fault_addr <= Int.max_unsigned).
            {
              functional inversion H7; subst.
              repeat discharge_unsigned_range.
            }
            rewrite <- Int.unsigned_repr in H2 at 1; try omega.
            rewrite <- Int.unsigned_repr in H3 at 1; try omega.
            rewrite <- Int.unsigned_repr in H4 at 1; try omega.
            rewrite <- Int.unsigned_repr in H5 at 1; try omega.
            rewrite <- Int.unsigned_repr in H6 at 1; try omega.
            rewrite <- Int.unsigned_repr in H7 at 1; try omega.
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            instantiate (1:= (Int.repr 48)).
            rewrite Int.unsigned_repr; try omega.
            reflexivity.
            repeat vcgen.
            repeat vcgen.
          }
          {
            assert(0 <= reason <= Int.max_unsigned).
            {
              functional inversion H1; subst.
              apply Z_land_range.
              repeat discharge_unsigned_range.
              omega.
            }
            assert(0 <= port <= Int.max_unsigned).
            {
              functional inversion H2.
              repeat discharge_unsigned_range.
            }

            assert(0 <= width <= Int.max_unsigned).
            {
              functional inversion H3;
              intomega.
            }

            assert(0 <= write <= Int.max_unsigned).
            {
              functional inversion H4;
              intomega.
            }

            assert(0 <= rep <= Int.max_unsigned).
            {
              functional inversion H5; subst.
              apply Z_land_range.
              split.
              apply Z.shiftr_nonneg.
              discharge_unsigned_range.
              rewrite Z.shiftr_div_pow2.
              change (2 ^ 5) with 32.
              generalize (Int.unsigned_range_2 v); intro.
              xomega.
              omega.
              omega.
            }
            assert(0 <= str <= Int.max_unsigned).
            {
              functional inversion H6; subst.
              apply Z_land_range.
              split.
              apply Z.shiftr_nonneg.
              discharge_unsigned_range.
              rewrite Z.shiftr_div_pow2.
              change (2 ^ 4) with 16.
              generalize (Int.unsigned_range_2 v); intro.
              xomega.
              omega.
              omega.
            }
            assert(0 <= fault_addr <= Int.max_unsigned).
            {
              functional inversion H7; subst.
              repeat discharge_unsigned_range.
            }
            rewrite <- Int.unsigned_repr in H1 at 1; try omega.
            rewrite <- Int.unsigned_repr in H2 at 1; try omega.
            rewrite <- Int.unsigned_repr in H3 at 1; try omega.
            rewrite <- Int.unsigned_repr in H4 at 1; try omega.
            rewrite <- Int.unsigned_repr in H5 at 1; try omega.
            rewrite <- Int.unsigned_repr in H6 at 1; try omega.
            rewrite <- Int.unsigned_repr in H7 at 1; try omega.
            unfold sys_get_exitinfo_body.
            esplit.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            d3 vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
            repeat vcgen.
          }
        Qed.
          
      End SysGetExitinfoBody.

      Theorem sys_get_exitinfo_body_code_correct:
        spec_le
          (sys_get_exitinfo ↦ trap_get_exitinfo_spec_low)
          (〚sys_get_exitinfo ↦ f_sys_get_exitinfo 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_get_exitinfo_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             b5 Hb5fs Hb5fp
             b6 Hb6fs Hb6fp
             b7 Hb7fs Hb7fp
             b8 Hb8fs Hb8fp
             b9 Hb9fs Hb9fp
             b10 Hb10fs Hb10fp
             b11 Hb11fs Hb11fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_get_exitinfo)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_get_exitinfo)))) H.
      Qed.

    End SYSGETEXITINFO.

    
    Section SYSHANDLERDMSR.

      Let L: compatlayer (cdata RData) :=
        rdmsr ↦ gensem rdmsr_spec
              ⊕ vmx_get_reg ↦ gensem vmx_get_reg_spec
              ⊕ vmx_set_reg ↦ gensem vmx_set_reg_spec
              ⊕ vmx_get_next_eip ↦ gensem vmx_get_next_eip_spec
              ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysHandleRdmsrBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** rdmsr *)
        Variable brdmsr: block.
        Hypothesis hrdmsr1 : Genv.find_symbol ge rdmsr = Some brdmsr.
        Hypothesis hrdmsr2 : Genv.find_funct_ptr ge brdmsr =
                             let arg_type := (Tcons tint Tnil) in
                             let ret_type := tulong in
                             let cal_conv := cc_default in
                             let prim := rdmsr in
                             Some (External (EF_external prim
                                                         (signature_of_type arg_type ret_type cal_conv))
                                            arg_type ret_type cal_conv).

        (** vmx_get_reg *)
        Variable bvmx_get_reg: block.
        Hypothesis hvmx_get_reg1 : Genv.find_symbol ge vmx_get_reg = Some bvmx_get_reg.
        Hypothesis hvmx_get_reg2 : Genv.find_funct_ptr ge bvmx_get_reg =
                                   let arg_type := Tcons tuint Tnil in
                                   let ret_type := tuint in
                                   let cal_conv := cc_default in
                                   let prim := vmx_get_reg in
                                   Some (External (EF_external
                                                     prim
                                                     (signature_of_type arg_type ret_type cal_conv))
                                                  arg_type ret_type cal_conv).

        (** vmx_set_reg *)
        Variable bvmx_set_reg: block.
        Hypothesis hvmx_set_reg1 : Genv.find_symbol ge vmx_set_reg = Some bvmx_set_reg.
        Hypothesis hvmx_set_reg2 : Genv.find_funct_ptr ge bvmx_set_reg =
                                   let arg_type := Tcons tuint (Tcons tuint Tnil) in
                                   let ret_type := tvoid in
                                   let cal_conv := cc_default in
                                   let prim := vmx_set_reg in
                                   Some (External (EF_external
                                                     prim
                                                     (signature_of_type arg_type ret_type cal_conv))
                                                  arg_type ret_type cal_conv).

        
        (** vmx_get_next_eip *)
        Variable bvmx_get_next_eip: block.
        Hypothesis hvmx_get_next_eip1 : Genv.find_symbol ge vmx_get_next_eip = Some bvmx_get_next_eip.
        Hypothesis hvmx_get_next_eip2 : Genv.find_funct_ptr ge bvmx_get_next_eip =
                                     let arg_type := Tnil in
                                     let ret_type := tuint in
                                     let cal_conv := cc_default in
                                     let prim := vmx_get_next_eip in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).        

        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_handle_rdmsr_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_handle_rdmsr_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_handle_rdmsr_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize max_unsigned64_val; intro muval64.
          
          intros; subst.
          functional inversion H0; subst.
          unfold sys_handle_rdmsr_body.
          assert(0 <= val <= Int64.max_unsigned).
          {
            functional inversion H2.
            omega.
          }
          assert(0 <= next_eip <= Int.max_unsigned).
          {
            functional inversion H5; subst.
            assumption.
          }

          assert(0 <= msr <= Int.max_unsigned).
          {
            functional inversion H1; subst;
            apply Int.unsigned_range_2.
          }
         
          unfold   val_low, val_high in *.
          change (2 ^ 32) with 4294967296 in *.

          assert (Hvalmodrange: 0 <= val mod 4294967296 <= Int64.max_unsigned).
          {
            split.
            apply Z_mod_range.
            omega.
            apply Z.le_trans with (m:=Int.max_unsigned).
            apply Z_mod_range.
            omega.
            omega.
          }
          
          assert (Hvalmodrange2: 0 <= val mod 4294967296 <= Int.max_unsigned).
          {
            split.
            apply Z_mod_range.
            omega.
            apply Z_mod_range.
            omega.
          }

          assert(Hvaldivrange:   0 <= val / 4294967296 <= Int64.max_unsigned).
          {
            unfold Int64.max_unsigned.
            simpl.
            unfold Int64.max_unsigned in H7.
            simpl in H7.
            xomega.
          }

          assert(Hvaldivrange2:  0 <=  val / 4294967296 <= Int.max_unsigned).
          {
            unfold Int.max_unsigned.
            simpl.
            xomega.
          }
          esplit.

          d3 vcgen.
          repeat vcgen.
          instantiate (1:=Int.repr msr); rewrite Int.unsigned_repr.
          reflexivity.
          assumption.

          d3 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          instantiate (1:=Int64.repr val).
          rewrite Int64.unsigned_repr.
          reflexivity.
          assumption.

          d3 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          unfold Int64.modu.
          repeat rewrite Int64.unsigned_repr.
          eassumption.
          intomega.
          assumption.
          assumption.
          intomega.
          assumption.

          d3 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          unfold Int64.divu.
          repeat rewrite Int64.unsigned_repr.
          eassumption.
          intomega.
          assumption.
          assumption.
          intomega.
          assumption.

          d3 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          instantiate (1:=Int.repr next_eip); rewrite Int.unsigned_repr.
          reflexivity.
          assumption.

          d3 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
        Qed.

      End SysHandleRdmsrBody.

      Theorem sys_handle_rdmsr_body_code_correct:
        spec_le
          (sys_handle_rdmsr ↦ trap_handle_rdmsr_spec_low)
          (〚sys_handle_rdmsr ↦ f_sys_handle_rdmsr 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_handle_rdmsr_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_handle_rdmsr)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_handle_rdmsr)))) H.
      Qed.

    End SYSHANDLERDMSR.
    
    
    Section SYSHANDLEWRMSR.

      Let L: compatlayer (cdata RData) :=
        wrmsr ↦ gensem wrmsr_spec
              ⊕ vmx_get_reg ↦ gensem vmx_get_reg_spec
              ⊕ vmx_set_reg ↦ gensem vmx_set_reg_spec
              ⊕ vmx_get_next_eip ↦ gensem vmx_get_next_eip_spec
              ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysHandleWrmsrBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** wrmsr *)
        Variable bwrmsr: block.
        Hypothesis hwrmsr1 : Genv.find_symbol ge wrmsr = Some bwrmsr.
        Hypothesis hwrmsr2 : Genv.find_funct_ptr ge bwrmsr =
                             let arg_type := (Tcons tuint (Tcons tulong Tnil)) in
                             let ret_type := tuint in
                             let cal_conv := cc_default in
                             let prim := wrmsr in
                             Some (External (EF_external prim
                                                         (signature_of_type arg_type ret_type cal_conv))
                                            arg_type ret_type cal_conv).

        (** vmx_get_reg *)
        Variable bvmx_get_reg: block.
        Hypothesis hvmx_get_reg1 : Genv.find_symbol ge vmx_get_reg = Some bvmx_get_reg.
        Hypothesis hvmx_get_reg2 : Genv.find_funct_ptr ge bvmx_get_reg =
                                   let arg_type := Tcons tuint Tnil in
                                   let ret_type := tuint in
                                   let cal_conv := cc_default in
                                   let prim := vmx_get_reg in
                                   Some (External (EF_external
                                                     prim
                                                     (signature_of_type arg_type ret_type cal_conv))
                                                  arg_type ret_type cal_conv).

        (** vmx_set_reg *)
        Variable bvmx_set_reg: block.
        Hypothesis hvmx_set_reg1 : Genv.find_symbol ge vmx_set_reg = Some bvmx_set_reg.
        Hypothesis hvmx_set_reg2 : Genv.find_funct_ptr ge bvmx_set_reg =
                                   let arg_type := Tcons tuint (Tcons tuint Tnil) in
                                   let ret_type := tvoid in
                                   let cal_conv := cc_default in
                                   let prim := vmx_set_reg in
                                   Some (External (EF_external
                                                     prim
                                                     (signature_of_type arg_type ret_type cal_conv))
                                                  arg_type ret_type cal_conv).

        
        (** vmx_get_next_eip *)
        Variable bvmx_get_next_eip: block.
        Hypothesis hvmx_get_next_eip1 : Genv.find_symbol ge vmx_get_next_eip = Some bvmx_get_next_eip.
        Hypothesis hvmx_get_next_eip2 : Genv.find_funct_ptr ge bvmx_get_next_eip =
                                     let arg_type := Tnil in
                                     let ret_type := tuint in
                                     let cal_conv := cc_default in
                                     let prim := vmx_get_next_eip in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).        

        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_handle_wrmsr_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_handle_wrmsr_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_handle_wrmsr_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize max_unsigned64_val; intro muval64.
          
          intros; subst.
          functional inversion H0; subst.
          unfold sys_handle_wrmsr_body.
          assert(0 <= eax <= Int.max_unsigned).
          {
            functional inversion H2.
            apply Int.unsigned_range_2.
            apply Int.unsigned_range_2.
            
          }
          assert(0 <= edx <= Int.max_unsigned).
          {
            functional inversion H3.
            apply Int.unsigned_range_2.
            apply Int.unsigned_range_2.
          }
          
          assert(0 <= msr <= Int.max_unsigned).
          {
            functional inversion H1.
            apply Int.unsigned_range_2.
            apply Int.unsigned_range_2.
          }
          
          assert(0 <= val <= Int64.max_unsigned).
          {
            functional inversion H4.
            unfold val.
            unfold Int64.max_unsigned.
            change (2 ^ 32) with 4294967296.
            simpl.
            unfold Int.max_unsigned in *.
            simpl in *.
            omega.
          }
          change (2 ^ 32) with 4294967296 in *.

          assert (Hvalmodrange: 0 <= val mod 4294967296 <= Int64.max_unsigned).
          {
            split.
            apply Z_mod_range.
            omega.
            apply Z.le_trans with (m:=Int.max_unsigned).
            apply Z_mod_range.
            omega.
            omega.
          }
          
          assert (Hvalmodrange2: 0 <= val mod 4294967296 <= Int.max_unsigned).
          {
            split.
            apply Z_mod_range.
            omega.
            apply Z_mod_range.
            omega.
          }

          assert(Hvaldivrange:   0 <= val / 4294967296 <= Int64.max_unsigned).
          {
            unfold Int64.max_unsigned.
            simpl.
            unfold Int64.max_unsigned in H7.
            simpl in H7.
            xomega.
          }

          assert(Hvaldivrange2:  0 <=  val / 4294967296 <= Int.max_unsigned).
          {
            unfold Int.max_unsigned.
            simpl.
            xomega.
          }

          unfold val in *.
          esplit.

          repeat vcgen.
          instantiate (1:=Int.repr msr); rewrite Int.unsigned_repr.
          reflexivity.
          assumption.

          rewrite H2.
          instantiate (1:=Int.repr eax); rewrite Int.unsigned_repr.
          reflexivity.
          assumption.

          rewrite H3.
          instantiate (1:=Int.repr edx); rewrite Int.unsigned_repr.
          reflexivity.
          assumption.

          repeat rewrite Int.unsigned_repr.
          rewrite H4.
          reflexivity.
          functional inversion H4.
          intomega.
          assumption.
          assumption.
          assumption.
          rewrite Int.unsigned_repr.
          intomega.
          assumption.
          rewrite Int.unsigned_repr.
          omega.
          assumption.
          rewrite Int.unsigned_repr.
          intomega.
          assumption.
          repeat rewrite Int.unsigned_repr.
          apply H11.
          assumption.          
          assumption.
          rewrite Int.unsigned_repr.
          omega.
          assumption.
          rewrite Int.unsigned_repr.
          omega.
          assumption.
          rewrite Int.unsigned_repr.
          intomega.
          assumption.
          repeat rewrite Int.unsigned_repr.
          intomega.
          assumption.
          assumption.
          rewrite Int.unsigned_repr.
          omega.
          assumption.
          rewrite Int.unsigned_repr.
          omega.
          assumption.
          rewrite Int.unsigned_repr.
          intomega.
          assumption.
          rewrite H5.
          instantiate (1:=Int.repr next_eip); rewrite Int.unsigned_repr.
          reflexivity.
          assumption.
          rewrite Int.unsigned_repr.
          rewrite H7.
          reflexivity.
          assumption.
          rewrite Int.unsigned_repr.
          apply Z.le_trans with (m:=Int.max_unsigned).
          omega.
          omega.
          assumption.
        Qed.
          
      End SysHandleWrmsrBody.

      Theorem sys_handle_wrmsr_body_code_correct:
        spec_le
          (sys_handle_wrmsr ↦ trap_handle_wrmsr_spec_low)
          (〚sys_handle_wrmsr ↦ f_sys_handle_wrmsr 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_handle_wrmsr_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_handle_wrmsr)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_handle_wrmsr)))) H.
      Qed.

    End SYSHANDLEWRMSR.
    
    
    Section SYSSETTSCOFFSET.

      Let L: compatlayer (cdata RData) :=
        vmx_set_tsc_offset ↦ gensem vmx_set_tsc_offset_spec
                    ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
                    ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
                    ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysSetTscOffsetBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_set_tsc_offset *)
        Variable bvmx_set_tsc_offset: block.
        Hypothesis hvmx_set_tsc_offset1 : Genv.find_symbol ge vmx_set_tsc_offset = Some bvmx_set_tsc_offset.
        Hypothesis hvmx_set_tsc_offset2 : Genv.find_funct_ptr ge bvmx_set_tsc_offset =
                                     let arg_type := Tcons tulong Tnil in
                                     let ret_type := tvoid in
                                     let cal_conv := cc_default in
                                     let prim := vmx_set_tsc_offset in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).

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
        

        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_set_tsc_offset_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_set_tsc_offset_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_set_tsc_offset_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize max_unsigned64_val; intro muval64.
          
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1.
          functional inversion H2.
          unfold sys_set_tsc_offset_body.
          generalize (Int.unsigned_range_2 n); intro.
          generalize (Int.unsigned_range_2 n0); intro.

          rewrite <- H4 in *.
          rewrite <- H9 in *.
          unfold ofs in *.
          
          esplit.          
          repeat vcgen.

          unfold Int64.add.
          rewrite <- H9 in H3.
          rewrite <- H4 in H3.
          assumption.
        Qed.

      End SysSetTscOffsetBody.

      Theorem sys_set_tsc_offset_body_code_correct:
        spec_le
          (sys_set_tsc_offset ↦ trap_set_tsc_offset_spec_low)
          (〚sys_set_tsc_offset ↦ f_sys_set_tsc_offset 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_set_tsc_offset_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_set_tsc_offset)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_set_tsc_offset)))) H.
      Qed.

    End SYSSETTSCOFFSET.
    
    Section SYSGETTSCOFFSET.

      Let L: compatlayer (cdata RData) :=
        vmx_get_tsc_offset ↦ gensem vmx_get_tsc_offset_spec
                    ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                    ⊕ uctx_set_retval2  ↦ gensem uctx_set_retval2_spec
                    ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysGetTscOffsetBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_get_tsc_offset *)
        Variable bvmx_get_tsc_offset: block.
        Hypothesis hvmx_get_tsc_offset1 : Genv.find_symbol ge vmx_get_tsc_offset = Some bvmx_get_tsc_offset.
        Hypothesis hvmx_get_tsc_offset2 : Genv.find_funct_ptr ge bvmx_get_tsc_offset =
                                     let arg_type := Tnil in
                                     let ret_type := tulong in
                                     let cal_conv := cc_default in
                                     let prim := vmx_get_tsc_offset in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).

        (** uctx_set_retval1 *)
        Variable buctx_set_retval1: block.
        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.
        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 =
                                        Some (External (EF_external uctx_set_retval1
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).

        (** uctx_set_retval2 *)
        Variable buctx_set_retval2: block.
        Hypothesis huctx_set_retval21 : Genv.find_symbol ge uctx_set_retval2 = Some buctx_set_retval2.
        Hypothesis huctx_set_retval22 : Genv.find_funct_ptr ge buctx_set_retval2 =
                                        Some (External (EF_external uctx_set_retval2
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).


        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_get_tsc_offset_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_get_tsc_offset_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_get_tsc_offset_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize max_unsigned64_val; intro muval64.
          
          intros; subst.
          functional inversion H0; subst.
          unfold ofs1, ofs2 in *.
          unfold sys_get_tsc_offset_body.
          assert(ofsrange: 0 <= ofs <= Int64.max_unsigned).
          {
            functional inversion H1; subst.
            unfold Z64Lemma.Z64ofwords.
            apply Z64_lor_range.
            apply Z_shiftl_32_range.
            apply Int.unsigned_range_2.
            split.
            discharge_unsigned_range.
            apply Z.le_trans with (m:=Int.max_unsigned).
            apply Int.unsigned_range_2.
            omega.
          }

          assert(ofsmodrange: 0 <= ofs mod 4294967296 <= Int.max_unsigned).
          {
            apply Z_mod_range.
            omega.
          }

          esplit.
          d3 vcgen.
          repeat vcgen.
          instantiate (1:= (Int64.repr ofs)).
          rewrite Int64.unsigned_repr.
          reflexivity.
          omega.
          d3 vcgen.
          repeat vcgen.
          d3 vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          unfold Int64.divu.
          repeat vcgen.
          xomega.
          xomega.
          xomega.
          xomega.
          xomega.
          repeat vcgen.
          unfold Int64.modu.
          repeat vcgen.
        Qed.

      End SysGetTscOffsetBody.

      Theorem sys_get_tsc_offset_body_code_correct:
        spec_le
          (sys_get_tsc_offset ↦ trap_get_tsc_offset_spec_low)
          (〚sys_get_tsc_offset ↦ f_sys_get_tsc_offset 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_get_tsc_offset_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_get_tsc_offset)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_get_tsc_offset)))) H.
      Qed.

    End SYSGETTSCOFFSET.


    Section SYSSETSEG.

      Let L: compatlayer (cdata RData) :=
        vmx_set_desc ↦ gensem vmx_set_desc_spec
                    ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
                    ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
                    ⊕ uctx_arg4  ↦ gensem uctx_arg4_spec
                    ⊕ uctx_arg5  ↦ gensem uctx_arg5_spec
                    ⊕ uctx_arg6  ↦ gensem uctx_arg6_spec
                    ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysSetSegBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_set_seg *)
        Variable bvmx_set_desc: block.
        Hypothesis hvmx_set_desc1 : Genv.find_symbol ge vmx_set_desc = Some bvmx_set_desc.
        Hypothesis hvmx_set_desc2 : Genv.find_funct_ptr ge bvmx_set_desc =
                                     let arg_type := Tcons tuint (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) in
                                     let ret_type := tvoid in
                                     let cal_conv := cc_default in
                                     let prim := vmx_set_desc in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).
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

        (** uctx_arg5 *)
        Variable buctx_arg5: block.
        Hypothesis huctx_arg51 : Genv.find_symbol ge uctx_arg5 = Some buctx_arg5.
        Hypothesis huctx_arg52 : Genv.find_funct_ptr ge buctx_arg5 = 
                                 Some (External (EF_external uctx_arg5 (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** uctx_arg6 *)
        Variable buctx_arg6: block.
        Hypothesis huctx_arg61 : Genv.find_symbol ge uctx_arg6 = Some buctx_arg6.
        Hypothesis huctx_arg62 : Genv.find_funct_ptr ge buctx_arg6 =
                                 Some (External (EF_external uctx_arg6 (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).


        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_set_seg_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_set_seg_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_set_seg_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst;
          functional inversion H1; subst;
          functional inversion H2; subst;
          functional inversion H3; subst;
          functional inversion H4; subst;
          functional inversion H5; subst.
          
          functional inversion H7; subst;
          unfold sys_set_seg_body;
          esplit;
          repeat vcgen.
          
          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.

          destruct _x;
          unfold sys_set_seg_body;
          esplit;
          repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.

        Qed.

      End SysSetSegBody.

      Theorem sys_set_seg_body_code_correct:
        spec_le
          (sys_set_seg ↦ trap_set_seg_spec_low)
          (〚sys_set_seg ↦ f_sys_set_seg 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_set_seg_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             b5 Hb5fs Hb5fp
             b6 Hb6fs Hb6fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_set_seg)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_set_seg)))) H.
      Qed.

    End SYSSETSEG.

    
    Section SYSSETREG.

      Let L: compatlayer (cdata RData) :=
        vmx_set_reg ↦ gensem vmx_set_reg_spec
                    ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
                    ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
                    ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysSetRegBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_set_reg *)
        Variable bvmx_set_reg: block.
        Hypothesis hvmx_set_reg1 : Genv.find_symbol ge vmx_set_reg = Some bvmx_set_reg.
        Hypothesis hvmx_set_reg2 : Genv.find_funct_ptr ge bvmx_set_reg =
                                     let arg_type := Tcons tuint (Tcons tuint Tnil) in
                                     let ret_type := tvoid in
                                     let cal_conv := cc_default in
                                     let prim := vmx_set_reg in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).

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


        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_set_reg_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_set_reg_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_set_reg_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; subst;
          functional inversion H2; subst;
          functional inversion H4; subst;
          rewrite Int.repr_unsigned in H, H4;

          unfold sys_set_reg_body;
          esplit;
            repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.

          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.

          functional inversion H1; subst;
          functional inversion H2; subst.

          destruct _x;
          unfold sys_set_reg_body;
          esplit;
          repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.

        Qed.

      End SysSetRegBody.

      Theorem sys_set_reg_body_code_correct:
        spec_le
          (sys_set_reg ↦ trap_set_reg_spec_low)
          (〚sys_set_reg ↦ f_sys_set_reg 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_set_reg_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_set_reg)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_set_reg)))) H.
      Qed.

    End SYSSETREG.

    
    Section SYSGETREG.

      Let L: compatlayer (cdata RData) :=
        vmx_get_reg ↦ gensem vmx_get_reg_spec
                    ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
                    ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                    ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysGetRegBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_get_reg *)
        Variable bvmx_get_reg: block.
        Hypothesis hvmx_get_reg1 : Genv.find_symbol ge vmx_get_reg = Some bvmx_get_reg.
        Hypothesis hvmx_get_reg2 : Genv.find_funct_ptr ge bvmx_get_reg =
                                     let arg_type := Tcons tuint Tnil in
                                     let ret_type := tuint in
                                     let cal_conv := cc_default in
                                     let prim := vmx_get_reg in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).

        (** uctx_arg2 *)
        Variable buctx_arg2: block.
        Hypothesis huctx_arg21 : Genv.find_symbol ge uctx_arg2 = Some buctx_arg2.
        Hypothesis huctx_arg22 : Genv.find_funct_ptr ge buctx_arg2 =
                                 Some (External (EF_external uctx_arg2 (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** uctx_set_retval1 *)
        Variable buctx_set_retval1: block.
        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.
        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 =
                                        Some (External (EF_external uctx_set_retval1
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).


        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_get_reg_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_get_reg_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_get_reg_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; subst.
          functional inversion H3; subst.
          unfold sys_get_reg_body.
          esplit;
            repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.

          unfold sys_get_reg_body.
          esplit;
            repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.
          

          unfold sys_get_reg_body.
          functional inversion H1; subst.

          destruct _x.
          
          esplit;
            repeat vcgen.

          esplit; repeat vcgen.
          discharge_cmp.
          econstructor.
          discharge_cmp.
          repeat vcgen.
        Qed.

      End SysGetRegBody.

      Theorem sys_get_reg_body_code_correct:
        spec_le
          (sys_get_reg ↦ trap_get_reg_spec_low)
          (〚sys_get_reg ↦ f_sys_get_reg 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_get_reg_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_get_reg)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_get_reg)))) H.
      Qed.

    End SYSGETREG.
    
    Section SYSGETNEXTEIP.

      Let L: compatlayer (cdata RData) :=
        vmx_get_next_eip ↦ gensem vmx_get_next_eip_spec
                         ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                         ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysGetNextEipBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_get_next_eip *)
        Variable bvmx_get_next_eip: block.
        Hypothesis hvmx_get_next_eip1 : Genv.find_symbol ge vmx_get_next_eip = Some bvmx_get_next_eip.
        Hypothesis hvmx_get_next_eip2 : Genv.find_funct_ptr ge bvmx_get_next_eip =
                                     let arg_type := Tnil in
                                     let ret_type := tuint in
                                     let cal_conv := cc_default in
                                     let prim := vmx_get_next_eip in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).        


        (** uctx_set_retval1 *)
        Variable buctx_set_retval1: block.
        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.
        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 =
                                        Some (External (EF_external uctx_set_retval1
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).


        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_get_next_eip_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_get_next_eip_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_get_next_eip_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; subst.
          unfold sys_get_next_eip_body.
          esplit;
            repeat vcgen.
          instantiate (1:= (Int.repr (Int.unsigned v1 + Int.unsigned v2))).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.
          rewrite Int.unsigned_repr; try omega.
          eassumption.
        Qed.

      End SysGetNextEipBody.

      Theorem sys_get_next_eip_code_correct:
        spec_le
          (sys_get_next_eip ↦ trap_get_next_eip_spec_low)
          (〚sys_get_next_eip ↦ f_sys_get_next_eip 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_get_next_eip_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_get_next_eip)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_get_next_eip)))) H.
      Qed.

    End SYSGETNEXTEIP.

    
    Section SYSINTERCEPTINTWINDOW.

      Let L: compatlayer (cdata RData) :=
        vmx_set_intercept_intwin ↦ gensem vmx_set_intercept_intwin_spec
                                 ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
                                 ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysInterceptIntWindowBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_set_intercept_intwin *)
        Variable bvmx_set_intercept_intwin: block.
        Hypothesis hvmx_set_intercept_intwin1 : Genv.find_symbol ge vmx_set_intercept_intwin = Some bvmx_set_intercept_intwin.
        Hypothesis hvmx_set_intercept_intwin2 : Genv.find_funct_ptr ge bvmx_set_intercept_intwin =
                                     let arg_type := Tcons tint Tnil in
                                     let ret_type := Tvoid in
                                     let cal_conv := cc_default in
                                     let prim := vmx_set_intercept_intwin in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).        
        
        (** uctx_arg2 *)
        Variable buctx_arg2: block.
        Hypothesis huctx_arg21 : Genv.find_symbol ge uctx_arg2 = Some buctx_arg2.
        Hypothesis huctx_arg22 : Genv.find_funct_ptr ge buctx_arg2 =
                                 Some (External (EF_external uctx_arg2 (signature_of_type Tnil tuint cc_default))
                                                Tnil tint cc_default).

        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_intercept_int_window_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_intercept_int_window_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_set_intercept_intwin_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; subst.
          functional inversion H2; subst;
          unfold sys_set_intercept_intwin_body;
          esplit;
          repeat vcgen.
        Qed.

      End SysInterceptIntWindowBody.

      Theorem sys_intercept_int_window_code_correct:
        spec_le
          (sys_intercept_int_window ↦ trap_intercept_int_window_spec_low)
          (〚sys_intercept_int_window ↦ f_sys_set_intercept_intwin 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_intercept_int_window_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_set_intercept_intwin)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_set_intercept_intwin)))) H.
      Qed.

    End SYSINTERCEPTINTWINDOW.

    Section SYSCHECKPENDINGEVENT.

      Let L: compatlayer (cdata RData) :=
        vmx_check_pending_event ↦ gensem vmx_check_pending_event_spec
                                ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                                ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysCheckPendingEventBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_check_int_shadow *)
        Variable bvmx_check_pending_event: block.
        Hypothesis hvmx_check_pending_event1 : Genv.find_symbol ge vmx_check_pending_event = Some bvmx_check_pending_event.
        Hypothesis hvmx_check_pending_event2 : Genv.find_funct_ptr ge bvmx_check_pending_event =
                                     let arg_type := Tnil in
                                     let ret_type := tuint in
                                     let cal_conv := cc_default in
                                     let prim := vmx_check_pending_event in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).        


        (** uctx_set_retval1 *)
        Variable buctx_set_retval1: block.
        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.
        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 =
                                        Some (External (EF_external uctx_set_retval1
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).


        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_check_pending_event_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_check_pending_event_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_check_pending_event_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; subst;
          rewrite <- Int.unsigned_repr in H1 at 1;
            try omega;
            unfold sys_check_pending_event_body;
            esplit;
            repeat vcgen.
        Qed.

      End SysCheckPendingEventBody.

      Theorem sys_check_pending_event_code_correct:
        spec_le
          (sys_check_pending_event ↦ trap_check_pending_event_spec_low)
          (〚sys_check_pending_event ↦ f_sys_check_pending_event 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_check_pending_event_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_check_pending_event)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_check_pending_event)))) H.
      Qed.

    End SYSCHECKPENDINGEVENT.

    
    Section SYSCHECKINTSHADOW.

      Let L: compatlayer (cdata RData) :=
        uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                          ⊕ vmx_check_int_shadow ↦ gensem vmx_check_int_shadow_spec
                          ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysCheckIntShadowBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** vmx_check_int_shadow *)
        Variable bvmx_check_int_shadow: block.
        Hypothesis hvmx_check_int_shadow1 : Genv.find_symbol ge vmx_check_int_shadow = Some bvmx_check_int_shadow.
        Hypothesis hvmx_check_int_shadow2 : Genv.find_funct_ptr ge bvmx_check_int_shadow =
                                     let arg_type := Tnil in
                                     let ret_type := tuint in
                                     let cal_conv := cc_default in
                                     let prim := vmx_check_int_shadow in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).        


        (** uctx_set_retval1 *)
        Variable buctx_set_retval1: block.
        Hypothesis huctx_set_retval11 : Genv.find_symbol ge uctx_set_retval1 = Some buctx_set_retval1.
        Hypothesis huctx_set_retval12 : Genv.find_funct_ptr ge buctx_set_retval1 =
                                        Some (External (EF_external uctx_set_retval1
                                                                    (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                       (Tcons tint Tnil) Tvoid cc_default).


        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_check_int_shadow_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_check_int_shadow_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_check_int_shadow_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; subst;
          rewrite <- Int.unsigned_repr in H1 at 1;
            try omega;
            unfold sys_check_int_shadow_body;
            esplit;
            repeat vcgen.
        Qed.

      End SysCheckIntShadowBody.

      Theorem sys_check_int_shadow_code_correct:
        spec_le
          (sys_check_int_shadow ↦ trap_check_int_shadow_spec_low)
          (〚sys_check_int_shadow ↦ f_sys_check_int_shadow 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_check_int_shadow_body_correct
             s (Genv.globalenv p) makeglobalenv
             b1 Hb1fs Hb1fp
             b0 Hb0fs Hb0fp
             b2 Hb2fs Hb2fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_check_int_shadow)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_check_int_shadow)))) H.
      Qed.

    End SYSCHECKINTSHADOW.

    
    Section SYSINJECTEVENT.

      Let L: compatlayer (cdata RData) :=
        uctx_arg2  ↦ gensem uctx_arg2_spec
        ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
        ⊕ uctx_arg4  ↦ gensem uctx_arg4_spec
        ⊕ uctx_arg5  ↦ gensem uctx_arg5_spec
        ⊕ vmx_inject_event ↦ gensem vmx_inject_event_spec
        ⊕ uctx_set_errno  ↦ gensem  uctx_set_errno_spec.
      
      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysInjectEventBody.

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

        (** uctx_arg5 *)
        Variable buctx_arg5: block.
        Hypothesis huctx_arg51 : Genv.find_symbol ge uctx_arg5 = Some buctx_arg5.
        Hypothesis huctx_arg52 : Genv.find_funct_ptr ge buctx_arg5 = 
                                 Some (External (EF_external uctx_arg5 (signature_of_type Tnil tuint cc_default))
                                         Tnil tint cc_default).

        (** vmx_inject_event *)
        Variable bvmx_inject_event: block.
        Hypothesis hvmx_inject_event1 : Genv.find_symbol ge vmx_inject_event = Some bvmx_inject_event.
        Hypothesis hvmx_inject_event2 : Genv.find_funct_ptr ge bvmx_inject_event =
                                     let arg_type := (Tcons tuint (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))) in
                                     let ret_type := tvoid in
                                     let cal_conv := cc_default in
                                     let prim := vmx_inject_event in
                                     Some (External (EF_external
                                                       prim
                                                       (signature_of_type arg_type ret_type cal_conv))
                                                    arg_type ret_type cal_conv).        

        (** uctx_set_errno *)
        Variable buctx_set_errno: block.
        Hypothesis huctx_set_errno1 : Genv.find_symbol ge uctx_set_errno = Some buctx_set_errno.
        Hypothesis huctx_set_errno2 : Genv.find_funct_ptr ge buctx_set_errno =
                                      Some (External (EF_external uctx_set_errno
                                                                  (signature_of_type (Tcons tint Tnil) Tvoid cc_default))
                                                     (Tcons tint Tnil) Tvoid cc_default).

        Lemma sys_inject_event_body_correct: forall m d d' env le,
            env = PTree.empty _ ->
            trap_inject_event_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_inject_event_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          functional inversion H0; subst.
          functional inversion H1; subst.
          functional inversion H2; subst.
          functional inversion H3; subst.
          functional inversion H4; subst.
          unfold sys_inject_event_body.
          esplit.
          repeat vcgen.
        Qed.

      End SysInjectEventBody.

      Theorem sys_inject_event_code_correct:
        spec_le
          (sys_inject_event ↦ trap_inject_event_spec_low)
          (〚sys_inject_event ↦ f_sys_inject_event 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_inject_event_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             b5 Hb5fs Hb5fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_inject_event)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_inject_event)))) H.
      Qed.

    End SYSINJECTEVENT.*)

    
    (*
    Section SYSSENDTOCHAN.

      Let L: compatlayer (cdata RData) := uctx_arg2  ↦ gensem uctx_arg2_spec
                      ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
                      ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec
                      ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                      ⊕ sendto_chan ↦ gensem sendto_chan_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SysSendToChanBody.

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

        (** sendto_chan *)
        Variable bsendto_chan: block.
        Hypothesis hsendto_chan1 : Genv.find_symbol ge sendto_chan = Some bsendto_chan.
        Hypothesis hsendto_chan2 : Genv.find_funct_ptr ge bsendto_chan =
                                   Some (External (EF_external sendto_chan
                                                               (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default))
                                                  (Tcons tint (Tcons tint Tnil)) tint cc_default).


        Lemma sys_sendto_chan_body_correct:
          forall m d d' env le,
            env = PTree.empty _ ->
            trap_sendtochan_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_sendto_chan_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          unfold sys_sendto_chan_body.
          functional inversion H0; subst.
          functional inversion H1; subst;
          try omega.
          functional inversion H2; subst;
          try omega.
          functional inversion H3; subst;
          try omega;
          esplit;
          try rewrite Int.repr_unsigned in H4;
          repeat vcgen.
        Qed.

      End SysSendToChanBody.

      Theorem sys_sendto_chan_code_correct:
        spec_le (sys_sendto_chan ↦ trap_sendtochan_spec_low)
                (〚sys_sendto_chan ↦ f_sys_sendto_chan 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep
          (sys_sendto_chan_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp
             b1 Hb1fs Hb1fp
             b2 Hb2fs Hb2fp
             b3 Hb3fs Hb3fp
             b4 Hb4fs Hb4fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_sendto_chan)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_sendto_chan)))) H.        
      Qed.
      
    End SYSSENDTOCHAN.


    Section SYSISCHANREADY.

      Let L: compatlayer (cdata RData) :=
        uctx_set_errno  ↦ gensem uctx_set_errno_spec
                        ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
                        ⊕ is_chan_ready ↦ gensem is_chan_ready_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section SysIsChanReadyBody.
        
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

        (** is_chan_ready *)
        Variable bis_chan_ready: block.
        Hypothesis his_chan_ready1 : Genv.find_symbol ge is_chan_ready = Some bis_chan_ready.
        Hypothesis his_chan_ready2 : Genv.find_funct_ptr ge bis_chan_ready =
                                     Some (External (EF_external is_chan_ready
                                                                 (signature_of_type Tnil tint cc_default))
                                                    Tnil tint cc_default).


        Lemma sys_is_chan_ready_body_correct:
          forall m d d' env le,
            env = PTree.empty _ ->
            trap_ischanready_spec d = Some d' ->
            exists le',
              exec_stmt ge env le ((m, d): mem) sys_is_chan_ready_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          functional inversion H0; subst.
          unfold sys_is_chan_ready_body.
          functional inversion H1; subst;
          rewrite <- Int.unsigned_repr in H1 at 1;
          try omega;
          esplit;
          repeat vcgen.
        Qed.

      End SysIsChanReadyBody.

      Theorem sys_is_chan_ready_code_correct:
        spec_le (sys_is_chan_ready ↦ trap_ischanready_spec_low)
                (〚sys_is_chan_ready ↦ f_sys_is_chan_ready 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        generalize H; intro inv.
        fbigstep
          (sys_is_chan_ready_body_correct
             s (Genv.globalenv p) makeglobalenv
             b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp
             m'0 labd labd0
             (PTree.empty _) 
             (bind_parameter_temps' (fn_params f_sys_is_chan_ready)
                                    nil
                                    (create_undef_temps (fn_temps f_sys_is_chan_ready)))) H.
      Qed.

    End SYSISCHANREADY.
*)
    
  End WithPrimitives.

End TTRAPARGCODE.
