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
Require Import LinkTemplate.
Require Import PIPCIntro.
Require Import IPCIntroGen.
Require Import IPCIntroGenLinkSource.
Require Import PThread.
Require Import PThreadCSource.
Require Import PThreadCode.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma init_correct:
    init_correct_type PIPCIntro_module pthread pipcintro.
  Proof.
    init_correct.
    - intros. 
      inv_monad' H0.
      generalize (make_program_make_globalenv _ _ _ _ H1).
      intros HP. pose proof HP as HP'.
      eapply make_globalenv_stencil_matches in HP'.
      inv_make_globalenv HP.
      rewrite  (stencil_matches_symbols _ _ HP') in *.
      inv HP'.

        * econstructor; eauto.
          specialize (Genv.init_mem_characterization _ _ Hbvi H3); eauto.
          unfold Genv.perm_globvar; simpl; intros [Hperm _].
          assert(HVALID: forall ofs, 0<= ofs < num_chan * 3 ->
                                     Mem.valid_access m2 Mint32 b (ofs * 4) Writable).
          {
            intros; split; simpl.
            change (Z.max 768 0) with 768 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. omega.
            apply Zdivide_mult_r. apply Zdivide_refl.
          }
          assert(HEX: forall ofs,  0<= ofs < num_chan * 3 ->
                                   (exists v, Mem.load Mint32 m2 b (ofs * 4) = Some v)).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID; trivial.
            constructor.
          }
          intros.
          assert (HOS1: 0<= ofs * 3 < 64 * 3) by omega.
          assert (HOS2: 0<= ofs * 3 + 1 < 64 * 3) by omega.
          assert (HOS3: 0<= ofs * 3 + 2 < 64 * 3) by omega.
          destruct (HEX _ HOS1) as [v1 HEX1].
          destruct (HEX _ HOS2) as [v2 HEX2].
          destruct (HEX _ HOS3) as [v3 HEX3].
          pose proof (HVALID _ HOS1) as HV1.
          pose proof (HVALID _ HOS2) as HV2.
          pose proof (HVALID _ HOS3) as HV3.
          replace (ofs * 3 * 4) with (ofs * 12) in * by omega.
          replace ((ofs * 3 + 1) * 4) with (ofs * 12 + 4) in * by omega.
          replace ((ofs * 3 + 2) * 4) with (ofs * 12 + 8) in * by omega.
          refine_split'; eauto.
          rewrite ZMap.gi. constructor.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type PIPCIntro_module pthread pipcintro.
  Proof.
    link_correct_aux.
    - link_cfunction
        get_sync_chan_to_spec_ref
        PTHREADCODE.get_sync_chan_to_code_correct.
    - link_cfunction
        get_sync_chan_paddr_spec_ref
        PTHREADCODE.get_sync_chan_paddr_code_correct.
    - link_cfunction
        get_sync_chan_count_spec_ref
        PTHREADCODE.get_sync_chan_count_code_correct.
    - link_cfunction
        set_sync_chan_to_spec_ref
        PTHREADCODE.set_sync_chan_to_code_correct.
    - link_cfunction
        set_sync_chan_paddr_spec_ref
        PTHREADCODE.set_sync_chan_paddr_code_correct.
    - link_cfunction
        set_sync_chan_count_spec_ref
        PTHREADCODE.set_sync_chan_count_code_correct.
    - link_cfunction
        init_sync_chan_spec_ref
        PTHREADCODE.init_sync_chan_code_correct.
    - link_cfunction
        get_kernel_pa_spec_ref
        PTHREADCODE.get_kernel_pa_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type PIPCIntro_module pthread pipcintro.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type PIPCIntro_module pthread pipcintro.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type PIPCIntro_module pthread pipcintro.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type PIPCIntro_module pthread pipcintro.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
