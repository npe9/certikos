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
Require Import MShareIntro.
Require Import ShareIntroGen.
Require Import ShareIntroGenLinkSource.
Require Import MPTNew.
Require Import MPTNewCSource.
Require Import MPTNewCode.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma make_program_find_symbol (CTXT md : module)(m : mem) s :
      (p <- make_program s (CTXT ⊕ (md
              ⊕ SHRDMEMPOOL_LOC ↦ smspool_loc_type) ⊕ ∅) (mptnew ⊕ L64);
       ret (Genv.init_mem p) = OK (Some m))
      -> exists b, find_symbol s SHRDMEMPOOL_LOC = Some b /\
         forall pid1 pid2, 0 <= pid1 < num_proc -> 0 <= pid2 < num_proc ->
           Mem.valid_access m Mint32 b (pid1 * 768 + pid2 * 12) Writable /\
           Mem.valid_access m Mint32 b (pid1 * 768 + pid2 * 12 + 4) Writable /\
           Mem.valid_access m Mint32 b (pid1 * 768 + pid2 * 12 + 8) Writable.
  Proof.
    intros mkprog; inv_monad' mkprog.
    assert (mkgenv := make_program_make_globalenv _ _ _ _ mkprog0).
    pose proof mkgenv as mkgenv'.
    eapply make_globalenv_stencil_matches in mkgenv'.
    inv_make_globalenv mkgenv. subst.
    rewrite (stencil_matches_symbols _ _ mkgenv') in *. inv mkgenv'.
    eexists; split; try eassumption.

    specialize (Genv.init_mem_characterization _ _ Hbvi H0); eauto.
    unfold Genv.perm_globvar; simpl; intros [Hperm _].
    change (Z.max 49152 0) with 49152 in Hperm.
    intros; repeat split.
    - unfold Mem.range_perm; intros; apply Hperm.
      simpl in H2.
      omega.
    - replace (pid1 * 768 + pid2 * 12) with ((pid1 * 192 + pid2 * 3) * 4) by omega.
      eexists; reflexivity.
    - unfold Mem.range_perm; intros; apply Hperm.
      simpl in H2.
      omega.
    - replace (pid1 * 768 + pid2 * 12 + 4) with ((pid1 * 192 + pid2 * 3 + 1) * 4) by omega.
      eexists; reflexivity.
    - unfold Mem.range_perm; intros; apply Hperm.
      simpl in H2.
      omega.
    - replace (pid1 * 768 + pid2 * 12 + 8) with ((pid1 * 192 + pid2 * 3 + 2) * 4) by omega.
      eexists; reflexivity.
  Qed.

  Lemma init_correct:
    init_correct_type MShareIntro_module mptnew mshareintro.
  Proof.
    init_correct.

    exploit make_program_find_symbol; eauto.
    intros (b & find_symbol_SHRDMEMPOOL_LOC & access).
    econstructor; try eassumption; intros.
    rewrite 2 ZMap.gi.

    specialize (access _ _ H1 H2).
    destruct access as [ ? [] ].
    assert (readable : Mem.valid_access m2 Mint32 b (pid1 * 768 + pid2 * 12) Readable).
    { eapply Mem.valid_access_implies; try eassumption; constructor. }
    assert (readable4 : Mem.valid_access m2 Mint32 b (pid1 * 768 + pid2 * 12 + 4) Readable).
    { eapply Mem.valid_access_implies; try eassumption; constructor. }
    assert (readable8 : Mem.valid_access m2 Mint32 b (pid1 * 768 + pid2 * 12 + 8) Readable).
    { eapply Mem.valid_access_implies; try eassumption; constructor. }

    destruct (Mem.valid_access_load _ _ _ _ readable) as [ v load ].
    destruct (Mem.valid_access_load _ _ _ _ readable4) as [ v4 load4 ].
    destruct (Mem.valid_access_load _ _ _ _ readable8) as [ v8 load8 ].
    exists v, v4, v8; repeat (split; [ eassumption |]).
    constructor.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type MShareIntro_module mptnew mshareintro.
  Proof.
    link_correct_aux.
    - link_cfunction
        clear_shared_mem_spec_ref
        MSHAREINTROCODE.clear_shared_mem_code_correct.
    - link_cfunction
        get_shared_mem_state_spec_ref
        MSHAREINTROCODE.get_shared_mem_state_code_correct.
    - link_cfunction
        get_shared_mem_seen_spec_ref
        MSHAREINTROCODE.get_shared_mem_seen_code_correct.
    - link_cfunction
        get_shared_mem_loc_spec_ref
        MSHAREINTROCODE.get_shared_mem_loc_code_correct.
    - link_cfunction
        set_shared_mem_state_spec_ref
        MSHAREINTROCODE.set_shared_mem_state_code_correct.
    - link_cfunction
        set_shared_mem_seen_spec_ref
        MSHAREINTROCODE.set_shared_mem_seen_code_correct.
    - link_cfunction
        set_shared_mem_loc_spec_ref
        MSHAREINTROCODE.set_shared_mem_loc_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type MShareIntro_module mptnew mshareintro.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type MShareIntro_module mptnew mshareintro.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type MShareIntro_module mptnew mshareintro.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type MShareIntro_module mptnew mshareintro.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
