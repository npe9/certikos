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
Require Import MPTIntro.
Require Import PTIntroGen.
Require Import PTIntroGenLinkSource.
Require Import MContainer.
Require Import MContainerCSource.
Require Import MContainerCode.
Require Import PTIntroGenAsm.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma make_program_find_symbol (CTXT md : module)(m : mem) s :
      (p <- make_program s (CTXT ⊕ ((md
              ⊕ PTPool_LOC ↦ CDataTypes.ptpool_loc_type)
              ⊕ IDPMap_LOC ↦ CDataTypes.idpmap_loc_type) ⊕ ∅) (mcontainer ⊕ L64);
       ret (Genv.init_mem p) = OK (Some m))
      -> (exists b, find_symbol s PTPool_LOC = Some b /\
          forall n i, 0 <= n < num_proc -> 0 <= i <= PDX Int.max_unsigned ->
                      Mem.valid_access m Mint32 b (n * 4096 + i * 4) Writable) /\
         (exists b, find_symbol s IDPMap_LOC = Some b /\
          forall i j, 0 <= i <= PDX Int.max_unsigned -> 0 <= j <= PTX Int.max_unsigned ->
                      Mem.valid_access m Mint32 b (i * 4096 + j * 4) Writable).
  Proof.
    intros mkprog; inv_monad' mkprog.
    assert (mkgenv := make_program_make_globalenv _ _ _ _ mkprog0).
    pose proof mkgenv as mkgenv'.
    eapply make_globalenv_stencil_matches in mkgenv'.
    inv_make_globalenv mkgenv. subst.
    rewrite (stencil_matches_symbols _ _ mkgenv') in *. inv mkgenv'.
    split; eexists; split; try eassumption.
    - specialize (Genv.init_mem_characterization _ _ Hbvi H0); eauto.
      unfold Genv.perm_globvar; simpl; intros [Hperm _].
      change (Z.max 262144 0) with 262144 in Hperm.
      intros; split.
      + unfold Mem.range_perm; intros; apply Hperm.
        simpl in H2.
        change (PDX Int.max_unsigned) with 1023 in H1.
        omega.
      + replace (n * 4096 + i * 4) with ((n * 1024 + i) * 4) by omega.
        eexists; reflexivity.
    - specialize (Genv.init_mem_characterization _ _ Hb0vi H0); eauto.
      unfold Genv.perm_globvar; simpl; intros [Hperm _].
      Print CDataTypes.idpmap_loc_type.
      change (Z.max 4194304 0) with 4194304 in Hperm.
      intros; split.
      + unfold Mem.range_perm; intros; apply Hperm.
        simpl in H2.
        change (PDX Int.max_unsigned) with 1023 in H.
        change (PTX Int.max_unsigned) with 1023 in H1.
        omega.
      + replace (i * 4096 + j * 4) with ((i * 1024 + j) * 4) by omega.
        eexists; reflexivity.
  Qed.

  Lemma init_correct:
    init_correct_type MPTIntro_module mcontainer mptintro.
  Proof.
    init_correct.
    - intro.
      rewrite !ZMap.gi.
      constructor.
    - constructor.
    - constructor.
      intros.
      exists Vundef.
      + unfold FlatMem.load.
        rewrite FlatMem.getN_emptymem.
        split.
        * reflexivity.
        * rewrite !ZMap.gi in H3.
          inversion H3.
    - exploit make_program_find_symbol; eauto.
      intros [ (b & find_symbol_PTPool_LOC & access) _ ].
      econstructor; try eassumption.
      constructor; intros.
      rewrite 2 ZMap.gi.

      assert (readable : Mem.valid_access m2 Mint32 b (n * 4096 + i * 4) Readable).
      { eapply Mem.valid_access_implies; eauto; constructor. }

      exploit Mem.valid_access_load; eauto.
      intros [ v load ].
      exists v; split; [| split ]; eauto; constructor.
    - exploit make_program_find_symbol; eauto.
      intros [ _ (b & find_symbol_IDPMap_LOC & access) ].
      econstructor; try eassumption; intros.
      rewrite 2 ZMap.gi.

      assert (readable : Mem.valid_access m2 Mint32 b (i * 4096 + j * 4) Readable).
      { eapply Mem.valid_access_implies; eauto; constructor. }

      exploit Mem.valid_access_load; eauto.
      intros [ v load ].
      exists v; split; [| split ]; eauto; constructor.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type MPTIntro_module mcontainer mptintro.
  Proof.
    link_correct_aux.
    - link_cfunction setPT_spec_ref MCONTAINERCODE.set_pt_code_correct.
    - link_cfunction getPDE_spec_ref MCONTAINERCODE.get_pde_code_correct.
    - link_cfunction setPDE_spec_ref MCONTAINERCODE.set_pde_code_correct.
    - link_cfunction rmvPDE_spec_ref MCONTAINERCODE.rmv_pde_code_correct.
    - link_cfunction setPDEU_spec_ref MCONTAINERCODE.set_pdeu_code_correct.
    - link_cfunction getPTE_spec_ref MCONTAINERCODE.get_pte_code_correct.
    - link_cfunction setPTE_spec_ref MCONTAINERCODE.set_pte_code_correct.
    - link_cfunction rmvPTE_spec_ref MCONTAINERCODE.rmv_pte_code_correct.
    - link_cfunction setIDPTE_spec_ref MCONTAINERCODE.set_idpte_code_correct.
    - link_asmfunction pt_in_spec_ref pt_in_code_correct.
    - link_asmfunction pt_out_spec_ref pt_out_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type MPTIntro_module mcontainer mptintro.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type MPTIntro_module mcontainer mptintro.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type MPTIntro_module mcontainer mptintro.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type MPTIntro_module mcontainer mptintro.
  Proof.
    make_program_exists link_correct_aux.
  Qed.

End WITHCOMPCERTIKOS.
