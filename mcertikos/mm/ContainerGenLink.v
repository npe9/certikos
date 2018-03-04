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
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import MemoryX.
Require Import MemWithData.
Require Import EventsX.
Require Import Globalenvs.
Require Import LAsm.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import MALT.
Require Import MContainer.
Require Import ZArith.Zwf.
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
Require Import I64Layer.
Require Import ContainerGen.
Require Import MALTCode.
Require Import ContainerGenSpec.
Require Import LinkTactic.
Require Import MALTCSource.
Require Import ContainerGenLinkSource.
Require Import CompCertiKOSproof.
Require Import AbstractDataType.

Require Import FlatMemory.
Require Import Decision.
Require Import LAsmModuleSem.
Require Import Soundness.
Require Import CompatExternalCalls.
Require Import CommonTactic.
Require Import LayerCalculusLemma.
Require Import Behavior.

Notation HDATA := RData.
Notation LDATA := RData.

Notation HDATAOps := (cdata (cdata_ops := mcontainer_data_ops) HDATA).
Notation LDATAOps := (cdata (cdata_ops := malt_data_ops) LDATA).

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  Record MContainer_impl_inverted (M: module) : Prop:=
    {
      MCONTAINER_init: module;
      MCONTAINER_get_parent: module;
      MCONTAINER_get_nchildren: module;
      MCONTAINER_get_quota: module;
      MCONTAINER_get_usage: module;
      MCONTAINER_can_consume: module;
      MCONTAINER_split: module;
      MCONTAINER_alloc: module;
      MCONTAINER_init_transf: 
        CompCertiKOS.transf_module (container_init ↦ f_container_init) = ret MCONTAINER_init;
      MCONTAINER_get_parent_transf: 
        CompCertiKOS.transf_module (container_get_parent ↦ f_container_get_parent) = ret MCONTAINER_get_parent;
      MCONTAINER_get_nchildren_transf: 
        CompCertiKOS.transf_module (container_get_nchildren ↦ f_container_get_nchildren) = ret MCONTAINER_get_nchildren;
      MCONTAINER_get_quota_transf:
        CompCertiKOS.transf_module (container_get_quota ↦ f_container_get_quota) = ret MCONTAINER_get_quota;
      MCONTAINER_get_usage_transf:
        CompCertiKOS.transf_module (container_get_usage ↦ f_container_get_usage) = ret MCONTAINER_get_usage;
      MCONTAINER_can_consume_transf: 
        CompCertiKOS.transf_module (container_can_consume ↦ f_container_can_consume) = ret MCONTAINER_can_consume;
      MCONTAINER_split_transf:
        CompCertiKOS.transf_module (container_split ↦ f_container_split) = ret MCONTAINER_split;
      MCONTAINER_alloc_transf:
        CompCertiKOS.transf_module (container_alloc ↦ f_container_alloc) = ret MCONTAINER_alloc;
      MCONTAINER_M: M = ((MCONTAINER_init ⊕ MCONTAINER_get_parent 
                                        ⊕ MCONTAINER_get_nchildren ⊕ MCONTAINER_get_quota 
                                        ⊕ MCONTAINER_get_usage ⊕ MCONTAINER_can_consume
                                        ⊕ MCONTAINER_split ⊕ MCONTAINER_alloc) ⊕ 
                         AC_LOC ↦ container_loc_type) ⊕ ∅;
      MCONTAINER_Mok: LayerOK (〚M 〛 (malt ⊕ L64) ⊕ malt ⊕ L64);
      MCONTAINER_Lok: LayerOK (〚MCONTAINER_init ⊕ MCONTAINER_get_parent ⊕
                                 MCONTAINER_get_nchildren ⊕
                                 MCONTAINER_get_quota ⊕ MCONTAINER_get_usage ⊕
                                 MCONTAINER_can_consume ⊕ MCONTAINER_split ⊕
                                 MCONTAINER_alloc 〛((malt ⊕ L64) ⊕ AC_LOC ↦ container_loc_type)
                                   ⊕ ((malt ⊕ L64) ⊕ AC_LOC ↦ container_loc_type))
    }.

  Lemma module_impl_imply:
    forall M, MContainer_impl = OK M -> MContainer_impl_inverted M.
  Proof.
    unfold MContainer_impl. intros M HM.
    inv_monad' HM.
    inv_monad' HM0.
    inv_monad' HM1.
    econstructor; try eassumption; reflexivity.
  Qed.

  Let L1 : compatlayer LDATAOps := 
               mem_init ↦ gensem mem_init_spec
             ⊕ get_nps ↦ gensem get_nps_spec
             ⊕ is_norm ↦ gensem is_at_norm_spec ⊕ at_get ↦ gensem get_at_u_spec.
  Lemma L1_le: L1 ≤ malt.
  Proof.
    sim_oplus.
  Qed.

  Lemma container_init_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_init ↦ f_container_init),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_init ↦ f_container_init) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_init ↦ gensem container_init_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_init_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_init_code_correct.
    - apply oplus_monotonic; [ reflexivity | exact L1_le ].
  Qed.

  Lemma container_get_parent_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_get_parent ↦ f_container_get_parent),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_get_parent ↦ f_container_get_parent) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_get_parent ↦ gensem container_get_parent_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_get_parent_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_get_parent_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma container_get_nchildren_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_get_nchildren ↦ f_container_get_nchildren),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_get_nchildren ↦ f_container_get_nchildren) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_get_nchildren ↦ gensem container_get_nchildren_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_get_nchildren_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_get_nchildren_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma container_get_quota_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_get_quota ↦ f_container_get_quota),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_get_quota ↦ f_container_get_quota) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_get_quota ↦ gensem container_get_quota_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_get_quota_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_get_quota_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma container_get_usage_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_get_usage ↦ f_container_get_usage),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_get_usage ↦ f_container_get_usage) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_get_usage ↦ gensem container_get_usage_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_get_usage_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_get_usage_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma container_can_consume_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_can_consume ↦ f_container_can_consume),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_can_consume ↦ f_container_can_consume) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_can_consume ↦ gensem container_can_consume_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_can_consume_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_can_consume_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma container_split_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_split ↦ f_container_split),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_split ↦ f_container_split) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_split ↦ gensem container_split_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_split_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_split_code_correct.
    - apply left_upper_bound.
  Qed.

  Let Lalloc : compatlayer LDATAOps := 
    palloc ↦ gensem palloc'_spec.
  Lemma Lalloc_le: Lalloc ≤ malt.
  Proof.
    sim_oplus.
  Qed.

  Lemma container_alloc_correct:
    forall COMPILABLE: LayerCompilable ((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64),
    forall MOK: ModuleOK (container_alloc ↦ f_container_alloc),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (container_alloc ↦ f_container_alloc) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (container_alloc ↦ gensem container_alloc_spec)
             (〚 M2 〛((AC_LOC ↦ container_loc_type ⊕ malt) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply container_alloc_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply MALTCODE.container_alloc_code_correct.
    - apply oplus_monotonic; [ reflexivity | exact Lalloc_le ].
  Qed.

  Lemma link_correct_aux:
    forall M, MContainer_impl = OK M ->
              malt ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : mcontainer ⊕ L64.
  Proof.   
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold mcontainer, mcontainer_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      eapply transfer_variable.
      apply MCONTAINER_Lok.
      eapply (LayerOK_impl_subst MCONTAINER_Mok0).
      apply module_le_left.
      reflexivity.

      layer_link_split_tac.
      - apply container_init_correct; code_correct_tac.
      - apply container_get_parent_correct; code_correct_tac.
      - apply container_get_nchildren_correct; code_correct_tac.
      - apply container_get_quota_correct; code_correct_tac.
      - apply container_get_usage_correct; code_correct_tac.
      - apply container_can_consume_correct; code_correct_tac.
      - apply container_split_correct; code_correct_tac.
      - apply container_alloc_correct; code_correct_tac.
    }
    {
      eapply layer_link_new_glbl_both.
      apply oplus_sim_monotonic.
      apply passthrough_correct.
      apply L64_auto_sim.
    }
  Qed.

  (* Modification to init_mem_characterization.
     Initial data created by Init_space should contain zeros.
     Move this section to a separate file at some point. *)

  Section INITMEM.

  Lemma init_data_list_size_pos : 
    forall il, Genv.init_data_list_size il >= 0.
  Proof.
    induction il; simpl; try omega.
    assert (H:= Genv.init_data_size_pos a); omega.
  Qed.

  Fixpoint load_init_space_zeros (m: mem) (b: block) (p: Z) (il: list AST.init_data) {struct il} : Prop :=
  match il with
  | Init_space n :: il' => 
      (forall i, 0 <= i < n -> Mem.load Mint8unsigned m b (p + i) = Some Vzero)
      /\ load_init_space_zeros m b (p + Zmax n 0) il'
  | _ => True
  end.

  Remark load_init_space_zeros_invariant:
    forall m m' b,
      (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) ->
      forall il p,
        load_init_space_zeros m b p il -> load_init_space_zeros m' b p il.
  Proof.
    induction il; intro p; simpl; auto.
    destruct a; auto.
    intro Hm; split.
    intros i Hi; rewrite H.
    apply (proj1 Hm); auto.
    apply (IHil _ (proj2 Hm)).
  Qed.

  Lemma store_zeros_charact : 
    forall m b p n m',
      store_zeros m b p n = Some m' -> 
      forall i, p <= i < p+n -> Mem.load Mint8unsigned m' b i = Some Vzero.
  Proof.
    intros m b p n m' Hsz i Hi.
    functional induction (store_zeros m b p n); try omega.
    assert (Hcases: i = p \/ p+1 <= i < p+1+(n-1)) by omega.
    destruct Hcases as [Hi'|Hi']; subst; auto.
    assert (Hsz':= Genv.store_zeros_outside).
    rewrite (Hsz' _ _ _ _ _ Hsz).
    rewrite (Mem.load_store_same _ _ _ _ _ _ e0); auto.
    right; simpl; omega.
    inv Hsz.
  Qed.

  Lemma init_space_zeros_charact {F V} :
    forall ge b il m p m',
      (forall i, p <= i < p + Genv.init_data_list_size il -> 
                 Mem.load Mint8unsigned m b i = Some Vzero) ->
      Genv.store_init_data_list(F:=F)(V:=V) ge m b p il = Some m' ->
      load_init_space_zeros m' b p il.
  Proof.
    induction il; intros m p m' Hz Hstore; simpl; auto.
    destruct a; simpl; auto.
    simpl in Hstore; split.
    intros i Hi; assert (Hout:= Genv.store_init_data_list_outside).
    assert (Hzpos: Z.max z 0 >= z).
    unfold Z.max; destruct z; simpl; try omega.
    assert (Hneg:= Zlt_neg_0 p0); omega.
    rewrite (Hout _ _ _ _ _ _ _ _ Hstore).
    apply Hz; simpl.
    assert (H2:= init_data_list_size_pos il); omega.
    simpl; right; omega.
    apply (IHil m); auto.
    intros i Hi; apply Hz; simpl.
    split; try omega.
    unfold Z.max in Hi; destruct z; simpl in Hi; try omega.
    assert (Hpos:= Zle_0_pos p0); omega.
  Qed.

  Definition variables_initialized' {F V} (ge g: Genv.t F V) (m: mem) :=
    forall b gv,
      Genv.find_var_info g b = Some gv ->
      Mem.range_perm m b 0 (Genv.init_data_list_size gv.(gvar_init)) Cur (Genv.perm_globvar gv)
      /\ (forall ofs k p, Mem.perm m b ofs k p ->
            0 <= ofs < Genv.init_data_list_size gv.(gvar_init) /\ perm_order (Genv.perm_globvar gv) p)
      /\ (gv.(gvar_volatile) = false -> Genv.load_store_init_data ge m b 0 gv.(gvar_init) )
      /\ (gv.(gvar_volatile) = false -> load_init_space_zeros m b 0 gv.(gvar_init)).

  Lemma alloc_global_initialized' {F V} :
    forall ge ge' m id g m',
      Genv.genv_next(F:=F)(V:=V) ge' = Mem.nextblock m ->
      Genv.alloc_global ge m (id, g) = Some m' ->
      variables_initialized' ge ge' m ->
      Genv.functions_initialized ge' m ->
      variables_initialized' ge (Genv.add_global ge' (id, g)) m'
      /\ Genv.functions_initialized (Genv.add_global ge' (id, g)) m'
      /\ Genv.genv_next (Genv.add_global ge' (id, g)) = Mem.nextblock m'.
  Proof.
    intros. 
    exploit Genv.alloc_global_nextblock; eauto. intros NB. split.
    (* variables-initialized *)
    destruct g as [[f|v]|].
    (* function *)
    red; intros. unfold Genv.find_var_info in H3. simpl in H3. 
    exploit H1; eauto. intros [A [B [C Hisz]]].
    assert (D: Mem.valid_block m b). 
    red. exploit Genv.genv_vars_range; eauto. rewrite H; auto.
    split. red; intros. erewrite <- Genv.alloc_global_perm; eauto. 
    split. intros. eapply B. erewrite Genv.alloc_global_perm; eauto. 
    split. intros. apply Genv.load_store_init_data_invariant with m; auto. 
    intros. eapply Genv.load_alloc_global; eauto. 
    intros. apply load_init_space_zeros_invariant with m; auto. 
    intros. eapply Genv.load_alloc_global; eauto. 
    (* variable *)
    red; intros. unfold Genv.find_var_info in H3. simpl in H3. rewrite PTree.gsspec in H3.
    destruct (peq b (Genv.genv_next ge')).
    (* same *)
    inv H3. simpl in H0.
    set (init := gvar_init gv) in *.
    set (sz := Genv.init_data_list_size init) in *.
    destruct (Mem.alloc m 0 sz) as [m1 b'] eqn:?.
    destruct (store_zeros m1 b' 0 sz) as [m2|] eqn:?; try discriminate.
    destruct (Genv.store_init_data_list ge m2 b' 0 init) as [m3|] eqn:?; try discriminate.
    exploit Mem.alloc_result; eauto. intro RES. 
    replace (Genv.genv_next ge') with b' by congruence.
    split. red; intros. eapply Mem.perm_drop_1; eauto.
    split. intros.
    assert (0 <= ofs < sz).
    eapply Mem.perm_alloc_3; eauto.
    erewrite Genv.store_zeros_perm; [idtac|eauto].
    erewrite Genv.store_init_data_list_perm; [idtac|eauto]. 
    eapply Mem.perm_drop_4; eauto.
    split. auto. eapply Mem.perm_drop_2; eauto.
    split. intros. apply Genv.load_store_init_data_invariant with m3. 
    intros. eapply Mem.load_drop; eauto. 
    right; right; right. unfold Genv.perm_globvar. rewrite H3. 
    destruct (gvar_readonly gv); auto with mem.
    eapply Genv.store_init_data_list_charact; eauto.
    intros. apply load_init_space_zeros_invariant with m3. 
    intros. eapply Mem.load_drop; eauto. 
    right; right; right. unfold Genv.perm_globvar. rewrite H3. 
    destruct (gvar_readonly gv); auto with mem.
    eapply init_space_zeros_charact; eauto.
    eapply store_zeros_charact; eauto.
    (* older var *)
    exploit H1; eauto. intros [A [B [C Hisz]]].
    assert (D: Mem.valid_block m b). 
    red. exploit Genv.genv_vars_range; eauto. rewrite H; auto. 
    split. red; intros. erewrite <- Genv.alloc_global_perm; eauto. 
    split. intros. eapply B. erewrite Genv.alloc_global_perm; eauto. 
    split. intros. apply Genv.load_store_init_data_invariant with m; auto. 
    intros. eapply Genv.load_alloc_global; eauto.
    intros. apply load_init_space_zeros_invariant with m; auto. 
    intros. eapply Genv.load_alloc_global; eauto.
    (** [CompCertX:test-compcert-void-symbols] case none *)
    red; intros. unfold Genv.find_var_info in H3. simpl in H3. 
    exploit H1; eauto. intros [A [B [C Hisz]]].
    assert (D: Mem.valid_block m b). 
    red. exploit Genv.genv_vars_range; eauto. rewrite H; auto.
    split. red; intros. erewrite <- Genv.alloc_global_perm; eauto. 
    split. intros. eapply B. erewrite Genv.alloc_global_perm; eauto. 
    split. intros. apply Genv.load_store_init_data_invariant with m; auto. 
    intros. eapply Genv.load_alloc_global; eauto. 
    intros. apply load_init_space_zeros_invariant with m; auto. 
    intros. eapply Genv.load_alloc_global; eauto.
    (* functions-initialized *)
    split. destruct g as [[f|v]|].
    (* function *)
    red; intros. unfold Genv.find_funct_ptr in H3. simpl in H3. rewrite PTree.gsspec in H3.
    destruct (peq b (Genv.genv_next ge')).
    (* same *)
    inv H3. simpl in H0. 
    destruct (Mem.alloc m 0 1) as [m1 b'] eqn:?. 
    exploit Mem.alloc_result; eauto. intro RES. 
    replace (Genv.genv_next ge') with b' by congruence.
    split. eapply Mem.perm_drop_1; eauto. omega. 
    intros.
    assert (0 <= ofs < 1).
    eapply Mem.perm_alloc_3; eauto.
    eapply Mem.perm_drop_4; eauto.
    split. omega. eapply Mem.perm_drop_2; eauto.
    (* older function *)
    exploit H2; eauto. intros [A B].
    assert (D: Mem.valid_block m b). 
    red. exploit Genv.genv_funs_range; eauto. rewrite H; auto.
    split. erewrite <- Genv.alloc_global_perm; eauto. 
    intros. eapply B. erewrite Genv.alloc_global_perm; eauto.
    (* variables *)
    red; intros. unfold Genv.find_funct_ptr in H3. simpl in H3. 
    exploit H2; eauto. intros [A B].
    assert (D: Mem.valid_block m b). 
    red. exploit Genv.genv_funs_range; eauto. rewrite H; auto.
    split. erewrite <- Genv.alloc_global_perm; eauto. 
    intros. eapply B. erewrite Genv.alloc_global_perm; eauto.
    (** [CompCertX:test-compcert-void-symbols] case none *)
    red; intros. unfold Genv.find_funct_ptr in H3. simpl in H3. 
    exploit H2; eauto. intros [A B].
    assert (D: Mem.valid_block m b). 
    red. exploit Genv.genv_funs_range; eauto. rewrite H; auto.
    split. erewrite <- Genv.alloc_global_perm; eauto. 
    intros. eapply B. erewrite Genv.alloc_global_perm; eauto.
    (* nextblock *)
    rewrite NB. simpl. rewrite H. auto.
  Qed.

  Lemma alloc_globals_initialized' {F V} :
    forall (ge : Genv.t F V) gl ge' m m',
      Genv.genv_next ge' = Mem.nextblock m ->
      Genv.alloc_globals ge m gl = Some m' ->
      variables_initialized' ge ge' m ->
      Genv.functions_initialized ge' m ->
      variables_initialized' ge (Genv.add_globals ge' gl) m' /\ 
      Genv.functions_initialized (Genv.add_globals ge' gl) m'.
  Proof.
    induction gl; simpl; intros.
    inv H0; auto.
    destruct a as [id g]. destruct (Genv.alloc_global ge m (id, g)) as [m1|] eqn:?; try discriminate.
    exploit (alloc_global_initialized'(F:=F)(V:=V)); eauto. intros [P [Q R]].
    eapply IHgl; eauto. 
  Qed.

  Theorem init_mem_characterization' {F V} :
    forall p b gv m,
      Genv.find_var_info (Genv.globalenv(F:=F)(V:=V) p) b = Some gv ->
      Genv.init_mem p = Some m ->
      Mem.range_perm m b 0 (Genv.init_data_list_size gv.(gvar_init)) Cur (Genv.perm_globvar gv)
      /\ (forall ofs k p, Mem.perm m b ofs k p ->
            0 <= ofs < Genv.init_data_list_size gv.(gvar_init) /\ perm_order (Genv.perm_globvar gv) p)
      /\ (gv.(gvar_volatile) = false -> Genv.load_store_init_data (Genv.globalenv p) m b 0 gv.(gvar_init))
      /\ (gv.(gvar_volatile) = false -> load_init_space_zeros m b 0 gv.(gvar_init)).
  Proof.
    intros. eapply alloc_globals_initialized'; eauto.
    rewrite Mem.nextblock_empty. auto. 
    red; intros. unfold Genv.find_var_info in H1. simpl in H1. rewrite PTree.gempty in H1. congruence.
    red; intros. unfold Genv.find_funct_ptr in H1. simpl in H1. rewrite PTree.gempty in H1. congruence.
  Qed.


  Lemma zero_bytes : forall m b i bytes, 
    Mem.loadbytes m b i 1 = Some bytes -> decode_val Mint8unsigned bytes = Vzero -> 
    bytes = Byte Byte.zero :: nil.
  Proof.
    intros m b i bytes Hlb Hdec.
    assert (Hmax:= max_unsigned_val).
    assert (Hlength:= Mem.loadbytes_length _ _ _ _ _ Hlb).
    assert (exists byte, bytes = byte :: nil).
    destruct bytes; inv Hlength.
    destruct bytes; inv H0.
    exists m0; auto.
    destruct H as [byte]; subst.
    unfold decode_val in Hdec; simpl in Hdec.
    destruct byte as [|byte|].
    inv Hdec.
    rewrite <- decode_encode_int_1 in Hdec.
    unfold decode_int, encode_int in Hdec.
    rewrite rev_if_be_involutive in Hdec.
    unfold rev_if_be in Hdec; simpl in Hdec.
    replace (if Archi.big_endian then byte::nil else byte::nil) with (byte::nil) in Hdec.
    simpl in Hdec.
    assert (Hrange:= Byte.unsigned_range byte).
    assert (Hmod: Byte.modulus = 256) by auto.
    rewrite Byte.unsigned_repr in Hdec.
    rewrite 2 Z.add_0_r in Hdec.
    rewrite Int.repr_unsigned in Hdec.
    unfold Vzero, Int.zero in Hdec.
    assert (Int.repr (Byte.unsigned byte) = Int.repr 0).
    assert (forall i1 i2, Vint i1 = Vint i2 -> i1 = i2).
    intros i1 i2 Hi; inv Hi; auto.
    apply H; auto.
    apply f_equal with (f:= Int.unsigned) in H.
    rewrite 2 Int.unsigned_repr in H; try omega.
    apply f_equal with (f:= Byte.repr) in H.
    rewrite Byte.repr_unsigned in H; subst; auto.
    rewrite Z.add_0_r; rewrite Int.unsigned_repr; try omega.
    assert (Byte.max_unsigned = 255) by auto.
    omega.
    destruct Archi.big_endian; auto.
    inv Hdec.
  Qed.

  Lemma load_four_bytes_zero : forall m b p, (4 | p) ->
    (forall i, 0 <= i < 4 -> Mem.load Mint8unsigned m b (p+i) = Some Vzero) ->
    Mem.load Mint32 m b p = Some Vzero.
  Proof.
    intros m b p Hdiv Hbytes.
    assert (H0: 0 <= 0 < 4) by omega.
    assert (H1: 0 <= 1 < 4) by omega.
    assert (H2: 0 <= 2 < 4) by omega.
    assert (H3: 0 <= 3 < 4) by omega.
    assert (Hl0:= Hbytes 0 H0).
    assert (Hl1:= Hbytes 1 H1).
    assert (Hl2:= Hbytes 2 H2).
    assert (Hl3:= Hbytes 3 H3).
    apply Mem.load_loadbytes in Hl0; destruct Hl0 as [bytes0 [Hlb0 Hdec0]].
    apply Mem.load_loadbytes in Hl1; destruct Hl1 as [bytes1 [Hlb1 Hdec1]].
    apply Mem.load_loadbytes in Hl2; destruct Hl2 as [bytes2 [Hlb2 Hdec2]].
    apply Mem.load_loadbytes in Hl3; destruct Hl3 as [bytes3 [Hlb3 Hdec3]].
    assert (bytes0 = Byte Byte.zero :: nil) by (apply (zero_bytes m b (p+0)); auto).
    assert (bytes1 = Byte Byte.zero :: nil) by (apply (zero_bytes m b (p+1)); auto).
    assert (bytes2 = Byte Byte.zero :: nil) by (apply (zero_bytes m b (p+2)); auto).
    assert (bytes3 = Byte Byte.zero :: nil) by (apply (zero_bytes m b (p+3)); auto).
    assert (Hchunk: size_chunk Mint8unsigned >= 0) by (simpl; omega).
    rewrite Z.add_0_r in Hlb0; unfold size_chunk in *.
    assert (Hlb01:= Mem.loadbytes_concat _ _ _ _ _ _ _ Hlb0 Hlb1 Hchunk Hchunk).
    simpl in Hlb01.
    assert (Hlb012:= Mem.loadbytes_concat _ _ _ _ _ _ _ Hlb01 Hlb2 Hchunk Hchunk).
    simpl in Hlb012.
    assert (Hlb:= Mem.loadbytes_concat _ _ _ _ _ _ _ Hlb012 Hlb3 Hchunk Hchunk).
    subst; simpl in Hlb.
    replace 4 with (size_chunk Mint32) in Hlb; auto.
    apply Mem.loadbytes_load in Hlb; auto.
  Qed.

  End INITMEM.
  
  Lemma init_correct:
    forall M, MContainer_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (mcontainer ⊕ L64) M (malt ⊕ L64).
  Proof.
    Opaque oplus.
    intros M Himpl Hok.
    pose proof (fun i => module_ok_variable M i (Hok i)) as MOK; clear Hok.
    apply cl_init_sim_intro.
    { 
      intros ? ? ? Hmake. 
      eapply module_impl_imply in Himpl; destruct Himpl; subst.
      inv_monad' Hmake.
      generalize (make_program_make_globalenv _ _ _ _ Hmake0).
      intros HP. pose proof HP as HP'.
      eapply make_globalenv_stencil_matches in HP'.
      inv_make_globalenv HP.
      constructor.
      {
        constructor; simpl; trivial. 
        apply FlatMem.flatmem_empty_inj.
      }
      { 
        econstructor; eauto.
        {
          intros i Hi.
          specialize (init_mem_characterization' x b).
          unfold Genv.perm_globvar; simpl; intro Hperm.
          destruct (Hperm _ _ Hbvi H0) as [Hperm1 [Hperm2 [Hperm3 Hperm4]]]; clear Hperm; simpl in *.

          assert (Hwrite: forall ofs, (0 <= ofs < num_id * CSIZE /\ (4 | ofs)) ->
                                      Mem.valid_access m2 Mint32 b ofs Writable).
          intros ofs [Hofs Hdiv].
          unfold Mem.valid_access; simpl; split; auto.
          intros ofs' Hofs'.
          unfold Mem.range_perm, CSIZE in *; simpl in Hperm1.
          apply Hperm1.
          replace (Z.max 1280 0) with 1280; auto.
          destruct Hdiv as [n Hn]; omega.

          assert (Hquota: 0 <= i * CSIZE + QUOTA < num_id * CSIZE /\ (4 | i * CSIZE + QUOTA)).
          unfold CSIZE, QUOTA; split; try omega.
          exists (i*5); omega.
          assert (Husage: 0 <= i * CSIZE + USAGE < num_id * CSIZE /\ (4 | i * CSIZE + USAGE)).
          unfold CSIZE, USAGE; split; try omega.
          exists (i*5+1); omega.
          assert (Hparent: 0 <= i * CSIZE + PARENT < num_id * CSIZE /\ (4 | i * CSIZE + PARENT)).
          unfold CSIZE, PARENT; split; try omega.
          exists (i*5+2); omega.
          assert (Hnchildren: 0 <= i * CSIZE + NCHILDREN < num_id * CSIZE /\ (4 | i * CSIZE + NCHILDREN)).
          unfold CSIZE, NCHILDREN; split; try omega.
          exists (i*5+3); omega.
          assert (Hused: 0 <= i * CSIZE + USED < num_id * CSIZE /\ (4 | i * CSIZE + USED)).
          unfold CSIZE, USED; split; try omega.
          exists (i*5+4); omega.

          exists Int.zero, Int.zero, Int.zero, Int.zero, Int.zero.
          split.
          apply load_four_bytes_zero.
          destruct Hquota; auto.          
          intros; apply (Hperm4 (eq_refl _)); unfold CSIZE, QUOTA; omega.
          split.
          apply load_four_bytes_zero.
          destruct Husage; auto.          
          intros; apply (Hperm4 (eq_refl _)); unfold CSIZE, USAGE; omega.
          split.
          apply load_four_bytes_zero.
          destruct Hparent; auto.          
          intros; apply (Hperm4 (eq_refl _)); unfold CSIZE, PARENT; omega.
          split.
          apply load_four_bytes_zero.
          destruct Hnchildren; auto.          
          intros; apply (Hperm4 (eq_refl _)); unfold CSIZE, NCHILDREN; omega.
          split.
          apply load_four_bytes_zero.
          destruct Hused; auto.          
          intros; apply (Hperm4 (eq_refl _)); unfold CSIZE, USED; omega.
          repeat (split; auto).
          rewrite ZMap.gi; constructor.
        }
        {
          rewrite <- stencil_matches_symbols with (ge:= Genv.globalenv x); auto.
        }
      }
    }
    {
      intros. destruct H as [HF|HF]; inv HF; reflexivity.
    }
    {
      intros. destruct H as [HF|HF]; inv HF; reflexivity.
    }
    {
      intros.
      eapply module_impl_imply in Himpl; destruct Himpl; subst.
      transf_none i. specialize (MOK i).

      destruct H as [HF|HF]; inv HF; econstructor.
      get_module_variable_relfexivity.
    }
    {
      intros.
      eapply module_impl_imply in Himpl; destruct Himpl; subst.
      transf_none i. specialize (MOK i).

      destruct (peq i AC_LOC); subst.
      {
        apply (get_module_varible_OK_Some_left container_loc_type) in H; subst.
        reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      }
      {
        assert (get_module_variable
                  i (((MCONTAINER_init
                        ⊕ MCONTAINER_get_parent
                        ⊕ MCONTAINER_get_nchildren
                        ⊕ MCONTAINER_get_quota
                        ⊕ MCONTAINER_get_usage
                        ⊕ MCONTAINER_can_consume
                        ⊕ MCONTAINER_split ⊕ MCONTAINER_alloc) ⊕ AC_LOC ↦ container_loc_type) ⊕ ∅) = OK None).
        get_module_variable_relfexivity.
        unfold module, module_ops in *.
        congruence.
      }
    }
    {
      decision.
    }
  Qed.

  Theorem cl_simulation:
    forall p (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MContainer_impl = OK M ->
      make_program s CTXT (mcontainer ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (malt ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (mcontainer ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (malt ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MContainer_impl = OK M ->
      make_program s CTXT (mcontainer ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (malt ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (mcontainer ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (malt ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MContainer_impl = OK M ->
      make_program s CTXT (mcontainer ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (malt ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (mcontainer ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (malt ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      MContainer_impl = OK M ->
      make_program s (CTXT ⊕ M) (malt ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (mcontainer ⊕ L64) = OK ph.
  Proof.
    intros.
    exploit link_correct_aux; eauto.
    eapply make_program_vertical' in H0.
    destruct H0 as [p' Hmake].
    intros Hle.
    eapply make_program_sim_monotonic_exists.
    2: eapply Hle.
    reflexivity.
    eassumption.

    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

End WITHCOMPCERTIKOS.
