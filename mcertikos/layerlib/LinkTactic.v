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
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.logic.Semantics.
Require Import CompCertiKOSproof.
Require Import CompatClightSem.
Require Import I64Layer.
Require Export I64LayerAutosim.
Require Import LAsmModuleSemSpec.
Require Import LayerCalculusLemma.
Require Import Decision.
Require Import LAsm.
(*Require Import LayerModuleLemma.*)
Require Import LAsmModuleSemTransfer.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Lemma link_compiler D1 D2 R i (κ: Clight.function) σ_spec_high σ_spec_low L2 L_impl M:
    LayerCompilable (L2 ⊕ L64) ->
    ModuleOK (i ↦ κ) ->
    module_layer_disjoint (i ↦ κ) (L2 ⊕ L64) ->
    CompCertiKOS.transf_module (i ↦ κ) = OK M ->
    compatsim (freerg_inj _ _ _ R) σ_spec_high σ_spec_low ->
    (forall j σ1,
       get_layer_primitive j (i ↦ σ_spec_low) = OK (Some (compatsem_inl σ1)) ->
       forall s WB args m res m',
         σ1 s WB args m res m' ->
         Mem.nextblock m' = Mem.nextblock m) ->
    forall KERNEL_MODE: forall j σ1,
       get_layer_primitive j (i ↦ σ_spec_low) = OK (Some (compatsem_inl σ1)) ->
       forall s WB args m res m',
         σ1 s WB args m res m' ->
         kernel_mode (π_data m),
    spec_le (i ↦ σ_spec_low) (〚i ↦ κ 〛 L_impl) ->
    L_impl ≤ L2 ->
    cl_sim D1 D2 (freerg_inj _ _ _ R) (i ↦ σ_spec_high) (〚M〛 (L2 ⊕ L64)).
  Proof.
    intros.
    eapply cl_sim_compiler_layersim_compose.
    * pose proof layer_sim_intro as Hlsi.
      eapply Hlsi.
      simpl.
      eassumption.
    * assumption.
    * assumption.
    * eapply compiler_layersim_spec_le_compose.
      + eapply spec_le_right.
        - eassumption.
        - instantiate (1 := 〚i ↦ κ〛 (L2 ⊕ L64)).
          eapply clight_semantics_monotonic.
          reflexivity.
          rewrite <- left_upper_bound.
          assumption.
      + eapply compiler_correct; eauto.
        apply right_upper_bound.
  Qed.

  (* We have to define the le reflation for assembly spec relation *)
  Lemma link_assembly D1 D2 R i (κ: LAsm.function) σ_spec_high σ_spec_low L2:
    compatsim (freerg_inj _ _ _ R) σ_spec_high σ_spec_low ->
    asm_spec_le (i ↦ σ_spec_low) (〚i ↦ κ 〛 L2) ->
    cl_sim D1 D2 (freerg_inj _ _ _ R) (i ↦ σ_spec_high) (〚i ↦ κ〛 L2).
  Proof.
    intros.
    destruct σ_spec_high as [σ_spec_high|σ_spec_high].
    * eapply asm_spec_compose_inl; eauto.
      pose proof layer_sim_intro as Hlsi.
      eapply Hlsi.
      eassumption.
    * eapply asm_spec_compose; eauto.
      pose proof layer_sim_intro as Hlsi.
      eapply Hlsi.
      eassumption.
  Qed.

  (** This version can unify against a larger base layer, simliar to
    [link_compiler] *)
  Lemma link_assembly_le D1 D2 R i (κ: LAsm.function) σh σl L2 L_impl:
    compatsim (freerg_inj _ _ _ R) σh σl ->
    asm_spec_le (i ↦ σl) (〚i ↦ κ 〛 L_impl) ->
    L_impl ≤ L2 ->
    cl_sim D1 D2 (freerg_inj _ _ _ R) (i ↦ σh) (〚i ↦ κ〛 L2).
  Proof.
    intros H1 H2 H3.
    change (cl_sim D1 D2 (freerg_inj compatrel D1 D2 R)) with
           (sim (freerg_inj compatrel D1 D2 R)).
    rewrite <- H3.
    eapply link_assembly; eauto.
  Qed.

  Lemma cl_le_intro:
    forall D (L L': compatlayer D),
      L ≤ L' ->
      cl_sim D D id L L'.
  Proof.
    simpl. tauto.
  Qed.

  Lemma layer_link_newglbl_impl_comm {D1: compatdata} {D2: compatdata} {R: compatrel D1 D2}:
    forall L Lvar d prim,
      cl_sim D1 D2 (freerg_inj _ _ _ R) prim (〚d 〛 (Lvar ⊕ L)) ->
      L ⊕ Lvar ⊢ (freerg_inj _ _ _ R, d) : prim.
  Proof.
    intros. apply LayerLogicImpl.logic_intro.
    eapply cl_le_sim_compat.
    + reflexivity.
    + apply cl_le_intro.
      etransitivity.
      2: eapply oplus_le_left.
      eapply Semantics.lang_semof_sim_monotonic.
      reflexivity.
      pose proof (commutativity (A := compatlayer D2) (R := (≤))) as Hc.
      apply Hc.
    + assumption.
  Qed.

  Lemma layer_link_new_glbl_right {D1 D2} {R: freerg compatrel D1 D2}:
    forall L Lvar d prim,
      cl_sim D1 D2 R prim Lvar ->
      L ⊕ Lvar ⊢ (R, d) : prim.
  Proof.
    intros. apply LayerLogicImpl.logic_intro.
    eapply cl_le_sim_compat.
    + reflexivity.
    + apply cl_le_intro.
      etransitivity.
      2: apply oplus_comm_le.
      etransitivity.
      2: apply oplus_le_left.
      etransitivity.
      2: apply oplus_comm_le.
      apply oplus_le_left.
    + assumption.
  Qed.

  Lemma layer_link_new_glbl_both {D1 D2} {R: freerg compatrel D1 D2}:
    forall L d prim,
      sim R prim L ->
      L ⊢ (R, d) : prim.
  Proof.
    intros. apply LayerLogicImpl.logic_intro.
    eapply cl_le_sim_compat.
    + reflexivity.
    + apply cl_le_intro.
      etransitivity.
      2: apply oplus_comm_le.
      etransitivity.
      2: apply oplus_le_left.
      reflexivity.
    + assumption.
  Qed.

  Lemma link_cfunction_intro D1 D2 R L (M: module) prim:
    cl_sim D1 D2 (freerg_inj compatrel D1 D2 R) prim (〚M 〛 (L ⊕ L64)) ->
    L ⊕ L64 ⊢ (freerg_inj compatrel D1 D2 R, M) : prim.
  Proof.
    intro H.
    eapply (Language.conseq_le_left _ _ (L64 ⊕ L)); try le_oplus.
    apply layer_link_newglbl_impl_comm; eauto.
  Qed.

  Lemma conseq_le_left_join {D1 D2} (R: freerg compatrel D1 D2) M L1 L2 L3:
    L1 ⊢ (R, M) : L3 ->
    L1 ⊕ L2 ⊢ (R, M) : L3.
  Proof.
    intros.    
    eapply Language.conseq_le_left; try eassumption.
    (* for paths we used to have here: constructor.*)
    eapply le_left.
    reflexivity.
  Qed.

  Lemma le_assoc_comm {D: compatdata } (L2 L3 L4: compatlayer D):
    (L2 ⊕ L3) ⊕ L4 ≤ L2 ⊕ L3 ⊕ L4.
  Proof.
    rewrite associativity.
    reflexivity.
  Qed.

  Lemma conseq_le_assoc_comm {D1 D2} (R: freerg compatrel D1 D2) (L1: compatlayer D2)
        (L2 L3 L4: compatlayer D1) M:
    L1 ⊢ (R, M) : (L2 ⊕ (L3 ⊕ L4)) ->
    L1 ⊢ (R, M) : ((L2 ⊕ L3) ⊕ L4).
  Proof.
    intros.        
    eapply Language.conseq_le_right; try eassumption.
    (* for paths we used to have here: constructor.*)
    eapply le_assoc_comm.
  Qed.

  Lemma layer_le_trans `{D: compatdata}:
    forall (LT LL LH: compatlayer D),
      LL ⊕ LT = LH ->
      LL ≤ LH.
  Proof.
    intros.
    rewrite <- H.
    apply left_upper_bound.
  Qed.

Require Import liblayers.compcertx.MakeProgram.

  Lemma make_program_oplus_right `{D: compatdata} {L: compatlayer D}:
    forall s (CTXT M: module) pl,
      make_program s (CTXT ⊕ M) L = OK pl ->
      ModuleOK M.
  Proof. 
    intros.
    assert (ModuleOK (CTXT ⊕ M)).
    {
      eapply make_program_module_ok.
      esplit; eassumption.
    }
    eapply module_ok_antitonic; try eassumption.
    apply right_upper_bound.
  Qed.

  Lemma transf_module_variable_none:
    forall i id (f: Clight.function) x,
      CompCertiKOS.transf_module (id ↦ f) = ret x ->
      get_module_variable i x = OK None.
  Proof.
    intros.
    apply CompCertiKOS.get_module_variable_transf with (i:=i) in H.
    get_module_normalize_in H.
    assumption.
  Qed.

  Lemma transfer_variable_compose:
    forall
      DL DH (LL: compatlayer DL)
      v
      (τ: AST.globvar Ctypes.type)
      R
      (M: LAsm.module) (** important to specify this type, otherwise it defaults to Clight module, and apply loops forever *)
      (LH: compatlayer DH)
      (OK_Le: (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ) ≤ (〚M ⊕ v ↦ τ 〛 LL ⊕ LL)),
      (LL ⊕ (v ↦ τ) ⊢ (R, M): LH) ->
      LL ⊢ (R, M ⊕ (v ↦ τ)): LH.
  Proof.
    intros.
    Local Opaque oplus semof ptree_layer_ops simRR id.
    simpl in *.
    rewrite <- OK_Le.
    assumption.
  Qed.

  (*Lemma compat_semantics_spec_var_error {D} M (L: compatlayer D) i msg:
    get_module_variable i M = Error msg ->
    get_layer_globalvar i (〚M〛 L) = Error msg.
  Proof.
  Qed.*)

  Lemma transfer_variable_le:
    forall
      DL (LL: compatlayer DL)
      v
      (τ: AST.globvar Ctypes.type)
      (M: LAsm.module) (** important to specify this type, otherwise it defaults to Clight module, and apply loops forever *)
      (LOK_L: LayerOK (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ))
      (LOK_L': LayerOK (〚M ⊕ v ↦ τ 〛 LL ⊕ LL)),
      (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ) ≤ (〚M ⊕ v ↦ τ 〛 LL ⊕ LL).
  Proof.
    intros.
    Local Opaque mapsto oplus semof compatlayer_ops.
    constructor. 
    - eapply cl_le_layer_pointwise.
      pose proof LOK_L as LOK_L1.
      split.
      + intros. 
        destruct (LOK_L i) as [PrimOK VarOK _].
        destruct (get_layer_primitive i (〚M ⊕ v ↦ τ 〛 LL ⊕ LL)) eqn:primH; [| constructor].
        assert (LOK: isOK (get_layer_primitive i (〚M ⊕ v ↦ τ 〛 LL ⊕ LL))).
        {
          esplit; eassumption.
        }
        specialize (get_layer_primitive_isOK _ _ _ LOK).
        intros [HOK1 HOK2]. clear LOK.
        destruct HOK1 as [o1 HOK1].
        destruct HOK2 as [o2 HOK2].
        specialize (get_layer_primitive_oplus i (〚M ⊕ v ↦ τ 〛 LL) LL).
        rewrite primH, HOK1, HOK2. intros Hle.
        Local Transparent oplus.
        destruct o.
        {
          destruct o2.
          {
            (* i is in L *)
            assert (HW: get_layer_primitive i (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ) = OK (Some c)).
            {
              simpl in Hle.
              destruct o1; inv_monad Hle; inv H0.
              specialize (get_layer_primitive_isOK _ _ _ PrimOK).
              intros [PrimOK1 PrimOK2].
              assert (prim1: get_layer_primitive i (LL ⊕ v ↦ τ) = OK (Some c)).
              {
                eapply get_layer_primitive_left; eauto.
              }
              eapply get_layer_primitive_right; eauto.
            }
            rewrite HW. constructor. constructor. reflexivity.
          }
          {
            destruct o1.
            { (* i is in M *)
              Local Opaque mapsto semof compatlayer_ops.
              simpl in Hle. inv_monad Hle. inv H0.
              Local Opaque oplus.
              specialize (get_layer_primitive_isOK _ _ _ PrimOK).
              intros [PrimOK1 PrimOK2].
              assert (prim1: get_layer_primitive i (LL ⊕ v ↦ τ) = OK None).
              {
                eapply get_layer_primitive_none; eauto.
                get_layer_normalize. reflexivity.
              }
              (*eapply get_layer_primitive_left; eauto.*)
              rewrite get_layer_primitive_oplus.
              rewrite prim1, id_right.
              rewrite get_semof_primitive.
              rewrite get_semof_primitive in HOK1.
              rewrite get_module_function_oplus in HOK1.
              rewrite get_module_function_mapsto_variable in HOK1.
              rewrite (id_right (get_module_function i M)) in HOK1.
              unfold semof_function in *; simpl in *.
              destruct (get_module_function i M) as [[|]|]; try discriminate.
              monad_norm.
              rewrite <- HOK1.
              eapply LAsm_transfer_variable.
              assumption.
            }
            {
              Local Transparent oplus.
              simpl in Hle. inv_monad Hle. inv H0.
            }
          }
        }
        {
          Local Transparent oplus.
          simpl in Hle.
          destruct o1; destruct o2; inv_monad Hle; inv H0.
          Local Opaque oplus.
          assert (HW: get_layer_primitive i (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ) = OK None).
          {
            specialize (get_layer_primitive_isOK _ _ _ PrimOK).
            intros [PrimOK1 PrimOK2].
            assert (prim1: get_layer_primitive i (LL ⊕ v ↦ τ) = OK None).
            {
              eapply get_layer_primitive_none; eauto.
              get_layer_normalize. reflexivity.
            }
            eapply get_layer_primitive_none; eauto.
            destruct PrimOK1 as [? PrimOK1].
            destruct x; try assumption.
            rewrite get_semof_primitive in HOK1, PrimOK1.
            rewrite get_module_function_oplus in HOK1.
            rewrite get_module_function_mapsto_variable in HOK1.
            rewrite id_right in HOK1.
            unfold semof_function in *.
            destruct (get_module_function i M) as [[|]|]; discriminate.
          }
          Local Opaque compatlayer_ops.    
          simpl in *. unfold module, module_ops in *.
          rewrite HW. constructor. reflexivity.
        }

      + intros. 
        destruct (LOK_L i) as [PrimOK VarOK Hor].
        specialize (get_layer_globalvar_oplus i (〚M ⊕ v ↦ τ 〛 LL) LL).
        destruct (get_layer_globalvar i (〚M ⊕ v ↦ τ 〛 LL ⊕ LL)) eqn: varH;
        intros Hle; [| constructor].
        assert (LOK: isOK (get_layer_globalvar i (〚M ⊕ v ↦ τ 〛 LL ⊕ LL))).
        {
          esplit; eassumption.
        }
        specialize (get_layer_globalvar_isOK _ _ _ LOK).
        intros  [HOK1 HOK2]. 
        destruct HOK1 as [o1 HOK1].
        destruct HOK2 as [o2 HOK2].
        simpl in *.
        rewrite HOK1, HOK2 in Hle. 
        destruct o.
        {
          (* get_layer_globalvar i (cl_base_layer (〚M ⊕ v ↦ τ 〛 LL ⊕ LL)) = Some _ *)
          destruct o2.
          { (* i is in L *)
            simpl in Hle.
            Local Transparent oplus.
            destruct o1; inv_monad Hle.
            specialize (get_layer_globalvar_isOK _ _ _ VarOK).
            intros [PrimOK1 PrimOK2].
            assert (prim1: get_layer_globalvar i (LL ⊕ v ↦ τ) = OK (Some g0) /\ i <> v).
            {
              destruct (peq i v); subst.
              - specialize (get_layer_globalvar_oplus v LL (v ↦ τ)).
                destruct PrimOK2 as [? PrimOK2].
                rewrite get_layer_globalvar_mapsto.
                simpl in *.
                rewrite PrimOK2. rewrite HOK2.
                intros Hle. inv_monad Hle. inv H0.
              - split; [| assumption].
                eapply get_layer_globalvar_left; eauto.
            }
            destruct prim1 as [prim1 Hneq].
            assert (HW: get_layer_globalvar i (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ) = OK (Some g0)).
            {
              eapply get_layer_globalvar_right; eauto.
            }
            unfold module, module_ops in HW |-*.
            simpl in HW |- *.
            unfold AST.ident in HW |-*. 
            rewrite HW.
            reflexivity.
          }

          { (* i in the 〚M ⊕ v ↦ τ 〛 *)
            simpl in Hle.
            Local Opaque compatlayer_ops.
            destruct o1; inv_monad Hle; inv H0.
            specialize (get_layer_globalvar_isOK _ _ _ VarOK).
            intros [PrimOK1 PrimOK2].
            destruct (LOK_L' i) as [PrimOK' VarOK' HF].
            rewrite varH in HF.
            Local Opaque oplus.
            destruct HF as [HF|HF]; inv HF.
            specialize (get_layer_primitive_cancel i (〚M ⊕ v ↦ τ 〛 LL) LL H0).
            intros [LNone MNone].
            assert (Hmo_none: get_module_function i (M ⊕ v ↦ τ) = OK None).
            {
              setoid_rewrite compat_get_semof_primitive in MNone.
              get_module_normalize_in MNone.
              destruct (get_module_function i (M ⊕ v ↦ τ)) eqn: Hmo_none.
              - destruct o; [|reflexivity].
                get_module_normalize_in Hmo_none.
                rewrite Hmo_none in MNone.
                discriminate.
              - get_module_normalize_in Hmo_none.
                rewrite Hmo_none in MNone.
                discriminate.
            }
            pose proof Hmo_none as Hmo_none'.
            apply get_module_function_cancel in Hmo_none.
            destruct Hmo_none as [Hmo Hmo'].
            assert (Hprim:get_layer_primitive i (LL ⊕ v ↦ τ) = OK None).
            {
              apply get_layer_primitive_isOK in PrimOK.
              destruct PrimOK as [_ PrimOK].
              eapply get_layer_primitive_none; try assumption.
              get_layer_normalize; reflexivity.
            }

            assert (HM: get_module_variable i (M ⊕ v ↦ τ) = OK (Some g)).
            {
              get_layer_normalize_in varH.
              pose proof (get_semof_globalvar i (M ⊕ v ↦ τ) LL) as H.
              setoid_rewrite H in varH.
              rewrite HOK2 in varH.
              rewrite id_right in varH.
              assumption.
            }

            destruct (peq i v); subst.
            { (* i = v*)
              assert (Heq : g = τ).
              {
                eapply get_module_varible_OK_Some_right; try eassumption.
                get_module_normalize; reflexivity.
              }
              subst.
              assert (HW: get_layer_globalvar v (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ) = OK (Some τ)).
              {
                eapply get_layer_globalvar_right; try assumption.
                eapply get_layer_globalvar_right; try assumption.
                get_layer_normalize; reflexivity.
              }
              unfold module, module_ops in HW |-*.
              simpl in HW |- *.
              unfold AST.ident in HW |-*. 
              rewrite HW.
              reflexivity.
            }
            { (* i <> v *)
              assert (HW: get_layer_globalvar i (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ) = OK (Some g)).
              {
                eapply get_layer_globalvar_left; try assumption.
                assert (HW: get_module_variable i M = OK (Some g)).
                {
                  assert (Hm: get_module_variable i (v ↦ τ) = OK None).
                  {
                    get_module_normalize; reflexivity.
                  }
                  specialize (get_module_variable_oplus i M (v ↦ τ)).
                  rewrite HM, Hm.
                  intros Hle.
                  Local Transparent oplus.
                  destruct (get_module_variable i M); try destruct o; inv_monad Hle.
                  reflexivity.
                }
                rewrite <- HW.
                apply get_semof_globalvar.
              }
              unfold module, module_ops in HW |- *.
              simpl in HW |- *.
              unfold AST.ident in HW |- * . 
              rewrite HW.
              reflexivity.
            }
          }              
        }
        {
          assert (HW: isOKNone (get_layer_globalvar i (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ))).
          {
            destruct o1; destruct o2; inv_monad Hle.
            destruct Hor as [Hor | Hor]; try assumption.
            eapply get_layer_primitive_cancel in Hor.
            destruct Hor as [Hprim1 Hprim2].
            pose proof Hprim1 as Hprim1'.
            eapply get_layer_primitive_cancel in Hprim1.
            destruct Hprim1 as [_ Hprim1].
            destruct (LOK_L' i) as [PrimOK' VarOK' Hor'].
            apply get_layer_primitive_isOK in PrimOK'.
            destruct PrimOK' as [PrimOK' _].

            assert (Hmo: get_module_function i (M ⊕ v ↦ τ) = OK None).
            {
              destruct (get_module_function i (M ⊕ v ↦ τ)) eqn: Hmo.
              destruct o; [|reflexivity].
              - specialize (get_module_function_oplus i M (v ↦ τ)).
                rewrite Hmo.
                assert (get_module_function i (v ↦ τ) = OK None).
                {
                  get_module_normalize.
                  reflexivity.
                }
                rewrite H.
                intros Hle.
                destruct (get_module_function i M) eqn:Hmo'; try destruct o; inv_monad Hle.
                pose proof (get_semof_primitive i M (LL ⊕ v ↦ τ)) as Hprim2'.
                setoid_rewrite Hprim2' in Hprim2; clear Hprim2'.
                rewrite Hmo' in Hprim2.
                discriminate.
              - get_module_normalize_in Hmo.
                rewrite id_right in Hmo.
                pose proof (get_semof_primitive i M (LL ⊕ v ↦ τ)) as Hprim2'.
                setoid_rewrite Hprim2' in Hprim2; clear Hprim2'.
                rewrite Hmo in Hprim2.
                discriminate.
            }
            assert (Hmo': get_module_variable i (M ⊕ v ↦ τ) = OK None).
            {
              destruct (get_module_variable i (M ⊕ v ↦ τ)) eqn: Hmo'.
              destruct o; [|reflexivity].
              - pose proof (get_semof_globalvar i (M ⊕ v ↦ τ) LL).
                setoid_rewrite H in HOK1.
                congruence.
              - pose proof (get_semof_globalvar i (M ⊕ v ↦ τ) LL).
                setoid_rewrite H in HOK1.
                congruence.
            }
            
            eapply get_module_function_cancel in Hmo.
            destruct Hmo as [Hmo Hmo''].
            eapply get_module_variable_cancel in Hmo'.
            destruct Hmo' as [Hmo1 Hmo2].
            destruct (peq i v); subst.
            get_module_normalize_in Hmo1.
            inv Hmo1.
            pose proof (get_layer_globalvar_isOK _ _ _ VarOK) as VarOK''.
            destruct VarOK'' as [_ VarOK''].
            eapply get_layer_globalvar_none; try assumption.
            eapply get_layer_globalvar_none; try assumption.
          }
          rewrite HW.
          reflexivity.
        }

    - Local Transparent semof mapsto oplus compatlayer_ops.
      simpl.
      destruct (cl_exec_load LL);
      try destruct o; monad_norm; reflexivity.
    - simpl.
      destruct (cl_exec_store LL);
      try destruct o; monad_norm; reflexivity.
  Qed.

  Lemma transfer_variable:
    forall
      DL DH (LL: compatlayer DL)
      v
      (τ: AST.globvar Ctypes.type)
      R
      (M: LAsm.module) (** important to specify this type, otherwise it defaults to Clight module, and apply loops forever *)
      (LH: compatlayer DH)
      (LOK_L: LayerOK (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ))
      (LOK_L': LayerOK (〚M ⊕ v ↦ τ 〛 LL ⊕ LL)),
      (LL ⊕ (v ↦ τ) ⊢ (R, M): LH) ->
      LL ⊢ (R, M ⊕ (v ↦ τ)): LH.
  Proof.
    intros.
    eapply transfer_variable_compose; try eassumption.
    eapply transfer_variable_le; try assumption.
  Qed.

  Lemma transfer_variable_L64 (DL DH: compatdata) LL v τ (R: _ _ DH DL) M LH:
    LayerOK (〚M 〛 ((LL ⊕ v ↦ τ) ⊕ L64) ⊕ ((LL ⊕ v ↦ τ) ⊕ L64)) ->
    LayerOK (〚M ⊕ v ↦ τ 〛 (LL ⊕ L64) ⊕ (LL ⊕ L64)) ->
    (LL ⊕ v ↦ τ) ⊕ L64 ⊢ (R, M) : LH ->
    LL ⊕ L64 ⊢ (R, M ⊕ v ↦ τ) : LH.
  Proof.
    intros Hok1 Hok2 H.
    eapply transfer_variable; eauto.
    - eapply layer_ok_antitonic; [ | apply Hok1].
      assert ((LL ⊕ L64) ⊕ v ↦ τ ≤ (LL ⊕ v ↦ τ) ⊕ L64) by le_oplus.
      solve_monotonicity.
      reflexivity.
    - eapply Language.conseq_le_left; eauto.
      le_oplus.
  Qed.

  Lemma module_le_left:
    forall (L L1 L2: module),
      L ≤ L1 ->
      L ≤ (L1 ⊕ L2).
  Proof.
    intros.
    rewrite <- left_upper_bound.
    assumption.
  Qed.

  Lemma module_le_right:
    forall (L L1 L2: module),
      L ≤ L2 ->
      L ≤ (L1 ⊕ L2).
  Proof.
    intros.
    rewrite <- right_upper_bound.
    assumption.
  Qed.

  Require Import LAsmModuleSem.
  Require Import LayerCalculusLemma.

  Lemma LayerOK_impl_subst `{D: compatdata} {M M': module} {L: compatlayer D}:
    LayerOK (〚M 〛 L ⊕ L) ->
    M' ≤ M ->
    LayerOK (〚M' 〛 L ⊕ L).
  Proof.
    intros.
    eapply layer_ok_antitonic; try eassumption.
    solve_monotonic.
  Qed.

End WITHCOMPCERTIKOS.

(** Thanks to this hint we don't need to modify the code that uses
  [link_compiler]. We may want to push it back to CompatLayers if we
  want to adopt that approach for good. *)
Hint Extern 10 (module_layer_disjoint _ _) => decision.

Ltac link_nextblock :=
  intros;
  match goal with
    | Hprim: get_layer_primitive _ (_ ↦ _ ) = _ |- Mem.nextblock ?m' = Mem.nextblock ?m =>
      apply get_layer_primitive_OK_eq in Hprim; inv Hprim;
      match goal with
        | Hstep: _ _ _ _ m _ m' |- _ =>  
          inv Hstep;
            repeat match goal with
                     | Hstore: Mem.store _ _ _ _ _ = Some ?fm |- Mem.nextblock ?fm = _ =>
                       rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore)
                     | |- Mem.nextblock (_, _) = _ => simpl; unfold lift; simpl
                   end; reflexivity
      end
  end.

Ltac link_kernel_mode :=
  intros;
  match goal with
    | Hprim: get_layer_primitive _ (_ ↦ _ ) = _ |- kernel_mode (π_data ?m) =>
      apply get_layer_primitive_OK_eq in Hprim; inv Hprim;
      match goal with
        | Hstep: _ _ _ _ m _ _ |- _ =>  
          inv Hstep; 
            tauto
      end
  end.

Ltac hcomp_tac :=
  apply Language.hcomp_rule; [decision | | ].    

Ltac transfer_variables :=
  match goal with
    | |- ?L1 ⊢ (?R, ?M ⊕ ?vi ↦ ?vt) : ?L2 =>
      apply transfer_variable_L64; [assumption .. | transfer_variables]
    | |- _ =>
      idtac
  end.

Ltac layer_link_split_tac :=
  match goal with
    | |- _ ⊢ (_, _ ⊕ ∅) : _ => apply LayerLogicImpl.vdash_oplus_empty; layer_link_split_tac
    | |- _ ⊢ _ : _ ⊕ _ => hcomp_tac; layer_link_split_tac
    | |- _ ⊕ L64 ⊢ _ : _ => eapply link_cfunction_intro
    | |- _ => eapply layer_link_newglbl_impl_comm
  end.

(** Prove the simulation for a single C function, using the provided
  refinement and code proofs. *)
Ltac link_cfunction refthm codethm :=
  eapply link_compiler;
  [ Decision.decision | (* LayerCompilable *)
    Decision.decision | (* ModuleOK *)
    Decision.decision | (* layer_module_disjoint *)
    eassumption | (* transf_module _ = _ *)
    eapply refthm |
    link_nextblock |
    link_kernel_mode |
    eapply codethm |
    le_oplus ]. (* implem. layer contained in base layer *)

(** Similar tactic for assembly functions: *)
Ltac link_asmfunction refthm codethm :=
  eapply link_assembly_le;
  [ eapply refthm |
    eapply codethm |
    le_oplus ].


Ltac code_correct_tac :=
  try assumption ; decision.

(*Ltac inv_monad_rewrite H :=
  repeat match type of H with
    | context C[Errors.OK ?x] =>
      change (OK x) with (ret (M:=res) x) in H
    | context C[@Errors.bind ?A ?B ?ra ?f] =>
      change (@Errors.bind A B ra f) with (bind (M:=res) (A:=A) (B:=B) f ra)
    | context C[Some ?x] =>
      change (Some x) with (ret x) in H
  end.

Ltac inv_monad_destruct H:=
  match type of H with
    | ret ?x = ret ?y =>
      apply monad_inv_ret in H

    | ret ?mb = bind ?f ?ma =>
      symmetry in H;
      inv_monad_destruct H

    | bind ?f ?ma = ret ?mb =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct (monad_inv_bind f ma mb H) as [? [H1 H2]];
      clear H; rename H2 into H;
      inv_monad_destruct H

    | bind ?f ?ma = ret ?mb =>
      destruct (monad_inv_bind_weak f ma mb H) as [? ?]

    | _ => inversion H; clear H; subst
  end.

Ltac inv_monad' H:=
  inv_monad_rewrite H;
  inv_monad_destruct H; subst.*)

Ltac inv_monad_rewrite H :=
  repeat match type of H with
    | context C[Errors.OK ?x] =>
      change (OK x) with (ret (M:=res) x) in H
    | context C[@Errors.bind ?A ?B ?ra ?f] =>
      change (@Errors.bind A B ra f) with (bind (M:=res) (A:=A) (B:=B) f ra)
    | context C[Some ?x] =>
      change (Some x) with (ret x) in H
  end.

Ltac inv_monad_destruct H:=
  lazymatch type of H with
(*
    | ret ?x = ret ?y =>
      apply monad_inv_ret in H
*)

    | ret ?mb = bind ?f ?ma =>
      symmetry in H;
      inv_monad_destruct H

    | @bind ?M ?Mfmap ?Mops ?A ?B ?f ?ma = ret ?mb =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct (@monad_inv_bind M Mfmap Mops _ _ A B f ma mb H) as [? [H1 H2]];
      clear H; rename H2 into H;
      inv_monad_destruct H

(*
    | bind ?f ?ma = ret ?mb =>
      destruct (monad_inv_bind_weak f ma mb H) as [? ?]
*)


    | _ => inversion H; clear H; subst
  end.

Ltac inv_monad' H:=
  inv_monad_rewrite H;
  inv_monad_destruct H; subst.


Ltac transf_none i:=
  repeat match goal with
           | H: CompCertiKOS.transf_module _ = ret _ |- _ => apply (transf_module_variable_none i) in H
         end.

Ltac get_module_variable_isOK_split_tac H:=
  let HT1 := fresh "HOK" in
  let HT2 := fresh "HOK" in
  destruct (get_module_variable_isOK _ _ _ H) as [HT1 HT2].

Ltac get_module_variable_relfexivity :=
  repeat match goal with
           | H0: isOK (get_module_variable ?id (?a ⊕ ?b)) |- get_module_variable ?id (?a ⊕ ?b) = _
             => match a with
                  | context[id] => 
                    get_module_variable_isOK_split_tac H0;
                      eapply get_module_variable_left; try eassumption
                  | _ => 
                    match b with
                      | context[id] =>
                        get_module_variable_isOK_split_tac H0;
                          eapply get_module_variable_right; try eassumption
                      | _ =>
                        get_module_variable_isOK_split_tac H0;
                          eapply get_module_variable_none; try eassumption
                    end
                end
           | _ => try reflexivity; try get_module_normalize; try reflexivity
         end.
