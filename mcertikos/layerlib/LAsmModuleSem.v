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
(** This file provide the semantics for the [Asm] instructions. Since we introduce paging mechanisms, the semantics of memory load and store are different from [Compcert Asm]*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import AsmX.
Require Import Conventions.
Require Import Machregs.
Require Import AuxLemma.
Require Import CommonTactic.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import CompCertBuiltins.
Require Import LAsm.
Require Import MemoryExtra.
Require Import Observation.

Require Export LAsmModuleSemDef.
Require Export LAsmModuleSemProp.
Require Import LAsmModuleSemHighInv.
Require Import LAsmModuleSemLowInv.
Require Import LAsmModuleSemAsmInv.
Require Import LAsmModuleSemAux.
Require Import LAsmModuleSemMonotonic.
Require Import LAsmModuleSemSim.
Require Import LAsmModuleSemMakeProgram.

(** ** Semantics of LAsm modules *)

Section ModuleSemantics.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Lemma one_step_monotonic {D: compatdata}
        (L: compatlayer D)
        `{acc_def_prf1: !AccessorsDefined L}
        `{acc_def_prf2: !AccessorsDefined L}
        `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet}
        (s: stencil) ge ge' rs rs' (m m': mwd D) t:
    stencil_matches s ge ->
    stencil_matches s ge' ->
    ge ≤ ge' ->
    step (lcfg_ops:= LC (acc_def_prf:= acc_def_prf1) L) ge (State rs m) t (State rs' m') -> 
    step (lcfg_ops:= LC (acc_def_prf:= acc_def_prf2) L) ge' (State rs m) t (State rs' m').
  Proof.
    intros. inv H. inv H0.
    replace acc_def_prf2 with acc_def_prf1 by (apply Axioms.proof_irr).
    eapply module_le_step; eauto; unfold fundef in *; congruence.
  Qed.

  Remark set_regs_inject'': 
    forall f rl vl rs rs' r,
      (~ In r rl -> val_inject f (rs r) (rs' r))
      -> val_list_inject f vl (map rs' rl)
      -> val_inject f ((set_regs rl vl rs) r) (rs' r).
  Proof.
    induction rl; simpl. auto.
    intros. destruct vl; inv H0.
    eapply IHrl; eauto.
    intros.
    destruct (preg_eq a r).
    + subst. rewrite Pregmap.gss. assumption.
    + rewrite Pregmap.gso; try congruence.
      eapply H. tauto.
  Qed.

  Remark undef_regs_inject'': 
    forall f rl rs rs' r,
      (~ In r rl -> val_inject f (rs r) (rs' r))
      -> val_inject f ((undef_regs rl rs) r) (rs' r).
  Proof.
    induction rl; simpl. auto.
    intros.
    eapply IHrl; eauto.
    intros.
    destruct (preg_eq a r).
    + subst. rewrite Pregmap.gss. constructor.
    + rewrite Pregmap.gso; try congruence.
      eapply H. tauto.
  Qed.
 
  Lemma one_step_sim_monotonic {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{names2: !LayerNamesMatch D2 L2}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall (s: stencil) ge ge' f rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 t, 
    forall (Hglobalenv: exists M, make_globalenv (D:=D2) s M L2 = OK ge'),
    forall (Hge_external: 
              forall b ef, 
                Genv.find_funct_ptr ge b = Some (External ef) ->
                exists i sg, ef = EF_external i sg),
    forall (OKLayer: LayerOK L2),
    forall (ValidLayer: get_layer_prim_valid L2 s),
      stencil_matches s ge ->
      stencil_matches s ge' ->
      ge ≤ ge' ->
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      high_level_invariant d1 ->
      high_level_invariant d2 ->
      low_level_invariant (Mem.nextblock m2) d2 ->
      asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      (step (lcfg_ops:= LC L1)) 
        ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
      exists f' rs2' m2' d2',
        (step (lcfg_ops:= LC L2)) 
          ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
        /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    intros.
    assert (Hsymbol: forall i, Genv.find_symbol ge i = Genv.find_symbol ge' i).
    {
      inv H; inv H0.
      intros; congruence.
    }
    assert (Hgenv_next: Genv.genv_next ge = Genv.genv_next ge').
    {
      inv H; inv H0.
      intros; congruence.
    }
    assert(Hvolatile: forall b1 : block, block_is_volatile ge b1 = block_is_volatile ge' b1).
    {
      inv H; inv H0.
      intros; congruence.
    }  
    assert(HPC: forall b ofs ef, rs1 PC = Vptr b ofs -> 
                                 Genv.find_funct_ptr ge b = Some ef ->
                                 rs2 PC = Vptr b ofs).
    {
      intros. inv H7. inv match_extcall_states. specialize (match_reg PC).
      unfold Pregmap.get in *. rewrite H9 in match_reg.
      inv match_reg. exploit (stencil_find_funct_ptr_inject (ge:= ge) f); eauto.
      intros HFB. rewrite HFB in H13. inv H13.
      rewrite Int.add_zero; eauto.
    }  
    inv H1.
    assert(Hfunct: forall b f,  Genv.find_funct_ptr ge b = Some f
                                -> Genv.find_funct_ptr ge' b = Some f).
    {
      intros. specialize (genv_le_find_funct_ptr b).
      rewrite H1 in genv_le_find_funct_ptr.
      inv genv_le_find_funct_ptr.
      trivial.
    }
    inv H8.

    - (* instruction *)
      erewrite exec_instr_symbols_preserved with (ge1:= ge') in H16; eauto.
      exploit exec_instr_sim_monotonic; eauto.
      intros [?[?[?[?[Hexec Hmatch]]]]].
      refine_split'; eauto.
      econstructor; eauto.
      simpl in *; rewrite <- relate_kernel_mode; eauto.
      inv H7; inv match_extcall_states; eauto.

    - (* builtin *)
      eapply (external_call_preserved _ _ ge ge') in H16; eauto.
      inv H7.
      exploit (external_call_sim_monotonic ge'); eauto.
      exploit (val_list_inject_args rs1 rs2 args); eauto. 
      intros [?[?[?[?[Hext[HM [Hinj Hlist]]]]]]].
      refine_split'; eauto.
      econstructor; eauto.
      simpl in *; rewrite <- relate_kernel_mode; inv match_extcall_states; eauto.
      econstructor; eauto.
      assert(HV: forall r, val_inject x (Pregmap.get r rs1) (Pregmap.get r rs2)).
      {
        intros. eapply val_inject_incr; eauto.
      }
      clear match_reg.
      val_inject_simpl.
      eapply set_regs_inject'; eauto.
      eapply undef_regs_inject; eauto.

    - (* annot *)
      eapply (external_call_preserved _ _ ge ge') in H17; eauto.
      inv H7. pose proof match_extcall_states as Hmatch'.
      inv match_extcall_states.      
      exploit (annot_args_inject d1 d2); eauto.
      intros [?[Han Hval]].
      exploit (external_call_sim_monotonic ge'); eauto.
      intros [?[?[?[?[Hext[HM [Hinj Hlist]]]]]]].
      refine_split'; eauto.
      eapply exec_step_annot; eauto.
      simpl in *; rewrite <- relate_kernel_mode; eauto.
      econstructor; eauto.
      assert(HV: forall r, val_inject x0 (Pregmap.get r rs1) (Pregmap.get r rs2)).
      {
        intros. eapply val_inject_incr; eauto.
      }
      clear match_reg.
      val_inject_simpl. 

    - (* external call *)
      exploit Hge_external; eauto.
      intros [i[sg ?]]; subst.
      inv H16. inv H1.
      destruct H8 as [Hlayer Hsem]. inv H2.
      eapply cl_sim_layer_pointwise in cl_sim_layer.
      destruct cl_sim_layer as [Hsim _].
      specialize (Hsim i). 
      rewrite Hlayer in *.
      inv Hsem.
      destruct H1 as [?[Hstencil'[Hsem[?[? ?]]]]]; subst.
      eapply stencil_matches_unique in Hstencil'; try apply H; subst.              
      pose proof H7 as Hmatch. inv H7.
      pose proof match_extcall_states as Hmatch'; inv Hmatch'.
      exploit (extcall_args_inject d1 d2); eauto.
      intros[vargs'[Hext Hval]].
      inv Hsim.
      + (* OK y = get_layer_primitive i L2 *)
        inv H7. inv H8. 
        * destruct H7 as [Hstep Hcsig Hvalid Hinvs].
          exploit Hstep; eauto 2; clear Hstep.
          instantiate (1:= fun _: block => True). trivial.
          (* sextcall_valid sem2 s = true *)
          specialize (ValidLayer i). simpl in ValidLayer.
          rewrite <- H2 in ValidLayer. specialize (ValidLayer _ refl_equal).
          apply ValidLayer.

          eapply decode_longs_inject; eauto.
          intros [f'[?[?[?[Hsem'[Hval'[Hmatche Hincr]]]]]]].
          refine_split'; eauto.
          eapply exec_step_external; eauto.
          simpl in *; rewrite <- relate_kernel_mode; eauto.
          econstructor; eauto.
          econstructor; eauto.
          split; eauto.
          econstructor; eauto.
          refine_split'; eauto.
          unfold sextcall_sig. rewrite Hcsig.
          trivial.
          inv H6. inv inv_inject_neutral.
          intros; split.
          specialize (match_reg ESP). unfold Pregmap.get in match_reg.
          rewrite H1 in match_reg. inv match_reg; try congruence.
          rewrite <- H6 in STACK. destruct (STACK _ _ refl_equal) as [Hple _].
          exploit match_inject_forward; eauto. intros [_ ?].
          unfold fundef in *.
          rewrite <- Hgenv_next. xomega.
          lift_unfold.
          specialize (inv_reg_inject_neutral ESP).
          rewrite H1 in *. inversion inv_reg_inject_neutral.
          unfold Mem.flat_inj in H9.
          destruct (plt b0 (Mem.nextblock m2)); contra_inv. trivial.
          eapply reg_val_inject_defined; eauto.
          eapply reg_val_inject_defined; eauto.
          econstructor; eauto.
          assert(HV: forall r, val_inject f' (Pregmap.get r rs1) (Pregmap.get r rs2)).
          {
            intros. eapply val_inject_incr; eauto.
          }
          clear match_reg.
          val_inject_simpl.
          eapply set_regs_inject'; eauto.
          eapply undef_regs_inject; eauto.
          eapply undef_regs_inject; eauto.
          eapply encode_long_inject; eauto.

        * (* I'm not sure whether we should have this case or not?*)
          destruct H7 as [(name & Hname & Hstep) Hsig Hvalid Hinvs].
          exploit Hstep; try eapply Hext; eauto 2; clear Hstep.
          specialize (ValidLayer i). simpl in ValidLayer.
          rewrite <- H2 in ValidLayer. specialize (ValidLayer _ refl_equal).
          apply ValidLayer.
          {
            symmetry in H2.
            pose proof (layer_names_match _ _ _ H2 Hname) as Hname'.
            subst.
            destruct Hglobalenv as [M Hge].
            edestruct (make_globalenv_find_funct_ptr s M L2 ge' b) as [i Hi];
              eauto.
            destruct Hi as (Hgei & [(fi & HMi & Hfi) | (fe & HL1i & Hfe)]).
            + discriminate.
            + simpl in Hfe.
              inversion Hfe.
              subst.
              erewrite <- stencil_matches_symbols; eauto.
          }
          eapply reg_val_inject_defined; eauto.
          eapply reg_val_inject_defined; eauto.
          intros.
          specialize (match_reg ESP). unfold Pregmap.get in match_reg.
          rewrite H1 in match_reg. inv match_reg; try congruence.
          rewrite <- H7 in STACK. destruct (STACK _ _ refl_equal) as [Hple _].
          exploit match_inject_forward; eauto. intros [_ ?].
          inv H. rewrite <- stencil_matches_genv_next.
          unfold fundef in *. xomega.
          intros [f'[?[?[?[Hsem'[Hmatche [Hincr[Hvallist [Hles[HPC' HESP']]]]]]]]]].
          refine_split'; eauto.
          eapply exec_step_prim_call; eauto.
          econstructor; eauto.
          refine_split'; eauto.
          econstructor; eauto.
          econstructor; eauto.

          (* val_inject f' *)
          intro reg.
          unfold Pregmap.get.
          destruct (preg_eq reg RA).
          {
            subst.
            rewrite Pregmap.gss.
            constructor.
          }
          rewrite Pregmap.gso; auto.
          Require ValuesX.
          destruct (preg_eq reg PC).
          {
            subst.
            rewrite Pregmap.gss.
            eapply ValuesX.val_inject_lessdef_compose.
            eapply val_inject_incr; eauto.
            unfold Pregmap.get; assumption.
          }
          rewrite Pregmap.gso; auto.          
          apply set_regs_inject''; auto.
          intros.
          apply undef_regs_inject''.
          intros.
          apply undef_regs_inject''.
          intros.
          eapply ValuesX.val_inject_lessdef_compose.
          eapply val_inject_incr. eassumption. eauto.
          destruct (preg_eq reg ESP).
          {
            subst. unfold Pregmap.get; assumption.
          }
          assert (exists m, reg = preg_of m).
          {
            exists (match reg with
                      | IR EAX => AX
                      | IR EBX => BX
                      | IR ECX => CX
                      | IR EDX => DX
                      | IR ESI => SI
                      | IR EDI => DI
                      | IR EBP => BP
                      | FR XMM0 => X0
                      | FR XMM1 => X1
                      | FR XMM2 => X2
                      | FR XMM3 => X3
                      | FR XMM4 => X4
                      | FR XMM5 => X5
                      | FR XMM6 => X6
                      | FR XMM7 => X7
                      | ST0 => FP0
                      | _ => (* dummy *) FP0
                    end).
            destruct reg; auto; try congruence.
            destruct i0; auto; congruence.
            destruct f0; auto; congruence.
            destruct c; destruct H7; simpl; tauto.
          }
          destruct H9; auto.
          subst.
          eapply Hles.
          intro Habs.
          apply H8.
          apply in_map.
          assumption.

      + (* Error msg = get_layer_primitive i L2 *)
        exfalso.
        destruct (OKLayer i) as [[σ Hσ] _ _].
        simpl in Hσ.
        congruence.

    - (* primitive call *)
      exploit Hge_external; eauto.
      intros [i[sg ?]]; subst.
      inv H15.
      destruct H1 as [?[?[Hef[Hlayer Hsem]]]]. inv Hef.
      inv H2. eapply cl_sim_layer_pointwise in cl_sim_layer.
      destruct cl_sim_layer as [Hsim _].
      specialize (Hsim x). rewrite Hlayer in *.
      inv Hsem.
      eapply stencil_matches_unique in H1; try apply H; subst.              
      inv Hsim.
      + (* OK y = get_layer_primitive i L2 *)
        inv H9. inv H10. 
        destruct H9 as [H9 H9sig H9valid H9invs].
        exploit H9; eauto 2.
        (* sprimcall_valid sem2 s = true *)
        specialize (ValidLayer x). simpl in ValidLayer.
        rewrite <- H8 in ValidLayer. specialize (ValidLayer _ refl_equal).
        apply ValidLayer.

        intros [Hsprim[?[?[?[?[Hsem' Hmatch']]]]]].
        refine_split'; eauto.
        eapply exec_step_prim_call; eauto.
        econstructor; eauto.
        refine_split'; eauto.
        econstructor; eauto.
        econstructor; eauto.
      + (* Error msg = get_layer_primitive i L2 *)
        destruct (OKLayer x) as [[σ' Hσ'] _ _].
        simpl in Hσ'.
        congruence.
  Qed.
 
  Lemma one_step_sim_monotonic'_avail {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{names2: !LayerNamesMatch D2 L2}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall `{extcall_inv_avail_prf1: !ExtcallInvariantsAvailable L1},
    forall `{primcall_inv_avail_prf1: !PrimcallInvariantsAvailable L1},
    forall `{extcall_inv_avail_prf2: !ExtcallInvariantsAvailable L2},
    forall `{primcall_inv_avail_prf2: !PrimcallInvariantsAvailable L2},
    forall `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet},
    forall (s: stencil) ge ge' f rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 t, 
    forall (Hglobalenv: exists M, make_globalenv (D:=D2) s M L2 = OK ge'),
    forall (Hge_external': 
              forall b ef, 
                Genv.find_funct_ptr ge' b = Some (External ef) ->
                exists i sg, ef = EF_external i sg),
    forall (OKLayer: LayerOK L2),
    forall (ValidLayer: get_layer_prim_valid L2 s),
      stencil_matches s ge ->
      stencil_matches s ge' ->
      ge ≤ ge' ->
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      high_level_invariant d1 ->
      high_level_invariant d2 ->
      low_level_invariant (Mem.nextblock m2) d2 ->
      asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      (step (lcfg_ops:= LC L1)) 
        ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
      exists f' rs2' m2' d2',
        (step (lcfg_ops:= LC L2)) 
          ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
        /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'
        /\ high_level_invariant d1'
        /\ high_level_invariant d2'
        /\ low_level_invariant (Mem.nextblock m2') d2'
        /\ asm_invariant (mem:= mwd D2) s rs2' (m2', d2').
  Proof.
    intros. 
    pose proof (ge_external_valid_le _ _ Hge_external' H1) as Hge_external.
    exploit (one_step_sim_monotonic s ge ge'); eauto 2.
    intros[?[?[?[?[Hstep Hmatch]]]]].
    pose proof H6 as Hasm.
    eapply (asm_invariant_equiv ge') in H6; eauto.
    pose proof Hstep as Hstep'.
    eapply step_asm_invariant in Hstep; eauto.
    refine_split'; eauto.
    eapply (step_high_level_invariant ge); eauto.
    eapply (step_high_level_invariant ge'); eauto.
    eapply (step_low_level_invariant ge'); eauto.
    eapply asm_invariant_equiv in Hstep; eauto.
  Qed.

  Lemma one_step_sim_monotonic' {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{acc_def_prf2: !AccessorsDefined L2}
        `{names2: !LayerNamesMatch D2 L2}:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall `{extcall_inv_def_prf2: !ExtcallInvariantsDefined L2},
    forall `{primcall_inv_def_prf2: !PrimcallInvariantsDefined L2},
    forall `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet},
    forall (s: stencil) ge ge' f rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 t, 
    forall (Hglobalenv: exists M, make_globalenv (D:=D2) s M L2 = OK ge'),
    forall (Hge_external': 
              forall b ef, 
                Genv.find_funct_ptr ge' b = Some (External ef) ->
                exists i sg, ef = EF_external i sg),
    forall (OKLayer: LayerOK L2),
    forall (ValidLayer: get_layer_prim_valid L2 s),
      stencil_matches s ge ->
      stencil_matches s ge' ->
      ge ≤ ge' ->
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      high_level_invariant d1 ->
      high_level_invariant d2 ->
      low_level_invariant (Mem.nextblock m2) d2 ->
      asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      (step (lcfg_ops:= LC L1)) 
        ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
      exists f' rs2' m2' d2',
        (step (lcfg_ops:= LC L2)) 
          ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
        /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'
        /\ high_level_invariant d1'
        /\ high_level_invariant d2'
        /\ low_level_invariant (Mem.nextblock m2') d2'
        /\ asm_invariant (mem:= mwd D2) s rs2' (m2', d2').
  Proof.
    intros.
    assert (extcall_inv_def_prf1: ExtcallInvariantsDefined L1).
    {
      eapply cl_sim_invs_ext; eassumption.
    }
    assert (primcall_inv_def_prf1: PrimcallInvariantsDefined L1).
    { 
      eapply cl_sim_invs_prim; eassumption.
    }
    apply (one_step_sim_monotonic'_avail s ge ge' f rs1 rs1' m1 m1' d1 d1');
    assumption.
  Qed.

  Lemma plus_step_sim_monotonic {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{names2: !LayerNamesMatch D2 L2}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall `{extcall_inv_def_prf2: !ExtcallInvariantsDefined L2},
    forall `{primcall_inv_def_prf2: !PrimcallInvariantsDefined L2},
    forall `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet},
    forall (s: stencil) ge ge' f rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 t, 
    forall (Hglobalenv: exists M, make_globalenv (D:=D2) s M L2 = OK ge'),
    forall (Hge_external': 
              forall b ef, 
                Genv.find_funct_ptr ge' b = Some (External ef) ->
                exists i sg, ef = EF_external i sg),
    forall (OKLayer: LayerOK L2),
    forall (ValidLayer: get_layer_prim_valid L2 s),
      stencil_matches s ge ->
      stencil_matches s ge' ->
      ge ≤ ge' ->
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      high_level_invariant d1 ->
      high_level_invariant d2 ->
      low_level_invariant (Mem.nextblock m2) d2 ->
      asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      plus (step (lcfg_ops:= LC L1)) 
           ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
      exists f' rs2' m2' d2',
        plus (step (lcfg_ops:= LC L2)) 
             ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
        /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    intros. eapply (plus_step_match_plus s ge ge'); eauto.
    intros. exploit (one_step_sim_monotonic' s ge ge'); eauto.
    intros [?[?[?[?[Hstep Hmatch]]]]].
    repeat_esplit.
    split; eauto.
    apply plus_one; eauto.
  Qed.

  Opaque module_oplus.
  (*
  Lemma one_step_vertical_composition' {D} `{L: compatlayer D}
        (acc_def_prf: AccessorsDefined L) {i: ident} {σi: compatsem D}
        (acc_def_prf': AccessorsDefined (L ⊕ i ↦ σi)):
    forall `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet},
    forall (s: stencil) (ge ge': Genv.t (AST.fundef function) unit)
           (M: module)  (m m': mem) (d d': D) (κi: function) r r' t,
    forall (prim_None: get_layer_primitive i L = OK None),
    forall (extinv: ExtcallInvariantsDefined L),
    forall (priminv: PrimcallInvariantsDefined L),
    forall (valid_prim: get_layer_prim_valid L s),
    forall (mk_prog: isOK(make_program s M L)),
      make_globalenv s M (L ⊕ i ↦ σi) = ret ge
      -> make_globalenv s (M ⊕ i ↦ κi) L = ret ge'
      -> semof_fundef D M L i κi = OK σi
      -> step (lcfg_ops:= LC (L ⊕ i ↦ σi)) ge (State r (m, d)) t (State r' (m', d'))
      -> plus (step (lcfg_ops:= LC L)) ge' 
              (State r (m, d)) t (State r' (m', d')).
  Proof. 
    intros. pose proof H0 as Hge_match'. pose proof H as Hge_match.
    apply make_globalenv_stencil_matches in H0.
    apply make_globalenv_stencil_matches in H.
    pose proof H as Hge. pose proof H0 as Hge'.
    inv H. inv H0.
    assert (Hsymbol: forall i, Genv.find_symbol ge' i = Genv.find_symbol ge i).
    {
      intros; abstract congruence.
    }
    unfold fundef in *.
    assert (Hgenv_next: Genv.genv_next ge' = Genv.genv_next ge).
    {
      intros; abstract congruence.
    }
    assert(Hvolatile: forall b1 : block, block_is_volatile ge' b1 = block_is_volatile ge b1).
    {
      intros; abstract congruence.
    } 

    generalize Hge_match'. intro HgeL_dup.
    eapply make_globalenv_vertical in HgeL_dup; eauto.
    destruct HgeL_dup as [Hinternal [Hext Hext']].

    assert (Hge_external':
              forall b ef, 
                Genv.find_funct_ptr ge b = Some (External ef) ->
                exists i sg, ef = EF_external i sg).
    {
      intros until ef; eapply ge_external_valid; eauto.
    } 

    eapply vcomp_step; try eapply H2; eauto 2; intros.
    - assert(HW: acc_exec_load (L ⊕ i ↦ σi) = acc_exec_load L).
      {
        unfold acc_exec_load.
        destruct (acc_exec_load_strong (L ⊕ i ↦ σi)).
        rewrite cl_exec_load_inL in e.
        destruct (acc_exec_load_strong L). congruence.
      }
      rewrite <- HW.
      erewrite CompatLayers.exec_load_symbols_preserved; eauto.
    - assert(HW': acc_exec_store (L ⊕ i ↦ σi) = acc_exec_store L).
      {
        unfold acc_exec_store.
        destruct (acc_exec_store_strong (L ⊕ i ↦ σi)).
        rewrite cl_exec_store_inL in e.
        destruct (acc_exec_store_strong L). congruence.
      }
      rewrite <- HW'.
      erewrite CompatLayers.exec_store_symbols_preserved; eauto.
    - eapply Hge_external' in H.
      destruct H as [?[? ?]]; subst. inv H0.
    - (* external call *)
      destruct (peq i0 i); subst.
      (* i0 = i *)
      apply get_layer_primitive_right_eq in H0; eauto; subst.
      inv H1. inv H0. 

      (* i0 <> i *)
      split; eauto.
      eapply get_layer_primitive_right_neq; eauto. 
    - (* primitive call *)
      destruct (peq i0 i); subst.
      + (* i0 = i *)
        apply get_layer_primitive_right_eq in H0; eauto; subst.
        specialize (Hext' _ _ H). 
        exploit (compatsem_primcall_le (D:= D)); eauto.
        * econstructor; eauto.
        * inv H1. simpl. intros.
          eapply stencil_matches_unique in H1; try apply Hge. subst.
          destruct (Decision.decide (ExtcallInvariantsDefined L)).
          destruct (Decision.decide (PrimcallInvariantsDefined L)).
          destruct (Decision.decide (get_layer_prim_valid L s1)).
          rewrite accessors_defined_weak; try assumption.
          destruct mk_prog as [? mk_prog].
          unfold fundef.
          rewrite mk_prog. reflexivity.
          elim n; assumption.
          elim n; assumption.
          elim n; assumption.
        * intros Hsem'; inv Hsem'.
          eapply stencil_matches_unique in H6; try apply Hge. subst.
          inv H1; simpl in *. inv H7; simpl in *.
          pose proof Hge0 as Hge0'.
          apply make_globalenv_stencil_matches in Hge0.
          apply make_globalenv_split_module_left in Hge_match'.
          destruct Hge_match' as [?[HgeL' Hle]].
          unfold fundef in *.
          rewrite Hge0' in HgeL'. inv HgeL'.
          eapply one_sim_plus; eauto. intros.
          eapply one_step_monotonic; eauto.
      + (* i0 <> i*)
        eapply stencil_matches_unique in H3; try apply Hge. subst.      
        apply Hext in H; auto.
        apply plus_one. 
        eapply exec_step_prim_call; eauto.
        eapply get_layer_primitive_right_neq in H0; eauto; subst.
        econstructor; eauto.
        refine_split'; eauto.
        econstructor; eauto.
  Qed.*)

Global Instance asm_ptree_sem_prf:
  forall `{memory_model_x: !Mem.MemoryModelX mem},
  forall `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet},
    FunctionSemantics _ _ _ _ module compatlayer.
Proof.
  split.

  - intros D1 D2 R.
    destruct R as [ | D2 R].

  (** (≤)-monotonicity *)
  {
    rename D1 into D.
    intros M1 M2 M_le L1 L2 L_le i f.
    constructor. simpl.
    econstructor; simpl.
    econstructor; simpl; try (constructor; reflexivity).
    econstructor; simpl; [| reflexivity |].
    + intros. 
      (*destruct (Decision.decide (LayerOK L2)); try discriminate.*)
      destruct (Decision.decide (ExtcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (LayerNamesMatch D L2)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L2 s)); try discriminate.
      caseEq (accessors_weak_defined L2); intros; rewrite H0 in H;
      try discriminate.
      rename H0 into Hacc.
      assert (Hmake: isOK (make_program s M2 L2)).
      {
        caseEq (make_program s M2 L2); intros;
        rewrite H0 in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK L2).
      {
        eapply make_program_layer_ok; eauto.
      }
      assert (Hge': exists ge', make_globalenv s M2 L2 = ret ge').
      {
        destruct Hmake as [p' Hmake].
        eapply make_program_make_globalenv in Hmake.
        eauto.
      }
      destruct Hge' as [ge' Hge'].
      inversion_clear 1. 
      specialize (accessors_monotonic_le L_le Hacc acc_def_prf).
      intros acc_def_prf'.
      econstructor; eauto.
            
      eapply one_sim_plus; try eassumption. intros.

      pose proof Hge as Hge_match.
      apply make_globalenv_stencil_matches in Hge.
      pose proof Hge' as Hge_match'.
      apply make_globalenv_stencil_matches in Hge'.
      inv Hge. pose proof Hge' as Hge''. inv Hge'.

      eapply (module_le_step L1 ge ge') in H0; intros; try congruence.
      eapply (layer_le_step L1 L2); try eassumption; intros.
      * inv L_le.
        unfold acc_exec_load in *.
        destruct (acc_exec_load_strong L1).
        destruct (acc_exec_load_strong L2).
        rewrite e0 in cl_sim_load.
        rewrite e1 in cl_sim_load.
        inv cl_sim_load. inv H4.
        simpl in *; subst.
        assumption.
      * inv L_le.
        unfold acc_exec_store in *.
        destruct (acc_exec_store_strong L1).
        destruct (acc_exec_store_strong L2).
        rewrite e0 in cl_sim_store.
        rewrite e1 in cl_sim_store.
        inv cl_sim_store. inv H4.
        simpl in *; subst.
        assumption.
      * eapply stencil_matches_unique in H1; try apply Hge''; subst.              
        assumption.
      * inv L_le. 
        change (freerg_id compatrel D) with (id (A := freerg compatrel D D)) in cl_sim_layer.
        eapply cl_le_layer_pointwise in cl_sim_layer.
        destruct cl_sim_layer as [Hprim _].
        specialize (Hprim i0).
        rewrite H1 in Hprim. inv Hprim. 
        inv H4. simpl; rewrite <- H3. 
        esplit; eauto.

        destruct (OKLayer i0) as [[σ' Hσ'] _ _].
        simpl in *.
        congruence.
      * eapply make_globlenv_monotonic_weak'; eauto.
        assumption.

    + intros.
      (*destruct (Decision.decide (LayerOK L2)); try discriminate.*)
      destruct (Decision.decide (ExtcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (LayerNamesMatch D L2)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L2 s)); try discriminate.
      caseEq (accessors_weak_defined L2); intros; rewrite H0 in H; try discriminate.
      rename H0 into Hacc.
      assert (Hmake: isOK (make_program s M2 L2)).
      {
        caseEq (make_program s M2 L2); intros;
        rewrite H0 in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK L2).
      {
        eapply make_program_layer_ok; eauto.
      }
      destruct Hmake as [pr Hmake].
      destruct (Decision.decide (ExtcallInvariantsDefined L1)).
      destruct (Decision.decide (PrimcallInvariantsDefined L1)).
      destruct (Decision.decide (LayerNamesMatch D L1)).
      destruct (Decision.decide (get_layer_prim_valid L1 s)).      
      erewrite accessors_monotonic_weak_le; try eassumption.

      * destruct (make_program_monotonic_exists (L1:=L1) (L2:=L2) M1 M2 s pr); eauto 1.
        rewrite H0. reflexivity.
      * elim n.
        eapply (cl_le_get_layer_prim_valid _ L_le); try eassumption.
      * elim n.
        rewrite L_le.
        assumption.
      * (* Instance of PrimcallInvariantsDefined L1*)
        elim n.
        eapply (cl_le_invs_prim _ L_le); eassumption.
      * (* Instance of ExtcallInvariantsDefined L1*)
        elim n.
        eapply (cl_le_invs_ext _ L_le); eassumption.
  }

  (** sim-monotonicity *)
  {
    intros M1 M2 Hle.
    intros L1 L2 Hsim.
    intros id func.
    constructor. simpl.
    constructor.
    split; try constructor; simpl in *.

    + intros. inv H. pose proof H0 as Hmatch. inv H0.
      destruct (Decision.decide (ExtcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (LayerNamesMatch D2 L2)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L2 s)); try discriminate.
      caseEq (accessors_weak_defined L2); intros; rewrite H in *;
      try discriminate.
      rename H into Hacc.

      assert (Hmake: isOK (make_program s M2 L2)).
      {
        caseEq (make_program s M2 L2); intros;
        rewrite H in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK L2).
      {
        eapply make_program_layer_ok; eauto.
      }
      assert (Hge': exists ge', make_globalenv s M2 L2 = ret ge').
      {
        destruct Hmake as [p' Hmake].
        eapply make_program_make_globalenv in Hmake.
        eauto.
      }
      destruct Hge' as [ge' Hge'].
      exploit (make_globlenv_monotonic_weak (L1:= L1) (L2:= L2)); eauto.
      intros Hle_ge.
      assert (Hpc: rs2 PC = Vptr b Int.zero).
      {
        inv match_extcall_states.
        eapply reg_symbol_inject; eassumption.
      }
      apply make_globalenv_stencil_matches in Hge.
      pose proof Hge' as Hge''.
      apply make_globalenv_stencil_matches in Hge'.
      pose proof (accessors_monotonic_sim Hsim Hacc acc_def_prf) as acc_def_prf'.

      (* valid external ge, should be proved somewhere else *)
      assert (Hge_external':
                forall b ef, 
                  Genv.find_funct_ptr ge' b = Some (External ef) ->
                  exists i sg, ef = EF_external i sg) by
          (intros until ef; eapply ge_external_valid; eauto).

      exploit (plus_step_sim_monotonic s ge ge'); eauto.
      intros [?[?[?[?[Hplus Hmatch']]]]].
      repeat_esplit; eauto.
      split; eauto.
      econstructor; eauto.

    + intros.
      destruct (Decision.decide (ExtcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L2)); try discriminate.
      destruct (Decision.decide (LayerNamesMatch D2 L2)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L2 s)); try discriminate.
      caseEq (accessors_weak_defined L2); intros; rewrite H0 in *;
      try discriminate.
      rename H0 into Hacc.

      assert (Hmake: isOK (make_program s M2 L2)).
      {
        caseEq (make_program s M2 L2); intros;
        rewrite H0 in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK L2).
      {
        eapply make_program_layer_ok; eauto.
      }
      destruct Hmake as [p' Hmake].
      destruct (Decision.decide (ExtcallInvariantsDefined L1)).
      destruct (Decision.decide (PrimcallInvariantsDefined L1)).
      destruct (Decision.decide (LayerNamesMatch D1 L1)).
      destruct (Decision.decide (get_layer_prim_valid L1 s)).      
      erewrite accessors_monotonic_weak_sim; try eassumption.

      * destruct (make_program_sim_monotonic_exists (L1:=L1) (L2:=L2) M1 M2 s p'); eauto 1.
        rewrite H0. reflexivity.
      * elim n.
        eapply cl_sim_get_layer_prim_valid; eassumption.
      * elim n.
        apply (layer_names_match_sim D2 D1 _ L2 L1 Hsim).
        assumption.
      * (* Instance of PrimcallInvariantsDefined L1*)
        elim n.
        eapply cl_sim_invs_prim; eassumption.
      * (* Instance of ExtcallInvariantsDefined L1*)
        elim n.
        eapply cl_sim_invs_ext; eassumption.
    + reflexivity.
  }

  (** vertical composition *)
  (*
  - intros D M L i κi σi j κj HiL HiV Hσi.
    Opaque oplus mapsto.
    econstructor.
    econstructor; simpl.
    econstructor; simpl; [| constructor; reflexivity]. 
    econstructor; simpl; [ | reflexivity |]. 
    + intros s Hs.
      inversion 1. 

      exploit (AccessorsDefined_oplus (D:=D) (L:=L)); try eassumption.
      intros acc_def_prf'.

      pose proof Hge as HgeL.
      simpl in *.
      destruct (Decision.decide (ExtcallInvariantsDefined L)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L s)); try discriminate.
      caseEq (accessors_weak_defined L); intros; rewrite H0 in *;
      try discriminate.
      rename H0 into Hacc.

      assert (Hmake: isOK (make_program s (M ⊕ i ↦ κi) L)).
      {
        caseEq (make_program s (M ⊕ i ↦ κi) L); intros;
        rewrite H0 in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK L).
      {
        eapply make_program_layer_ok; eauto.
      }
      assert (Hge': exists ge', make_globalenv s (M ⊕ i ↦ κi) L = ret ge').
      {
        destruct Hmake as [p' Hmake].
        eapply make_program_make_globalenv in Hmake.
        eauto.
      }
      destruct Hge' as [ge' Hge'].
      generalize Hge'. intro HgeL_dup.
      eapply make_globalenv_vertical in HgeL_dup; eauto.
      econstructor; eauto.
      eapply plus_sim_plus; eauto.
      intros. destruct m, m'.
      eapply (one_step_vertical_composition' _ _ s ge ge' M); eauto.
      destruct Hmake as [? Hmake].
      eapply make_program_monotonic_exists; try eassumption; try reflexivity.
      apply left_upper_bound.

    + (* sprimcall_valid *)
      simpl. intros.
      destruct (Decision.decide (ExtcallInvariantsDefined L)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined L)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid L s)); try discriminate. 
      caseEq (accessors_weak_defined L); intros; rewrite H0 in *;
      try discriminate.
      rename H0 into Hacc.

      assert (Hmake: isOK (make_program s (M ⊕ i ↦ κi) L)).
      {
        caseEq (make_program s (M ⊕ i ↦ κi) L); intros;
        rewrite H0 in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK L).
      {
        eapply make_program_layer_ok; eauto.
      }
      specialize (layer_oplus_primitive_ok (D:= D) _ _ σi HiL HiV OKLayer).
      intros HlayerOK. 
      pose proof Hσi as Hfundef.
      inv Hσi.
      destruct Hmake as [p' Hmake].        
      destruct (Decision.decide
                  (ExtcallInvariantsDefined (L ⊕ i ↦ lasm_primsem M L i κi))).
      destruct (Decision.decide
                  (PrimcallInvariantsDefined (L ⊕ i ↦ lasm_primsem M L i κi))).
      destruct (Decision.decide
                  (get_layer_prim_valid (L ⊕ i ↦ lasm_primsem M L i κi) s)).
      Transparent layer_oplus mapsto.
      specialize (accessors_weak_oplus i M κi Hacc).
      simpl. intros Hacc'. rewrite Hacc'.

      * edestruct make_program_vertical as [p'' Hp]; try eassumption.
        simpl in Hp.
        rewrite Hp. reflexivity.
      * elim n.
        exploit make_program_vertical; eauto 2.
        intros Hprogram.
        assert (Hom: isOK (make_program s M L)).
        {
          eapply make_program_le; eauto 2.
        }
        destruct Hom as [p'' Hom].
        eapply (layer_oplus_prim_valid (accessors_def:= Hacc)); eauto.
      * elim n.
        eapply layer_oplus_invs_prim; eassumption.
      * elim n.
        eapply layer_oplus_invs_ext; eassumption.
  *)
Qed.

Global Instance lasm_semantics_ops:
  SemanticsOps _ _ _ _ module compatlayer :=
  compat_semantics_ops.


Global Instance lasm_semantics:
  forall `{memory_model_x: !Mem.MemoryModelX mem},
  forall `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet},
  Semantics ident function compatsem (globvar Ctypes.type) module compatlayer.
Proof.
  intros.
  apply compat_semantics_prf.
Qed.

End ModuleSemantics.
