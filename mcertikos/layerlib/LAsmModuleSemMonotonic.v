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
Require Import LAsmModuleSemDef.
Require Import Observation.

(** ** Monotonic lemmas of LAsm modules *)

Section ModuleSemantics_Monotonic.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.
 
  Lemma exec_load_sim_monotonic {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall {F V} (ge ge': Genv.t F V) (s: stencil) f rs1 m1 d1 rs2 m2 d2, 
      stencil_matches s ge -> 
      stencil_matches s ge' -> 
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      high_level_invariant d1 ->
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      forall rs1' m1' d1' rd chunk a,
        (acc_exec_load L1) F V ge chunk (m1, d1) a rs1 rd = Next rs1' (m1', d1') ->
        exists f' rs2' m2' d2',
          (acc_exec_load L2) F V ge' chunk (m2, d2) a rs2 rd = Next rs2' (m2', d2') 
          /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    intros. inv H1.
    unfold acc_exec_load in *.
    destruct (acc_exec_load_strong (acc_def:= acc_def_prf1) L1).
    destruct x. simpl in *.
    destruct (acc_exec_load_strong (acc_def:= acc_def_prf2) L2).
    rewrite e, e0 in cl_sim_load.
    inv cl_sim_load. inv H6.
    pose proof H3 as Hmatch.
    inv H3. exists f.
    exploit (H7 _ _ ge ge'); eauto.
    val_inject_simpl.    
  Qed.
  
  Lemma exec_store_sim_monotonic {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall {F V} (ge ge': Genv.t F V) (s: stencil) f rs1 m1 d1 rs2 m2 d2, 
      stencil_matches s ge -> 
      stencil_matches s ge' -> 
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      high_level_invariant d1 ->
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      forall rs1' m1' d1' rd chunk a rl,
        (acc_exec_store L1) F V ge chunk (m1, d1) a rs1 rd rl = Next rs1' (m1', d1') ->
        exists f' rs2' m2' d2',
          (acc_exec_store L2) F V ge' chunk (m2, d2) a rs2 rd rl = Next rs2' (m2', d2') 
          /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    intros. inv H1.
    unfold acc_exec_store in *.
    destruct (acc_exec_store_strong (acc_def:= acc_def_prf1) L1).
    destruct x; simpl in *.
    destruct (acc_exec_store_strong (acc_def:= acc_def_prf2) L2).
    rewrite e, e0 in cl_sim_store.
    inv cl_sim_store. inv H6.
    pose proof H3 as Hmatch.
    inv H3. exists f.
    exploit (H7 _ _ ge ge'); eauto.
    val_inject_simpl.    
  Qed.

  Lemma goto_label_sim_monotonic {D1: compatdata} {D2: compatdata}
        {R: compatrel D1 D2}:
    forall (s: stencil) f rs1 m1 d1 rs2 m2 d2 b ofs, 
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      rs1 PC = Vptr b ofs -> 
      f b = Some (b, 0%Z) ->
      forall rs1' m1' d1' f0 l,
        goto_label (Hfl:= FindLabels_instance_0) f0 l rs1 (m1, d1) = 
        Next (mem:= mwd D1) rs1' (m1', d1') ->
        exists f' rs2' m2' d2',
          goto_label (Hfl:= FindLabels_instance_0) f0 l rs2 (m2, d2)
          = Next (mem:= mwd D2) rs2' (m2', d2') 
          /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    unfold goto_label; intros.
    destruct (label_pos l 0 (fn_code f0)); try discriminate.
    inv H. rewrite H0 in H2. inv H2.
    pose proof (match_reg PC) as Hmatch.
    unfold Pregmap.get in Hmatch.
    rewrite H0 in Hmatch. inv Hmatch.
    rewrite H4 in H1. inv H1. 
    refine_split'; eauto.
    econstructor; eauto.
    val_inject_simpl.      
    econstructor; eauto.
    rewrite Int.add_zero. reflexivity.
  Qed.

  Lemma exec_instr_sim_monotonic {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall ge (s: stencil) f rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 f0 i b ofs ef, 
      (exec_instr (lcfg_ops:= LC L1)) ge f0 i rs1 (m1, d1) = Next rs1' (m1', d1') ->
      stencil_matches s ge -> 
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      high_level_invariant d1 ->
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      rs1 PC = Vptr b ofs -> 
      Genv.find_funct_ptr ge b = Some ef ->
      exists f' rs2' m2' d2',
        (exec_instr (lcfg_ops:= LC L2)) ge f0 i rs2 (m2, d2) = Next rs2' (m2', d2') 
        /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    intros. unfold exec_instr in *.
    pose proof (exec_load_sim_monotonic _ _ _ _ _ _ _ _ _ _ H0 H0 H1 H2 H3) as Hload.  
    pose proof (exec_store_sim_monotonic _ _ _ _ _ _ _ _ _ _ H0 H0 H1 H2 H3) as Hstore.
    pose proof (stencil_symbol_offset_inject _ _ match_inject_flat H0) as Hsymbol.
    pose proof H3 as Hmatch. inv H3.
    destruct i;
      match goal with
          | [|- context[exec_loadex _ _ _ _ _ _]] => simpl in *; eapply Hload; eauto 1
          | [|- context[exec_storeex _ _ _ _ _ _ _]] => simpl in *; eapply Hstore; eauto 1
          | [|- context[Asm.exec_instr _ _ _ _ _]] => idtac
          | [HW: _ = Next _ _ |- _]=> 
            inv HW; exists f; refine_split'; eauto;
            try econstructor; eauto; val_inject_simpl
      end.
    pose proof (val_compare_ints_inject_neutral _ _ _ _ _ match_reg match_inject) as Hcompare_ints.
    pose proof (eval_testcond_inject _ _ _ match_reg) as Htestcond.
    pose proof match_extcall_states as Hmatch'. inv Hmatch'.
    assert(HFB: f b = Some (b, 0%Z)).
    {
      eapply flat_inj_func in H5; eauto.
      eapply match_inject_flat.
      inv H0. congruence.
    }
    pose proof (goto_label_sim_monotonic _ _ _ _ _ _ _ _ _ _ Hmatch H4 HFB) as Hgoto_label.
    
    destruct i; inv H; simpl;
    lazymatch goal with
      | [|- context[(acc_exec_load _)]] => eapply Hload; eauto 1
      | [|- context[(acc_exec_store _)]] => eapply Hstore; eauto 1
      | _ => clear Hstore Hload
    end;
    repeat lazymatch goal with
             | [|- context[eval_testcond ?c rs2]] => 
               let J:= fresh in
               pose proof (Htestcond c) as J; destruct (eval_testcond c rs1) as [[|] |];
               [rewrite (J _ refl_equal)| rewrite (J _ refl_equal)| 
                try discriminate; destruct (eval_testcond c rs2) as [[|] |]];
               try match goal with
                     |[HW: _ = Next _ _ |- _] => inv HW
                   end
             | [|- context[goto_label _ _ _ _ ]] => 
               eapply Hgoto_label; eauto 1
           end;
    try(refine_split'; eauto; try econstructor; eauto; val_inject_simpl;
        lazymatch goal with
          | [|- context[compare_ints _ _ _ _ _]] => 
            apply Hcompare_ints; val_inject_simpl
                               | [|- context[eval_addrmode _ _ _ ]] => eapply eval_addrmode_correct; eauto
        end; fail).

    - (* unsigned division *)
      case_eq (Val.divu (rs1 EAX) (rs1 # EDX <- Vundef r1)); intros;
      rewrite H in H6; try discriminate.
      case_eq (Val.modu (rs1 EAX) (rs1 # EDX <- Vundef r1)); intros;
      rewrite H3 in H6; try discriminate.

      eapply val_divu_inject in H; val_inject_simpl.
      destruct H as [v'[Hdiv' Hinj']]. rewrite Hdiv'.
      eapply val_modu_inject in H3; val_inject_simpl.
      destruct H3 as [v''[Hmod' Hinj'']]. rewrite Hmod'.
      inv H6. refine_split'; eauto. 
      econstructor; eauto. val_inject_simpl.

    - (* signed division *)
      case_eq (Val.divs (rs1 EAX) (rs1 # EDX <- Vundef r1)); intros;
      rewrite H in H6; try discriminate.
      case_eq (Val.mods (rs1 EAX) (rs1 # EDX <- Vundef r1)); intros;
      rewrite H3 in H6; try discriminate.

      eapply val_divs_inject in H; val_inject_simpl.
      destruct H as [v'[Hdiv' Hinj']]. rewrite Hdiv'.
      eapply val_mods_inject in H3; val_inject_simpl.
      destruct H3 as [v''[Hmod' Hinj'']]. rewrite Hmod'.
      inv H6. refine_split'; eauto. 
      econstructor; eauto. val_inject_simpl.

    - refine_split'; eauto.
      econstructor; eauto; val_inject_simpl.
      intros. destruct (Pregmap.elt_eq r rd); subst.
      rewrite Pregmap.gss. constructor.
      rewrite Pregmap.gso; eauto.

    - (* switch *) 
      pose proof (match_reg r) as Hmatch'.
      unfold Pregmap.get in Hmatch'.
      destruct (rs1 r); try discriminate. inv Hmatch'.
      subdestruct. eauto.

    - (* Pallocframe *)
      lift_unfold. simpl in *.
      case_eq (Mem.alloc m1 0 sz); intros; rewrite H in H6; simpl in H6.
      case_eq (Mem.store Mint32 m b0 (Int.unsigned (Int.add Int.zero ofs_link)) (rs1 ESP));
        intros; rewrite H3 in H6; contra_inv; simpl in H6.
      case_eq(Mem.store Mint32 m0 b0 (Int.unsigned (Int.add Int.zero ofs_ra)) (rs1 RA));
        intros; rewrite H7 in H6; contra_inv; simpl in H6. inv H6.
      exploit Mem.alloc_parallel_inject; try eapply Zle_refl; eauto.
      intros [f' [m2' [b2[HAL1[HINJ1 [HINCR1 [HF1 HBB1]]]]]]].
      setoid_rewrite HAL1.
      assert (HVJ: forall reg, val_inject f' (Pregmap.get reg rs1) (Pregmap.get reg rs2)).
      {
        intros; eapply val_inject_incr; eauto.
      }          
      exploit Mem.store_mapped_inject; eauto.
      intros [n2 [HST2 HINJ2]].
      rewrite Z.add_0_r in HST2. setoid_rewrite HST2.
      exploit Mem.store_mapped_inject; eauto.
      intros [n3 [HST3 HINJ3]].
      rewrite Z.add_0_r in HST3. setoid_rewrite HST3.
      unfold set; simpl. refine_split'; eauto. 
      econstructor; val_inject_simpl.
      assert(Hsym_not: forall i b, In i new_glbl -> find_symbol s i = Some b -> b <> b0).
      { 
        red; intros; subst. exploit match_newglob_nextblock; eauto.
        eapply Mem.alloc_result in H. rewrite H. xomega.
      }
      econstructor; eauto.
         
      * eapply relate_incr; eauto.
      * assert(Hsym_not': forall i b, In i new_glbl -> find_symbol s i = Some b -> b <> b2).
        { 
          red; intros; subst. exploit match_newglob_nextblock; eauto.
          eapply Mem.alloc_result in HAL1. rewrite HAL1. xomega.
        }
        eapply store_match_correct; eauto.
        eapply store_match_correct; eauto.
        eapply alloc_match_correct; eauto.
      * eapply inject_incr_trans; eauto.
      * intros. destruct (peq b1 b0); subst.
        rewrite H6 in HF1. inv HF1.
        split; trivial. eapply Mem.alloc_result in H.
        eapply Mem.alloc_result in HAL1. rewrite H, HAL1. trivial.
        eapply match_inject_forward; eauto.
        rewrite <- HBB1; auto.
      * erewrite Mem.nextblock_store; eauto.
        erewrite Mem.nextblock_store; eauto.
        erewrite Mem.nextblock_alloc; eauto.
        rewrite (Mem.nextblock_store _ _ _ _ _ _ HST3).
        rewrite (Mem.nextblock_store _ _ _ _ _ _ HST2).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ HAL1).
        xomega.
      * red; intros. exploit match_newglob_noperm; eauto.
        eapply (Mem.perm_store_2 _ _ _ _ _ _ H7) in H9; eauto.
        eapply (Mem.perm_store_2 _ _ _ _ _ _ H3) in H9; eauto.
        eapply Mem.perm_alloc_4; eauto.
      * intros. exploit match_newglob_nextblock; eauto.
        intros Hlt.
        rewrite (Mem.nextblock_store _ _ _ _ _ _ H7).
        rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ H).
        xomega.

    - (* Pfreeframe *)
      lift_unfold. simpl in *.
      case_eq (Mem.loadv (mem:= mwd D1) Mint32 (m1, d1) (Val.add (rs1 ESP) (Vint ofs_ra))); intros;
      rewrite H in H6; contra_inv; simpl in H6.
      case_eq (Mem.loadv (mem:= mwd D1) Mint32 (m1, d1) (Val.add (rs1 ESP) (Vint ofs_link))); intros;
      rewrite H3 in H6; contra_inv; simpl in H6.
      assert (HVJ1:val_inject f (Val.add (rs1 ESP) (Vint ofs_ra))  (Val.add (rs2 ESP) (Vint ofs_ra)))
        by val_inject_simpl.
      specialize (Mem.loadv_inject _ _ _ _ _ _ _ match_inject H HVJ1).
      intros [v2[ HLD1 HINJ1]]. setoid_rewrite HLD1.
      assert (HVJ2:val_inject f (Val.add (rs1 ESP) (Vint ofs_link))  (Val.add (rs2 ESP) (Vint ofs_link)))
        by val_inject_simpl.
      specialize(Mem.loadv_inject _ _ _ _ _ _ _ match_inject H3 HVJ2).
      intros[v3[ HLD2 HINJ2]]. setoid_rewrite HLD2.
      pose proof (match_reg ESP) as Hval. unfold Pregmap.get in Hval.
      destruct (rs1 ESP); contra_inv. inv Hval.
      case_eq(Mem.free m1 b0 0 sz); intros; rewrite H7 in H6; contra_inv. inv H6.
      exploit match_inject_forward; eauto. intros [? _]; subst.
      specialize (MemEx.free_parallel_inject _ _ _ _ _ _ _ _ _ match_inject H10 H7).
      intros [m2' [HFREE3 HINJ3]].
      repeat rewrite Z.add_0_r in HFREE3. setoid_rewrite HFREE3.
      unfold set; simpl. exists f. refine_split'; eauto.
      econstructor; eauto; val_inject_simpl.
      econstructor; eauto.
      * exploit Mem.free_range; eauto.
        intros HF; inv HF; trivial.
        eapply free_match_correct; eauto.
        red; intros; subst.
        exploit inject_forward_equal; eauto.
        intros HF; inv HF.
        exploit match_newglob_noperm; eauto.
        eapply Mem.free_range_perm; eauto.
        instantiate (1:= 0%Z). omega.
      * erewrite Mem.nextblock_free; eauto.
        rewrite (Mem.nextblock_free _ _ _ _ _ HFREE3); eauto.
      * red; intros. exploit match_newglob_noperm; eauto.
        eapply Mem.perm_free_3; eauto.
      * erewrite Mem.nextblock_free; eauto.
  Qed.

  Lemma volatile_store_sim_monotonic {D1: compatdata} {D2: compatdata}
        {R: compatrel D1 D2}:
    forall {F V} (ge: Genv.t F V) s f m1 m2 m1' d1 d2 chunk t b b' ofs ofs' v v',
      stencil_matches s ge ->
      MatchExtcallStates R s f m1 d1 m2 d2 ->
      volatile_store (fun b => True) ge chunk m1 b ofs v t m1' ->
      val_inject f v v' ->
      val_inject f (Vptr b ofs) (Vptr b' ofs') ->
      exists m2',
        volatile_store (fun b => True) ge chunk m2 b' ofs' v' t m2'
        /\ MatchExtcallStates R s f m1' d1 m2' d2.
  Proof.
    intros. pose proof H0 as Hmatch. inv H0.
    exploit volatile_store_inject; eauto.
    - eapply meminj_preserves_globals_incr; eauto 1.
    - instantiate (1:= fun b => True). trivial.
    - intros [?[Hst' [Hinj'[Hun1 Hun2]]]].
      refine_split'; eauto.
      inv H1; inv Hst'; trivial.
      econstructor; eauto.
      + eapply store_match_correct; eauto.
        red; intros; subst. inv H3.
        eapply match_newglob_noperm; eauto.
        eapply inject_forward_equal in H7; eauto.
        inv H7. eapply Mem.store_valid_access_3 in H4.
        eapply H4. instantiate (1:= Int.unsigned ofs).
        destruct chunk; simpl; omega.
      + erewrite Mem.nextblock_store; eauto.
        rewrite (Mem.nextblock_store _ _ _ _ _ _ H5); eauto.
      + red; intros.       
        eapply match_newglob_noperm; eauto.
        eapply Mem.perm_store_2; eauto.
      + erewrite Mem.nextblock_store; eauto.
  Qed.

  Lemma external_call_sim_monotonic {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall {F V} (ge: Genv.t F V) s ef
           args args' m1 m1' m2 t vl d1 d1' d2 f
           (BUILTIN_ENABLED : match ef with
                                | EF_external _ _ => False
                                | _ => True
                              end),
      external_call' (mem:= mwd D1)
                     (external_calls_ops:= (compatlayer_extcall_ops L1))
                     (fun b => True) ef ge args (m1, d1) t vl (m1', d1') ->
      stencil_matches s ge ->
      MatchExtcallStates R s f m1 d1 m2 d2 ->
      high_level_invariant d1 ->
      val_list_inject f args args' ->
      exists f' m2' d2' vl',
        external_call' (mem:= mwd D2) 
                       (external_calls_ops:= (compatlayer_extcall_ops L2))
                       (fun b => True) ef ge args' (m2, d2) t vl' (m2', d2')
        /\ MatchExtcallStates R s f' m1' d1' m2' d2'
        /\ inject_incr f f'
        /\ val_list_inject f' vl vl'.
  Proof.
    intros. rename H1 into match_extcall_states.
    rename H3 into Hval.

    Opaque decode_longs encode_long.
    destruct ef; inv BUILTIN_ENABLED;
    inv H; simpl in *;
    match goal with
      | [H: context[decode_longs ?a _] |- _] =>
        eapply (decode_longs_inject a) in Hval
      | _ => idtac
    end.
  - (* builtin_functions *)
    inv H1;
    rewrite <- H3 in Hval; inv_val_inject;
    refine_split'; eauto;
    match goal with
      | [|- context[val_list_inject _ _ _]] =>
        eapply encode_long_inject; eauto
      | _ => econstructor; eauto; simpl;
             rewrite <- H4
    end.
    eapply builtin_sem_i64_neg; eauto.
    eapply val_negl_inject; eauto.
    eapply builtin_sem_i64_add; eauto.
    eapply val_addl_inject; eauto.
    eapply builtin_sem_i64_sub; eauto.
    eapply val_subl_inject; eauto.
    eapply builtin_sem_i64_mul; eauto.
    eapply val_mull'_inject; eauto.

  - (* volatile load*)
    inv H1. rewrite <- H in Hval.
    inv Hval. inv H6.
    destruct v'; try(inv H5; fail).
    exploit (volatile_load_without_d (D:= D1) ge); eauto.
    intros Hld. clear H7.
    pose proof match_extcall_states as Hmatch.
    inv match_extcall_states.    
    exploit volatile_load_inject; eauto.
    eapply meminj_preserves_globals_incr; eauto 1.
    intros [?[Hld' Hinj']].
    refine_split'; eauto.
    econstructor; eauto.
    simpl. rewrite <- H4.
    econstructor; eauto.
    eapply volatile_load_with_d; eauto.
    eapply encode_long_inject; eauto.

  - (* volatile store *)
    inv H1. rewrite <- H in Hval.
    inv_val_inject.
    destruct v'; try(inv H6; fail).
    exploit (volatile_store_without_d (D:= D1) ge); eauto.
    intros [Hld ?]; subst. clear H3.
    pose proof match_extcall_states as Hmatch.
    inv match_extcall_states.
    exploit (volatile_store_sim_monotonic ge); eauto.
    intros [?[Hst' Hmatch']].
    refine_split'; eauto.
    econstructor; eauto.
    simpl. rewrite <- H5.
    econstructor; eauto.
    eapply volatile_store_with_d; eauto.
    eapply encode_long_inject; eauto.

  - (* volatile load global *)
    inv H1.
    exploit (volatile_load_without_d (D:= D1) ge); eauto.
    intros Hld. clear H8.
    pose proof match_extcall_states as Hmatch.
    inv match_extcall_states.        
    exploit (stencil_find_symbol_inject (ge:= ge)); eauto.
    intros HFB.
    assert (Hinj: val_inject f (Vptr b ofs) (Vptr b ofs)).
    {
      econstructor; eauto. rewrite Int.add_zero. trivial.
    }
    exploit volatile_load_inject; eauto.
    eapply meminj_preserves_globals_incr; eauto 1.
    intros [?[Hld' Hinj']].
    refine_split'; eauto.
    econstructor; eauto.
    simpl. econstructor; eauto.
    eapply volatile_load_with_d; eauto.
    eapply encode_long_inject; eauto.

  - (* volatile store global *)
    inv H1. rewrite <- H in Hval.
    inv_val_inject.
    exploit (volatile_store_without_d (D:= D1) ge); eauto.
    intros [Hld ?]; subst. clear H4.
    pose proof match_extcall_states as Hmatch.
    inv match_extcall_states.
    exploit (stencil_find_symbol_inject (ge:= ge)); eauto.
    intros HFB.
    assert (Hinj: val_inject f (Vptr b ofs) (Vptr b ofs)).
    {
      econstructor; eauto. rewrite Int.add_zero. trivial.
    }
    exploit (volatile_store_sim_monotonic ge); eauto.
    intros [?[Hst' Hmatch']].
    refine_split'; eauto.
    econstructor; eauto.
    simpl. rewrite <- H6.
    econstructor; eauto.
    eapply volatile_store_with_d; eauto.
    eapply encode_long_inject; eauto.

  - (* malloc *)
    inv H1. rewrite <- H in Hval.
    inv_val_inject. destruct m'. lift_unfold.
    destruct H3 as [? Hstore]; subst.
    destruct H4 as [? Halloc]; subst.
    inv match_extcall_states.
    exploit Mem.alloc_parallel_inject; try eapply Zle_refl; eauto.
    intros [f' [m2' [b2[Halloc1[HINJ1 [HINCR1 [HF1 HBB1]]]]]]].
    exploit Mem.store_mapped_inject; eauto.
    intros [n2 [HST2 HINJ2]].
    rewrite Z.add_0_r in HST2. 
    refine_split'; eauto.
    econstructor; eauto.
    simpl. rewrite <- H6.
    econstructor; eauto. 
    lift_simpl. instantiate (1:= (m2', d2)). 
    split; eauto.
    lift_simpl. eauto. 
    assert(Hsym_not: forall i b0, In i new_glbl -> find_symbol s i = Some b0 -> b0 <> b).
    { 
      red; intros; subst. exploit match_newglob_nextblock; eauto.
      eapply Mem.alloc_result in H1. rewrite H1. xomega.
    }
    econstructor; eauto.         
    * eapply relate_incr; eauto.
    * assert(Hsym_not': forall i b0, In i new_glbl -> find_symbol s i = Some b0 -> b0 <> b2).
      { 
        red; intros; subst. exploit match_newglob_nextblock; eauto.
        eapply Mem.alloc_result in Halloc1. rewrite Halloc1. xomega.
      }
      eapply store_match_correct; eauto.
      eapply alloc_match_correct; eauto.
    * eapply inject_incr_trans; eauto.
    * intros. destruct (peq b1 b); subst.
      rewrite H4 in HF1. inv HF1.
      split; trivial. eapply Mem.alloc_result in H1.
      eapply Mem.alloc_result in Halloc1. rewrite H1, Halloc1. trivial.
      eapply match_inject_forward; eauto.
      rewrite <- HBB1; auto.
    * erewrite Mem.nextblock_store; eauto.
      erewrite Mem.nextblock_alloc; eauto.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ HST2).
      rewrite (Mem.nextblock_alloc _ _ _ _ _ Halloc1).
      xomega.
    * red; intros. exploit match_newglob_noperm; eauto.
      eapply (Mem.perm_store_2 _ _ _ _ _ _ H3) in H7; eauto.
      eapply Mem.perm_alloc_4; eauto.
    * intros. exploit match_newglob_nextblock; eauto.
      intros Hlt.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H3).
      rewrite (Mem.nextblock_alloc _ _ _ _ _ H1).
      xomega.
    * eapply encode_long_inject; eauto.

  - (* mfree *)
    inv H1. rewrite <- H in Hval.
    inv_val_inject. lift_unfold.
    destruct H5 as [? Hfree]; subst.
    inv match_extcall_states.
    exploit match_inject_forward; eauto.
    intros [? _]; subst.
    exploit Mem.load_inject; eauto.
    rewrite Z.add_0_r.
    intros [v2[ HLD1 HINJ1]]. inv HINJ1.
    exploit MemEx.free_parallel_inject; eauto.
    repeat rewrite Z.add_0_r.
    intros [m2' [HFREE3 HINJ3]].
    refine_split'; eauto.
    econstructor; eauto.
    simpl. rewrite <- H7. rewrite Int.add_zero.
    econstructor; eauto. 
    lift_simpl. eauto. 
    econstructor; eauto.
    * exploit Mem.free_range; eauto.
      intros HF; inv HF; trivial.
      eapply free_match_correct; eauto.
      red; intros; subst.
      exploit inject_forward_equal; eauto.
      intros HF; inv HF.
      exploit match_newglob_noperm; eauto.
      eapply Mem.free_range_perm; eauto.
      instantiate (1:= (Int.unsigned lo - 4)%Z). omega.
    * erewrite Mem.nextblock_free; eauto.
      rewrite (Mem.nextblock_free _ _ _ _ _ HFREE3); eauto.
    * red; intros. exploit match_newglob_noperm; eauto.
      eapply Mem.perm_free_3; eauto.
    * erewrite Mem.nextblock_free; eauto.
    * eapply encode_long_inject; eauto.

  - (* memcpy *)
    inv H1. rewrite <- H in Hval.
    inv_val_inject. lift_unfold.
    destruct H10 as [Hst ?]; subst.
    pose proof match_extcall_states as Hmatch.
    inv match_extcall_states.
    destruct (match_inject_forward _ _ _ H14) as [? _]; subst.
    destruct (match_inject_forward _ _ _ H15) as [? _]; subst.
    repeat rewrite Int.add_zero in *.
    destruct (zeq sz 0).
    + (* sz = 0*) 
      subst.
      assert (bytes = nil). 
      { exploit (Mem.loadbytes_empty m1 bsrc (Int.unsigned osrc) 0). omega. congruence. }
      subst.
      destruct (Mem.range_perm_storebytes m2 b0 (Int.unsigned odst) nil) as [m2' SB].
      simpl. rewrite Z.add_0_r. intros i. omega.
      exploit Mem.storebytes_empty_inject; eauto. intros Hinj'.
      specialize (storebytes_empty _ _ _ _ Hst).
      specialize (storebytes_empty _ _ _ _ SB).
      intros; subst.
      refine_split'; eauto.
      econstructor; eauto.
      simpl. rewrite <- H12.
      econstructor; eauto. 
      right; right. omega.
      apply Mem.loadbytes_empty. omega. 
      lift_simpl. eauto.
      eapply encode_long_inject; eauto.
    + (* sz > 0 *)
      specialize (Mem.loadbytes_length _ _ _ _ _ H9). intros LEN.
      exploit Mem.loadbytes_inject; eauto.
      intros [?[Hld Hlist]].
      exploit Mem.storebytes_mapped_inject; eauto.
      intros[?[Hst' Hinj']].
      rewrite Z.add_0_r in *. 
      refine_split'; eauto.
      econstructor; eauto.
      simpl. rewrite <- H12.
      econstructor; eauto. 
      assert (RPSRC: Mem.range_perm m1 bsrc (Int.unsigned osrc) (Int.unsigned osrc + sz) Max Nonempty).
      {
        apply Mem.range_perm_max with Cur.
        eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. constructor.
      }
      assert (RPDST: Mem.range_perm m1 bdst (Int.unsigned odst) (Int.unsigned odst + sz) Max Nonempty).
      {
        apply Mem.range_perm_max with Cur.
        replace sz with (Z_of_nat (length bytes)).
        eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. constructor.
        rewrite LEN. apply nat_of_Z_eq. omega.
      }
      exploit (Mem.disjoint_or_equal_inject _ _ _ _ _ _ _ _ _ _ _ _ match_inject H14 H15 RPSRC RPDST); eauto.
      omega.
      repeat rewrite Z.add_0_r; trivial.
      lift_simpl. eauto. 
      econstructor; eauto.
      * eapply storebytes_match_correct; eauto.
        red; intros. subst b.
        eapply match_newglob_noperm; eauto.
        exploit inject_forward_equal; eauto.
        intros HW; inv HW.
        eapply Mem.storebytes_range_perm; eauto.
        instantiate (1:= Int.unsigned odst).
        assert(Hlen: Z.of_nat (length bytes) = sz).
        {
          rewrite LEN. apply nat_of_Z_eq. omega.
        }
        rewrite Hlen. omega.
      * erewrite Mem.nextblock_storebytes; eauto.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ Hst'); eauto.
      * red; intros. eapply match_newglob_noperm; eauto.
        eapply Mem.perm_storebytes_2; eauto.
      * erewrite Mem.nextblock_storebytes; eauto.
      * eapply encode_long_inject; eauto.

  - (* annot *)
    inv H1. 
    refine_split'; eauto.
    econstructor; eauto.
    econstructor; eauto.
    eapply eventval_list_match_inject; eauto.
    inv match_extcall_states.
    eapply meminj_preserves_globals_incr; eauto 1.
    eapply encode_long_inject; eauto.

  - (* annot_val *)
    inv H1. rewrite <- H in Hval.
    inv_val_inject.
    refine_split'; eauto.
    econstructor; eauto.
    simpl. rewrite <- H4.
    econstructor; eauto.
    eapply eventval_match_inject; eauto.    
    inv match_extcall_states.
    eapply meminj_preserves_globals_incr; eauto 1.
    eapply encode_long_inject; eauto.

  - (* inline asm *)
    inv H1.
  Qed.

End ModuleSemantics_Monotonic.
