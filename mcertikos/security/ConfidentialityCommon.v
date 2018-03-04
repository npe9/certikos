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
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.

Require Import compcert.cfrontend.Ctypes.
Require Import Conventions.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.

Require Import AbstractDataType.
Require Import Soundness.
Require Import TSysCall.
Require Import LoadStoreSem3.

Require Import SecurityTactic.
Require Import SecurityLib.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Local Instance : ExternalCallsOps (mwd (cdata RData)) := CompatExternalCalls.compatlayer_extcall_ops tsyscall.
  Local Instance : LayerConfigurationOps := compatlayer_configuration_ops tsyscall.


  Remark inv_some2 {A B} : 
    forall (x1 x2 : A) (y1 y2 : B), Some (x1,y1) = Some (x2,y2) -> x1 = x2 /\ y1 = y2.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Ltac inv_rewrite := 
    match goal with
      | [ H : Some (_,_) = Some (_,_) |- _ ] => apply inv_some2 in H; destruct H
      | [ H : Some _ = Some _ |- _ ] => apply inv_some in H
    end; subst; simpl; auto.

  Section OBS_EQ.

    Function vread i vadr d :=
      if zle_lt adr_low vadr adr_high  then
        match ZMap.get (PDX vadr) (ZMap.get i (ptpool d)) with
          | PDEValid _ pte =>
            match ZMap.get (PTX vadr) pte with
              | PTEValid pi _ => Some pi
              | _ => None
            end
          | _ => None
        end
      else None.

    (* Observable equivalence of abstract data *)
    Record obs_eq (i: Z) (d1 d2: cdata RData) :=
      {
        (* hidden *) obs_eq_MM: True;  
        (* hidden *) obs_eq_MMSize: True;
        obs_eq_vmxinfo: True;
        (* hidden *) obs_eq_CR3: True;
        obs_eq_ti: True;
        obs_eq_pg: pg d1 = pg d2;
        obs_eq_ikern: ikern d1 = ikern d2;
        obs_eq_ihost: ihost d1 = ihost d2;
        obs_eq_HP: forall vadr pi1 pi2, 
                     vread i vadr d1 = Some pi1 ->
                     vread i vadr d2 = Some pi2 ->
                     forall o, 
                       ZMap.get (PTADDR pi1 o) (HP d1) = ZMap.get (PTADDR pi2 o) (HP d2);
        obs_eq_AC_quota: cquota (ZMap.get i (AC d1)) - cusage (ZMap.get i (AC d1)) = 
                         cquota (ZMap.get i (AC d2)) - cusage (ZMap.get i (AC d2));
        obs_eq_AC_used: cused (ZMap.get i (AC d1)) = cused (ZMap.get i (AC d2));
        obs_eq_AT: True;
        obs_eq_nps: True;
        obs_eq_init: init d1 = init d2;
        obs_eq_pperm: True;
        obs_eq_PT: True;
        obs_eq_ptpool: forall vadr,
                         (vread i vadr d1 = None <-> vread i vadr d2 = None);
        obs_eq_idpde: True;
        obs_eq_ipt: ipt d1 = ipt d2;
        obs_eq_LAT: True;
        obs_eq_pb: True;
        obs_eq_smspool: True;
        obs_eq_kctxt: ZMap.get i (kctxt d1) = ZMap.get i (kctxt d2);
        (* hidden *) obs_eq_tcb: True;
        (* hidden *) obs_eq_tdq: True;
        obs_eq_abtcb: ZMap.get i (abtcb d1) = ZMap.get i (abtcb d2);
        obs_eq_abq: ZMap.get i (abq d1) = ZMap.get i (abq d2);
        obs_eq_cid: i = cid d1 <-> i = cid d2;
        obs_eq_syncchpool: True;
        obs_eq_uctxt: ZMap.get i (uctxt d1) = ZMap.get i (uctxt d2);
        obs_eq_ept: True;
        obs_eq_vmcs: True;
        obs_eq_vmx: True

        (*obs_eq_unshared: unshared d1 i <-> unshared d2 i*)
      }.

    Inductive obs_eq_st : Z -> Asm.state(mem:=mwd (cdata RData)) -> 
                          Asm.state(mem:=mwd (cdata RData)) -> Prop :=
    | obs_eq_st_intro :
        forall id rs1 rs2 d1 d2 m,
          obs_eq id d1 d2 ->
          (id = cid d1 -> rs1 = rs2) ->
          obs_eq_st id (State rs1 (m,d1)) (State rs2 (m,d2)).

    Lemma obs_eq_refl :
      forall id d, obs_eq id d d.
    Proof.
      intros; constructor; intros; rewrites; auto; reflexivity.
    Qed.
    
    Lemma obs_eq_sym :
      forall id d1 d2, obs_eq id d1 d2 -> obs_eq id d2 d1.
    Proof.
      intros id d1 d2 Hobs; destruct Hobs; constructor; auto; try solve [symmetry; auto].
      intros; symmetry; eapply obs_eq_HP0; eauto.
    Qed.

    Lemma obs_eq_trans : 
      forall id d1 d2 d3, 
        obs_eq id d1 d2 -> obs_eq id d2 d3 -> obs_eq id d1 d3.
    Proof.
      intros id d1 d2 d3 Hobs1 Hobs2.
      destruct Hobs1, Hobs2; constructor; try congruence.
      - intros vadr p1 p3 Harg Hp1 Hp3; assert (exists p2, vread id vadr d2 = Some p2).
        destruct (vread id vadr d2) eqn:Hp2; eauto.
        rewrite obs_eq_ptpool1 in Hp2; auto; rewrites.
        destruct H; intros; erewrite obs_eq_HP0, obs_eq_HP1; eauto.
      - intros; rewrite obs_eq_ptpool0; auto.
      - transitivity (id = cid d2); auto.
    Qed.

    Lemma obs_eq_st_refl :
      forall id d rs m,
        obs_eq_st id (State rs (m,d)) (State rs (m,d)).
    Proof.
      intros; constructor; auto; apply obs_eq_refl.
    Qed.

    Lemma obs_eq_st_sym :
      forall id d1 d2 rs1 rs2 m1 m2, 
        obs_eq_st id (State rs1 (m1,d1)) (State rs2 (m2,d2)) -> 
        obs_eq_st id (State rs2 (m2,d2)) (State rs1 (m1,d1)).
    Proof.
      intros id d1 d2 rs1 rs2 m1 m2 Hobs; inv Hobs; constructor.
      apply obs_eq_sym; auto.
      destruct H2; intros; subst.
      symmetry; apply H7; apply obs_eq_cid0; auto.
    Qed.

    Lemma obs_eq_st_trans : 
      forall id d1 d2 d3 rs1 rs2 rs3 m1 m2 m3, 
        obs_eq_st id (State rs1 (m1,d1)) (State rs2 (m2,d2)) -> 
        obs_eq_st id (State rs2 (m2,d2)) (State rs3 (m3,d3)) ->
        obs_eq_st id (State rs1 (m1,d1)) (State rs3 (m3,d3)).
    Proof.
      intros id d1 d2 d3 rs1 rs2 rs3 m1 m2 m3 Hobs1 Hobs2.
      inv Hobs1; inv Hobs2; constructor.
      apply obs_eq_trans with (d2:= d2); auto.
      intros; subst; destruct H2.
      transitivity rs2; auto; apply H9; apply obs_eq_cid0; auto.
    Qed.

  End OBS_EQ.

  Ltac unshared_simpl_iff :=
    match goal with
    | [ |- unshared _ _ <-> unshared (update_LAT (?f _ _) _) _ ] => 
      let H := fresh in let Hunsh := fresh in let Hown1 := fresh in let Hown2 := fresh in
        assert (H: forall d id v lat, unshared (update_LAT d lat) id <-> 
                                      unshared (update_LAT (f d v) lat) id) 
          by (unfold unshared; intros; split; intros Hunsh ? Hown1 ? Hown2;
              inv Hown1; inv Hown2; simpl in *; eapply Hunsh; rewrites; econstructor; eauto);
        rewrite <- H; clear H
    | [ |- unshared _ _ <-> unshared (?f _ _) _ ] => 
      let H := fresh in let Hunsh := fresh in let Hown1 := fresh in let Hown2 := fresh in
        assert (H: forall d id v, unshared d id <-> unshared (f d v) id) 
          by (unfold unshared; intros; split; intros Hunsh ? Hown1 ? Hown2;
              inv Hown1; inv Hown2; simpl in *; eapply Hunsh; rewrites; econstructor; eauto);
        rewrite <- H; clear H
    end.

  Ltac isOwner_rewrite :=
    match goal with
    | [ H: isOwner (?f _ _) _ _ |- _ ] =>
      let H' := fresh in let Hown := fresh in
        assert (H': forall d v id p, isOwner (f d v) id p -> isOwner d id p)
          by (intros ? ? ? ? Hown; inv Hown; econstructor; eauto);
        apply H' in H; clear H'
    | [ |- isOwner (?f _ _) _ _ ] =>
      let H' := fresh in let Hown := fresh in
        assert (H': forall d v id p, isOwner d id p -> isOwner (f d v) id p)
          by (intros ? ? ? ? Hown; inv Hown; econstructor; eauto);
        apply H'; clear H'
    end.

  Ltac solve_isOwner :=
    repeat isOwner_simpl_iff; try reflexivity; try assumption; auto.

  Ltac solve_unshared :=
    repeat unshared_simpl_iff; try reflexivity; try assumption; auto.

  Ltac solve_obs_eq :=
    match goal with
    | [ H: obs_eq _ _ _ |- _ ] =>
      destruct H; constructor; simpl; auto; 
          try solve [intros; isOwner_rewrite; auto
                   | match goal with
                     | [ Hcid: _ = cid _ <-> _ = cid _ |- _ ] =>
                       rewrite <- (proj1 Hcid); auto;
                         repeat rewrite ZMap.gss; subrewrite
                     end
                   | intro; solve_isOwner
                   | solve_unshared]
    end.

  Ltac vread_simpl :=
    match goal with
    | [ H: vread _ _ (?f _ _) = _ |- _ ] =>
      let H' := fresh in 
        assert (H': forall id vadr d v, vread id vadr (f d v) = vread id vadr d)
          by (unfold vread, ptRead_spec, getPTE_spec; simpl; reflexivity); rewrite H' in H; clear H'
    | [ |- context [vread _ _ (?f _ _) = _ ] ] =>
      let H' := fresh in 
        assert (H': forall id vadr d v, vread id vadr (f d v) = vread id vadr d)
          by (unfold vread, ptRead_spec, getPTE_spec; simpl; reflexivity); rewrite H'; clear H'
    | [ |- vread _ _ (?f _ _) <-> vread _ _ (?f _ _)] =>
      let H' := fresh in 
        assert (H': forall id vadr d v, vread id vadr (f d v) = vread id vadr d)
          by (unfold vread, ptRead_spec, getPTE_spec; simpl; reflexivity); rewrite H'; clear H'
    | [ H: vread _ _ (update_ptpool (?f _ _) _) = _ |- _ ] =>
      let H' := fresh in 
        assert (H': forall id vadr d v p, 
                      vread id vadr (update_ptpool (f d v) p) = 
                      vread id vadr (update_ptpool d p))
          by (unfold vread, ptRead_spec, getPTE_spec; simpl; reflexivity); rewrite H' in H; clear H'
    | [ |- context [vread _ _ (update_ptpool (?f _ _) _) = _ ] ] =>
      let H' := fresh in 
        assert (H': forall id vadr d v p, 
                      vread id vadr (update_ptpool (f d v) p) = 
                      vread id vadr (update_ptpool d p))
          by (unfold vread, ptRead_spec, getPTE_spec; simpl; reflexivity); rewrite H'; clear H'
    | [ |- vread _ _ (update_ptpool (?f _ _) _) <-> vread _ _ (update_ptpool (?f _ _) _) ] =>
      let H' := fresh in 
        assert (H': forall id vadr d v p, 
                      vread id vadr (update_ptpool (f d v) p) = 
                      vread id vadr (update_ptpool d p))
          by (unfold vread, ptRead_spec, getPTE_spec; simpl; reflexivity); rewrite H'; clear H'
    end.
    

  Lemma quota_convert :
    forall a b, (a <? b) = (0 <? b - a).
  Proof.
    intros.
    destruct (a <? b) eqn:H1; destruct (0 <? b - a) eqn:H2; auto.
    rewrite Z.ltb_lt in H1; rewrite Z.ltb_nlt in H2; omega.
    rewrite Z.ltb_nlt in H1; rewrite Z.ltb_lt in H2; omega.
  Qed.

  Ltac obs_eq_rewrites :=
    match goal with
    | [H: obs_eq _ _ _ |- _ ] => destruct H
    | _ => idtac
    end;
    repeat match goal with
    | [ H: _ = cid _ <-> _ = cid _ |- _ ] => 
      rewrite <- (proj1 H) in *; auto
    | [ H: ikern _ = ikern _ |- _ ] => rewrite <- H in *
    | [ H: ihost _ = ihost _ |- _ ] => rewrite <- H in *
    | [ H: pg _ = pg _ |- _ ] => rewrite <- H in *
    | [ H: ipt _ = ipt _ |- _ ] => rewrite <- H in *
    | [ H: PT _ = PT _ |- _ ] => rewrite <- H in *
    | [ H: nps _ = nps _ |- _ ] => rewrite <- H in *
    | [ H: init _ = init _ |- _ ] => rewrite <- H in *
    | [ H: cquota _ - cusage _ = cquota _ - cusage _ |- _ ] => 
      try rewrite quota_convert in *; rewrite <- H in *
    | [ H: cused (ZMap.get ?id (AC _)) = cused (ZMap.get ?id (AC _)) |- _ ] =>
      rewrite <- H in *
    | [ H: ZMap.get ?id (uctxt _) = ZMap.get ?id (uctxt _) |- _ ] => 
      rewrite <- H in *
    | [ H: ZMap.get ?id (ptpool _) = ZMap.get ?id (ptpool _) |- _ ] => 
      rewrite <- H in *
    | [ H: ZMap.get ?id (kctxt _) = ZMap.get ?id (kctxt _) |- _ ] => 
      rewrite <- H in *
    end; rewrites; auto.

  Section CONF_LEMMAS.

    Section CONF_UCTX.

      Lemma conf_uctx_set_errno :
        forall d1 d2 d1' d2' n,
          uctx_set_errno_spec n d1 = Some d1' ->
          uctx_set_errno_spec n d2 = Some d2' ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        inv_spec; inv Hspec1; inv Hspec2; solve_obs_eq.
      Qed.

      Lemma conf_uctx_arg1 :
        forall d1 d2 r1 r2,
          uctx_arg1_spec d1 = Some r1 ->
          uctx_arg1_spec d2 = Some r2 ->
          obs_eq (cid d1) d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; obs_eq_rewrites.
      Qed.

      Lemma conf_uctx_arg2 :
        forall d1 d2 r1 r2,
          uctx_arg2_spec d1 = Some r1 ->
          uctx_arg2_spec d2 = Some r2 ->
          obs_eq (cid d1) d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; obs_eq_rewrites.
      Qed.

      Lemma conf_uctx_arg3 :
        forall d1 d2 r1 r2,
          uctx_arg3_spec d1 = Some r1 ->
          uctx_arg3_spec d2 = Some r2 ->
          obs_eq (cid d1) d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; obs_eq_rewrites.
      Qed.

      Lemma conf_uctx_arg4 :
        forall d1 d2 r1 r2,
          uctx_arg4_spec d1 = Some r1 ->
          uctx_arg4_spec d2 = Some r2 ->
          obs_eq (cid d1) d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; obs_eq_rewrites.
      Qed.

      Lemma conf_uctx_arg5 :
        forall d1 d2 r1 r2,
          uctx_arg5_spec d1 = Some r1 ->
          uctx_arg5_spec d2 = Some r2 ->
          obs_eq (cid d1) d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; obs_eq_rewrites.
      Qed.

      Lemma conf_uctx_set_retval1 :
        forall d1 d2 d1' d2' n,
          uctx_set_retval1_spec n d1 = Some d1' ->
          uctx_set_retval1_spec n d2 = Some d2' ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        inv_spec; inv Hspec1; inv Hspec2; solve_obs_eq.
      Qed.

      Lemma conf_uctx_set_retval2 :
        forall d1 d2 d1' d2' n,
          uctx_set_retval2_spec n d1 = Some d1' ->
          uctx_set_retval2_spec n d2 = Some d2' ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        inv_spec; inv Hspec1; inv Hspec2; solve_obs_eq.
      Qed.

      Lemma conf_uctx_set_retval3 :
        forall d1 d2 d1' d2' n,
          uctx_set_retval3_spec n d1 = Some d1' ->
          uctx_set_retval3_spec n d2 = Some d2' ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        inv_spec; inv Hspec1; inv Hspec2; solve_obs_eq.
      Qed.

      Lemma conf_uctx_set_retval4 :
        forall d1 d2 d1' d2' n,
          uctx_set_retval4_spec n d1 = Some d1' ->
          uctx_set_retval4_spec n d2 = Some d2' ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        inv_spec; inv Hspec1; inv Hspec2; solve_obs_eq.
      Qed.

      Lemma conf_uctx_set_retval5 :
        forall d1 d2 d1' d2' n,
          uctx_set_retval5_spec n d1 = Some d1' ->
          uctx_set_retval5_spec n d2 = Some d2' ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        inv_spec; inv Hspec1; inv Hspec2; solve_obs_eq.
      Qed.

    End CONF_UCTX.

    Ltac rewrites :=
      repeat (match goal with
              | [ Heq1: ?a = _, Heq2: ?a = _ |- _ ] => rewrite Heq2 in Heq1; inv Heq1
              | [ Heq: ?a = _ |- context [if ?a then _ else _] ] => rewrite Heq
              | [ Heq: _ = ?a |- context [if ?a then _ else _ ] ] => rewrite <- Heq
              | [ Heq: ?a = _ |- context [match ?a with _ => _ end ] ] => rewrite Heq
              | [ Heq: _ = ?a |- context [match ?a with _ => _ end ] ] => rewrite <- Heq
              end).

    Ltac eqdestruct :=
      repeat match goal with
      | [ |- if ?a then _ else _ = if ?a then _ else _ ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      | [ |- match ?a with _ => _ end = match ?a with _ => _ end ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      end.

    Ltac destructgoal :=
      repeat match goal with
      | [ |- if ?a then _ else _ = _ ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      | [ |- match ?a with _ => _ end = _ ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      end.

    Section CONF_GET_QUOTA.

      Lemma conf_trap_get_quota :
        forall d1 d2 d1' d2',
          trap_get_quota_spec d1 = Some d1' ->
          trap_get_quota_spec d2 = Some d2' ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        repeat inv_spec; repeat inv_rewrite; simpl in *.
        destruct Hobs_eq; constructor; simpl; auto.
        obs_eq_rewrites; repeat rewrite ZMap.gss; reflexivity.
      Qed.

    End CONF_GET_QUOTA.

    Ltac elim_stuck' H :=
      match type of H with
      | match ?X with | _ => _ end = Next _ _ => destruct X; try discriminate H
      | if ?X then _ else _ = Next _ _  => destruct X; try discriminate H
      end.

    Ltac elim_stuck_eqn' H H' :=
      match type of H with
      | match ?X with | _ => _ end = Next _ _ => destruct X eqn:H'; try discriminate H
      | if ?X then _ else _ = Next _ _ => destruct X eqn:H'; try discriminate H
      end.

    Section CONF_ACCESSORS.

      Lemma PDEValid_usr :
        forall id i d pti pte,
          high_level_invariant d -> ikern d = false -> 0 <= id < num_id ->
          ZMap.get (PDX (Int.unsigned i)) (ZMap.get id (ptpool d)) = PDEValid pti pte ->
          adr_low <= Int.unsigned i < adr_high.
      Proof.
        intros id i d pti pte Hinv Hkern Hid Hpdx.
        assert (Hrange:= Int.unsigned_range_2 i).
        assert (Hmax:= max_unsigned_val).
        destruct Hinv.
        destruct (valid_PMap (valid_kern Hkern) id Hid) as [Hpmap _].
        assert (Hcases: adr_low <= Int.unsigned i < adr_high \/
                (0 <= Int.unsigned i < 262144*PgSize \/ 
                 983040*PgSize <= Int.unsigned i < 1048576*PgSize)) by omega.
        destruct Hcases as [|Hcases]; auto.
        assert (Hk: 0 <= Int.unsigned i / PgSize < 262144 \/
                983040 <= Int.unsigned i / PgSize < 1048576) 
          by  (destruct Hcases; [left|right]; split;
               try (apply Zdiv_le_lower_bound; omega); 
               try (apply Zdiv_lt_upper_bound; omega)).
        specialize (Hpmap _ Hk); unfold PDE_kern in Hpmap.
        replace (PDX (Int.unsigned i / 4096 * 4096)) with (PDX (Int.unsigned i)) in Hpmap.
        rewrites.
        unfold PDX.
        rewrite (Z_div_mod_eq (Int.unsigned i) PgSize); try omega.
        repeat rewrite <- Zdiv.Zdiv_Zdiv; try omega.
        rewrite Z.mul_comm.
        rewrite Z_div_plus_full_l; try omega.
        rewrite (Zdiv_small (Int.unsigned i mod PgSize) PgSize).
        rewrite Zplus_0_r.
        rewrite Z_div_mult_full; try omega.
        apply Z_mod_lt; omega.
      Qed.

      Lemma conf_flatmem_load :
        forall id d1 d2, obs_eq id d1 d2 ->
          forall vadr p1 p2, vread id vadr d1 = Some p1 -> vread id vadr d2 = Some p2 ->
            forall o chunk, o mod PgSize + (size_chunk chunk) <= PgSize ->
                            FlatMem.load chunk (HP d1) (PTADDR p1 o) = FlatMem.load chunk (HP d2) (PTADDR p2 o).
      Proof.
        intros id d1 d2 Hobs_eq vadr p1 p2 Hrd1 Hrd2 o chunk Hchunk.
        eapply FlatMem.load_rep'; [|eauto|eauto].
        intros z Hz.
        assert (Hmath: forall p, PTADDR p o + z = PTADDR p (o+z)).
        {
          unfold PTADDR; intro p.
          rewrite <- Zplus_assoc; rewrite <- Zplus_mod_idemp_l.
          rewrite (Zmod_small (o mod PgSize + z)); auto.
          assert (Hlt: 0 < PgSize) by omega.
          assert (Hpos := Z.mod_pos_bound o _ Hlt); omega.
        }
        rewrite 2 Hmath; destruct Hobs_eq.
        eapply obs_eq_HP0; eauto.
      Qed.
      
      Lemma conf_exec_loadex {F V} :
        forall (m m1' m2' : mem) (d1 d2 d1' d2': cdata RData) rs rs1' rs2' ge chunk a rd, 
          exec_loadex(F:=F)(V:=V) ge chunk (m, d1) a rs rd = Next rs1' (m1', d1') ->
          exec_loadex ge chunk (m, d2) a rs rd = Next rs2' (m2', d2') ->
          high_level_invariant d1 -> high_level_invariant d2 -> 
          ikern d1 = false -> ihost d1 = true ->
          obs_eq (cid d1) d1 d2 -> (obs_eq (cid d1) d1' d2' /\ rs1' = rs2') /\ m1' = m2'.
      Proof.
        intros m m1' m2' d1 d2 d1' d2' rs rs1' rs2' ge chunk a rd
               Hstep1 Hstep2 Hinv1 Hinv2 Hkern Hhost Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq'.
        unfold exec_loadex, exec_loadex3 in *; subdestruct; simpl in *; try congruence.
        {
          (* host mode *)
          unfold HostAccess2.exec_host_load2, snd in *.
          elim_stuck_eqn' Hstep1 Hpdx1; elim_stuck_eqn' Hstep2 Hpdx2.
          rename pi into pti1, pi0 into pti2, pte into pte1, pte0 into pte2.
          assert (Hcases1: (exists v pm, ZMap.get (PTX (Int.unsigned i)) pte1 = PTEValid v pm) \/ 
                           ZMap.get (PTX (Int.unsigned i)) pte1 = PTEUnPresent)
            by (clear Hstep2; subdestruct; [left|left|right]; eauto).
          assert (Hcases2: (exists v pm, ZMap.get (PTX (Int.unsigned i)) pte2 = PTEValid v pm) \/ 
                           ZMap.get (PTX (Int.unsigned i)) pte2 = PTEUnPresent)
            by (clear Hstep1; subdestruct; [left|left|right]; eauto).
          destruct Hcases1 as [[pi1 [pm1 Hvalid1]]|Hunp1].
          {
            assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte1 with
                        | PTEValid v PTP =>
                          FlatLoadStoreSem.exec_flatmem_load chunk 
                            (m, d1) (PTADDR v (Int.unsigned i)) rs rd
                        | PTEValid v PTU =>
                          FlatLoadStoreSem.exec_flatmem_load chunk 
                            (m, d1) (PTADDR v (Int.unsigned i)) rs rd
                        | PTEValid v (PTK _) => Stuck
                        | PTEUnPresent => PageFault.exec_pagefault ge (m, d1) i rs
                        | PTEUndef => Stuck
                         end = FlatLoadStoreSem.exec_flatmem_load chunk 
                                 (m, d1) (PTADDR pi1 (Int.unsigned i)) rs rd)
              by (clear Hstep2; destruct pm1; rewrite Hvalid1 in Hstep1; 
                  subdestruct; rewrite Hvalid1; auto).
            rewrite Hm in Hstep1; clear Hm.
            assert (Husr: adr_low <= Int.unsigned i < adr_high).
            {             
              eapply PDEValid_usr; eauto.
              destruct Hinv2; rewrite valid_init_PT_cid; auto.
            }
            destruct Hcases2 as [[pi2 [pm2 Hvalid2]]|Hunp2].
            {
              assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte2 with
                        | PTEValid v PTP =>
                          FlatLoadStoreSem.exec_flatmem_load chunk 
                            (m, d2) (PTADDR v (Int.unsigned i)) rs rd
                        | PTEValid v PTU =>
                          FlatLoadStoreSem.exec_flatmem_load chunk 
                            (m, d2) (PTADDR v (Int.unsigned i)) rs rd
                        | PTEValid v (PTK _) => Stuck
                        | PTEUnPresent => PageFault.exec_pagefault ge (m, d2) i rs
                        | PTEUndef => Stuck
                         end = FlatLoadStoreSem.exec_flatmem_load chunk 
                                 (m, d2) (PTADDR pi2 (Int.unsigned i)) rs rd)
              by (clear Hstep1; destruct pm2; rewrite Hvalid2 in Hstep2; 
                  subdestruct; rewrite Hvalid2; auto).
            rewrite Hm in Hstep2; clear Hm.
            subdestruct.
            unfold FlatLoadStoreSem.exec_flatmem_load in *; inv Hstep1; inv Hstep2.
            assert (Hobs_eq': obs_eq (cid d1') d1' d2') by (constructor; auto; congruence).            
            rewrite (conf_flatmem_load (cid d1') _ d2' Hobs_eq' (Int.unsigned i) _ pi2); auto.
            - unfold vread; rewrite zle_lt_true; auto.
              destruct Hinv1; rewrite <- valid_init_PT_cid; rewrites; auto.
            - unfold vread; rewrite zle_lt_true; auto.
              destruct Hinv2; rewrite (proj1 obs_eq_cid0); auto.
              rewrite <- valid_init_PT_cid; rewrites; auto.
            - clear Hdestruct6; omega.
          }
          {
            assert (Hcon: vread (cid d1) (Int.unsigned i) d2 = None).
            {
              unfold vread; destructgoal.
              destruct Hinv2; rewrite (proj1 obs_eq_cid0) in Hdestruct7; auto.
              rewrite <- valid_init_PT_cid in Hdestruct7; rewrites; auto.
            }
            rewrite <- obs_eq_ptpool0 in Hcon; unfold vread in Hcon.
            rewrite zle_lt_true in Hcon; auto.
            destruct Hinv1; rewrite <- valid_init_PT_cid in Hcon; auto.
            rewrite Hpdx1, Hvalid1 in Hcon; discriminate Hcon.
          }
        }
        {
          destruct Hcases2 as [[pi2 [pm2 Hvalid2]]|Hunp2].
          {
            assert (Hm: match ZMap.get (PTX (Int.unsigned i)) pte2 with
                          | PTEValid v PTP =>
                            FlatLoadStoreSem.exec_flatmem_load chunk 
                              (m, d2) (PTADDR v (Int.unsigned i)) rs rd
                          | PTEValid v PTU =>
                            FlatLoadStoreSem.exec_flatmem_load chunk 
                              (m, d2) (PTADDR v (Int.unsigned i)) rs rd
                          | PTEValid v (PTK _) => Stuck
                          | PTEUnPresent => PageFault.exec_pagefault ge (m, d2) i rs
                          | PTEUndef => Stuck
                        end = FlatLoadStoreSem.exec_flatmem_load chunk 
                                                                 (m, d2) (PTADDR pi2 (Int.unsigned i)) rs rd)
              by (clear Hstep1; destruct pm2; rewrite Hvalid2 in Hstep2; 
                  subdestruct; rewrite Hvalid2; auto).
            rewrite Hm in Hstep2; clear Hm.
            assert (Hcon: vread (cid d1) (Int.unsigned i) d1 = None).
            {
              unfold vread; destructgoal.
              destruct Hinv1; rewrite <- valid_init_PT_cid in Hdestruct7; rewrites; auto.
            }
            rewrite obs_eq_ptpool0 in Hcon; unfold vread in Hcon.
            rewrite zle_lt_true in Hcon.
            rewrite (proj1 obs_eq_cid0) in Hcon; auto.
            destruct Hinv2; rewrite <- valid_init_PT_cid in Hcon; auto.
            rewrite Hpdx2, Hvalid2 in Hcon; discriminate Hcon.
            eapply PDEValid_usr; eauto.
            destruct Hinv2; rewrite valid_init_PT_cid; auto.
          }
          {
            unfold PageFault.exec_pagefault in *; subdestruct; inv Hstep1; inv Hstep2.
            unfold trapinfo_set; repeat (apply conj; auto).
            constructor; simpl; auto; congruence.
          }
        }
      }
      
        (* guest mode *)
       (*
        unfold GuestAccessIntel2.exec_guest_intel_load2 in *.
        unfold GuestAccessIntelDef2.exec_guest_intel_accessor2, GuestAccessIntel2.load_accessor2, snd in *.
        Print RData.
        Print VMCS.
        subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_load in *; inv Hstep1; inv Hstep2.
        repeat (apply conj; auto).
        unfold EPTADDR.
        Eval compute in FlatLoadStoreSem.exec_flatmem_load.
        unfold 
        Print ptRead_spec.
        Print EPT_PML4_INDEX.
        rewrite (conf_flatmem_load (cid d1') _ d2' Hobs_eq (Int.unsigned i) _ (hpa/PgSize)); auto.
        unfold vread.
        Print EPT_PDPT_INDEX.
        Print EPT_PML4_INDEX.
        Print EPT_PDIR_INDEX.
        Print EPT_PTAB_INDEX.
        clear Hdestruct4; omega.
*)
      (*
      {
        (* guest mode *)
        (* need to add epmap_consistent invariant to prove this lemma for guest mode *)
        
        unfold GuestAccessIntel2.exec_guest_intel_load2 in *.
        unfold GuestAccessIntelDef2.exec_guest_intel_accessor2, GuestAccessIntel2.load_accessor2 in *.
        subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_load, snd in *.
        rewrite_fld ept; inv Hstep1; inv Hstep2.
        rewrites; rewrite (conf_flatmem_load (cid d1') _ d2'); auto.
        eapply pmap_owners_consistent; eauto.
        apply valid_curid; auto.
        apply Int.unsigned_range.
        rewrite <- valid_init_PT_cid; eauto.
        unfold PTADDR.
        rewrite Z.add_1_r.
        rewrite <- Zmult_succ_l_reverse.
        rewrite (Zmod_small 0); try omega.
        }*)
      Qed.

      Lemma conf_exec_storeex {F V} :
        forall id (m m1' m2' : mem) (d1 d2 d1' d2': cdata RData) rs rs1' rs2' ge chunk a rs0 l, 
          exec_storeex(F:=F)(V:=V) ge chunk (m, d1) a rs rs0 l = Next rs1' (m1', d1') ->
          exec_storeex ge chunk (m, d2) a rs rs0 l = Next rs2' (m2', d2') ->
          ikern d1 = false -> obs_eq id d1 d2 -> (obs_eq id d1' d2' /\ rs1' = rs2') /\ m1' = m2'.
      Proof.
        intros id m m1' m2' d1 d2 d1' d2' rs rs1' rs2' ge chunk a s0 l
               Hstep1 Hstep2 Hkern Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold exec_storeex, exec_storeex3 in *; subdestruct; simpl in *;
        try solve [inv Hnh; simpl in *; congruence].
        {
          (* host mode *)
          unfold HostAccess2.exec_host_store2, snd in *.
          assert (Hpdx: ZMap.get (PDX (Int.unsigned i)) (ZMap.get (PT d1) (ptpool d1)) = 
                        ZMap.get (PDX (Int.unsigned i)) (ZMap.get (PT d2) (ptpool d2))) by (inv Hnh; auto).

          rewrite <- Hpdx in Hstep2; subdestruct.
          {
            unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in *.
            assert (Hperm: pperm d1 = pperm d2) by (inv Hnh; auto).
            unfold snd in *; rewrite <- Hperm in Hstep2; subdestruct; inv Hstep1; inv Hstep2.
            repeat (apply conj; auto); constructor.
            inv Hnh; constructor; auto.
            intros p Hown o; simpl.
            assert (Hcases: PTADDR v (Int.unsigned i) <= PTADDR p o < PTADDR v (Int.unsigned i) + 
                                                                      Z.of_nat (length (encode_val chunk (rs s0))) \/ 
                            (PTADDR p o < PTADDR v (Int.unsigned i) \/
                             PTADDR p o >= PTADDR v (Int.unsigned i) + 
                                           Z.of_nat (length (encode_val chunk (rs s0))))) by omega. 
            unfold FlatMem.store; destruct Hcases as [Hcase|Hcase].
            - rewrite 2 (get_setN_charact' _ _ _ _ Hcase); reflexivity.
            - rewrite 2 FlatMem.setN_outside; auto.
              apply Hhp; inv Hown; econstructor; eauto.
          }
          {
            unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in *.
            assert (Hperm: pperm d1 = pperm d2) by (inv Hnh; auto).
            unfold snd in *; rewrite <- Hperm in Hstep2; subdestruct; inv Hstep1; inv Hstep2.
            repeat (apply conj; auto); constructor.
            inv Hnh; constructor; auto.
            intros p Hown o; simpl.
            assert (Hcases: PTADDR v (Int.unsigned i) <= PTADDR p o < PTADDR v (Int.unsigned i) + 
                                                                      Z.of_nat (length (encode_val chunk (rs s0))) \/ 
                            (PTADDR p o < PTADDR v (Int.unsigned i) \/
                             PTADDR p o >= PTADDR v (Int.unsigned i) + 
                                           Z.of_nat (length (encode_val chunk (rs s0))))) by omega. 
            unfold FlatMem.store; destruct Hcases as [Hcase|Hcase].
            - rewrite 2 (get_setN_charact' _ _ _ _ Hcase); reflexivity.
            - rewrite 2 FlatMem.setN_outside; auto.
              apply Hhp; inv Hown; econstructor; eauto.
          }
          {
            unfold PageFault.exec_pagefault in *; subdestruct; inv Hstep1; inv Hstep2.
            unfold trapinfo_set; repeat (apply conj; auto); solve_obs_eq Hhp.
          }
        }
        {
          (* guest mode *)
          unfold GuestAccessIntel2.exec_guest_intel_store2 in *.
          unfold GuestAccessIntelDef2.exec_guest_intel_accessor2, GuestAccessIntel2.store_accessor2 in *.
          subdestruct.
          unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store, snd in *; inv Hstep1; inv Hstep2.
          rewrite_fld ept; rewrite_fld pperm; rewrites.
          subdestruct; inv H0; inv H1.
          repeat (apply conj; auto); constructor.
          nonHP_simpl; auto.
          intros p Hown o; simpl.
          assert (Hcases: EPTADDR (hpa0/PgSize) (Int.unsigned i) <= PTADDR p o 
                          < EPTADDR (hpa0/PgSize) (Int.unsigned i) + 
                            Z.of_nat (length (encode_val chunk (rs s0))) \/ 
                          (PTADDR p o < EPTADDR (hpa0/PgSize) (Int.unsigned i) \/
                           PTADDR p o >= EPTADDR (hpa0/PgSize) (Int.unsigned i) + 
                                         Z.of_nat (length (encode_val chunk (rs s0))))) by omega. 
          unfold FlatMem.store; destruct Hcases as [Hcase|Hcase].
          - rewrite 2 (get_setN_charact' _ _ _ _ Hcase); reflexivity.
          - rewrite 2 FlatMem.setN_outside; auto.
            apply Hhp; inv Hown; econstructor; eauto.
        }
      Qed.

    End CONF_ACCESSORS.

    End CONF_GET_QUOTA.


    Section CONF_TSC_OFFSET.

      Print vmx_get_tsc_offset_spec.

      Lemma conf_vmx_get_tsc_offset :
        

      Print trap_get_tsc_offset_spec.

      Lemma conf_vmx_get_tsc_off_set :
        

    End CONF_TSC_OFFSET.

(* can i just turn off trap_mmap? seems needed only for virtualization *)
    Section CONF_MMAP.

      Lemma ptAllocPDE0_vread_gso :
        forall id v vadr p d,
          PDX v <> PDX vadr ->
          vread id v d{ptpool: ZMap.set id (ZMap.set (PDX vadr) 
                                       (PDEValid p CalRealInitPTE.real_init_PTE) 
                                       (ZMap.get id (ptpool d))) (ptpool d)} = vread id v d.
      Proof.
        unfold vread, ptRead_spec, getPTE_spec; intros; subdestruct; simpl in *.        
        rewrite ZMap.gss; rewrite ZMap.gso; auto.
      Qed.

      Lemma ptAllocPDE0_vread_gss :
        forall id v vadr p d,          
          PDX v = PDX vadr ->
          vread id v d{ptpool: ZMap.set id (ZMap.set (PDX vadr) 
                                       (PDEValid p CalRealInitPTE.real_init_PTE) 
                                       (ZMap.get id (ptpool d))) (ptpool d)} = None.
      Proof.
        unfold vread, ptRead_spec, getPTE_spec; intros; subdestruct; simpl in *; rewrites.
        destructgoal; subdestruct.
        rewrite H in Hdestruct7; rewrite 2 ZMap.gss in Hdestruct7; inv Hdestruct7.
        rewrite CalRealInitPTE.real_init_PTE_unp in Hdestruct8; inv Hdestruct8.
        unfold PTX; apply Z.mod_pos_bound; omega.
        inv_rewrite; contradiction n; auto.
      Qed.

      Lemma vread_owner :
        forall v p d,
          high_level_invariant d -> 
          vread (cid d) v d = Some p -> isOwner d (cid d) p.
      Proof.
        intros v p d Hinv Hrd.
        assert (Hinv':= Hinv); destruct Hinv'.
        unfold_specs; subdestruct.
        unfold_specs; subdestruct; repeat inv_rewrite; try omega.
        eapply pmap_owners_consistent; eauto; try omega.
        unfold PageI; replace ((v0 * 4096 + PermtoZ p0) / 4096) with v0; eauto.
        symmetry; eapply Zdiv_unique; eauto.
        destruct p0; simpl; try omega.
        destruct b; omega.
      Qed.

      Lemma conf_ptAllocPDE0 : 
        forall d1 d2 d1' d2' vadr r1' r2',          
          ptAllocPDE0_spec (cid d1) vadr d1 = Some (d1', r1') ->
          ptAllocPDE0_spec (cid d1) vadr d2 = Some (d2', r2') ->
          init d1 = true -> high_level_invariant d1 -> high_level_invariant d2 ->
          obs_eq (cid d1) d1 d2 -> obs_eq (cid d1) d1' d2'.
      Proof.
        intros d1 d2 d1' d2' vadr r1' r2' Hspec1 Hspec2 Hinit Hinv1 Hinv2 Hobs_eq.
        unfold_specs; obs_eq_rewrites; subdestruct; repeat inv_rewrite.
        {
          constructor; simpl; try assumption; try congruence.
          {
            intros v p1 p2 Hrd1 Hrd2; repeat vread_simpl.
            destruct (zeq (PDX v) (PDX vadr)).
            - rewrite ptAllocPDE0_vread_gss in Hrd1, Hrd2; try assumption; try congruence.
            - rewrite ptAllocPDE0_vread_gso in Hrd1, Hrd2; try assumption.
              intro o; rewrite 2 FlatMem.free_page_gso.
              eapply obs_eq_HP0; eauto.
              rewrite (proj1 obs_eq_cid0) in Hrd2; try reflexivity.
              apply vread_owner in Hrd2; try assumption.
              rewrite pagei_ptaddr; intro Hcon; subst.
              destruct a as [a [Hcon a']]; inv Hrd2; rewrites; contradiction.
              apply vread_owner in Hrd1; try assumption.
              rewrite pagei_ptaddr; intro Hcon; subst.
              destruct a0 as [a0 [Hcon a0']]; inv Hrd1; rewrites; contradiction.
          }
          {
            repeat rewrite ZMap.gss; simpl; omega.
          }
          {
            repeat rewrite ZMap.gss; auto.
          }
          {
            intro v; repeat vread_simpl.
            destruct (zeq (PDX v) (PDX vadr)).
            - rewrite 2 ptAllocPDE0_vread_gss; auto; reflexivity.
            - rewrite 2 ptAllocPDE0_vread_gso; auto.
          }
        }
        {
          Print trap_mmap_spec.
          Print vmx_set_mmap_spec.
          Print ept_add_mapping_spec.
          Print getPTE_spec.
Print ptfault_resv_spec.

          Print high_level_invariant.
          Print PMap_usr.
          Print PDE_usr.
          Print ptResv_spec.
Print ptInsert0_spec.
          Print palloc_spec.
          {
            repeat unshared_simpl_iff.
            unfold unshared; split; intros Hunsh p Hown1 id Hown2.
            inv Hown1; inv Hown2; simpl in *.
            destruct (zeq p r2'); subst.
            - rewrite ZMap.gss in *.
              inv H; contradiction.              
            - rewrite ZMap.gso in *; auto; rewrites.
              eapply Hunsh; econstructor; simpl; eauto.
              rewrite ZMap.gso; eauto.
            vread_simpl.
            auto.
              inv H1.
Print ptRead_spec.
Print getPTE_spec.
Check pmap_owners_consistent.



              intro o; rewrite 2 FlatMem.free_page_gso.

            try solve [unfold PageI, PTADDR; simpl; rewrite Zdiv.Zdiv_small; try omega;
                       apply Z.mod_pos_bound; omega].
            apply (obs_eq_HP0 vadr).
            unfold ptRead_spec, getPTE_spec.
; rewrites.
          erewrite Hdestruct14.
          
          inv_rewrite.
          simpl.
Print ptAllocPDE0_spec.
Print trap_mmap_spec.
Print ptRead_spec.
Print getPTE_spec.
Print ptResv_spec.
Print ptInsert0_spec.
Print palloc_spec.
Print vmx_set_mmap_spec.
Print ept_add_mapping_spec.
          subdestruct.
          rewrites.
; obs_eq_rewrites.
          unfold ptRead_spec, getPTE_spec; simpl.
          intros.
          
 auto.
        rewrite quota_convert in *.
        rewrite <- obs_eq_AC_quota0 in *.
        unfold ptAllocPDE0_spec in *.
        rewrite_fld LAT; rewrite_fld nps; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld AC.
        subdestruct; inv Hspec1; inv Hspec2; auto.
        split; constructor.
        repeat nonHP_simpl; auto.
        simpl; intros p Hown o; inv Hown.
        simpl in H.
        destruct (zeq p r2'); subst.
        rewrite ZMap.gss in H; inv H; inv H0.
        rewrite 2 FlatMem.free_page_gso; try (rewrite pagei_ptaddr; auto).
        rewrite ZMap.gso in H; auto; apply Hhp; econstructor; eauto.
      Qed.

      Lemma conf_palloc : 
        forall id (d1 d2 d1' d2' : cdata RData) i r1 r2,
          palloc_spec i d1 = Some (d1', r1) ->
          palloc_spec i d2 = Some (d2', r2) ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1 = r2.
      Proof.
        intros id d1 d2 d1' d2' i r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold palloc_spec in *.
        rewrite_fld LAT; rewrite_fld nps; rewrite_fld pperm; rewrite_fld AC.
        inv_spec; inv Hspec1; inv Hspec2; auto.
        split; constructor.
        repeat nonHP_simpl; assumption.
        simpl; intros p Hown o; inv Hown.
        simpl in H.
        destruct (zeq p r2); subst.
        rewrite ZMap.gss in H; inv H; inv H0.
        rewrite ZMap.gso in H; auto; apply Hhp; econstructor; eauto.
      Qed.

      (* ptResv is a special case for confidentiality - it is composed of a sequence of specs, some
         of which (ptInsert0_spec in particular) violate noninterference. However, it is possible to
         use high level invariants to prove that ptResv as a whole is nevertheless noninterfering. *)
      Lemma conf_ptResv : 
        forall id (d1 d2 d1' d2' : cdata RData) n vadr pm r1 r2,      
          ptResv_spec n vadr pm d1 = Some (d1', r1) ->
          ptResv_spec n vadr pm d2 = Some (d2', r2) ->
          high_level_invariant d1 -> high_level_invariant d2 ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1 = r2.
      Proof.
        intros id d1 d2 d1' d2' n vadr pm r1 r2 Hspec1 Hspec2 Hinv1 Hinv2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold ptResv_spec in *.
        conf_simpl id conf_palloc d1'' d2'' r.
        subdestruct; inv Hspec1; inv Hspec2; auto.
        split.
        constructor.
        {
          unfold ptInsert0_spec in *.
          clear Hnh; rewrite_fld ptpool; rewrite_fld nps.
          subdestruct; inv H0; inv H1.
          {
            unfold ptInsertPTE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; repeat inv_rewrite'; repeat nonHP_simpl; assumption.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [Hobs _].
            inv Hobs; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto. 
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [Hobs Heq]; subst.
            inv Hobs.
            unfold ptInsertPTE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; repeat inv_rewrite'; repeat nonHP_simpl; assumption.
          }
        }
        {
          unfold ptInsert0_spec in *.
          clear Hnh; rewrite_fld ptpool; rewrite_fld nps.
          subdestruct; inv H0; inv H1.
          {
            unfold ptInsertPTE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; repeat inv_rewrite'.
            {
              intros p' Hown o; inv Hown.
              simpl in H.
              destruct (zeq p' r); subst.
              {
                rewrite ZMap.gss in H; inv H.
                destruct H0.
                inv H.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a0 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev pperm.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply Hhp0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H; auto.
                apply Hhp0; econstructor; eauto.
              }
            }
            {
              intros p' Hown o; inv Hown.
              simpl in H.
              destruct (zeq p' r); subst.
              {
                rewrite ZMap.gss in H; inv H.
                destruct H0.
                inv H.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a0 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev pperm.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply Hhp0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H; auto.
                apply Hhp0; econstructor; eauto.
              }
            }
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [Hobs _].
            inv Hobs; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [Hobs Heq]; subst.
            rename r4 into d1''', r0 into d2'''.
            unfold ptAllocPDE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps; rewrite_fld AC.
            subdestruct.
            unfold ptInsertPTE0_spec in *.
            inv Hobs; rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; simpl in *.
            {
              inv Hdestruct11; inv Hdestruct14; inv Hdestruct15; inv Hdestruct18; simpl in *.
              intros p' Hown o; inv Hown.
              simpl in H1.
              destruct (zeq p' r); subst.
              {
                destruct (zeq r2 r); subst.
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                rewrite ZMap.gss in H1; inv H1.
                destruct H2.
                inv H1.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a1 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite 2 FlatMem.free_page_gso; try solve [rewrite pagei_ptaddr; auto].
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev' pperm H1.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply H0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H1; [|auto].
                apply H0; econstructor; eauto.
              }
            }
            {
              inv Hdestruct11; inv Hdestruct14; inv Hdestruct15; inv Hdestruct18; simpl in *.
              intros p' Hown o; inv Hown.
              simpl in H1.
              destruct (zeq p' r); subst.
              {
                destruct (zeq r2 r); subst.
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                rewrite ZMap.gss in H1; inv H1.
                destruct H2.
                inv H1.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a1 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite 2 FlatMem.free_page_gso; try solve [rewrite pagei_ptaddr; auto].
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev' pperm H1.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply H0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H1; [|auto].
                apply H0; econstructor; eauto.
              }
            }
            inv Hdestruct11; contradiction n1; auto.
            inv Hdestruct11; contradiction n1; auto.
          }
        }
        {
          unfold ptInsert0_spec in *.
          rewrite_fld nps; rewrite_fld ptpool.
          subdestruct; inv H0; inv H1; auto.
          destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                     Hdestruct14 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
          contradiction n1; auto.
          destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                     Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
          contradiction n1; auto.
          destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                     Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst; auto.
        }
      Qed.

    End CONF_PTRESV.

    

    Section CONF_MMAP.

      Lemma conf_vmx_set_mmap : 
        forall id (d1 d2 d1' d2' : cdata RData) gpa hpa ty r1' r2',
          vmx_set_mmap_spec gpa hpa ty d1 = Some (d1', r1') ->
          vmx_set_mmap_spec gpa hpa ty d2 = Some (d2', r2') ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1' = r2'.
      Proof.
        intros id d1 d2 d1' d2' gpa hpa ty r1' r2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold vmx_set_mmap_spec, ept_add_mapping_spec in *.
        rewrite_fld ept; subdestruct; inv Hspec1; inv Hspec2;
        solve [split; try solve_obs_eq Hhp; inv_spec; repeat inv_rewrite'].
      Qed.

      Lemma conf_trap_mmap : 
        forall id (d1 d2 d1' d2' : cdata RData),      
          trap_mmap_spec d1 = Some d1' ->
          trap_mmap_spec d2 = Some d2' ->
          high_level_invariant d1 -> high_level_invariant d2 ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hinv1 Hinv2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold trap_mmap_spec in *.
        rewrite_fld cid.
        repeat conf_arg_simpl.
        elim_none.
        {
          conf_goal; [rewrite_fld ptpool; subdestruct; rewrites; auto|].
          clear H H0; subst; elim_none; elim_none.
          {
            conf_simpl id conf_ptResv d1'' d2'' r.
            conf_goal; [rewrite_fld ptpool; subdestruct; rewrites; auto|].
            clear H H0; subst; elim_none.
            conf_simpl id conf_vmx_set_mmap d1''' d2''' r'.
            eapply conf_uctx_set_errno; eauto.
          }
          {
            conf_simpl id conf_vmx_set_mmap d1'' d2'' r.
            eapply conf_uctx_set_errno; eauto.
          }
        }
        {
          eapply conf_uctx_set_errno; eauto.
        }
      Qed.

    End CONF_MMAP.

    Section CONF_PROC_CREATE.

      Lemma conf_proc_create :
        forall id (d1 d2 d1' d2' : cdata RData) b b' buc ofs q r1 r2,
          proc_create_spec d1 b b' buc ofs q = Some (d1',r1) ->
          proc_create_spec d2 b b' buc ofs q = Some (d2',r2) ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1 = r2.
      Proof.
        intros id d1 d2 d1' d2' b b' buc ofs q r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld pb; rewrite_fld kctxt; rewrite_fld abq.
        rewrite_fld abtcb; rewrite_fld uctxt; rewrite_fld AC; rewrite_fld cid.
        subdestruct; inv Hspec1; inv Hspec2.
        split; auto; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_proc_create : 
        forall id (d1 d2 d1' d2' : cdata RData) s m,
          trap_proc_create_spec s m d1 = Some d1' ->
          trap_proc_create_spec s m d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' s m Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl.
        rewrite_fld cid; rewrite_fld AC.
        destruct (zle_le 0 z0
                         (cquota (ZMap.get (cid d1) (AC d1)) -
                          cusage (ZMap.get (cid d1) (AC d1)))).
        conf_arg_simpl.
        elim_none; elim_none; elim_none; elim_none; elim_none; elim_none.
        elim_none; elim_none; elim_none; elim_none; elim_none.
        conf_simpl' id conf_proc_create d1'' d2'' r.
        conf_simpl_noret id conf_uctx_set_retval1 d1''' d2'''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_PROC_CREATE.

    Section CONF_TSC.

      Lemma conf_vmx_set_tsc_offset : 
        forall id (d1 d2 d1' d2' : cdata RData) ofs,
          vmx_set_tsc_offset_spec ofs d1 = Some d1' ->
          vmx_set_tsc_offset_spec ofs d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' ofs Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_get_tsc_offset : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_tsc_offset_spec d1 = Some d1' ->
          trap_get_tsc_offset_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        unfold vmx_get_tsc_offset_spec in *.
        rewrite_fld vmcs.
        subdestruct.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_retval2; eauto.
        eapply conf_uctx_set_retval1; eauto.
      Qed.

      Lemma conf_trap_set_tsc_offset : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_set_tsc_offset_spec d1 = Some d1' ->
          trap_set_tsc_offset_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl.
        conf_simpl_noret id conf_vmx_set_tsc_offset d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_TSC.

    Section CONF_EXITINFO.

      Hint Unfold vmx_get_exit_reason_spec vmx_get_exit_io_port_spec vmx_get_io_width_spec 
           vmx_get_io_write_spec vmx_get_exit_io_rep_spec vmx_get_exit_io_str_spec
           vmx_get_exit_fault_addr_spec.

      Lemma conf_trap_get_exitinfo : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_exitinfo_spec d1 = Some d1' ->
          trap_get_exitinfo_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs; autounfold in *. 
        rewrite_fld vmcs; rewrite_fld vmx; rewrite_fld ikern; rewrite_fld pg; rewrite_fld ihost.
        elim_none; elim_none; elim_none; elim_none; elim_none; elim_none; elim_none.
        conf_simpl_noret id conf_uctx_set_retval1 dr1 dr1'.
        elim_none.
        {
          conf_simpl_noret id conf_uctx_set_retval2 dr2 dr2'.
          conf_simpl_noret id conf_uctx_set_retval3 dr3 dr3'.
          conf_simpl_noret id conf_uctx_set_retval4 dr4 dr4'.
          eapply conf_uctx_set_errno; eauto.
        }
        {
          elim_none.
          conf_simpl_noret id conf_uctx_set_retval2 dr2 dr2'.
          eapply conf_uctx_set_errno; eauto.
          eapply conf_uctx_set_errno; eauto.
        }
      Qed.

    End CONF_EXITINFO.

    Section CONF_REG.

      Lemma conf_vmx_get_reg : 
        forall id (d1 d2 : cdata RData) reg r1 r2,
          vmx_get_reg_spec reg d1 = Some r1 ->
          vmx_get_reg_spec reg d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 reg r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; rewrite_fld vmx; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_vmx_set_reg : 
        forall id (d1 d2 d1' d2' : cdata RData) reg v,
          vmx_set_reg_spec reg v d1 = Some d1' ->
          vmx_set_reg_spec reg v d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' reg v Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; rewrite_fld vmx; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_get_reg : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_reg_spec d1 = Some d1' ->
          trap_get_reg_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; elim_none.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z1) by (eapply conf_vmx_get_reg; eauto); subst.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_trap_set_reg : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_set_reg_spec d1 = Some d1' ->
          trap_set_reg_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl; elim_none.    
        conf_simpl_noret id conf_vmx_set_reg d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_REG.

    Section CONF_SEG.

      Lemma conf_vmx_set_desc : 
        forall id (d1 d2 d1' d2' : cdata RData) seg sel base lim ar,
          vmx_set_desc_spec seg sel base lim ar d1 = Some d1' ->
          vmx_set_desc_spec seg sel base lim ar d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' seg sel base lim ar Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_set_seg : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_set_seg_spec d1 = Some d1' ->
          trap_set_seg_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; elim_none.    
        conf_simpl_noret id conf_vmx_set_desc d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_SEG.

    Section CONF_EIP.

      Lemma conf_vmx_get_next_eip : 
        forall id (d1 d2 : cdata RData) r1 r2,
          vmx_get_next_eip_spec d1 = Some r1 ->
          vmx_get_next_eip_spec d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; rewrite_fld vmx; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_trap_get_next_eip : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_next_eip_spec d1 = Some d1' ->
          trap_get_next_eip_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_get_next_eip; eauto); subst; elim_none.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_EIP.

    Section CONF_EVENT.

      Lemma conf_vmx_inject_event : 
        forall id (d1 d2 d1' d2' : cdata RData) ty vec err ev,
          vmx_inject_event_spec ty vec err ev d1 = Some d1' ->
          vmx_inject_event_spec ty vec err ev d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' ty vec err ev Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct'; apply inv_some in Hspec1; 
        apply inv_some in Hspec2; subst; auto; solve_obs_eq Hhp.
      Qed.
      
      Lemma conf_trap_inject_event : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_inject_event_spec d1 = Some d1' ->
          trap_inject_event_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; conf_arg_simpl.
        conf_simpl_noret id conf_vmx_inject_event d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_vmx_check_pending_event : 
        forall id (d1 d2 : cdata RData) r1 r2,
          vmx_check_pending_event_spec d1 = Some r1 ->
          vmx_check_pending_event_spec d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_trap_check_pending_event : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_check_pending_event_spec d1 = Some d1' ->
          trap_check_pending_event_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_check_pending_event; eauto); subst.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_EVENT.

    Section CONF_INT.

      Lemma conf_vmx_check_int_shadow : 
        forall id (d1 d2 : cdata RData) r1 r2,
          vmx_check_int_shadow_spec d1 = Some r1 ->
          vmx_check_int_shadow_spec d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_vmx_set_intercept_intwin : 
        forall id (d1 d2 d1' d2' : cdata RData) en,
          vmx_set_intercept_intwin_spec en d1 = Some d1' ->
          vmx_set_intercept_intwin_spec en d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' en Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.
      
      Lemma conf_trap_check_int_shadow : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_check_int_shadow_spec d1 = Some d1' ->
          trap_check_int_shadow_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_check_int_shadow; eauto); subst.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_trap_intercept_int_window : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_intercept_int_window_spec d1 = Some d1' ->
          trap_intercept_int_window_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl. 
        conf_simpl_noret id conf_vmx_set_intercept_intwin d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_INT.

    Section CONF_MSR.

      Lemma conf_rdmsr : 
        forall id (d1 d2 : cdata RData) z r1 r2,
          rdmsr_spec z d1 = Some r1 ->
          rdmsr_spec z d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; rewrites; auto.
      Qed.
      
      Lemma conf_wrmsr : 
        forall id (d1 d2 : cdata RData) z1 z2 r1 r2,
          wrmsr_spec z1 z2 d1 = Some r1 ->
          wrmsr_spec z1 z2 d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; rewrites; auto.
      Qed.

      Lemma conf_trap_handle_rdmsr : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_handle_rdmsr_spec d1 = Some d1' ->
          trap_handle_rdmsr_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none_eqn' Hspec1 Hget1'; elim_none_eqn' Hspec2 Hget2'.
        assert (z = z1) by (eapply conf_rdmsr; eauto); subst; elim_none.
        conf_simpl_noret id conf_vmx_set_reg dr1 dr1'.
        conf_simpl_noret id conf_vmx_set_reg dr2 dr2'.
        elim_none_eqn' Hspec1 Hget1''; elim_none_eqn' Hspec2 Hget2''.
        assert (z1 = z2) by (eapply conf_vmx_get_next_eip; eauto); subst; elim_none.
        conf_simpl_noret id conf_vmx_set_reg dr3 dr3'.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_trap_handle_wrmsr : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_handle_wrmsr_spec d1 = Some d1' ->
          trap_handle_wrmsr_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none_eqn' Hspec1 Hget1'; elim_none_eqn' Hspec2 Hget2'.
        assert (z = z1) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none_eqn' Hspec1 Hget1''; elim_none_eqn' Hspec2 Hget2''.
        assert (z = z2) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none' Hspec1; elim_none' Hspec2.
        elim_none_eqn' Hspec1 Hget1''''; elim_none_eqn' Hspec2 Hget2''''.
        assert (z4 = z5) by (eapply conf_vmx_get_next_eip; eauto); subst; elim_none.    
        conf_simpl_noret id conf_vmx_set_reg d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_MSR.

  End CONF_LEMMAS.


  Section INTEG_LEMMAS.

    Variable (id : Z).

    Section INTEG_UCTX_SET_ERRNO.

      Lemma integ_uctx_set_errno :
        forall d d' n,
          uctx_set_errno_spec n d = Some d' ->
          obs_eq id d d'.
      Proof.
        intros; inv_spec; inv_rewrite; constructor; auto.
        intro; isOwner_simpl_iff; reflexivity.
        unshared_simpl_iff; reflexivity.
      Qed.      

    End INTEG_UCTX_SET_ERRNO.

    Section INTEG_MMAP.

      Lemma integ_ptAllocPDE0 : 
        forall d d' vadr r,
          ptAllocPDE0_spec (cid d) vadr d = Some (d',r) -> 
          id <> cid d -> obs_eq id d d'.
      Proof.
        intros d d' vadr r Hspec Hid.
        inv_spec; inv_rewrite; try apply obs_eq_refl.
        constructor; simpl in *; auto; try solve [rewrite ZMap.gso; auto].
        {
          (* obs_eq_HP *)
          intros p Hown o.
          destruct (zeq p r); subst.
          decompose [and] a; inv Hown; rewrites; contradiction.
          rewrite FlatMem.free_page_gso; auto.
          rewrite pagei_ptaddr; auto.
        }
        {
          (* obs_eq_pperm *)
          intros p Hown.
          destruct (zeq p r); subst.
          decompose [and] a; inv Hown; rewrites; contradiction.
          rewrite ZMap.gso; auto.
        }
        {
          (* obs_eq_LAT *)
          intros p Hown.
          destruct (zeq p r); subst.
          decompose [and] a; inv Hown; rewrites; contradiction.
          rewrite ZMap.gso; auto.
        }
        {
          (* obs_eq_owner *)
          intro p.
          destruct (zeq p r); subst.
          - decompose [and] a; split; intro Hown; inv Hown.
            rewrites; contradiction.
            simpl in *; rewrite ZMap.gss in *; rewrites; inv H0; contradiction.
          - solve_isOwner_iff.
        }
        {
          (* obs_eq_unshared *)
          repeat unshared_simpl_iff.
          unfold unshared; split; intros Hunsh p Hown1 ? Hown2.
          - destruct (zeq p r); subst.
            + inv Hown1.
              simpl in *; rewrite ZMap.gss in *; inv H; inv H0.
            + inv Hown1; inv Hown2; rewrites; simpl in *; rewrite ZMap.gso in *; auto.
              eapply Hunsh; econstructor; eauto.
          - destruct (zeq p r); subst.
            + decompose [and] a; inv Hown1; rewrites; contradiction.
            + inv Hown1; inv Hown2; rewrites.
              eapply Hunsh; econstructor; simpl; eauto; rewrite ZMap.gso; eauto.
        }
      Qed.
      
      Lemma integ_palloc : 
        forall d d' r,
          palloc_spec (cid d) d = Some (d',r) -> 
          id <> cid d -> obs_eq id d d'.
      Proof.
        intros d d' r Hspec Hid.
        inv_spec; inv_rewrite; try apply obs_eq_refl.
        constructor; simpl in *; auto; try solve [rewrite ZMap.gso; auto].
        {
          (* obs_eq_pperm *)
          intros p Hown.
          destruct (zeq p r); subst.
          decompose [and] a; inv Hown; rewrites; contradiction.
          rewrite ZMap.gso; auto.
        }
        {
          (* obs_eq_LAT *)
          intros p Hown.
          destruct (zeq p r); subst.
          decompose [and] a; inv Hown; rewrites; contradiction.
          rewrite ZMap.gso; auto.
        }
        {
          (* obs_eq_owner *)
          intro p.
          destruct (zeq p r); subst; [|solve_isOwner_iff].
          decompose [and] a.
          split; intro Hown; inv Hown.
          rewrites; contradiction.
          simpl in *; rewrite ZMap.gss in *; rewrites; inv H0; contradiction.
        }
        {
          (* obs_eq_unshared *)
          repeat unshared_simpl_iff.
          unfold unshared; split; intros Hunsh p Hown1 ? Hown2.
          - destruct (zeq p r); subst.
            + inv Hown1.
              simpl in *; rewrite ZMap.gss in *; inv H; inv H0.
            + inv Hown1; inv Hown2; rewrites; simpl in *; rewrite ZMap.gso in *; auto.
              eapply Hunsh; econstructor; eauto.
          - destruct (zeq p r); subst.
            + decompose [and] a; inv Hown1; rewrites; contradiction.
            + inv Hown1; inv Hown2; rewrites.
              eapply Hunsh; econstructor; simpl; eauto; rewrite ZMap.gso; eauto.
        }
      Qed.

      Lemma integ_ptInsertPTE0 :
        forall d d' vadr padr pm,
          ptInsertPTE0_spec (cid d) vadr padr pm d = Some d' -> 
          ~ isOwner d id padr -> id <> cid d -> obs_eq id d d'.
      Proof.
        intros d d' vadr padr pm Hspec Hnown Hid.
        inv_spec; inv_rewrite.
        {
          constructor; simpl; auto; try solve [rewrite ZMap.gso; auto].
          {
            (* obs_eq_LAT *)
            intros p Hown.
            destruct (zeq p padr); subst; try contradiction.
            rewrite ZMap.gso; auto.
          }
          {
            (* obs_eq_owner *)
            intro p.
            destruct (zeq p padr); subst; [|solve_isOwner_iff].
            isOwner_simpl_iff; split; intro Hown; inv Hown; rewrites.
            - econstructor; simpl.
              rewrite ZMap.gss; eauto.
              right; eauto.
            - simpl in *; rewrite ZMap.gss in *; inv H.
              destruct H0.
              inv H; contradict Hid; auto.
              econstructor; eauto.
          }
          {
            (* obs_eq_unshared *)
            repeat unshared_simpl_iff.
            unfold unshared; split; intros Hunsh p Hown1 ? Hown2.
            - destruct (zeq p padr); subst.
              + inv Hown1.
                simpl in *; rewrite ZMap.gss in *; inv H; inv H0.
                contradict Hid; inv H; auto.
                contradict Hnown; econstructor; eauto.
              + inv Hown1; inv Hown2; simpl in *; rewrites.
                rewrite ZMap.gso in *; auto; eapply Hunsh; econstructor; eauto.
            - destruct (zeq p padr); subst; try contradiction.
              inv Hown1; inv Hown2; rewrites.
              eapply Hunsh; econstructor; simpl; eauto; rewrite ZMap.gso; eauto.
          }
        }
        {
          constructor; simpl; auto; try solve [rewrite ZMap.gso; auto].
          {
            (* obs_eq_LAT *)
            intros p Hown.
            destruct (zeq p padr); subst; try contradiction.
            rewrite ZMap.gso; auto.
          }
          {
            (* obs_eq_owner *)
            intro p.
            destruct (zeq p padr); subst; [|solve_isOwner_iff].
            isOwner_simpl_iff; split; intro Hown; inv Hown; rewrites.
            - econstructor; simpl.
              rewrite ZMap.gss; eauto.
              right; eauto.
            - simpl in *; rewrite ZMap.gss in *; inv H.
              destruct H0.
              inv H; contradict Hid; auto.
              econstructor; eauto.
          }
          {
            (* obs_eq_unshared *)
            repeat unshared_simpl_iff.
            unfold unshared; split; intros Hunsh p Hown1 ? Hown2.
            - destruct (zeq p padr); subst.
              + inv Hown1.
                simpl in *; rewrite ZMap.gss in *; inv H; inv H0.
                contradict Hid; inv H; auto.
                contradict Hnown; econstructor; eauto.
              + inv Hown1; inv Hown2; simpl in *; rewrites.
                rewrite ZMap.gso in *; auto; eapply Hunsh; econstructor; eauto.
            - destruct (zeq p padr); subst; try contradiction.
              inv Hown1; inv Hown2; rewrites.
              eapply Hunsh; econstructor; simpl; eauto; rewrite ZMap.gso; eauto.
          }
        }
      Qed.

      Lemma integ_ptInsert0 :
        forall d d' vadr padr pm r,
          ptInsert0_spec (cid d) vadr padr pm d = Some (d',r) -> 
          ~ isOwner d id padr -> id <> cid d -> obs_eq id d d'.
      Proof.
        intros d d' vadr padr pm r Hspec Hnown Hid.
        inv_spec; inv Hspec.
        eapply integ_ptInsertPTE0; eauto.
        eapply integ_ptAllocPDE0; eauto.
        apply integ_ptAllocPDE0 in Hdestruct6; auto.
        eapply obs_eq_trans; eauto.
        destruct Hdestruct6.
        eapply integ_ptInsertPTE0; eauto.
        rewrite <- obs_eq_cid0; eauto.
        rewrite <- obs_eq_owner0; auto.
        rewrite <- obs_eq_cid0; auto.
      Qed.

      Lemma integ_ptResv :
        forall d d' vadr pm r,
          ptResv_spec (cid d) vadr pm d = Some (d',r) -> 
          id <> cid d -> obs_eq id d d'.
      Proof.
        intros d d' vadr pm r Hspec Hid.
        inv_spec; inv Hspec; try apply obs_eq_refl.
        assert (Hpalloc:= Hdestruct); apply integ_palloc in Hdestruct; auto.
        eapply obs_eq_trans; eauto.
        destruct Hdestruct.
        rewrite obs_eq_cid0 in H0; eapply integ_ptInsert0; eauto; try congruence.
        clear H0; inv_spec; inv_rewrite.
        intro Hcon; inv Hcon; simpl in *.
        rewrite ZMap.gss in *; inv H; inv H0.
      Qed.

      Print trap_mmap_spec.
      
      Print uctx_arg2_spec.
      Print ptRead_spec.
      Print getPTE_spec.

    End INTEG_PTRESV.

    Section INTEG_MMAP.
(*
      Lemma conf_vmx_set_mmap : 
        forall id (d1 d2 d1' d2' : cdata RData) gpa hpa ty r1' r2',
          vmx_set_mmap_spec gpa hpa ty d1 = Some (d1', r1') ->
          vmx_set_mmap_spec gpa hpa ty d2 = Some (d2', r2') ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1' = r2'.
      Proof.
        intros id d1 d2 d1' d2' gpa hpa ty r1' r2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold vmx_set_mmap_spec, ept_add_mapping_spec in *.
        rewrite_fld ept; subdestruct; inv Hspec1; inv Hspec2;
        solve [split; try solve_obs_eq Hhp; inv_spec; repeat inv_rewrite'].
      Qed.
*)
      Lemma integ_trap_mmap : 
        forall id (d d' : cdata RData),      
          trap_mmap_spec d = Some d' ->
          high_level_invariant d ->
          id <> cid d -> obs_eq id d d'.
      Proof.
        intros id d d' Hspec Hinv Hid.
        unfold trap_mmap_spec in Hspec.
      Qed.

    End CONF_MMAP.

      (* ptResv is a special case for confidentiality - it is composed of a sequence of specs, some
     of which (ptInsert0_spec in particular) violate noninterference. However, it is possible to
     use high level invariants to prove that ptResv as a whole is nevertheless noninterfering. *)
      Lemma conf_ptResv : 
        forall id (d1 d2 d1' d2' : cdata RData) n vadr pm r1 r2,      
          ptResv_spec n vadr pm d1 = Some (d1', r1) ->
          ptResv_spec n vadr pm d2 = Some (d2', r2) ->
          high_level_invariant d1 -> high_level_invariant d2 ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1 = r2.
      Proof.
        intros id d1 d2 d1' d2' n vadr pm r1 r2 Hspec1 Hspec2 Hinv1 Hinv2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold ptResv_spec in *.
        conf_simpl id conf_palloc d1'' d2'' r.
        subdestruct; inv Hspec1; inv Hspec2; auto.
        split.
        constructor.
        {
          unfold ptInsert0_spec in *.
          clear Hnh; rewrite_fld ptpool; rewrite_fld nps.
          subdestruct; inv H0; inv H1.
          {
            unfold ptInsertPTE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; repeat inv_rewrite'; repeat nonHP_simpl; assumption.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [Hobs _].
            inv Hobs; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto. 
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [Hobs Heq]; subst.
            inv Hobs.
            unfold ptInsertPTE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; repeat inv_rewrite'; repeat nonHP_simpl; assumption.
          }
        }
        {
          unfold ptInsert0_spec in *.
          clear Hnh; rewrite_fld ptpool; rewrite_fld nps.
          subdestruct; inv H0; inv H1.
          {
            unfold ptInsertPTE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; repeat inv_rewrite'.
            {
              intros p' Hown o; inv Hown.
              simpl in H.
              destruct (zeq p' r); subst.
              {
                rewrite ZMap.gss in H; inv H.
                destruct H0.
                inv H.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a0 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev pperm.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply Hhp0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H; auto.
                apply Hhp0; econstructor; eauto.
              }
            }
            {
              intros p' Hown o; inv Hown.
              simpl in H.
              destruct (zeq p' r); subst.
              {
                rewrite ZMap.gss in H; inv H.
                destruct H0.
                inv H.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a0 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev pperm.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply Hhp0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H; auto.
                apply Hhp0; econstructor; eauto.
              }
            }
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [Hobs _].
            inv Hobs; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct14 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
            contradiction n1; auto.
          }
          {
            destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                       Hdestruct15 Hdestruct11 Hobs_eq0) as [Hobs Heq]; subst.
            rename r4 into d1''', r0 into d2'''.
            unfold ptAllocPDE0_spec in *.
            rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps; rewrite_fld AC.
            subdestruct.
            unfold ptInsertPTE0_spec in *.
            inv Hobs; rewrite_fld LAT; rewrite_fld pperm; rewrite_fld ptpool; rewrite_fld nps.
            subdestruct; simpl in *.
            {
              inv Hdestruct11; inv Hdestruct14; inv Hdestruct15; inv Hdestruct18; simpl in *.
              intros p' Hown o; inv Hown.
              simpl in H1.
              destruct (zeq p' r); subst.
              {
                destruct (zeq r2 r); subst.
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                rewrite ZMap.gss in H1; inv H1.
                destruct H2.
                inv H1.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a1 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite 2 FlatMem.free_page_gso; try solve [rewrite pagei_ptaddr; auto].
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev' pperm H1.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply H0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H1; [|auto].
                apply H0; econstructor; eauto.
              }
            }
            {
              inv Hdestruct11; inv Hdestruct14; inv Hdestruct15; inv Hdestruct18; simpl in *.
              intros p' Hown o; inv Hown.
              simpl in H1.
              destruct (zeq p' r); subst.
              {
                destruct (zeq r2 r); subst.
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                rewrite ZMap.gss in H1; inv H1.
                destruct H2.
                inv H1.
                unfold palloc_spec in *.
                inv Hobs_eq; rewrite_fld nps; rewrite_fld LAT; rewrite_fld AC.
                subdestruct; inv Hspec; inv Hspec0; simpl in *.
                assert (Hneq: ZMap.get r (pperm d1) <> PGAlloc).
                {
                  intro Hcon.
                  assert (Hneq: ZMap.get r (pperm d1) <> PGUndef) by 
                      (destruct (ZMap.get r (pperm d1)); inv Hcon; discriminate).
                  destruct a1 as [Hrange [Hlat Hx]].
                  assert (Hrange' : 0 <= r < nps d1) by omega.
                  destruct (valid_pperm_ppage _ Hinv1 _ Hrange') as [Hperm _].
                  destruct (Hperm Hneq) as [n Hlat'].
                  rewrite Hlat in Hlat'; inv Hlat'.
                }
                rewrite 2 FlatMem.free_page_gso; try solve [rewrite pagei_ptaddr; auto].
                rewrite (valid_dirty _ Hinv1 _ Hneq).
                rewrite_fld_rev' pperm H1.
                rewrite (valid_dirty _ Hinv2 _ Hneq).
                rewrite <- (pagei_ptaddr r o) at 2 4.
                rewrite 2 FlatMem.free_page_gss; auto.
                contradiction n0; auto.
                contradiction n0; auto.
                apply H0; econstructor; eauto.
              }
              {
                rewrite ZMap.gso in H1; [|auto].
                apply H0; econstructor; eauto.
              }
            }
            inv Hdestruct11; contradiction n1; auto.
            inv Hdestruct11; contradiction n1; auto.
          }
        }
        {
          unfold ptInsert0_spec in *.
          rewrite_fld nps; rewrite_fld ptpool.
          subdestruct; inv H0; inv H1; auto.
          destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                     Hdestruct14 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
          contradiction n1; auto.
          destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                     Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst.
          contradiction n1; auto.
          destruct (conf_ptAllocPDE0 id _ _ _ _ _ _ _ _ 
                                     Hdestruct15 Hdestruct11 Hobs_eq0) as [_ Heq]; subst; auto.
        }
      Qed.

    End CONF_PTRESV.
*)
(*
    Section CONF_UCTX_ARG.

      Lemma conf_uctx_set_errno :
        forall id (d1 d2 d1' d2' : cdata RData) n,
          uctx_set_errno_spec n d1 = Some d1' ->
          uctx_set_errno_spec n d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        inv_spec; inv Hspec1; inv Hspec2.
        rewrite_fld cid; rewrite_fld uctxt; solve_obs_eq Hhp.
      Qed.

      Lemma conf_uctx_set_retval1 :
        forall id (d1 d2 d1' d2' : cdata RData) n,
          uctx_set_retval1_spec n d1 = Some d1' ->
          uctx_set_retval1_spec n d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        inv_spec; inv Hspec1; inv Hspec2.
        rewrite_fld cid; rewrite_fld uctxt; solve_obs_eq Hhp.
      Qed.

      Lemma conf_uctx_set_retval2 :
        forall id (d1 d2 d1' d2' : cdata RData) n,
          uctx_set_retval2_spec n d1 = Some d1' ->
          uctx_set_retval2_spec n d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        inv_spec; inv Hspec1; inv Hspec2.
        rewrite_fld cid; rewrite_fld uctxt; solve_obs_eq Hhp.
      Qed.

      Lemma conf_uctx_set_retval3 :
        forall id (d1 d2 d1' d2' : cdata RData) n,
          uctx_set_retval3_spec n d1 = Some d1' ->
          uctx_set_retval3_spec n d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        inv_spec; inv Hspec1; inv Hspec2.
        rewrite_fld cid; rewrite_fld uctxt; solve_obs_eq Hhp.
      Qed.

      Lemma conf_uctx_set_retval4 :
        forall id (d1 d2 d1' d2' : cdata RData) n,
          uctx_set_retval4_spec n d1 = Some d1' ->
          uctx_set_retval4_spec n d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        inv_spec; inv Hspec1; inv Hspec2.
        rewrite_fld cid; rewrite_fld uctxt; solve_obs_eq Hhp.
      Qed.

      Lemma conf_uctx_set_retval5 :
        forall id (d1 d2 d1' d2' : cdata RData) n,
          uctx_set_retval5_spec n d1 = Some d1' ->
          uctx_set_retval5_spec n d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' n Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        inv_spec; inv Hspec1; inv Hspec2.
        rewrite_fld cid; rewrite_fld uctxt; solve_obs_eq Hhp.
      Qed.

    End CONF_UCTX_ARG.
*)
    Section INTEG_MMAP.
(*
      Lemma conf_vmx_set_mmap : 
        forall id (d1 d2 d1' d2' : cdata RData) gpa hpa ty r1' r2',
          vmx_set_mmap_spec gpa hpa ty d1 = Some (d1', r1') ->
          vmx_set_mmap_spec gpa hpa ty d2 = Some (d2', r2') ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1' = r2'.
      Proof.
        intros id d1 d2 d1' d2' gpa hpa ty r1' r2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold vmx_set_mmap_spec, ept_add_mapping_spec in *.
        rewrite_fld ept; subdestruct; inv Hspec1; inv Hspec2;
        solve [split; try solve_obs_eq Hhp; inv_spec; repeat inv_rewrite'].
      Qed.
*)
      Lemma integ_trap_mmap : 
        forall id (d d' : cdata RData),      
          trap_mmap_spec d = Some d' ->
          high_level_invariant d ->
          id <> cid d -> obs_eq id d d'.
      Proof.
        intros id d d' Hspec Hinv Hid.
        unfold trap_mmap_spec in Hspec.
      Qed.

    End CONF_MMAP.

    Section CONF_PROC_CREATE.

      Lemma conf_proc_create :
        forall id (d1 d2 d1' d2' : cdata RData) b b' buc ofs q r1 r2,
          proc_create_spec d1 b b' buc ofs q = Some (d1',r1) ->
          proc_create_spec d2 b b' buc ofs q = Some (d2',r2) ->
          obs_eq id d1 d2 -> obs_eq id d1' d2' /\ r1 = r2.
      Proof.
        intros id d1 d2 d1' d2' b b' buc ofs q r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld pb; rewrite_fld kctxt; rewrite_fld abq.
        rewrite_fld abtcb; rewrite_fld uctxt; rewrite_fld AC; rewrite_fld cid.
        subdestruct; inv Hspec1; inv Hspec2.
        split; auto; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_proc_create : 
        forall id (d1 d2 d1' d2' : cdata RData) s m,
          trap_proc_create_spec s m d1 = Some d1' ->
          trap_proc_create_spec s m d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' s m Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl.
        rewrite_fld cid; rewrite_fld AC.
        destruct (zle_le 0 z0
                         (cquota (ZMap.get (cid d1) (AC d1)) -
                          cusage (ZMap.get (cid d1) (AC d1)))).
        conf_arg_simpl.
        elim_none; elim_none; elim_none; elim_none; elim_none; elim_none.
        elim_none; elim_none; elim_none; elim_none; elim_none.
        conf_simpl' id conf_proc_create d1'' d2'' r.
        conf_simpl_noret id conf_uctx_set_retval1 d1''' d2'''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_PROC_CREATE.

    Section CONF_TSC.

      Lemma conf_vmx_set_tsc_offset : 
        forall id (d1 d2 d1' d2' : cdata RData) ofs,
          vmx_set_tsc_offset_spec ofs d1 = Some d1' ->
          vmx_set_tsc_offset_spec ofs d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' ofs Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_get_tsc_offset : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_tsc_offset_spec d1 = Some d1' ->
          trap_get_tsc_offset_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        unfold vmx_get_tsc_offset_spec in *.
        rewrite_fld vmcs.
        subdestruct.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_retval2; eauto.
        eapply conf_uctx_set_retval1; eauto.
      Qed.

      Lemma conf_trap_set_tsc_offset : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_set_tsc_offset_spec d1 = Some d1' ->
          trap_set_tsc_offset_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl.
        conf_simpl_noret id conf_vmx_set_tsc_offset d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_TSC.

    Section CONF_EXITINFO.

      Hint Unfold vmx_get_exit_reason_spec vmx_get_exit_io_port_spec vmx_get_io_width_spec 
           vmx_get_io_write_spec vmx_get_exit_io_rep_spec vmx_get_exit_io_str_spec
           vmx_get_exit_fault_addr_spec.

      Lemma conf_trap_get_exitinfo : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_exitinfo_spec d1 = Some d1' ->
          trap_get_exitinfo_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs; autounfold in *. 
        rewrite_fld vmcs; rewrite_fld vmx; rewrite_fld ikern; rewrite_fld pg; rewrite_fld ihost.
        elim_none; elim_none; elim_none; elim_none; elim_none; elim_none; elim_none.
        conf_simpl_noret id conf_uctx_set_retval1 dr1 dr1'.
        elim_none.
        {
          conf_simpl_noret id conf_uctx_set_retval2 dr2 dr2'.
          conf_simpl_noret id conf_uctx_set_retval3 dr3 dr3'.
          conf_simpl_noret id conf_uctx_set_retval4 dr4 dr4'.
          eapply conf_uctx_set_errno; eauto.
        }
        {
          elim_none.
          conf_simpl_noret id conf_uctx_set_retval2 dr2 dr2'.
          eapply conf_uctx_set_errno; eauto.
          eapply conf_uctx_set_errno; eauto.
        }
      Qed.

    End CONF_EXITINFO.

    Section CONF_REG.

      Lemma conf_vmx_get_reg : 
        forall id (d1 d2 : cdata RData) reg r1 r2,
          vmx_get_reg_spec reg d1 = Some r1 ->
          vmx_get_reg_spec reg d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 reg r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; rewrite_fld vmx; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_vmx_set_reg : 
        forall id (d1 d2 d1' d2' : cdata RData) reg v,
          vmx_set_reg_spec reg v d1 = Some d1' ->
          vmx_set_reg_spec reg v d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' reg v Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; rewrite_fld vmx; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_get_reg : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_reg_spec d1 = Some d1' ->
          trap_get_reg_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; elim_none.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z1) by (eapply conf_vmx_get_reg; eauto); subst.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_trap_set_reg : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_set_reg_spec d1 = Some d1' ->
          trap_set_reg_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl; elim_none.    
        conf_simpl_noret id conf_vmx_set_reg d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_REG.

    Section CONF_SEG.

      Lemma conf_vmx_set_desc : 
        forall id (d1 d2 d1' d2' : cdata RData) seg sel base lim ar,
          vmx_set_desc_spec seg sel base lim ar d1 = Some d1' ->
          vmx_set_desc_spec seg sel base lim ar d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' seg sel base lim ar Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.

      Lemma conf_trap_set_seg : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_set_seg_spec d1 = Some d1' ->
          trap_set_seg_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; elim_none.    
        conf_simpl_noret id conf_vmx_set_desc d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_SEG.

    Section CONF_EIP.

      Lemma conf_vmx_get_next_eip : 
        forall id (d1 d2 : cdata RData) r1 r2,
          vmx_get_next_eip_spec d1 = Some r1 ->
          vmx_get_next_eip_spec d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; rewrite_fld vmx; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_trap_get_next_eip : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_get_next_eip_spec d1 = Some d1' ->
          trap_get_next_eip_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_get_next_eip; eauto); subst; elim_none.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_EIP.

    Section CONF_EVENT.

      Lemma conf_vmx_inject_event : 
        forall id (d1 d2 d1' d2' : cdata RData) ty vec err ev,
          vmx_inject_event_spec ty vec err ev d1 = Some d1' ->
          vmx_inject_event_spec ty vec err ev d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' ty vec err ev Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct'; apply inv_some in Hspec1; 
        apply inv_some in Hspec2; subst; auto; solve_obs_eq Hhp.
      Qed.
      
      Lemma conf_trap_inject_event : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_inject_event_spec d1 = Some d1' ->
          trap_inject_event_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl; conf_arg_simpl; conf_arg_simpl; conf_arg_simpl.
        conf_simpl_noret id conf_vmx_inject_event d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_vmx_check_pending_event : 
        forall id (d1 d2 : cdata RData) r1 r2,
          vmx_check_pending_event_spec d1 = Some r1 ->
          vmx_check_pending_event_spec d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_trap_check_pending_event : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_check_pending_event_spec d1 = Some d1' ->
          trap_check_pending_event_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_check_pending_event; eauto); subst.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_EVENT.

    Section CONF_INT.

      Lemma conf_vmx_check_int_shadow : 
        forall id (d1 d2 : cdata RData) r1 r2,
          vmx_check_int_shadow_spec d1 = Some r1 ->
          vmx_check_int_shadow_spec d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros id d1 d2 r1 r2 Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; auto.
      Qed.

      Lemma conf_vmx_set_intercept_intwin : 
        forall id (d1 d2 d1' d2' : cdata RData) en,
          vmx_set_intercept_intwin_spec en d1 = Some d1' ->
          vmx_set_intercept_intwin_spec en d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' en Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        rewrite_fld vmcs; subdestruct; inv Hspec1; inv Hspec2; solve_obs_eq Hhp.
      Qed.
      
      Lemma conf_trap_check_int_shadow : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_check_int_shadow_spec d1 = Some d1' ->
          trap_check_int_shadow_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_check_int_shadow; eauto); subst.
        conf_simpl_noret id conf_uctx_set_retval1 d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_trap_intercept_int_window : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_intercept_int_window_spec d1 = Some d1' ->
          trap_intercept_int_window_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        conf_arg_simpl. 
        conf_simpl_noret id conf_vmx_set_intercept_intwin d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_INT.

    Section CONF_MSR.

      Lemma conf_rdmsr : 
        forall id (d1 d2 : cdata RData) z r1 r2,
          rdmsr_spec z d1 = Some r1 ->
          rdmsr_spec z d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; rewrites; auto.
      Qed.
      
      Lemma conf_wrmsr : 
        forall id (d1 d2 : cdata RData) z1 z2 r1 r2,
          wrmsr_spec z1 z2 d1 = Some r1 ->
          wrmsr_spec z1 z2 d2 = Some r2 ->
          obs_eq id d1 d2 -> r1 = r2.
      Proof.
        intros; inv_spec; rewrites; auto.
      Qed.

      Lemma conf_trap_handle_rdmsr : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_handle_rdmsr_spec d1 = Some d1' ->
          trap_handle_rdmsr_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none_eqn' Hspec1 Hget1'; elim_none_eqn' Hspec2 Hget2'.
        assert (z = z1) by (eapply conf_rdmsr; eauto); subst; elim_none.
        conf_simpl_noret id conf_vmx_set_reg dr1 dr1'.
        conf_simpl_noret id conf_vmx_set_reg dr2 dr2'.
        elim_none_eqn' Hspec1 Hget1''; elim_none_eqn' Hspec2 Hget2''.
        assert (z1 = z2) by (eapply conf_vmx_get_next_eip; eauto); subst; elim_none.
        conf_simpl_noret id conf_vmx_set_reg dr3 dr3'.
        eapply conf_uctx_set_errno; eauto.
      Qed.

      Lemma conf_trap_handle_wrmsr : 
        forall id (d1 d2 d1' d2' : cdata RData),
          trap_handle_wrmsr_spec d1 = Some d1' ->
          trap_handle_wrmsr_spec d2 = Some d2' ->
          obs_eq id d1 d2 -> obs_eq id d1' d2'.
      Proof.
        intros id d1 d2 d1' d2' Hspec1 Hspec2 Hobs_eq.
        assert (Hobs_eq':= Hobs_eq); destruct Hobs_eq' as [Hnh Hhp].
        unfold_specs.
        elim_none_eqn' Hspec1 Hget1; elim_none_eqn' Hspec2 Hget2.
        assert (z = z0) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none_eqn' Hspec1 Hget1'; elim_none_eqn' Hspec2 Hget2'.
        assert (z = z1) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none_eqn' Hspec1 Hget1''; elim_none_eqn' Hspec2 Hget2''.
        assert (z = z2) by (eapply conf_vmx_get_reg; eauto); subst.
        elim_none' Hspec1; elim_none' Hspec2.
        elim_none_eqn' Hspec1 Hget1''''; elim_none_eqn' Hspec2 Hget2''''.
        assert (z4 = z5) by (eapply conf_vmx_get_next_eip; eauto); subst; elim_none.    
        conf_simpl_noret id conf_vmx_set_reg d1'' d2''.
        eapply conf_uctx_set_errno; eauto.
      Qed.

    End CONF_MSR.


  End INTEG_LEMMAS.



End WITHMEM.

  Ltac rewrites :=
    repeat (match goal with
            | [ Heq1: ?a = _, Heq2: ?a = _ |- _ ] => rewrite Heq2 in Heq1; inv Heq1
            end).

  Ltac rewrite_fld f := 
    match goal with
    | [ Hnh : nonHP_eq ?d1 ?d2 |- _ ] => 
        let H := fresh in (assert (H: f d1 = f d2) by (inv Hnh; auto); rewrite <- H in *; clear H)
    end.

  Ltac rewrite_fld_rev f := 
    match goal with
    | [ Hnh : nonHP_eq ?d1 ?d2 |- _ ] => 
        let H := fresh in (assert (H: f d2 = f d1) by (inv Hnh; auto); rewrite <- H in *; clear H)
    end.

  Ltac rewrite_fld' f Hnh:= 
    match type of Hnh with
    | nonHP_eq ?d1 ?d2 => 
        let H := fresh in (assert (H: f d1 = f d2) by (inv Hnh; auto); rewrite <- H in *; clear H)
    end.

  Ltac rewrite_fld_rev' f Hnh := 
    match type of Hnh with
    | nonHP_eq ?d1 ?d2 => 
        let H := fresh in (assert (H: f d2 = f d1) by (inv Hnh; auto); rewrite <- H in *; clear H)
    end.

  Ltac nonHP_simpl :=
    match goal with
    | [ |- nonHP_eq (update_HP _ _) (update_HP _ _) ] =>
      let H := fresh in let Hnh := fresh in 
        assert (H: forall d1 d2 h1 h2, nonHP_eq d1 d2 -> nonHP_eq (update_HP d1 h1) (update_HP d2 h2)) 
          by (intros ? ? ? ? Hnh; inv Hnh; constructor; auto); apply H; clear H
    | [ |- nonHP_eq (?f _ ?v) (?f _ ?v) ] => 
      let H := fresh in let Hnh := fresh in 
        assert (H: forall d1 d2 x, nonHP_eq d1 d2 -> nonHP_eq (f d1 x) (f d2 x)) 
          by (intros ? ? ? Hnh; inv Hnh; constructor; auto); apply H; clear H
    end.

  Ltac conf_simpl id conf_spec d1' d2' r2 :=
    match goal with
    | [ Hs1: match ?spec ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?a4 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?a4 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 a4 d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 a4 d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 a4 a5 d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 a4 a5 d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 a4 a5 a6 d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 a4 a5 a6 d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    end.

  Ltac conf_simpl' id conf_spec d1' d2' r2 :=
    match goal with
    | [ Hs1: match ?spec ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'') as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'') as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?d1'' ?a1 with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' ?a1 with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'' a1) as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'' a1) as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?d1'' ?a1 ?a2 with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' ?a1 ?a2 with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'' a1 a2) as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'' a1 a2) as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?d1'' ?a1 ?a2 ?a3 with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' ?a1 ?a2 ?a3 with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'' a1 a2 a3) as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'' a1 a2 a3) as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?d1'' ?a1 ?a2 ?a3 ?a4 with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' ?a1 ?a2 ?a3 ?a4 with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'' a1 a2 a3 a4) as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'' a1 a2 a3 a4) as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?d1'' ?a1 ?a2 ?a3 ?a4 ?a5 with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' ?a1 ?a2 ?a3 ?a4 ?a5 with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'' a1 a2 a3 a4 a5) as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'' a1 a2 a3 a4 a5) as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?d1'' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in let Hret := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in let r1 := fresh in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'' a1 a2 a3 a4 a5 a6) as [[d1' r1]|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'' a1 a2 a3 a4 a5 a6) as [[d2' r2]|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2' /\ r1 = r2) by (eapply conf_spec; eauto);
           destruct H as [H Hret]; subst;
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    end.

  Ltac conf_simpl_noret id conf_spec d1' d2' :=
    match goal with
    | [ Hs1: match ?spec ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec d1'') as [d1'|] eqn:Hspec1; [|inv Hs1];
           destruct (spec d2'') as [d2'|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2') by (eapply conf_spec; eauto);
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 d1'') as [d1'|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 d2'') as [d2'|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2') by (eapply conf_spec; eauto);
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 d1'') as [d1'|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 d2'') as [d2'|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2') by (eapply conf_spec; eauto);
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 d1'') as [d1'|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 d2'') as [d2'|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2') by (eapply conf_spec; eauto);
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?a4 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?a4 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 a4 d1'') as [d1'|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 a4 d2'') as [d2'|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2') by (eapply conf_spec; eauto);
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 a4 a5 d1'') as [d1'|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 a4 a5 d2'') as [d2'|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2') by (eapply conf_spec; eauto);
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    | [ Hs1: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?d1'' with Some _ => _ | None => _ end = _,
        Hs2: match ?spec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?d2'' with Some _ => _ | None => _ end = _ |- _ ] =>
        let Hobs_eq := fresh "Hobs_eq" in let H := fresh in
        let Hnh := fresh "Hnh" in let Hhp := fresh "Hhp" in
        let Hspec1 := fresh "Hspec" in let Hspec2 := fresh "Hspec" in 
          (destruct (spec a1 a2 a3 a4 a5 a6 d1'') as [d1'|] eqn:Hspec1; [|inv Hs1];
           destruct (spec a1 a2 a3 a4 a5 a6 d2'') as [d2'|] eqn:Hspec2; [|inv Hs2];
           assert (H: obs_eq id d1' d2') by (eapply conf_spec; eauto);
           assert (Hobs_eq:= H); destruct H as [Hnh Hhp])
    end.

  Ltac conf_arg_simpl :=
      let Harg1 := fresh in let Harg2 := fresh in
      match goal with
      | [ Hs1: match _ _ with Some _ => _ | None => _ end = _,
          Hs2: match _ _ with Some _ => _ | None => _ end = _ |- _ ] =>
        elim_none_eqn' Hs1 Harg1; elim_none_eqn' Hs2 Harg2;
        match type of Harg1 with
        | _ _ = Some ?r => 
        match type of Harg2 with
        | _ _ = Some ?r' =>                           
          assert (r = r') by
              (clear Hs1 Hs2; inv_spec; rewrite_fld uctxt; rewrite_fld cid; rewrites; auto); 
          subst; clear Harg1 Harg2
        end end end.

  Ltac conf_goal :=
    let Harg1 := fresh in let Harg2 := fresh in
      match goal with
      | [ Hs1: match _ _ with Some _ => _ | None => _ end = _,
          Hs2: match _ _ with Some _ => _ | None => _ end = _ |- _ ] => 
        elim_none_eqn' Hs1 Harg1; elim_none_eqn' Hs2 Harg2;
        match type of Harg1 with
        | _ _ = Some ?r => 
        match type of Harg2 with
        | _ _ = Some ?r' =>                           
          assert (r = r'); [clear Hs1 Hs2; unfold_specs|] end end
      | [ Hs1: match _ _ _ with Some _ => _ | None => _ end = _,
          Hs2: match _ _ _ with Some _ => _ | None => _ end = _ |- _ ] => 
        elim_none_eqn' Hs1 Harg1; elim_none_eqn' Hs2 Harg2;
        match type of Harg1 with
        | _ _ _ = Some ?r => 
        match type of Harg2 with
        | _ _ _ = Some ?r' =>                           
          assert (r = r'); [clear Hs1 Hs2; unfold_specs|] end end
      | [ Hs1: match _ _ _ _ with Some _ => _ | None => _ end = _,
          Hs2: match _ _ _ _ with Some _ => _ | None => _ end = _ |- _ ] => 
        elim_none_eqn' Hs1 Harg1; elim_none_eqn' Hs2 Harg2;
        match type of Harg1 with
        | _ _ _ _ = Some ?r => 
        match type of Harg2 with
        | _ _ _ _ = Some ?r' =>                           
          assert (r = r'); [clear Hs1 Hs2; unfold_specs|] end end
      | [ Hs1: match _ _ _ _ _ with Some _ => _ | None => _ end = _,
          Hs2: match _ _ _ _ _ with Some _ => _ | None => _ end = _ |- _ ] => 
        elim_none_eqn' Hs1 Harg1; elim_none_eqn' Hs2 Harg2;
        match type of Harg1 with
        | _ _ _ _ _ = Some ?r => 
        match type of Harg2 with
        | _ _ _ _ _ = Some ?r' =>                           
          assert (r = r'); [clear Hs1 Hs2; unfold_specs|] end end
      | [ Hs1: match _ _ _ _ _ _ with Some _ => _ | None => _ end = _,
          Hs2: match _ _ _ _ _ _ with Some _ => _ | None => _ end = _ |- _ ] => 
        elim_none_eqn' Hs1 Harg1; elim_none_eqn' Hs2 Harg2;
        match type of Harg1 with
        | _ _ _ _ _ _ = Some ?r => 
        match type of Harg2 with
        | _ _ _ _ _ _ = Some ?r' =>                           
          assert (r = r'); [clear Hs1 Hs2; unfold_specs|] end end
      | [ Hs1: match _ _ _ _ _ _ _ with Some _ => _ | None => _ end = _,
          Hs2: match _ _ _ _ _ _ _ with Some _ => _ | None => _ end = _ |- _ ] => 
        elim_none_eqn' Hs1 Harg1; elim_none_eqn' Hs2 Harg2;
        match type of Harg1 with
        | _ _ _ _ _ _ _ = Some ?r => 
        match type of Harg2 with
        | _ _ _ _ _ _ _ = Some ?r' =>                           
          assert (r = r'); [clear Hs1 Hs2; unfold_specs|] end end
      end.

  Ltac solve_obs_eq Hhp :=
    let p := fresh in let Hown := fresh in let o := fresh in
      constructor; [repeat nonHP_simpl; auto |
                    intros p Hown o; inv Hown; apply Hhp; econstructor; eauto].
