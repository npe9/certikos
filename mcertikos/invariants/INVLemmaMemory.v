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
(*              Lemmas for invariants                                  *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.

Section ATABLE.

  Lemma AT_kern_norm:
    forall a np,
      AT_kern a np ->
      forall n b c,
        ZMap.get n a = ATValid b ATNorm c ->
        forall b' c',
          AT_kern (ZMap.set n (ATValid b' ATNorm c') a) np.
  Proof.
    unfold AT_kern; intros.
    destruct (zeq i n); subst.
    - rewrite ZMap.gss.
      exploit H; eauto.
      subrewrite'. intros. congruence.
    - rewrite ZMap.gso; auto.
  Qed.       

  Lemma AT_kern_norm':
    forall a np,
      AT_kern a np ->
      forall n b P1 P2,
        (P1 /\ (exists c, ZMap.get n a = ATValid b ATNorm c) /\ P2)->
        forall b' c',
          AT_kern (ZMap.set n (ATValid b' ATNorm c') a) np.
  Proof.
    intros. destruct H0 as (_ & (c & Hr) & _).
    eapply AT_kern_norm; eauto.
  Qed.       

  Lemma AT_usr_norm:
    forall a np,
      AT_usr a np ->
      forall n b c,
        AT_usr (ZMap.set n (ATValid b ATNorm c) a) np.
  Proof.
    unfold AT_usr; intros.
    destruct (zeq i n); subst.
    - rewrite ZMap.gss. eauto.
    - rewrite ZMap.gso; auto.
  Qed.       

End ATABLE.

Section LATABLE.

  Lemma LAT_kern_norm:
    forall a np,
      LAT_kern a np ->
      forall n b c,
        ZMap.get n a = LATValid b ATNorm c ->
        forall b' c',
          LAT_kern (ZMap.set n (LATValid b' ATNorm c') a) np.
  Proof.
    unfold LAT_kern; intros.
    destruct (zeq i n); subst.
    - rewrite ZMap.gss.
      exploit H; eauto.
      subrewrite'. intros. congruence.
    - rewrite ZMap.gso; auto.
  Qed.       

  Lemma LAT_usr_norm:
    forall a np,
      LAT_usr a np ->
      forall n b c,
        LAT_usr (ZMap.set n (LATValid b ATNorm c) a) np.
  Proof.
    unfold LAT_usr; intros.
    destruct (zeq i n); subst.
    - rewrite ZMap.gss. eauto.
    - rewrite ZMap.gso; auto.
  Qed.       

  Lemma LAT_kern_consistent_pmap:
    forall a np,
      LAT_kern a np ->
      forall ptp p,
        consistent_pmap ptp p a np ->
        forall i,
          0 <= i < num_proc ->
          forall j,
            0<= j < adr_max ->
            forall n x,
              ZMap.get (PDX j) (ZMap.get i ptp) = PDEValid n x ->
              forall b c,
                LAT_kern (ZMap.set n (LATValid b ATNorm c) a) np.
  Proof.
    intros. exploit H0; eauto.
    intros (_ & _ & He).
    eapply LAT_kern_norm; eauto. 
  Qed.       

End LATABLE.

Section DIRTY_PPAGE.

  Lemma dirty_ppage_gso_alloc:
    forall pp h,
      dirty_ppage pp h ->
      forall n,
        dirty_ppage (ZMap.set n PGAlloc pp) h.
  Proof.
    intros. apply dirty_ppage_gso; try assumption.
    red; intros; congruence.
  Qed.

  Lemma dirty_ppage_gso_undef:
    forall pp h,
      dirty_ppage pp h ->
      forall n,
        dirty_ppage (ZMap.set n PGUndef pp) h.
  Proof.
    intros. apply dirty_ppage_gso; try assumption.
    red; intros; congruence.
  Qed.

End DIRTY_PPAGE.

Section PPAGE_INV.

  Lemma consistent_ppage_defined:
    forall a p n,
      consistent_ppage a p n -> 
      forall i,
        ZMap.get i p <> PGUndef ->
        forall o,
          o <> PGUndef ->
          consistent_ppage a (ZMap.set i o p) n.
  Proof.
    unfold consistent_ppage. intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss; split; intros; trivial.
      exploit H; eauto.
      + intros [HG _]. eapply HG. assumption.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_ppage_alloc_hide:
    forall a p n,
      consistent_ppage a p n -> 
      forall i,
        ZMap.get i p = PGAlloc ->
        forall o,
          consistent_ppage a (ZMap.set i (PGHide o) p) n.
  Proof.
    intros. apply consistent_ppage_defined; auto; congruence.
  Qed.

  Lemma consistent_ppage_hide_alloc:
    forall a p n,
      consistent_ppage a p n -> 
      forall i o,
        ZMap.get i p = PGHide o ->
        consistent_ppage a (ZMap.set i PGAlloc p) n.
  Proof.
    intros. apply consistent_ppage_defined; auto; congruence.
  Qed.

  Lemma consistent_ppage_norm_alloc:
    forall a p np,
      consistent_ppage a p np ->
      forall n c,
        consistent_ppage (ZMap.set n (ATValid true ATNorm c) a)
                         (ZMap.set n PGAlloc p) np.
  Proof.
    unfold consistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros; eauto.
      red; intros HM'; inv HM'.
    + repeat rewrite ZMap.gso; auto.
  Qed.

  Lemma consistent_ppage_norm_hide:
    forall a p np,
      consistent_ppage a p np ->
      forall n c o,
        consistent_ppage (ZMap.set n (ATValid true ATNorm c) a)
                         (ZMap.set n (PGHide o) p) np.
  Proof.
    unfold consistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros; eauto.
      red; intros HM'; inv HM'.
    + repeat rewrite ZMap.gso; auto.
  Qed.

  Lemma consistent_ppage_norm_undef:
    forall a p np,
      consistent_ppage a p np ->
      forall n c,
        consistent_ppage (ZMap.set n (ATValid false ATNorm c) a)
                         (ZMap.set n PGUndef p) np.
  Proof.
    unfold consistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros HM.
      elim HM. trivial. intros HF. inv HF.
    + repeat rewrite ZMap.gso; auto.
  Qed.

  Lemma consistent_ppage_norm:
    forall a p np,
      consistent_ppage a p np ->
      forall n c,
        ZMap.get n a = ATValid true ATNorm c ->
        forall c',
          consistent_ppage (ZMap.set n (ATValid true ATNorm c') a) p np.
  Proof.
    unfold consistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros; eauto.
      exploit H; eauto.
      intros [_ HP]. eapply HP; eauto.
    + repeat rewrite ZMap.gso; auto.
  Qed.

End PPAGE_INV.

Section LPPAGE_INV.

  Lemma Lconsistent_ppage_defined:
    forall a p n,
      Lconsistent_ppage a p n -> 
      forall i,
        ZMap.get i p <> PGUndef ->
        forall o,
          o <> PGUndef ->
          Lconsistent_ppage a (ZMap.set i o p) n.
  Proof.
    unfold Lconsistent_ppage. intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss; split; intros; trivial.
      exploit H; eauto.
      + intros [HG _]. eapply HG. assumption.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma Lconsistent_ppage_alloc_hide:
    forall a p n,
      Lconsistent_ppage a p n -> 
      forall i,
        ZMap.get i p = PGAlloc ->
        forall o,
          Lconsistent_ppage a (ZMap.set i (PGHide o) p) n.
  Proof.
    intros. apply Lconsistent_ppage_defined; auto; congruence.
  Qed.

  Lemma Lconsistent_ppage_hide_alloc:
    forall a p n,
      Lconsistent_ppage a p n -> 
      forall i o,
        ZMap.get i p = PGHide o ->
        Lconsistent_ppage a (ZMap.set i PGAlloc p) n.
  Proof.
    intros. apply Lconsistent_ppage_defined; auto; congruence.
  Qed.

  Lemma Lconsistent_ppage_norm_alloc:
    forall a p np,
      Lconsistent_ppage a p np ->
      forall n c,
        Lconsistent_ppage (ZMap.set n (LATValid true ATNorm c) a)
                          (ZMap.set n PGAlloc p) np.
  Proof.
    unfold Lconsistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros; eauto.
      red; intros HM'; inv HM'.
    + repeat rewrite ZMap.gso; auto.
  Qed.

  Lemma Lconsistent_ppage_norm_hide:
    forall a p np,
      Lconsistent_ppage a p np ->
      forall n c o,
        Lconsistent_ppage (ZMap.set n (LATValid true ATNorm c) a)
                          (ZMap.set n (PGHide o) p) np.
  Proof.
    unfold Lconsistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros; eauto.
      red; intros HM'; inv HM'.
    + repeat rewrite ZMap.gso; auto.
  Qed.

  Lemma Lconsistent_ppage_norm_undef:
    forall a p np,
      Lconsistent_ppage a p np ->
      forall n c,
        Lconsistent_ppage (ZMap.set n (LATValid false ATNorm c) a)
                          (ZMap.set n PGUndef p) np.
  Proof.
    unfold Lconsistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros HM.
      elim HM. trivial. intros HF. inv HF.
    + repeat rewrite ZMap.gso; auto.
  Qed.

  Lemma Lconsistent_ppage_norm:
    forall a p np,
      Lconsistent_ppage a p np ->
      forall n c,
        ZMap.get n a = LATValid true ATNorm c ->
        forall c',
          Lconsistent_ppage (ZMap.set n (LATValid true ATNorm c') a) p np.
  Proof.
    unfold Lconsistent_ppage; intros.
    destruct (zeq i n); subst.
    + repeat rewrite ZMap.gss.
      split; intros; eauto.
      exploit H; eauto.
      intros [_ HP]. eapply HP; eauto.
    + repeat rewrite ZMap.gso; auto.
  Qed.

End LPPAGE_INV.

Section PMAP_INV.

  Lemma consistent_pmap_gso_at:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i,
        ZMap.get i a <> LATValid true ATNorm nil ->
        forall pp aa,
          consistent_pmap ptp (ZMap.set i pp p) (ZMap.set i aa a) n.
  Proof.
    unfold consistent_pmap; intros.
    destruct (zeq pi i); subst.
    - exploit H; eauto.
      intros (_ & _ & HP).
      congruence.
    - repeat rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_pmap_gso_at_false:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i an c,
        ZMap.get i a = LATValid false an c ->
        forall pp aa,
          consistent_pmap ptp (ZMap.set i pp p) (ZMap.set i aa a) n.
  Proof.
    intros. eapply consistent_pmap_gso_at; eauto.
    congruence.
  Qed.

  Lemma consistent_pmap_gso_pperm:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i,
        (forall o, ZMap.get i p <> PGHide o) ->
        forall pp aa,
          consistent_pmap ptp (ZMap.set i pp p) (ZMap.set i aa a) n.
  Proof.
    unfold consistent_pmap; intros.
    destruct (zeq pi i); subst.
    - exploit H; eauto.
      intros (_ & HP & _).
      congruence.
    - repeat rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_pmap_gso_pperm_alloc:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i,
        ZMap.get i p = PGAlloc ->
        forall pp aa,
          consistent_pmap ptp (ZMap.set i pp p) (ZMap.set i aa a) n.
  Proof.
    intros. eapply consistent_pmap_gso_pperm; eauto.
    congruence.
  Qed.

  Lemma consistent_pmap_gso_pperm':
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i,
        (forall o, ZMap.get i p <> PGHide o) ->
        forall aa,
          consistent_pmap ptp p (ZMap.set i aa a) n.
  Proof.
    unfold consistent_pmap; intros.
    destruct (zeq pi i); subst.
    - exploit H; eauto.
      intros (_ & HP & _).
      congruence.
    - repeat rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_pmap_gso_pperm_alloc':
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i,
        ZMap.get i p = PGAlloc ->
        forall aa,
          consistent_pmap ptp p (ZMap.set i aa a) n.
  Proof.
    intros. eapply consistent_pmap_gso_pperm'; eauto.
    congruence.
  Qed.

  Lemma consistent_pmap_ptp_same:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i pdi pi pdt,
        ZMap.get pdi (ZMap.get i ptp) = PDEValid pi pdt ->
        forall pdt',
          consistent_pmap (ZMap.set i (ZMap.set pdi (PDEValid pi pdt') (ZMap.get i ptp)) ptp) p a n.
  Proof.
    unfold consistent_pmap. intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *.
      destruct (zeq pdi (PDX j)); subst.
      + rewrite ZMap.gss in *. inv H3.         
        exploit H; eauto.
      + rewrite ZMap.gso in *; eauto.
    - rewrite ZMap.gso in *; eauto.
  Qed.

  Lemma consistent_pmap_at_same:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      consistent_pmap_domain ptp p a n ->
      forall i,
        0<= i < num_proc ->
        forall vadr,
          0<= vadr < adr_max ->
          forall pi pdt,
            ZMap.get (PDX vadr) (ZMap.get i ptp) = PDEValid pi pdt ->
            forall z x,
              ZMap.get (PTX vadr) pdt = PTEValid z x ->
              forall v,
                consistent_pmap ptp p (ZMap.set z v a) n.
  Proof.
    unfold consistent_pmap, consistent_pmap_domain. intros.
    exploit (H0 _ H1 vadr); try eassumption.
    intros (_ & Hp & _).
    destruct (zeq pi0 z); subst.
    - exploit H; eauto. rewrite Hp.
      intros (_ & HF & _). inv HF.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_pmap_at_ptp_same:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      consistent_pmap_domain ptp p a n ->
      forall i,
        0<= i < num_proc ->
        forall vadr,
          0<= vadr < adr_max ->
          forall pi pdt,
            ZMap.get (PDX vadr) (ZMap.get i ptp) = PDEValid pi pdt ->
            forall z x,
              ZMap.get (PTX vadr) pdt = PTEValid z x ->
              forall pdt' v,
                consistent_pmap (ZMap.set i (ZMap.set (PDX vadr) (PDEValid pi pdt') (ZMap.get i ptp)) ptp)
                                p (ZMap.set z v a) n.
  Proof.
    intros. eapply consistent_pmap_ptp_same; eauto.
    eapply consistent_pmap_at_same; eauto.
  Qed.

  Lemma consistent_pmap_ptp_gss:
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i pdi v pte,
        0 < v < n ->
        ZMap.get v a = LATValid false ATNorm nil ->
        consistent_pmap (ZMap.set i (ZMap.set pdi (PDEValid v pte) (ZMap.get i ptp)) ptp) 
                        (ZMap.set v (PGHide (PGPMap i pdi)) p) 
                        (ZMap.set v (LATValid true ATNorm nil) a) n.
  Proof.
    unfold consistent_pmap. intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *.
      destruct (zeq pdi (PDX j)); subst.
      + rewrite ZMap.gss in *. inv H4.
        repeat rewrite ZMap.gss. eauto.
      + rewrite ZMap.gso in H4; eauto.
        destruct (zeq pi v); subst.
        * exploit H; eauto.
          intros (_ & _ & He). congruence.
        * repeat rewrite ZMap.gso; eauto.
    - rewrite ZMap.gso in H4; eauto.
      destruct (zeq pi v); subst.
      * exploit H; eauto.
        intros (_ & _ & He). congruence.
      * repeat rewrite ZMap.gso; eauto.          
  Qed.

  Lemma consistent_pmap_ptp_gss':
    forall ptp p a n,
      consistent_pmap ptp p a n ->
      forall i,
        0 <= i < num_proc ->
        forall vadr,
          0 <= vadr < adr_max ->
          forall v x,
            ZMap.get (PDX vadr) (ZMap.get i ptp) = PDEValid v x ->
            consistent_pmap (ZMap.set i (ZMap.set (PDX vadr) PDEUnPresent (ZMap.get i ptp)) ptp) 
                            (ZMap.set v PGUndef p) 
                            (ZMap.set v (LATValid false ATNorm nil) a) n.
  Proof.
    unfold consistent_pmap. intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *.
      destruct (zeq (PDX vadr) (PDX j)).
      + rewrite e in *. rewrite ZMap.gss in *. congruence.
      + rewrite ZMap.gso in H5; eauto.
        destruct (zeq pi v); subst.
        * exploit H; eauto. intros (_ & He & _). clear H4.
          exploit H; eauto. intros (_ & He' & _). congruence.
        * repeat rewrite ZMap.gso; eauto.
    - rewrite ZMap.gso in H5; eauto.
      destruct (zeq pi v); subst.
      * exploit H; eauto. intros (_ & He & _). clear H3 H4.
        exploit H; eauto. intros (_ & He' & _). congruence.
      * repeat rewrite ZMap.gso; eauto.          
  Qed.

End PMAP_INV.

Section PMAP_DOMAIN_INV.

  Lemma consistent_pmap_domain_gso_at:
    forall ptp p a n,
      consistent_pmap_domain ptp p a n ->
      forall i,
        (forall c,
           c <> nil ->
           ZMap.get i a <> LATValid true ATNorm c) ->
        forall pp aa,
          consistent_pmap_domain ptp (ZMap.set i pp p) (ZMap.set i aa a) n.
  Proof.
    unfold consistent_pmap_domain; intros.
    destruct (zeq v i); subst.
    - exploit H; eauto.
      intros (_ & _ & n0 & HP & Hgt).
      assert (Hgt': n0 <> nil).
      {
        red; intros; subst. inv Hgt.
      }
      specialize (H0 _ Hgt').
      congruence.
    - repeat rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_pmap_domain_gso_at_false:
    forall ptp p a n,
      consistent_pmap_domain ptp p a n ->
      forall i an c,
        ZMap.get i a = LATValid false an c ->
        forall pp aa,
          consistent_pmap_domain ptp (ZMap.set i pp p) (ZMap.set i aa a) n.
  Proof.
    intros. eapply consistent_pmap_domain_gso_at; eauto.
    congruence.
  Qed.

  Lemma consistent_pmap_domain_gso_at_0:
    forall ptp p a n,
      consistent_pmap_domain ptp p a n ->
      forall i,
        ZMap.get i a = LATValid true ATNorm nil ->
        forall pp aa,
          consistent_pmap_domain ptp (ZMap.set i pp p) (ZMap.set i aa a) n.
  Proof.
    intros. eapply consistent_pmap_domain_gso_at; eauto.
    subrewrite'. red; intros. congruence.
  Qed.

  Lemma consistent_pmap_domain_ptp_unp:
    forall ptp p a n,
      consistent_pmap_domain ptp p a n ->
      forall i pdi pte v,
        (forall j,
           0 <= j < one_k ->
           ZMap.get j pte = PTEUnPresent) ->
        consistent_pmap_domain (ZMap.set i (ZMap.set pdi (PDEValid v pte) (ZMap.get i ptp)) ptp) p a n.
  Proof.
    unfold consistent_pmap_domain. intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *.
      destruct (zeq pdi (PDX j)); subst.
      + rewrite ZMap.gss in *. inv H3.
        rewrite H0 in H4. congruence.
        apply Z_mod_lt. omega.            
      + rewrite ZMap.gso in H3; eauto.
    - rewrite ZMap.gso in H3; eauto.
  Qed.

  Lemma consistent_pmap_domain_ptp_pde_unp:
    forall ptp p a n,
      consistent_pmap_domain ptp p a n ->
      forall i pdi,
        consistent_pmap_domain (ZMap.set i (ZMap.set pdi PDEUnPresent (ZMap.get i ptp)) ptp) p a n.
  Proof.
    unfold consistent_pmap_domain. intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *.
      destruct (zeq pdi (PDX j)); subst.
      + rewrite ZMap.gss in *. congruence. 
      + rewrite ZMap.gso in H2; eauto.
    - rewrite ZMap.gso in H2; eauto.
  Qed.

  Lemma Lremove_count_outside:
    forall l x y, y <> x -> count_occ LATOwner_dec (Lremove x l) y = count_occ LATOwner_dec l y.
  Proof.
    induction l; intros.
    - trivial.
    - simpl.
      destruct (LATOwner_dec x a).
      + destruct (LATOwner_dec a y).
        * congruence.
        * eauto.
      + destruct (LATOwner_dec a y); subst.
        * rewrite count_occ_cons_eq; trivial.
          rewrite IHl; trivial.
        * rewrite count_occ_cons_neq; auto.
  Qed.

  Lemma consistent_pmap_domain_remove:
    forall ptp p a n,
      consistent_pmap_domain ptp p a n ->
      forall i pdi pi pdt,
        ZMap.get pdi (ZMap.get i ptp) = PDEValid pi pdt ->
        forall pti z x,
          ZMap.get pti pdt = PTEValid z x ->
          forall l,
            ZMap.get z a = LATValid true ATNorm l ->
            consistent_pmap_domain (ZMap.set i (ZMap.set pdi (PDEValid pi (ZMap.set pti PTEUnPresent pdt)) 
                                                         (ZMap.get i ptp)) ptp) p
                                   (ZMap.set z (LATValid true ATNorm (Lremove (LATO i pdi pti) l)) a) n.
  Proof.
    unfold consistent_pmap_domain. intros. 
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *.
      destruct (zeq pdi (PDX j)); subst.
      + rewrite ZMap.gss in *. inv H5.
        destruct (zeq pti (PTX j)); subst.
        * rewrite ZMap.gss in *. congruence.
        * rewrite ZMap.gso in H6; auto.
          exploit H; eauto. 
          intros (Hr & He & Hex).
          destruct (zeq v z); subst.
          {
            rewrite ZMap.gss.
            destruct Hex as (l' & He' & Hin).
            rewrite H2 in He'. inv He'.
            split; auto.
            refine_split'; trivial.
            rewrite Lremove_count_outside; eauto.
            congruence.
          }
          {
            rewrite ZMap.gso; eauto.
          }
      + rewrite ZMap.gso in H5; eauto.
        exploit H; eauto.
        intros (Hr & He & Hex).
        destruct (zeq v z); subst.
        {
          rewrite ZMap.gss.
          destruct Hex as (l' & He' & Hin).
          rewrite H2 in He'. inv He'.
          split; auto.
          refine_split'; trivial.
          rewrite Lremove_count_outside; eauto.
          congruence.
        }
        {
          rewrite ZMap.gso; eauto.
        }
    - rewrite ZMap.gso in H5; eauto.
      exploit H; eauto.
      intros (Hr & He & Hex).
      destruct (zeq v z); subst.
      {
        rewrite ZMap.gss.
        destruct Hex as (l' & He' & Hin).
        rewrite H2 in He'. inv He'.
        split; auto.
        refine_split'; trivial.
        rewrite Lremove_count_outside; eauto.
        congruence.
      }
      {
        rewrite ZMap.gso; eauto.
      }
  Qed.

  Lemma consistent_pmap_domain_append:
    forall ptp p a n,
      consistent_pmap_domain ptp p a n ->
      forall HConsist: (consistent_lat_domain ptp a n),
      forall i pdi pi pdt,
        ZMap.get pdi (ZMap.get i ptp) = PDEValid pi pdt ->
        forall pti z l,
          0 < z < n ->
          ZMap.get z a = LATValid true ATNorm l ->
          ZMap.get z p = PGAlloc ->
          forall x,
          forall Hnot: (~ (exists v0 p0, ZMap.get pti pdt = PTEValid v0 p0)),
            consistent_pmap_domain (ZMap.set i (ZMap.set pdi (PDEValid pi (ZMap.set pti (PTEValid z x) pdt)) 
                                                         (ZMap.get i ptp)) ptp) p
                                   (ZMap.set z (LATValid true ATNorm ((LATO i pdi pti) :: l)) a) n.
  Proof.
    unfold consistent_pmap_domain. intros. 
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *.
      destruct (zeq pdi (PDX j)); subst.
      + rewrite ZMap.gss in *. inv H6.
        destruct (zeq pti (PTX j)); subst.
        * rewrite ZMap.gss in *. inv H7.
          rewrite ZMap.gss. split; trivial.
          refine_split'; trivial.
          simpl.
          destruct (LATOwner_dec (LATO i0 (PDX j) (PTX j)) (LATO i0 (PDX j) (PTX j))); try congruence.
          assert (HnotInQ: ~ In (LATO i0 (PDX j) (PTX j)) l).
          {
            red; intros.
            exploit HConsist; eauto. intros.
            elim Hnot. destruct H7 as (_ & pi & pte & HR1 & p1 & HR2).
            rewrite H0 in HR1. inv HR1.
            rewrite HR2. eauto.
          }
          assert (Heq: count_occ LATOwner_dec l (LATO i0 (PDX j) (PTX j)) = O).
          {
            destruct (count_occ LATOwner_dec l (LATO i0 (PDX j) (PTX j))) eqn: Heq; trivial.
            elim HnotInQ.
            apply <- (count_occ_In LATOwner_dec). rewrite Heq. omega.
          }
          rewrite Heq. trivial.
        * rewrite ZMap.gso in H7; auto.
          exploit H; eauto.
          intros (Hr & He & Hex).
          split; trivial. split; trivial.
          destruct (zeq v z); subst.
          {
            rewrite ZMap.gss.
            destruct Hex as (l' & He' & Hin).
            rewrite H2 in He'. inv He'.
            refine_split'; trivial.
            simpl.
            destruct (LATOwner_dec (LATO i0 (PDX j) pti) (LATO i0 (PDX j) (PTX j))); try congruence.
          }
          {
            rewrite ZMap.gso; eauto.
          }
      + rewrite ZMap.gso in H6; eauto.
        exploit H; eauto.
        intros (Hr & He & Hex).
        destruct (zeq v z); subst.
        {
          rewrite ZMap.gss.
          destruct Hex as (l' & He' & Hin).
          rewrite H2 in He'. inv He'.
          split; auto.
          refine_split'; trivial.
          simpl.
          destruct (LATOwner_dec (LATO i0 pdi pti) (LATO i0 (PDX j) (PTX j))); try congruence.
        }
        {
          rewrite ZMap.gso; eauto.
        }
    - rewrite ZMap.gso in H6; eauto.
      exploit H; eauto.
      intros (Hr & He & Hex).
      destruct (zeq v z); subst.
      {
        rewrite ZMap.gss.
        destruct Hex as (l' & He' & Hin).
        rewrite H2 in He'. inv He'.
        split; auto.
        refine_split'; trivial.
        simpl.
        destruct (LATOwner_dec (LATO i pdi pti) (LATO i0 (PDX j) (PTX j))); try congruence.
      }
      {
        rewrite ZMap.gso; eauto.
      }
  Qed.

End PMAP_DOMAIN_INV.

Section LAT_DOMAIN_INV.

  Lemma consistent_lat_domain_gss_nil:
    forall p a n,
      consistent_lat_domain p a n ->
      forall i t m,
        consistent_lat_domain p (ZMap.set i (LATValid t m nil) a) n.
  Proof.
    unfold consistent_lat_domain; intros.
    destruct (zeq v i); subst.
    - rewrite ZMap.gss in H1. inv H1. inv H2.
    - rewrite ZMap.gso in H1; eauto.
  Qed.

  Lemma consistent_lat_domain_gss_remove:
    forall a z l p n ppt,
      ZMap.get z a = LATValid true ATNorm l ->
      consistent_lat_domain p a n ->
      consistent_pmap_domain p ppt a n ->
      forall i j pi pdt p',
        0 <= i < 64 ->
        0 <= j < 4294967296 ->
        ZMap.get (PDX j) (ZMap.get i p) = PDEValid pi pdt ->
        ZMap.get (PTX j) pdt = PTEValid z p' ->
        consistent_lat_domain
          (ZMap.set i (ZMap.set (PDX j) (PDEValid pi (ZMap.set (PTX j) PTEUnPresent pdt)) 
                                (ZMap.get i p)) p)
          (ZMap.set z (LATValid true ATNorm (Lremove (LATO i (PDX j) (PTX j)) l)) a) n.
  Proof.
    unfold consistent_lat_domain; intros. 
    destruct (zeq v z); subst.
    - rewrite ZMap.gss in *. inv H7.
      destruct (zeq n0 i); subst.
      + rewrite ZMap.gss.
        destruct (zeq pdi (PDX j)); subst.
        * rewrite ZMap.gss.
          destruct (zeq pti (PTX j)); subst.
          {
            contradict H8.
            eapply remove_In; eauto.
          }
          {
            assert (In (LATO i (PDX j) pti) l).
            {
              eapply Lremove_incl in H8. trivial.
            }
            exploit H0; eauto.
            rewrite H4. intros (Hrange & pi0 & pte & HR1 & p0 & HR2).
            inv HR1.
            refine_split'; trivial.
            rewrite ZMap.gso; eauto. 
          }
        * rewrite ZMap.gso; eauto.
          eapply H0; eauto.
          eapply Lremove_incl; eauto.
      + rewrite ZMap.gso; eauto.
        eapply H0; eauto.
        eapply Lremove_incl; eauto.
    - rewrite ZMap.gso in H7; eauto.
      exploit H1; eauto.
      rewrite H. intros (_ & _ & HP).
      destruct HP as (l1 & He & Hc). inv He.
      assert (HIn: In (LATO i (PDX j) (PTX j)) l1).
      {
        eapply (count_occ_In LATOwner_dec). omega.
      }
      destruct (zeq i n0); subst.
      exploit H0; eauto.
      + rewrite ZMap.gss.
        destruct (zeq pdi (PDX j)); subst.
        * rewrite ZMap.gss.
          destruct (zeq pti (PTX j)); subst.
          {            
            rewrite H4. intros (Hrange & pi0 & pte & HR1 & HR2).
            inv HR1. rewrite H5 in HR2.
            destruct HR2 as (p0 & He). inv He.
            congruence.
          }
          {
            rewrite H4. intros (Hrange & pi0 & pte & HR1 & HR2).
            inv HR1. destruct HR2 as(p0 & He).
            refine_split'; trivial.
            rewrite ZMap.gso; eauto.
          }
        * rewrite ZMap.gso; eauto.
      + rewrite ZMap.gso; eauto.
  Qed.

  Lemma Lremove_outside:
    forall (l: list LATOwner) x y, y <> x -> In y l -> In y (Lremove x l).
  Proof.
    induction l; intros.
    - inv H0.
    - simpl. destruct (LATOwner_dec x a); subst.
      + inv H0. congruence. auto.
      + inv H0. left; trivial.
        right; auto.
  Qed.

  Require Import Integers.

  Lemma PTX_range:
    forall i,
      0 <= PTX i <= PTX Int.max_unsigned.
  Proof.
    rewrite_omega.
    unfold PTX.
    intros.
    exploit (Z_mod_lt (i / 4096) 1024);
      intros; omega.
  Qed.

  Lemma consistent_lat_domain_gss_append:
    forall a p n,
      consistent_lat_domain p a n ->
      (*consistent_pmap_domain p ppt a n ->*)
      forall i pdi j pi pdt z pp l,
        ZMap.get pdi (ZMap.get i p) = PDEValid pi pdt ->
        ZMap.get z a = LATValid true ATNorm l ->
        ~ (exists v' p', ZMap.get (PTX j) pdt = PTEValid v' p') ->
        consistent_lat_domain
          (ZMap.set i (ZMap.set pdi (PDEValid pi (ZMap.set (PTX j) (PTEValid z pp) pdt)) 
                                (ZMap.get i p)) p)
          (ZMap.set z (LATValid true ATNorm ((LATO i pdi (PTX j)) :: l)) a) n.
  Proof.
    unfold consistent_lat_domain; intros. 
    destruct (zeq v z); subst.
    - rewrite ZMap.gss in *. inv H4.
      destruct (zeq n0 i); subst.
      + rewrite ZMap.gss.
        destruct (zeq pdi pdi0); subst.
        * rewrite ZMap.gss.
          destruct (zeq pti (PTX j)); subst.
          {
            refine_split'; trivial.
            eapply PTX_range.
            rewrite ZMap.gss; trivial.
          }
          {
            inv H5; try congruence.
            exploit H; eauto.
            rewrite H0.
            intros (Hrange & pi0 & pte & HR1 & p0 & HR2).
            inv HR1.
            refine_split'; trivial.
            rewrite ZMap.gso; eauto.
          }
        * rewrite ZMap.gso; eauto.
          eapply H; eauto.
          inv H5; try congruence.
      + rewrite ZMap.gso; eauto.
        eapply H; eauto.
        inv H5; try congruence.
    - rewrite ZMap.gso in H4; eauto.
      destruct (zeq i n0); subst.
      + rewrite ZMap.gss.
        destruct (zeq pdi pdi0); subst.
        * rewrite ZMap.gss.
          exploit H; eauto.
          rewrite H0.
          intros (Hrange & pi0 & pte & HR1 & HR2).
          inv HR1.
          destruct (zeq pti (PTX j)); subst.
          {
            elim H2; eauto.
          }
          {
            destruct HR2 as (p0 & HR2).
            refine_split'; trivial.
            rewrite ZMap.gso; eauto.
          }
        * rewrite ZMap.gso; eauto.
      + rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_lat_domain_gso_p:
    forall p a np pdi,
      consistent_lat_domain p a np ->
      forall pd n,
        ZMap.get pdi (ZMap.get n p) = PDEUnPresent ->
        consistent_lat_domain
          (ZMap.set n (ZMap.set pdi pd (ZMap.get n p)) p) a np.
  Proof.
    unfold consistent_lat_domain; intros. 
    destruct (zeq n0 n); subst.
    - rewrite ZMap.gss.
      destruct (zeq pdi pdi0); subst.
      + rewrite ZMap.gss.
        exploit H; eauto.
        rewrite H0.
        intros (Hrange & pi0 & pte & HR1 & _).
        inv HR1.
      + rewrite ZMap.gso; eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma consistent_lat_domain_gso_free:
    forall p a np pdi,
      consistent_lat_domain p a np ->
      forall pd n pte pi,
        ZMap.get pdi (ZMap.get n p) = PDEValid pi pte ->
        (forall i, 0 <= i <= PTX Int.max_unsigned
                   -> ZMap.get i pte = PTEUnPresent) ->
        consistent_lat_domain
          (ZMap.set n (ZMap.set pdi pd (ZMap.get n p)) p) a np.
  Proof.
    unfold consistent_lat_domain; intros. 
    destruct (zeq n0 n); subst.
    - rewrite ZMap.gss.
      destruct (zeq pdi pdi0); subst.
      + rewrite ZMap.gss.
        exploit H; eauto.
        rewrite H0.
        intros (Hrange & pi0 & pte' & HR1 & HE2).
        inv HR1.
        specialize(H1 _ Hrange).
        rewrite H1 in HE2.
        destruct HE2 as (? & He). inv He.
      + rewrite ZMap.gso; eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

End LAT_DOMAIN_INV.

Section PMAP_VALID_KERN_INV.

  Lemma PMap_valid_gso:
    forall ptp i,
      PMap_valid (ZMap.get i ptp) ->
      forall i' pdi pi pdt,
        ZMap.get pdi (ZMap.get i' ptp) = PDEValid pi pdt ->
        forall pti p,
          p <> PTEUndef ->
          PMap_valid
            (ZMap.get i (ZMap.set i' (ZMap.set pdi (PDEValid pi (ZMap.set pti p pdt)) 
                                               (ZMap.get i' ptp)) ptp)).
  Proof.
    unfold PMap_valid; intros.
    destruct (zeq i i'); subst.
    - rewrite ZMap.gss.
      destruct H as (HP1 & HP2). split.
      + unfold PMap_common, PDE_kern in *. intros. 
        destruct (zeq pdi (PDX (i * PgSize))); subst.
        * erewrite HP1 in H0; eauto. congruence.
        * rewrite ZMap.gso; auto.
      + unfold PMap_usr, PDE_usr in *. intros.
        destruct (zeq pdi (PDX (i * PgSize))); subst.
        * rewrite ZMap.gss. right. right.
          exploit HP2; eauto.
          intros HP. destruct HP as [HP | [HP| HP]]; try congruence.
          destruct HP as (pte & pi' & HE & HN).
          rewrite H0 in HE. inv HE.
          refine_split'. reflexivity.
          destruct (zeq pti (PTX (i * PgSize))); subst.
          {
            rewrite ZMap.gss. congruence.
          }              
          {
            rewrite ZMap.gso; auto.
          }
        * rewrite ZMap.gso; auto.
    - rewrite ZMap.gso; auto.
  Qed.

  Lemma PMap_valid_gso_unp:
    forall ptp i,
      PMap_valid (ZMap.get i ptp) ->
      forall i' pdi pi pdt,
        ZMap.get pdi (ZMap.get i' ptp) = PDEValid pi pdt ->
        forall pti,
          PMap_valid
            (ZMap.get i (ZMap.set i' (ZMap.set pdi (PDEValid pi (ZMap.set pti PTEUnPresent pdt)) 
                                               (ZMap.get i' ptp)) ptp)).
  Proof.
    intros. eapply PMap_valid_gso; eauto. congruence.
  Qed.

  Lemma PMap_valid_gso_valid:
    forall ptp i,
      PMap_valid (ZMap.get i ptp) ->
      forall i' pdi pi pdt,
        ZMap.get pdi (ZMap.get i' ptp) = PDEValid pi pdt ->
        forall pti v p,
          PMap_valid
            (ZMap.get i (ZMap.set i' (ZMap.set pdi (PDEValid pi (ZMap.set pti (PTEValid v p) pdt)) 
                                               (ZMap.get i' ptp)) ptp)).
  Proof.
    intros. eapply PMap_valid_gso; eauto. congruence.
  Qed.

  Lemma PMap_kern_gso:
    forall ptp,
      PMap_kern (ZMap.get 0 ptp) ->
      forall i,
        0 < i < num_proc ->
        forall pt,
          PMap_kern (ZMap.get 0 (ZMap.set i pt ptp)).
  Proof.
    intros. rewrite ZMap.gso; auto. 
    red; intros; subst. omega.
  Qed.

  Lemma PMap_valid_gso_pde_unp:
    forall ptp i,
      PMap_valid (ZMap.get i ptp) ->
      forall i' pdi,
        ZMap.get pdi (ZMap.get i' ptp) = PDEUnPresent ->
        forall v pt,
          (forall i,
             0 <= i < one_k ->
             ZMap.get i pt <> PTEUndef) ->
          PMap_valid
            (ZMap.get i (ZMap.set i' (ZMap.set pdi (PDEValid v pt) 
                                               (ZMap.get i' ptp)) ptp)).
  Proof.
    unfold PMap_valid; intros.
    destruct (zeq i i'); subst.
    - rewrite ZMap.gss.
      destruct H as (HP1 & HP2). split.
      + unfold PMap_common, PDE_kern in *. intros. 
        destruct (zeq pdi (PDX (i * PgSize))); subst.
        * erewrite HP1 in H0; eauto. congruence.
        * rewrite ZMap.gso; auto.
      + unfold PMap_usr, PDE_usr in *. intros.
        destruct (zeq pdi (PDX (i * PgSize))); subst.
        * rewrite ZMap.gss. right. right.
          refine_split'; trivial.
          apply H1. apply Z_mod_lt. omega.
        * rewrite ZMap.gso; auto.
    - rewrite ZMap.gso; auto.
  Qed.

  Lemma PMap_valid_gss_pde_unp:
    forall ptp i,
      PMap_valid (ZMap.get i ptp) ->
      forall i' pdi v pt,
        ZMap.get pdi (ZMap.get i' ptp) = PDEValid v pt ->
        PMap_valid
          (ZMap.get i (ZMap.set i' (ZMap.set pdi PDEUnPresent
                                             (ZMap.get i' ptp)) ptp)).
  Proof.
    unfold PMap_valid; intros.
    destruct (zeq i i'); subst.
    - rewrite ZMap.gss.
      destruct H as (HP1 & HP2). split.
      + unfold PMap_common, PDE_kern in *. intros. 
        destruct (zeq pdi (PDX (i * PgSize))); subst.
        * erewrite HP1 in H0; eauto. congruence.
        * rewrite ZMap.gso; auto.
      + unfold PMap_usr, PDE_usr in *. intros.
        destruct (zeq pdi (PDX (i * PgSize))); subst.
        * rewrite ZMap.gss. left. trivial.
        * rewrite ZMap.gso; auto.
    - rewrite ZMap.gso; auto.
  Qed.

End PMAP_VALID_KERN_INV.


