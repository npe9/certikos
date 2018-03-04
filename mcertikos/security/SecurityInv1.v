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
Require Import I64Layer.
Require Import LoadStoreSem2.

Require Import SecurityCommon.
Require Import ProofIrrelevance.

(* This file proves that some new state invariants are preserved by each step 
   of the tsyscall layer. Note that we do not specify whether these invariants hold
   on the initial state here, we only prove that they are preserved. The invariants are:
   1.) the high_level_invariant already provided by mCertiKOS (this is just a lifting)
   2.) the unshared predicate, saying that no process's mapped pages are mapped in any
       other process's page tables
   3.) the single_mapped predicate, saying that no page is mapped more than once in a
       single process's page tables
   4.) the spawned status of each process (i.e., once a process is spawned, it remains
       spawned forever) - this invariant is convenient for guaranteeing that the observer
       process exists, but will need to be altered once mCertiKOS is upgraded to support
       killing processes
   Paper Reference: Section 5 *)

Ltac fun_inv_spec :=
  match goal with
    | H: _ = Some ?a |- context[?a] =>
      try (functional inversion H; clear H)
  end.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Local Instance : ExternalCallsOps (mwd (cdata RData)) := 
    CompatExternalCalls.compatlayer_extcall_ops tsyscall_layer.
  Local Instance : LayerConfigurationOps := compatlayer_configuration_ops tsyscall_layer.

  Section FLATMEM_CHARACT.

    Lemma flatmem_get_one : 
      forall ofs m,
        FlatMem.getN 1 ofs m = FlatMem.FlatMem2MemVal (ZMap.get ofs m) :: nil.
    Proof.
      auto.
    Qed.

    Fixpoint getN_setN_charact_fun (n : nat) (bl : list memval) :=
      match n, bl with
        | S n, v::bl => (match v with Pointer _ _ _ => Undef | _ => v end) :: getN_setN_charact_fun n bl
        | _, _ => nil
      end.

    Lemma getN_setN_charact :
      forall n bl p m, 
        (n <= length bl)%nat ->
        FlatMem.getN n p (FlatMem.setN bl p m) = getN_setN_charact_fun n bl.
    Proof.
      induction n; simpl; intros; auto.
      inv H.
      destruct bl.
      inv H1.
      simpl in *.
      inv H1.
      rewrite IHn; auto.
      f_equal.
      assert (Hnil: forall (A : Type) (a b : A), a::nil = b::nil -> a = b).
      intros.
      inv H; auto.
      apply Hnil.
      rewrite <- flatmem_get_one.
      rewrite FlatMem.getN_setN_outside; simpl; try omega.
      rewrite ZMap.gss; destruct m0; auto.
      destruct bl; simpl.
      inv H0.
      simpl in H0; rewrite (IHn bl (p+1)); try omega.
      f_equal.
      assert (Hnil: forall (A : Type) (a b : A), a::nil = b::nil -> a = b).
      intros.
      inv H; auto.
      apply Hnil.
      rewrite <- flatmem_get_one.
      rewrite FlatMem.getN_setN_outside; simpl; try omega.
      rewrite ZMap.gss; destruct m1; auto.
    Qed.

    Lemma get1_setN_charact :
      forall bl p m v, 
        (length bl > 0)%nat -> FlatMem.getN 1 p (FlatMem.setN bl p m) = v :: nil ->
        ZMap.get p (FlatMem.setN bl p m) = FlatMem.Mem2FlatMemVal v.
    Proof.
      destruct bl; simpl; intros.
      inv H.
      inv H0.
      destruct (ZMap.get p (FlatMem.setN bl (p + 1) (ZMap.set p (FlatMem.Mem2FlatMemVal m) m0))); auto.
    Qed.

    Fixpoint get_setN_charact_fun (n : nat) (bl : list memval) : option FlatMem.flatmem_val :=
      match n, bl with
        | _, nil => None
        | O, v::_ => Some (FlatMem.Mem2FlatMemVal v)
        | S n, _::bl => get_setN_charact_fun n bl
      end.

    Definition get_setN_charact_fun_some : 
      forall n (bl : list memval), (n < length bl)%nat -> FlatMem.flatmem_val.
    Proof.
      induction n; intros bl Hlength.
      destruct bl as [|v tl].
      simpl in Hlength; omega.
      apply (FlatMem.Mem2FlatMemVal (match v with Pointer _ _ _ => Undef | _ => v end)).
      destruct bl; simpl in Hlength.
      omega.
      apply (IHn bl); omega.
    Defined.

    Lemma get_setN_charact_pi :
      forall n bl (H H' : (n < length bl)%nat), 
        get_setN_charact_fun_some n bl H = get_setN_charact_fun_some n bl H'.
    Proof.
      intros n bl H H'; rewrite (proof_irrelevance _ H H'); auto.
    Qed.

    Lemma get_setN_charact_pi' :
      forall n1 n2 bl1 bl2 (H1 : (n1 < length bl1)%nat) (H2 : (n2 < length bl2)%nat),
        n1 = n2 -> bl1 = bl2 ->
        get_setN_charact_fun_some n1 bl1 H1 = get_setN_charact_fun_some n2 bl2 H2.
    Proof.
      intros n1 n2 bl1 bl2 H1 H2 ? ?; subst; rewrite (proof_irrelevance _ H1 H2); auto.
    Qed.

    Lemma get_setN_charact' :
      forall n bl p m (Hlt: (n < length bl)%nat),
        ZMap.get (p + Z_of_nat n) (FlatMem.setN bl p m) = 
        get_setN_charact_fun_some n bl Hlt.
    Proof.
      induction n; intros.
      destruct bl.
      inv Hlt.
      replace (p + Z_of_nat 0) with p; try (simpl; omega).
      apply get1_setN_charact; auto.
      rewrite getN_setN_charact; auto.
      replace (p + Z_of_nat (S n)) with ((p+1) + Z_of_nat n).
      destruct bl.
      inv Hlt.
      assert (Hlt': (n < length bl)%nat) by (simpl in Hlt; omega).
      simpl; rewrite (IHn _ _ _ Hlt'); apply get_setN_charact_pi.
      rewrite Nat2Z.inj_succ; omega.
    Qed.

    Lemma get_setN_charact_aux {A} :
      forall (l : list A) p q, p <= q < p + Z_of_nat (length l) -> (nat_of_Z (q-p) < length l)%nat.
    Proof.
      intros l p q Hq.
      assert (Hqp: q - p < Z.of_nat (length l)) by omega.
      rewrite Z2Nat.inj_lt in Hqp; try omega.
      rewrite Nat2Z.id in Hqp; assumption.
    Qed.

    Lemma get_setN_charact :
      forall bl p q m (Hq : p <= q < p + Z_of_nat (length bl)), 
        ZMap.get q (FlatMem.setN bl p m) = 
        get_setN_charact_fun_some (nat_of_Z (q-p)) bl (get_setN_charact_aux _ _ _ Hq).
    Proof.
      intros bl p q m Hq.
      assert (Heq: q = p + Z_of_nat (nat_of_Z (q-p))).
      rewrite Z2Nat.id; try omega.
      rewrite Heq at 1.
      apply (get_setN_charact' _ _ _ _ (get_setN_charact_aux _ _ _ Hq)).
    Qed.    

  End FLATMEM_CHARACT.

  Section PROOF.

    Lemma size_chunk_range' :
      forall chunk, 1 <= size_chunk chunk <= 8.
    Proof.
      destruct chunk; simpl; omega.
    Qed.

    Lemma pagei_ptaddr : 
      forall p o, PageI (PTADDR p o) = p.
    Proof.
      unfold PageI, PTADDR; intros p o.
      symmetry; apply (Z.div_unique_pos _ _ _ (o mod 4096)); try omega.
      apply Z.mod_pos_bound; omega.
    Qed.

    Lemma div_charact : 
      forall a b x, 
        b > 0 -> (b * x <= a < b * (x+1) <-> x = a / b).
    Proof.      
      intros a b' x Hb; split; intro Hrange; subst.
      rewrite Z.mul_add_distr_l in Hrange.
      apply (Z.div_unique_pos _ _ _ (a - b'*x)); omega.
      split.
      apply Z.mul_div_le; omega.
      apply Z.mul_succ_div_gt; omega.
    Qed.

    Lemma pg_offset_math :
      forall a b x, 
        b > 0 -> (a + x) / b = a / b -> 
        forall y, 0 <= y <= x -> (a + y) / b = a / b.
    Proof.
      intros a b' x Hb Hdiv y Hy.
      symmetry in Hdiv; rewrite <- (div_charact (a+x)) in Hdiv; auto.
      symmetry; rewrite <- (div_charact (a+y)); auto; split; try omega.
      assert (Hmath:= Z.mul_div_le a b'); omega.
    Qed.

    Definition unshared lat nps id : Prop :=
      forall p, kern_low <= p < nps -> isOwner lat id p -> 
                forall (id_low: id > high_id),
                forall id', isOwner lat id' p -> id = id'.

    Lemma real_unshared : 
      forall id lat, unshared (real_LAT lat) real_nps id.
    Proof.
      unfold unshared; intros id lat p Hp Hown. intro. inv Hown.
      destruct (real_LAT_all_valid_false_nil lat p) as [? Heq]; try omega.
      rewrites; inv H0.
    Qed.

    Lemma isOwner_LAT_nil :
      forall id lat p p' b t,
        p <> p' ->
        (isOwner (ZMap.set p (LATValid b t nil) lat) id p' <-> isOwner lat id p').
    Proof.
      intros; split; intro Hown.
      inv Hown; simpl in *; zmap_simpl; econstructor; eauto.
      inv Hown; econstructor; eauto; simpl; zmap_simpl; eauto.
    Qed.

    Lemma unshared_LAT_nil :
      forall id lat nps p b t,
        unshared lat nps id -> unshared (ZMap.set p (LATValid b t nil) lat) nps id.
    Proof.
      unfold unshared; intros.
      destruct (zeq p p0); subst.
      inv H1; simpl in *; zmap_simpl.
      inv H3; contradiction.
      rewrite isOwner_LAT_nil in *; eauto.
    Qed.

    Fixpoint zero_occ l n :=
      match l with
        | nil => True
        | LATO m _ _ :: l => if zeq m n then False else zero_occ l n
      end.

    Fixpoint at_most_one_occ l n :=
      match l with
        | nil => True
        | LATO m _ _ :: l => if zeq m n then zero_occ l n else at_most_one_occ l n
      end.

    Definition single_mapped lat nps id :=
      forall p b t l, 
        kern_low <= p < nps ->
        ZMap.get p lat = LATValid b t l ->
        at_most_one_occ l id.

    Lemma zero_occ_notin :
      forall l id pdi pti,
        zero_occ l id -> ~ In (LATO id pdi pti) l.
    Proof.
      induction l; simpl; intros; auto.
      subdestruct; try inv H; subst.
      intro Hcases; destruct Hcases; subst.
      inv H0; contradiction n0; auto.
      contradiction (IHl _ _ _ H H0).
    Qed.

    Lemma real_single_mapped :
      forall id lat,
        single_mapped (real_LAT lat) real_nps id.
    Proof.
      unfold single_mapped; intros until l; intros Hp Heq.
      destruct (real_LAT_all_valid_false_nil lat p) as [? Heq']; try omega.
      rewrites; simpl; auto.
    Qed.

    Section LOAD_STORE.

      Definition P' d d' :=
        (high_level_invariant d ->
         forall id, cused (ZMap.get id (AC d)) = true -> cused (ZMap.get id (AC d')) = true)
        /\ (forall id, unshared (LAT d) (nps d) id -> unshared (LAT d') (nps d') id)
        /\ (forall id, single_mapped (LAT d) (nps d) id -> single_mapped (LAT d') (nps d') id).

      Definition P d d' :=
        (forall id, cused (ZMap.get id (AC d)) = true -> cused (ZMap.get id (AC d')) = true)
        /\ (forall id, unshared (LAT d) (nps d) id -> unshared (LAT d') (nps d') id)
        /\ (forall id, single_mapped (LAT d) (nps d) id -> single_mapped (LAT d') (nps d') id).

      Definition PP' d d' :=
        (high_level_invariant d -> high_level_invariant d')
        /\ P' d d'.

      Definition PP d d' :=
        (high_level_invariant d -> high_level_invariant d')
        /\ P d d'.

      Lemma P_imply:
        forall d d',
          P d d' -> P' d d'.
      Proof.
        intros. destruct H as (HP1 & HP2 & HP3).
        unfold P'. refine_split'; auto.
      Qed.

      Lemma PP_imply:
        forall d d',
          PP d d' -> PP' d d'.
      Proof.
        intros. destruct H as (HP1 & HP2).
        unfold PP'. refine_split'; auto.
        eapply P_imply; eauto.
      Qed.

      Lemma exec_loadex_inv1 {F V} :
        forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd,
          exec_loadex(F:=F)(V:=V) ge chunk (m,d) a rs rd = Next rs' (m',d') ->
          ihost d = true -> 
          PP d d'.
      Proof.
        unfold exec_loadex, exec_loadex2; intros; subdestruct; rename H into Hexec; unfold PP, P.
        - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
        - unfold HostAccess2.exec_host_load2 in Hexec; subdestruct; inv Hexec; auto.
          unfold PageFault.exec_pagefault in *; subdestruct.
          unfold trapinfo_set in H1. inv H1. simpl.
          refine_split'; trivial.
          intros. inv H. constructor; auto.
        - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
        - simpl in *; rewrites.
        - simpl in *; rewrites.
      Qed.

    Lemma exec_storeex_inv1 {F V} :
      forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd rds,
        exec_storeex(F:=F)(V:=V) ge chunk (m,d) a rs rd rds = Next rs' (m',d') ->
          ihost d = true -> 
          PP d d'.
    Proof.
      unfold exec_storeex, exec_storeex2; intros; subdestruct; rename H into Hexec; unfold PP, P.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - unfold HostAccess2.exec_host_store2 in Hexec; subdestruct.
        + split.
          * intros. unfold FlatLoadStoreSem.exec_flatmem_store in Hexec; subdestruct; inv Hexec.
            apply flatmem_store_inv in Hdestruct8; auto.
            apply PTADDR_mod_lt; auto.
          * unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        + split.
          * intros. unfold FlatLoadStoreSem.exec_flatmem_store in Hexec; subdestruct; inv Hexec.
            apply flatmem_store_inv in Hdestruct8; auto.
            apply PTADDR_mod_lt; auto.
          * unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        + unfold PageFault.exec_pagefault in *; subdestruct.
          unfold trapinfo_set in Hexec. inv Hexec. simpl.
          refine_split'; trivial.
          intros. inv H. constructor; auto.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - simpl in *; rewrites.
      - simpl in *; rewrites.
    Qed.

    End LOAD_STORE.

    Section TRAP_INTO_KERNEL.

      Lemma trap_into_kernel_inv1 :
        forall id s' m' rs d d' vargs sg0 b0 v0
               v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
          trap_into_kernel_spec id s' m' rs d d' vargs sg0 b0 v0
                                v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> 
          PP d d'.
      Proof.
        intros until v16; intro Hspec; inv Hspec; unfold PP, P.
        decompose [and] H0; inv_spec; inv_somes; refine_split'; auto.
        intro Hinv.
        destruct Hinv; constructor; simpl; auto; try omega; try discriminate.
      Qed.

    End TRAP_INTO_KERNEL.

    Lemma P_trans:
      forall d0 d1 d2,
        P d0 d1 ->
        P d1 d2 ->
        P d0 d2.
    Proof.
      unfold P; intros.
      destruct H as (HP1 & HP2 & HP3).
      destruct H0 as (HP1' & HP2' & HP3').
      refine_split'; intros; eauto.
    Qed.

    Section MEM.

      Lemma palloc_inv1:
        forall i r d d',
          alloc_spec i d = Some (d', r) ->
          P d d'.
      Proof.
        intros; inv_spec; inv_somes; unfold P; auto; simpl.
        refine_split'.
        - intros. 
          destruct (zeq id i); subst.
          + rewrite ZMap.gss. trivial.
          + rewrite ZMap.gso; auto.
        - intros.
          apply unshared_LAT_nil; auto.
        - intros.
          unfold single_mapped; simpl; intros; zmap_solve; eauto.
          inv H1; simpl; auto.
      Qed.

      Lemma ptInsertPTE0_inv1:
        forall i vadr padr pm d d',
          ptInsertPTE0_spec i vadr padr pm d = Some d' ->
          noOwner (LAT d) padr -> 
          P d d'.
      Proof.
        intros; inv_spec; inv_somes; unfold P; simpl; auto. 
        - refine_split'; trivial.
          * intros. inv H0. unfold unshared in *.
            rewrite H1 in Hdestruct5. inv Hdestruct5.
            intros. destruct (zeq p padr); subst.
            {
              inv H2. rewrite ZMap.gss in *. inv H4.
              inv H3. rewrite ZMap.gss in *. inv H2.
              inv H5. inv H2. inv H4. inv H2. trivial.
              inv H2. inv H2.
            }
            eapply H; eauto.
            {
              inv H2.
              rewrite ZMap.gso in H4; auto.
              econstructor; eauto.
            }
            {
              inv H3.
              rewrite ZMap.gso in H4; auto.
              econstructor; eauto.
            }
          * intros; inv_spec; inv_somes; unfold single_mapped; simpl; intros; zmap_solve; eauto. subst.
            inv H0; rewrites; inv H2; simpl; destructgoal; auto.
        - refine_split'; trivial.
          * intros. inv H0. unfold unshared in *.
            rewrite H1 in Hdestruct5. inv Hdestruct5.
            intros. destruct (zeq p padr); subst.
            {
              inv H2. rewrite ZMap.gss in *. inv H4.
              inv H3. rewrite ZMap.gss in *. inv H2.
              inv H5. inv H2. inv H4. inv H2. trivial.
              inv H2. inv H2.
            }
            eapply H; eauto.
            {
              inv H2.
              rewrite ZMap.gso in H4; auto.
              econstructor; eauto.
            }
            {
              inv H3.
              rewrite ZMap.gso in H4; auto.
              econstructor; eauto.
            }
          * intros; inv_spec; inv_somes; unfold single_mapped; simpl; intros; zmap_solve; eauto. subst.
            inv H0; rewrites; inv H2; simpl; destructgoal; auto.
      Qed.

      Lemma ptAllocPDE0_inv1 :
        forall i1 i2 n d d',
          ptAllocPDE0_spec i1 i2 d = Some (d', n) ->
          P d d'.
      Proof.
        intros. functional inversion H; subst; unfold P; auto; simpl;clear H.
        refine_split'; intros.
        - destruct (zeq id i1); subst.
          + rewrite ZMap.gss.
            subst cur c; simpl. trivial.
          + rewrite ZMap.gso; auto.
        - unfold unshared in *. intros.
          destruct (zeq p n); subst.
          + inv H1. rewrite ZMap.gss in H12. inv H12. inv H13.
          + eapply H; eauto.
            * inv H1. rewrite ZMap.gso in H12; auto.
              econstructor; eauto.
            * inv H11. rewrite ZMap.gso in H12; auto.
              econstructor; eauto.
        - unfold single_mapped in *. intros.
          destruct (zeq p n); subst.
          + rewrite ZMap.gss in H1. inv H1. simpl; trivial.
          + rewrite ZMap.gso in H1; eauto.
      Qed.

      Lemma ptAllocPDE0_noOwner:
        forall i1 i2 n d d' padr,
          ptAllocPDE0_spec i1 i2 d = Some (d', n) ->
          noOwner (LAT d) padr ->
          noOwner (LAT d') padr.
      Proof.
        intros. functional inversion H; subst; unfold P; auto; simpl;clear H.
        inv H0. 
        destruct (zeq n padr); subst.
        - econstructor.
          rewrite ZMap.gss. trivial.
        - econstructor.
          rewrite ZMap.gso; eauto.
      Qed.

      Lemma ptInsert0_inv1:
        forall i vadr padr pm r d d',
          ptInsert0_spec i vadr padr pm d = Some (d', r) ->
          noOwner (LAT d) padr -> 
          P d d'.
      Proof.
        intros; inv_spec; inv_somes; clear Hdestruct4.
        - eapply ptInsertPTE0_inv1; eauto.
        - eapply ptAllocPDE0_inv1; eauto.
        - exploit ptAllocPDE0_inv1; eauto. intros.
          eapply P_trans; eauto.
          eapply ptInsertPTE0_inv1; eauto.
          eapply ptAllocPDE0_noOwner; eauto.
      Qed.

      Lemma alloc_noOwner:
        forall i1 d d' b,
          alloc_spec i1 d = Some (d', b) ->
          b <> 0 ->
          noOwner (LAT d') b.
      Proof.
        intros. 
        functional inversion H.
        - simpl. econstructor.
          rewrite ZMap.gss. trivial.
        - congruence.
      Qed.

      Lemma ptInsertPTE0_inv1':
        forall vadr padr pm d d',
          ptInsertPTE0_spec 2 vadr padr pm d = Some d' ->
          (exists b t pdi pti, ZMap.get padr (LAT d) = LATValid b t ((LATO 1 pdi pti) :: nil)) ->
          P d d'.
      Proof.
        intros; inv_spec; inv_somes; unfold P; simpl; auto. 
        - refine_split'; trivial.
          * intros. unfold unshared in *.
            destruct H0 as (b & t & pdi & pti & Heq). inv Heq.
            intros. destruct (zeq p padr); subst.
            {
              inv H1. rewrite ZMap.gss in *. inv H3.
              inv H2. rewrite ZMap.gss in *. inv H1.
              inv H4. inv H1. omega.
              inv H1. inv H2. omega.
              inv H2.
            }
            eapply H; eauto.
            {
              inv H1.
              rewrite ZMap.gso in H3; auto.
              econstructor; eauto.
            }
            {
              inv H2.
              rewrite ZMap.gso in H3; auto.
              econstructor; eauto.
            }
          * intros; inv_spec; inv_somes; unfold single_mapped; simpl; intros; zmap_solve; eauto. subst.
            destruct H0 as (b' & t' & pdi & pti & Heq). inv Heq.
            inv H2.
            Opaque zero_occ zeq.
            simpl.
            destruct (zeq 2 id); subst.
            Transparent zero_occ.
            simpl. rewrite zeq_false; trivial. omega.
            destruct (zeq 1 id); subst; simpl; trivial.
        - refine_split'; trivial.
          * intros. unfold unshared in *.
            destruct H0 as (b & t & pdi & pti & Heq). inv Heq.
            intros. destruct (zeq p padr); subst.
            {
              inv H1. rewrite ZMap.gss in *. inv H3.
              inv H2. rewrite ZMap.gss in *. inv H1.
              inv H4. inv H1. omega.
              inv H1. inv H2. omega.
              inv H2.
            }
            eapply H; eauto.
            {
              inv H1.
              rewrite ZMap.gso in H3; auto.
              econstructor; eauto.
            }
            {
              inv H2.
              rewrite ZMap.gso in H3; auto.
              econstructor; eauto.
            }
          * intros; inv_spec; inv_somes; unfold single_mapped; simpl; intros; zmap_solve; eauto. subst.
            destruct H0 as (b' & t' & pdi & pti & Heq). inv Heq.
            inv H2.
            Opaque zero_occ zeq.
            simpl.
            destruct (zeq 2 id); subst.
            Transparent zero_occ.
            simpl. rewrite zeq_false; trivial. omega.
            destruct (zeq 1 id); subst; simpl; trivial.
      Qed.

      Lemma ptAllocPDE0_exists:
        forall i1 i2 n d d' padr,
          ptAllocPDE0_spec i1 i2 d = Some (d', n) ->
          (exists b t pdi pti, ZMap.get padr (LAT d) = LATValid b t ((LATO 1 pdi pti) :: nil)) ->
          (exists b t pdi pti, ZMap.get padr (LAT d') = LATValid b t ((LATO 1 pdi pti) :: nil)).
      Proof.
        intros. functional inversion H; subst; auto; simpl;clear H.
        destruct (zeq n padr); subst.
        - destruct H0 as (b & t & pdi' & pti & Heq). 
          pose proof _x as HP.
          destruct HP as (_ & Heq' & _).
          rewrite Heq in Heq'. inv Heq'.
        - rewrite ZMap.gso; eauto.
      Qed.

      Lemma ptInsert0_inv1':
        forall vadr padr pm r d d',
          ptInsert0_spec 2 vadr padr pm d = Some (d', r) ->
          (exists b t pdi pti, ZMap.get padr (LAT d) = LATValid b t ((LATO 1 pdi pti) :: nil)) ->
          P d d'.
      Proof.
        intros; inv_spec; inv_somes; clear Hdestruct4.
        - eapply ptInsertPTE0_inv1'; eauto.
        - eapply ptAllocPDE0_inv1; eauto.
        - exploit ptAllocPDE0_inv1; eauto. intros.
          eapply P_trans; eauto.
          eapply ptInsertPTE0_inv1'; eauto.
          eapply ptAllocPDE0_exists; eauto.
      Qed.

      Lemma ptInsertPTE0_exists:
        forall vadr padr pm d d',
          ptInsertPTE0_spec 1 vadr padr pm d = Some d' ->
          noOwner (LAT d) padr ->
          (exists b t pdi pti, ZMap.get padr (LAT d') = LATValid b t ((LATO 1 pdi pti) :: nil)).
      Proof.
        intros; inv_spec; inv_somes; unfold P; simpl; auto. 
        - rewrite ZMap.gss. inv H0. rewrite H in Hdestruct5. inv Hdestruct5.
          eauto.
        - rewrite ZMap.gss. inv H0. rewrite H in Hdestruct5. inv Hdestruct5.
          eauto.
      Qed.

      Lemma ptInsert0_exists:
        forall i2 b i3 d d' v,
          ptInsert0_spec 1 i2 b i3 d = Some (d', v) ->
          noOwner (LAT d) b ->
          v <> MagicNumber ->
          exists b0 t pdi pti,
            ZMap.get b (LAT d') = LATValid b0 t (LATO 1 pdi pti :: nil).
      Proof.
        intros; inv_spec; inv_somes; clear Hdestruct4.
        - eapply ptInsertPTE0_exists; eauto.
        - congruence. 
        - eapply ptInsertPTE0_exists; eauto.
          exploit ptAllocPDE0_noOwner; eauto. 
      Qed.

      Lemma ptResv2_inv1 :
        forall i2 i3 i5 i6 n d d',
          ptResv2_spec 1 i2 i3 2 i5 i6 d = Some (d', n) ->
          P d d'.
      Proof.
        intros. functional inversion H; subst; clear H.
        - unfold P; auto.
        - exploit palloc_inv1; eauto. intros.
          eapply P_trans; eauto.
          eapply ptInsert0_inv1; eauto.
          eapply alloc_noOwner; eauto.
        - exploit palloc_inv1; eauto. intros.
          eapply P_trans; eauto.
          exploit alloc_noOwner; eauto; intros.
          revert H3. intros.
          exploit ptInsert0_inv1; eauto. intros.
          eapply P_trans; eauto.
          eapply ptInsert0_inv1'; eauto.
          eapply ptInsert0_exists; eauto.
      Qed.

    End MEM.

    Section DISPATCH.

      Opaque Mem.load.

      Lemma sys_dispatch_inv1:
        forall s m d d',
          sys_dispatch_c_spec s m d = Some d' ->
          P d d'.
      Proof.
        intros; inv_spec; fun_inv_spec;
        inv_somes; unfold P; auto.      
        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
          refine_split'; auto. intros.
          unfold update_cusage, update_cchildren; simpl in *; zmap_solve; try congruence.      

        - repeat inv_spec;
          inv_somes; simpl in *; auto.      

        - functional inversion H0; subst. clear H0.
          subst uctx uctx'. simpl.
          functional inversion H5; subst; simpl in *. clear H5.
          subst uctx uctx'.
          functional inversion H4; subst; simpl in *; auto; clear H4.
          eapply ptResv2_inv1; eauto.
          eapply ptResv2_inv1; eauto.
        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
      Qed.

    End DISPATCH.

    Lemma ptfault_resv_inv1:
      forall v d d',
        ptfault_resv_spec v d = Some d' -> 
        P d d'.
    Proof.
      intros v d d' Hspec.
      inv_spec; inv_somes.
      inv_spec; inv_somes; simpl; auto; unfold P; simpl; eauto.
      exploit palloc_inv1; eauto. intros.
      eapply P_trans; eauto.
      eapply ptInsert0_inv1; eauto.
      eapply alloc_noOwner; eauto.
      unfold P; simpl; auto.
    Qed.

    Lemma proc_start_user_inv1 :
      forall rs d d',
        proc_start_user_spec d = Some (d', rs) -> 
        P d d'.
    Proof.
      intros; inv_spec; inv_somes; unfold P; auto.
    Qed.

    Lemma thread_yield_inv1 :
      forall rs rs' d d',
        thread_yield_spec d rs = Some (d',rs') -> 
        P d d'.
    Proof.
      intros; inv_spec; inv_somes; unfold P; auto.
    Qed.

    Lemma step_inv1:
      forall ge rs rs' (m m' : mem) (d d' : cdata RData) t,
        LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
        ihost d = true ->
        PP' d d'.
    Proof.
      intros.
      eapply (step_P (fun d d' : cdata RData => 
                        ihost d = true -> PP' d d')) in H; eauto.
      - unfold PP', P'; eauto.
      - simpl; intros; eapply PP_imply; eapply exec_loadex_inv1; eauto.
      - simpl; intros; eapply PP_imply; eapply exec_storeex_inv1; eauto.
      - intros. unfold PP', P'.
        destruct H1 as [t' [σ [Hl [s [σ' [Hmatch [Hsem [? [? ?]]]]]]]]]; subst.
        inv_layer Hl; inv Hsem; refine_split'; intros; try assumption.
        (*+ eapply print_inv; eauto.
        + gensem_simpl. functional inversion H5. simpl. trivial.
        + gensem_simpl. functional inversion H4. simpl. trivial.
        + gensem_simpl. functional inversion H4. simpl. trivial.*)
        + eapply proc_init_inv; eauto.
        + gensem_simpl.
          unfold proc_init_spec, ret in *; subdestruct; inv_somes; simpl.
          destruct H1; destruct valid_container.
          specialize (valid_preinit_container Hdestruct _ (cvalid_id _ H3)); congruence.
        + gensem_simpl.
          unfold proc_init_spec, ret in *; subdestruct; inv_somes; simpl.
          apply real_unshared.
        + gensem_simpl.
          unfold proc_init_spec, ret in *; subdestruct; inv_somes; simpl.
          apply real_single_mapped.

      - intros.
        destruct H1 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
        inv_layer Hl; inv Hsem; simpl in *.
        + (* dispatch *)
          split.
          * destruct primcall_sys_dispatch_c_invariants.
            eapply primitive_call_high_level_invariant; eauto.
          * inv H4. inv H9.
            eapply trap_into_kernel_inv1 in H1; eauto.
            eapply sys_dispatch_inv1 in H11; eauto.
            destruct H1 as [_ HP].
            destruct H4 as [HT _].
            eapply proc_start_user_inv1 in HT.
            eapply P_imply.
            eapply P_trans; eauto.
            eapply P_trans; eauto.
        + (* pagefault *)
          split.
          * destruct primcall_pgf_handler_sem_invariants.
            eapply primitive_call_high_level_invariant; eauto.
          * inv H4. inv H10.
            eapply trap_into_kernel_inv1 in H1; eauto.
            eapply ptfault_resv_inv1 in H12; eauto.
            destruct H1 as [_ HP].
            destruct H4 as [HT _].
            eapply proc_start_user_inv1 in HT.
            eapply P_imply.
            eapply P_trans; eauto.
            eapply P_trans; eauto.
        + (* yield *)
          split.
          * destruct primcall_sys_yield_sem_invariants.
            eapply primitive_call_high_level_invariant; eauto.
          * inv H4.
            eapply P_imply.
            eapply thread_yield_inv1 in H13; eauto.
            eapply trap_into_kernel_inv1 in H8; eauto.
            destruct H8 as [_ HP].
            eapply P_trans; eauto.
        + (* proc_startuser *)
          split; inv H4; intros.
          * apply (start_user_high_level_invariant proc_start_user_spec) in H8; auto.
          * eapply P_imply.
            eapply proc_start_user_inv1; eauto.
    Qed.

  End PROOF.

End WITHMEM.