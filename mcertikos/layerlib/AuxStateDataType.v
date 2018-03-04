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
(*              Definitions of AuxStateDataType                        *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide some [data types] that will be used in the layer definitions and refinement proofs*)
Require Import Coqlib.
Require Import Constant.
Require Import Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import AsmX.
Require Import CommonTactic.

(** *Data types for abstract data*)

Section MemoryManagement.

  Definition zle_le: 
    forall x y z : Z, { x <= y <= z } + { x > y \/ y > z}.
  Proof.
    intros. destruct (zle x y).
    - destruct (zle y z).
      + left. auto.
      + right. auto.
    - right. auto.
  Defined.

  Definition zle_lt: 
    forall x y z : Z, { x <= y < z } + { x > y \/ y >= z}.
  Proof.
    intros. destruct (zle x y).
    - destruct (zlt y z).
      + left. auto.
      + right. auto.
    - right. auto.
  Defined.

  Definition zlt_lt: 
    forall x y z : Z, { x < y < z } + { x >= y \/ y >= z}.
  Proof.
    intros. destruct (zlt x y).
    - destruct (zlt y z).
      + left. auto.
      + right. auto.
    - right. auto.
  Defined.

  Definition zlt_le: 
    forall x y z : Z, { x < y <= z } + { x >= y \/ y > z}.
  Proof.
    intros. destruct (zlt x y).
    - destruct (zle y z).
      + left. auto.
      + right. auto.
    - right. auto.
  Defined.

  Lemma zle_lt_true:
    forall (A: Type) (x y z: Z) (a b : A),
      x <= y < z -> (if zle_lt x y z then a else b) = a.
  Proof.
    intros. destruct (zle_lt x y z); trivial.
    inv o; omega.
  Qed.

  Lemma zle_le_true:
    forall (A: Type) (x y z: Z) (a b : A),
      x <= y <= z -> (if zle_le x y z then a else b) = a.
  Proof.
    intros. destruct (zle_le x y z); trivial.
    inv o; omega.
  Qed.

  Lemma zlt_lt_true:
    forall (A: Type) (x y z: Z) (a b : A),
      x < y < z -> (if zlt_lt x y z then a else b) = a.
  Proof.
    intros. destruct (zlt_lt x y z); trivial.
    inv o; omega.
  Qed.

  Lemma zlt_le_true:
    forall (A: Type) (x y z: Z) (a b : A),
      x < y <= z -> (if zlt_le x y z then a else b) = a.
  Proof.
    intros. destruct (zlt_le x y z); trivial.
    inv o; omega.
  Qed.

  Definition PDX (i:Z) := i/(PgSize * one_k).
  Definition PTX (i:Z) := (i/PgSize) mod one_k.
  Definition PTADDR (i:Z) (ofs:Z) := (i * PgSize) + (ofs mod PgSize).
  Definition PageI (i: Z) := i / PgSize.

  Lemma size_chunk_range:
    forall chunk,
      0<= size_chunk chunk <= 8.
  Proof.
    induction chunk; simpl; omega.
  Qed.

  Lemma mod_chunk':
    forall i,
      0 <= i < 1024 ->
      i * 4 <= 4096 - size_chunk Mint32.
  Proof.
    simpl. intros.
    omega.
  Qed.

  Lemma mod_chunk:
    forall i,
      (i mod 1024) * 4 <= PgSize - size_chunk Mint32.
  Proof.
    intros.
    exploit (Z.mod_pos_bound i 1024).
    omega. intros Hrange.
    eapply mod_chunk'.
    assumption.
  Qed.

  Lemma HPS: PgSize > 0.
  Proof. omega. Qed.

  (** Physical memory intromation table*)
  Inductive MMPerm:=
  | MMUsable
  | MMResv.
  
  Inductive MMInfo:=
  | MMValid (s l:Z) (p: MMPerm)
  | MMUndef.
  
  Definition MMTable := ZMap.t MMInfo.

  Definition VMXInfo := ZMap.t Z.

  Class RealParamsOps : Type :=
    {  
      real_mm: MMTable;
      real_size: Z;
      real_vmxinfo: VMXInfo
    }.

  Section MMTable_Property.

    (** ** Decidability of physical memory information table*)
    Remark MM_dec (mm: MMTable) (i:Z):
      { exists s l p,  ZMap.get i mm = MMValid s l p /\ s >= 0 /\ l > 0 /\ s + l < Int.max_unsigned} 
      +{~exists s l  p, ZMap.get i mm = MMValid s l p /\ s >= 0 /\ l > 0 /\ s + l < Int.max_unsigned}.
    Proof.
      induction (ZMap.get i mm); [|right; red; intros [s'[l'[p' [HT _]]]]; discriminate].
      destruct (zle 0 s); [|right; red; intros [s'[l'[p' [HT [HF _]]]]]; inv HT; omega].
      destruct (zlt 0 l); [|right; red; intros [s'[l'[p' [HT [_[HF _]]]]]]; inv HT; omega].
      destruct (zlt (s + l) Int.max_unsigned); [|right; red; intros [s'[l'[p' [HT [_[_ HF]]]]]]; inv HT; omega].
      left.
      exists s, l, p.
      split; trivial.
      split; omega.
    Qed.

    Definition MM_range (mm: MMTable) (lo high: Z) :=
      forall i , lo <= i < high -> exists s l p, (ZMap.get i mm = MMValid s l p /\ s >= 0 /\ l > 0 /\ s + l < Int.max_unsigned).

    Lemma general_range_dec:
      forall P, 
        (forall i, {P i} + {~P i}) -> 
        forall lo hi, {forall i, lo <= i < hi -> P i} + {~ forall i, lo <= i < hi -> P i}.
    Proof.
      intros.
      assert(HP: forall n, 0 <= n
                           -> {forall i, lo <= i < (lo+n) -> P i} + {~ forall i, lo <= i < (lo+n) -> P i}).
      {
        apply natlike_rec2.
        - left; intros. omegaContradiction.
        - destruct 2.      
          + destruct (H (lo+z)).
            * left; intros.
              destruct (zeq i (lo + z)); subst; trivial.
              apply p; omega. 
            * right; red; intro. 
              assert (lo <= (lo+z) < lo + Z.succ z) by omega.
              elim n; auto.
          + right; red; intro; elim n; clear n. intros.
            assert (lo <= i < lo + Z.succ z) by omega.
            auto.
      }      
      destruct (zlt lo hi).
      replace hi with (lo + (hi - lo)) by omega. apply HP. omega.
      left; intros. omegaContradiction. 
    Qed.

    Remark MM_range_dec:
      forall mm lo high, {MM_range mm lo high} + {~MM_range mm lo high}.
    Proof.
      intros. unfold MM_range.
      eapply general_range_dec. intros.
      apply MM_dec.
    Qed.
    
    Definition MM_valid (mm: MMTable) (size: Z) := MM_range mm 0 size.

    Remark MM_valid_dec (mm: MMTable) (size: Z) :
      {MM_valid mm size} +{~MM_valid mm size}.
    Proof.
      unfold MM_valid.
      apply (MM_range_dec mm 0 size).
    Qed.

    Definition perm_consist (s1 s2 l1 l2 :Z) (p1 p2: MMPerm):=
      s1 < s2 + l2 -> s2 < s1 + l1 -> p1 = p2.
    
    Remark perm_consist_dec (s1 s2 l1 l2 :Z) (p1 p2: MMPerm) :
      {perm_consist s1 s2 l1 l2 p1 p2} + {~perm_consist s1 s2 l1 l2 p1 p2}.
    Proof.
      unfold perm_consist.
      destruct(Z_lt_dec s1 (s2+l2)).
      destruct(Z_lt_dec s2 (s1+l1)).
      assert(HP1: {p1 = p2} + {~p1 = p2}) by decide equality.
      destruct HP1; [left; auto| right; red; auto].
      left; intros; omegaContradiction.
      left; intros; omega.
    Qed.

    Remark MMPerm_dec (p1 p2: MMPerm) :
      { p1 = p2} + { p1 <> p2}.
    Proof.
      decide equality.
    Qed.

    Definition MM_correct_pos (mm: MMTable) (i j: Z) :=
      forall s1 s2 l1 l2 p1 p2, 
        ZMap.get i mm = MMValid s1 l1 p1
        -> ZMap.get j mm = MMValid s2 l2 p2
        -> perm_consist s1 s2 l1 l2 p1 p2.

    Remark MM_correct_pos_dec (mm: MMTable) (i j:Z) :
      {MM_correct_pos mm i j} + {~ MM_correct_pos mm i j}.
    Proof.
      unfold MM_correct_pos.
      destruct (ZMap.get i mm); [| left; intros; discriminate].
      destruct (ZMap.get j mm); [| left; intros; discriminate].
      unfold perm_consist. 
      destruct (MMPerm_dec p p0).
      left; intros; inv H; inv H0; trivial.
      destruct (zlt s (s0 + l0)).
      destruct (zlt s0 (s + l)).
      
      right; red; intros. elim n; eauto.

      left; intros; inv H; inv H0; omega.
      left; intros; inv H; inv H0; omega.
    Qed.
    
    Definition MM_correct1 (mm: MMTable) (i size: Z) :=
      forall j, 0<= j < size -> MM_correct_pos mm i j.
    
    Remark MM_correct1_dec (mm: MMTable) (i size:Z) :
      {MM_correct1 mm i size} + {~ MM_correct1 mm i size}.
    Proof.
      unfold MM_correct1.
      eapply general_range_dec. intros.
      apply MM_correct_pos_dec.
    Qed.

    Definition MM_correct2 (mm: MMTable) (size size2: Z) :=
      forall i, 0<= i < size -> MM_correct1 mm i size2.
    
    Remark MM_correct2_dec (mm: MMTable) (size size2:Z) :
      {MM_correct2 mm size size2} + {~ MM_correct2 mm size size2}.
    Proof.
      unfold MM_correct2.
      eapply general_range_dec. intros.
      apply MM_correct1_dec.
    Qed.

    Definition MM_correct (mm: MMTable) (size: Z) :=
      forall i j s1 s2 l1 l2 p1 p2, 
        0<= i < size -> 0<= j < size
        -> ZMap.get i mm = MMValid s1 l1 p1
        -> ZMap.get j mm = MMValid s2 l2 p2
        -> perm_consist s1 s2 l1 l2 p1 p2.
    
    Remark MM_correct_dec (mm: MMTable) (size:Z) :
      {MM_correct mm size} + {~ MM_correct mm size}.
    Proof.
      destruct (MM_correct2_dec mm size size).
      left; unfold MM_correct,  MM_correct2, MM_correct1, MM_correct_pos in *; eauto.      
      right;red;intro; apply n.
      unfold MM_correct2, MM_correct1, MM_correct_pos; eauto.
    Qed.

    Definition MM_kern_valid (mm: MMTable)(n size:Z):=
      exists i s l, 
        0<= i < size /\ ZMap.get i mm = MMValid s l MMUsable /\ s<= n * PgSize /\ l + s >= ((n+1)* PgSize).

    Remark MM_kern_valid_dec (mm:MMTable) (n size:Z) :
      {MM_kern_valid mm n size} +{~MM_kern_valid mm n size}.
    Proof.
      assert(HQ: forall k, 0<= k -> {MM_kern_valid mm n k} +{~MM_kern_valid mm n k}).
      unfold MM_kern_valid; apply natlike_rec2.
      right; red; intros; destruct H as [i[_[_[HI _]]]]; omega.
      
      destruct 2.
      left.
      destruct e as [i [s[l[HI[HM[HS HL]]]]]].
      exists i, s, l; repeat (split;trivial); omega.

      Ltac right_simpl H0 H1 z n0:= 
        right; red; intros; destruct H1 as [i'[s'[l' HM]]]; destruct (zeq i' z); 
        [subst; destruct HM as [_ [HM [HM1 HF]]]; rewrite H0 in HM; inv HM; try omega
        | elim n0; exists i', s', l'; destruct HM as [HM1 HM2]; split; trivial; omega].

      caseEq (ZMap.get z mm); intros; [|right_simpl H0 H1 z n0].
      destruct (MMPerm_dec p MMUsable); [|right_simpl H0 H1 z n0; elim n1; trivial].
      destruct (zle s (n * PgSize)); [|right_simpl H0 H1 z n0].
      destruct (zle ((n+1)*PgSize) (l + s)); [|right_simpl H0 H1 z n0].
      
      left; exists z, s, l.
      rewrite e in H0.
      repeat(split;trivial);
        omega. 
      
      destruct (Z_le_dec size 0).
      right; red; unfold MM_kern_valid; intro.
      destruct H as [i[_[_[HI _]]]]; omega.
      
      apply HQ; omega.
    Qed.
    
    Definition MM_kern_range (mm:MMTable) (n size: Z):=
      forall i, 0<= i < n -> MM_kern_valid mm i size.
    
    Definition MM_kern (mm:MMTable) (size: Z):=
      MM_kern_range mm kern_low size.

  End MMTable_Property.

  Definition trapinfo := prod int val.

  Definition init_trap_info : trapinfo := (Int.zero, Vundef).  

  Inductive globalpointer :=
  | GLOBP (b: ident) (ofs: int)
  | GLOBUndef.

  Section CR3_Property.

    Definition CR3_valid (pt: globalpointer) := exists b ofs, pt = GLOBP b ofs. 

    Remark CR3_valid_dec (pt: globalpointer) :
      {CR3_valid pt } + { ~ CR3_valid pt}.
    Proof.
      unfold CR3_valid.
      destruct pt.
      left.
      eauto.
      right.
      red; intros.
      destruct H as [b0 [ofs0 HG]].
      inv HG.
    Qed.

  End CR3_Property.

  Section CONTAINER.

    (** Agent Container *)
    Inductive Container : Type := 
    | mkContainer : Z -> Z -> Z -> list Z -> bool -> Container.

    Definition cquota (c : Container) : Z := let (q,_,_,_,_) := c in q.
    Definition cusage (c : Container) : Z := let (_,u,_,_,_) := c in u.
    Definition cparent (c : Container) : Z := let (_,_,p,_,_) := c in p.
    Definition cchildren (c : Container) : list Z := let (_,_,_,ch,_) := c in ch.
    Definition cused (c : Container) : bool := let (_,_,_,_,u) := c in u.

    (* Pool represents a tree rooted at index 0 *)
    Definition ContainerPool : Type := ZMap.t Container.

    Definition update_cquota (C : ContainerPool) i q := 
      ZMap.set i 
        (mkContainer q (cusage (ZMap.get i C)) (cparent (ZMap.get i C)) 
                     (cchildren (ZMap.get i C)) (cused (ZMap.get i C))) C.

    Definition update_cusage (C : ContainerPool) i u := 
      ZMap.set i
        (mkContainer (cquota (ZMap.get i C)) u (cparent (ZMap.get i C)) 
                     (cchildren (ZMap.get i C)) (cused (ZMap.get i C))) C.

    Definition update_cparent (C : ContainerPool) i p := 
      ZMap.set i
        (mkContainer (cquota (ZMap.get i C)) (cusage (ZMap.get i C)) p
                     (cchildren (ZMap.get i C)) (cused (ZMap.get i C))) C.

    Definition update_cchildren (C : ContainerPool) i ch := 
      ZMap.set i
        (mkContainer (cquota (ZMap.get i C)) (cusage (ZMap.get i C)) 
                  (cparent (ZMap.get i C)) ch (cused (ZMap.get i C))) C.

    Definition update_cused (C : ContainerPool) i u := 
      ZMap.set i
        (mkContainer (cquota (ZMap.get i C)) (cusage (ZMap.get i C)) 
                  (cparent (ZMap.get i C)) (cchildren (ZMap.get i C)) u) C.    

    Definition Container_unused := mkContainer 0 0 0 nil false.

    Section Container_Property.

      Inductive child_quotas_bounded : ContainerPool -> list Z -> Z -> Prop :=
      | cqb_nil : forall C n, 0 <= n -> child_quotas_bounded C nil n
      | cqb_cons : forall C c cs n m, 0 <= cquota (ZMap.get c C) <= m ->
                                      child_quotas_bounded C cs n -> 
                                      child_quotas_bounded C (c::cs) (n+m).

      Lemma cqb_nonneg : forall cs C n, child_quotas_bounded C cs n -> 0 <= n.
      Proof.
        induction cs; simpl; intros.
        inv H; auto.
        inv H.
        apply Z.add_nonneg_nonneg; try omega.
        apply (IHcs C); auto.
      Qed.

      Lemma cqb_bound : forall cs C n1 n2, child_quotas_bounded C cs n1 -> 
                                           n1 <= n2 -> child_quotas_bounded C cs n2.
      Proof.
        induction cs; simpl; intros.
        inv H; constructor; omega.
        inv H.
        apply (IHcs _ _ (n2-m)) in H6; try omega.
        replace n2 with (n2 - m + m); try omega.
        constructor; auto.
      Qed.

      Lemma cqb_notin : forall cs C c n con, 
                          child_quotas_bounded C cs n -> ~ In c cs -> 
                          child_quotas_bounded (ZMap.set c con C) cs n.
      Proof.
        induction cs; simpl; intros.
        inv H; constructor; auto.
        inv H; constructor; auto.
        rewrite ZMap.gso; auto.
      Qed.

      Lemma cqb_weaken : forall cs C c n con,
                           child_quotas_bounded C cs n -> 0 <= cquota con <= cquota (ZMap.get c C) ->
                           child_quotas_bounded (ZMap.set c con C) cs n.
      Proof.
        induction cs; simpl; intros.
        inv H; constructor; auto.
        inv H; constructor; auto.
        destruct (zeq a c); subst.
        rewrite ZMap.gss; omega.
        rewrite ZMap.gso; auto.
      Qed.

      Fact remove_notin {A} : forall (l : list A) a eq, ~ In a l -> remove eq a l = l.
      Proof.
        induction l; simpl; intros; auto.
        destruct (eq a0 a); subst.
        contradict H; auto.
        rewrite IHl; auto.
      Qed.

      Lemma cqb_remove : 
        forall cs C c n,
          child_quotas_bounded C cs n -> In c cs ->
          child_quotas_bounded C (remove zeq c cs) (n - cquota (ZMap.get c C)).
      Proof.
        induction cs; simpl; intros.
        inv H0.
        inv H.
        destruct (in_dec zeq c cs) as [Hin|Hnin].
        destruct (zeq c a); subst.
        apply (IHcs _ a) in H6; auto.
        apply cqb_bound with (n1 := n0 - cquota (ZMap.get a C)); auto; try omega.
        replace (n0 + m - cquota (ZMap.get c C)) with (n0 - cquota (ZMap.get c C) + m); try omega.
        constructor; auto.
        destruct H0; subst; try contradiction.
        destruct (zeq c c).
        apply cqb_bound with (n1 := n0); try omega.
        rewrite remove_notin; auto.
        contradict n; auto.
      Qed.

      Inductive Container_valid (C : ContainerPool) : Prop := 
        mkContainer_valid {
            cvalid_id : forall i, cused (ZMap.get i C) = true -> 0 <= i < num_id;
            cvalid_root : forall i, cused (ZMap.get i C) = true -> 
                                    (i = cparent (ZMap.get i C) <-> i = 0);
            cvalid_quota : forall i, cused (ZMap.get i C) = true ->
                                     cquota (ZMap.get i C) <= Int.max_unsigned;
            cvalid_usage : forall i, cused (ZMap.get i C) = true -> 
                                     0 <= cusage (ZMap.get i C) <= cquota (ZMap.get i C);
            cvalid_parent_used : forall i, cused (ZMap.get i C) = true -> 
                                           cused (ZMap.get (cparent (ZMap.get i C)) C) = true;
            cvalid_children_used : forall i, cused (ZMap.get i C) = true ->
                                             Forall (fun j => cused (ZMap.get j C) = true) (cchildren (ZMap.get i C));
            cvalid_parents_child : forall i, cused (ZMap.get i C) = true -> (i <> 0)%Z ->
                                             In i (cchildren (ZMap.get (cparent (ZMap.get i C)) C));
            cvalid_childrens_parent : forall i, cused (ZMap.get i C) = true ->
                                                Forall (fun j => cparent (ZMap.get j C) = i) (cchildren (ZMap.get i C));
            cvalid_cqb : forall i, cused (ZMap.get i C) = true -> 
                                   child_quotas_bounded C (cchildren (ZMap.get i C)) (cusage (ZMap.get i C));
            cvalid_nodup : forall i, cused (ZMap.get i C) = true ->
                                     NoDup (cchildren (ZMap.get i C));

            (* MAX_CHILDREN invariants *)
            cvalid_max_children : forall i, cused (ZMap.get i C) = true -> 
                                            Z_of_nat (length (cchildren (ZMap.get i C))) <= max_children;
            cvalid_parent_id : forall i, cused (ZMap.get i C) = true -> 
                                         cparent (ZMap.get i C) = if zeq i 0 then 0 else (i-1) / max_children;
            cvalid_child_id_range : 
              forall i, cused (ZMap.get i C) = true -> 
                        Forall (fun j => i * max_children + 1 <= j <
                                         i * max_children + 1 + Z_of_nat (length (cchildren (ZMap.get i C))))
                               (cchildren (ZMap.get i C))            
          }.

    End Container_Property.

  End CONTAINER.

  (** Allocation table*)
  Inductive ATType: Type :=
  | ATKern 
  | ATResv 
  | ATNorm.

  Remark ATType_dec:
    forall x y: ATType,
      {x = y} + {x <> y}.
  Proof.
    intros. repeat progress (decide equality).
  Qed.

  Inductive ATInfo :=
  | ATValid (b: bool) (t: ATType) (n: Z)
  | ATUndef.

  Definition ATable := ZMap.t ATInfo.

  Function ZtoATType (i: Z) : option ATType :=
    match i with
      | 0 => Some ATResv
      | 1 => Some ATKern
      | 2 => Some ATNorm
      | _ => None
    end.

  Definition IntToBoolZ (n: int) : Z :=
    if Int.eq n Int.zero then 0
    else 1.

  Definition ZToATTypeZ (n: Z) : Z :=
    if zeq n 0 then 0
    else if zeq n 1 then 0
         else 1.

  Section AT_Property.

    Definition AT_kern (AT: ATable) (nps: Z) :=   
      forall i, 0<= i < kern_low \/ kern_high <= i < nps
                -> ZMap.get i AT = ATValid false ATKern 0.

    Definition AT_usr (AT: ATable) (nps: Z):= 
      forall i,  kern_low <= i < Z.min kern_high nps
                 -> exists b, (exists n, ZMap.get i AT = ATValid b ATNorm n)
                              \/ ZMap.get i AT = ATValid b ATResv 0.

    Remark AT_dec (info: ATInfo) (b: bool) (t: ATType) (n: Z):
      {info = ATValid b t n} + {~info = ATValid b t n}.
    Proof.
      repeat progress (decide equality).
    Qed.

    Lemma min_ex: forall (P: Z -> Prop) lo hi,
                    (forall n, {P n} + {~ P n}) ->
                    {n : Z | lo < n < hi /\ P n /\ forall n', lo < n' < n -> ~ P n'} +
                    {forall n, lo < n < hi -> ~ P n}.
    Proof.
      intros.
      assert(HP: forall k, 
                   0 <= k -> {n : Z | lo < n < lo + k + 1 /\ P n /\ (forall n' : Z, lo < n' < n -> ~ P n')} +
                             {(forall n : Z, lo < n < lo + k + 1 -> ~ P n)}).
      {
        apply natlike_rec2. 
        - right; intros; omega.
        - intros z HR HT.
          destruct HT.
          + left; destruct s as [n[HT HM]].
            exists n; split; trivial; omega.      
          + specialize (H (lo + z + 1)).
            destruct H.
            * left; exists (lo + z + 1); split; auto; omega.
            * right; intros; destruct (zeq n1 (lo + z + 1)); subst; trivial; apply n; omega.
      }
      destruct (zlt lo hi).
      - replace hi with (lo + (hi - lo - 1) + 1) by omega. apply HP. omega.
      - right; intros. omegaContradiction.
    Qed.

    (** ** Find the first free page*)  
    Definition first_free (At: ATable) (size: Z) :
      {n| 0 < n < size /\ (exists c, ZMap.get n At = ATValid false ATNorm c) /\ 
          (forall x, 0 < x < n -> ~ (exists c, ZMap.get x At = ATValid false ATNorm c))}
      + {forall x, 0 < x < size -> ~ (exists c, ZMap.get x At = ATValid false ATNorm c)}.
    Proof.
      eapply min_ex. intros.
      destruct (ZMap.get n At).
      - destruct b.
        + right. red; intros. destruct H as (? & He). inv He.
        + destruct t.
          * right. red; intros. destruct H as (? & He). inv He.
          * right. red; intros. destruct H as (? & He). inv He.
          * left. eauto.
      - right. red; intros. destruct H as (? & He). inv He.
    Defined.

  End AT_Property.

  Inductive LATOwner :=
    | LATO (n pdi pti: Z).

  Inductive LATInfo :=
  | LATValid (b: bool) (t: ATType) (l: list LATOwner)
  | LATUndef.

  Remark LATOwner_dec:
    forall x y: LATOwner,
      {x = y} + {x <> y}.
  Proof.
    intros. repeat progress (decide equality).
  Qed.

  Definition LATable := ZMap.t LATInfo.

  Section LAT_Property.

    Definition LAT_kern (AT: LATable) (nps: Z) :=   
      forall i, 0<= i < kern_low \/ kern_high <= i < nps
                -> ZMap.get i AT = LATValid false ATKern nil.

    Definition LAT_usr (AT: LATable) (nps: Z):= 
      forall i,  kern_low <= i < Z.min kern_high nps
                 -> exists b, (exists n, ZMap.get i AT = LATValid b ATNorm n)
                              \/ ZMap.get i AT = LATValid b ATResv nil.

    Remark LAT_dec (info: LATInfo) (b: bool) (t: ATType) (n: list LATOwner):
      {info = LATValid b t n} + {~info = LATValid b t n}.
    Proof.
      repeat progress (decide equality).
    Qed.

    (** ** Find the first free page*)  
    Definition Lfirst_free (At: LATable) (size: Z) :
      {n| 0 < n < size /\ ZMap.get n At = LATValid false ATNorm nil 
          /\ forall x, 0 < x < n -> ~ ZMap.get x At = LATValid false ATNorm nil}
      + {forall x, 0 < x < size -> ~ ZMap.get x At = LATValid false ATNorm nil}.
    Proof.
      eapply min_ex.
      intros.
      apply LAT_dec.
    Defined.

    Inductive relate_LATInfo : ATInfo -> LATInfo -> Prop :=
    | RELATE_Undef: relate_LATInfo ATUndef LATUndef
    | RELATE_VALID: 
        forall b t n l,
          n = Z_of_nat (length l) ->
          relate_LATInfo (ATValid b t n) (LATValid b t l).

    Definition relate_LATable (a1 : ATable) (a2 : LATable) :=
      forall i, relate_LATInfo (ZMap.get i a1) (ZMap.get i a2).

    Lemma relate_LATable_gss:
      forall a1 a2,
        relate_LATable a1 a2 ->
        forall s1 s2,
          relate_LATInfo s1 s2 ->
          forall i,
            relate_LATable (ZMap.set i s1 a1) (ZMap.set i s2 a2).
    Proof.
      unfold relate_LATable; intros.
      destruct (zeq i i0); subst.
      - repeat rewrite ZMap.gss. trivial.
      - repeat rewrite ZMap.gso; auto.
    Qed.

  End LAT_Property.

  Section QUOTA_BOUNDED_INV.

    Fixpoint sum_quotas ac i :=
      (if cused (ZMap.get (Z_of_nat i) ac) then
          cquota (ZMap.get (Z_of_nat i) ac) - cusage (ZMap.get (Z_of_nat i) ac) else 0) +
      match i with
      | O => 0
      | S i => sum_quotas ac i
      end.

    Fixpoint unused_pages_AT AT p :=
      match p with
      | O => 0
      | S p' => match ZMap.get (Z_of_nat p) AT with
                | ATValid false ATNorm _ => 1
                | _ => 0
                end + unused_pages_AT AT p'
      end.

    Definition quota_bounded_AT ac AT nps :=
      sum_quotas ac (nat_of_Z (num_id - 1)) <= unused_pages_AT AT (nat_of_Z (nps - 1)).

    Section SUM_QUOTAS_LEMMAS.

      Lemma sum_quotas_pos :
        forall ac, Container_valid ac -> 
                   forall i, 0 <= sum_quotas ac i.
      Proof.
        intros ac Hinv; destruct Hinv.
        induction i; simpl; intros.
        specialize (cvalid_usage0 0).
        destruct (cused (ZMap.get 0 ac)); try omega.
        specialize (cvalid_usage0 eq_refl); omega.
        specialize (cvalid_usage0 (Z.pos (Pos.of_succ_nat i))).
        destruct (cused (ZMap.get (Z.pos (Pos.of_succ_nat i)) ac)); try omega.
        specialize (cvalid_usage0 eq_refl); omega.
      Qed.

      Lemma sum_quotas_outside :
        forall n i ac C,
          Z_of_nat n < i ->
          sum_quotas (ZMap.set i C ac) n = sum_quotas ac n.
      Proof.
        induction n; simpl; intros; zmap_solve; try omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        rewrite IHn; omega.
      Qed.

      Lemma sum_quotas_outside_small :
        forall n i ac C,
          i < 0 ->
          sum_quotas (ZMap.set i C ac) n = sum_quotas ac n.
      Proof.
        induction n; simpl; intros.
        zmap_solve; try omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        zmap_solve; cases; try omega; rewrite IHn; auto.
      Qed.

      Lemma sum_quotas_inside :
        forall n i ac C, 
          0 <= i <= Z.of_nat n -> cused C = true ->
          sum_quotas (ZMap.set i C ac) n = 
          sum_quotas ac n + cquota C - cusage C - 
                            (if cused (ZMap.get i ac)
                             then cquota (ZMap.get i ac) - cusage (ZMap.get i ac) 
                             else 0).                         
      Proof.
        induction n; simpl; intros i ac C Hi Hused.
        zmap_solve; try omega; subst.
        rewrite Hused; omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        zmap_solve; subst.
        - rewrite Hused, sum_quotas_outside; omega.
        - rewrite IHn; auto; omega.
      Qed.

      Lemma sum_quotas_inside_false :
        forall n i ac C,
          0 <= i <= Z.of_nat n -> cused C = false ->
          sum_quotas (ZMap.set i C ac) n =
          sum_quotas ac n - (if cused (ZMap.get i ac)
                             then cquota (ZMap.get i ac) - cusage (ZMap.get i ac) 
                             else 0).
      Proof.
        induction n; simpl; intros i ac C Hi Hused.
        zmap_solve; cases; omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        zmap_solve; subst.
        - rewrites; rewrite sum_quotas_outside; omega.
        - rewrite IHn; auto; omega.
      Qed.

      Lemma sum_quotas_set :
        forall n i ac C,
          sum_quotas (ZMap.set i C ac) n =
          sum_quotas ac n + 
          if zlt i 0 then 0 else
            if zlt (Z.of_nat n) i then 0 else
              ((if cused C then cquota C - cusage C else 0) -
               (if cused (ZMap.get i ac) then cquota (ZMap.get i ac) - 
                                             cusage (ZMap.get i ac) else 0)).
      Proof.
        intros; destruct (zlt i 0).
        rewrite sum_quotas_outside_small; omega.
        destruct (zlt (Z.of_nat n) i).
        rewrite sum_quotas_outside; omega.
        cases; try solve [rewrite sum_quotas_inside; auto; cases; try omega |
                          rewrite sum_quotas_inside_false; auto; cases; omega].
      Qed.

    End SUM_QUOTAS_LEMMAS.

    Section QUOTA_BOUNDED_AT_LEMMAS.

      Lemma unused_pages_AT_outside :
        forall n i AT l,
          Z_of_nat n < i ->
          unused_pages_AT (ZMap.set i l AT) n = unused_pages_AT AT n.
      Proof.
        induction n; simpl; intros; zmap_solve; try omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        rewrite IHn; omega.
      Qed.

      Lemma unused_pages_AT_outside_small :
        forall n i AT l,
          i <= 0 ->
          unused_pages_AT (ZMap.set i l AT) n = unused_pages_AT AT n.
      Proof.
        induction n; simpl; intros; auto.
        change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        zmap_solve; subst; try omega.
        rewrite IHn; auto.
      Qed.

      Lemma unused_pages_AT_inside :
        forall n i AT ati,
          0 < i <= Z.of_nat n -> 
          match ati with
            | ATValid false ATNorm _ => False
            | _ => True 
          end ->
          unused_pages_AT (ZMap.set i ati AT) n =
          unused_pages_AT AT n - match ZMap.get i AT with
                                   | ATValid false ATNorm _ => 1
                                   | _ => 0 end.
      Proof.
        induction n; simpl; intros i AT ati Hi Hati; try omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        zmap_solve; subst.
        - rewrite unused_pages_AT_outside; try omega.
          destruct ati as [[|] [| |] v|]; inv Hati; omega.
        - rewrite IHn; auto; omega.
      Qed.

      Lemma unused_pages_AT_inside_false :
        forall n i AT v,
          0 < i <= Z.of_nat n -> 
          unused_pages_AT (ZMap.set i (ATValid false ATNorm v) AT) n =
          unused_pages_AT AT n + match ZMap.get i AT with
                                   | ATValid false ATNorm _ => 0
                                   | _ => 1 end.
      Proof.
        induction n; simpl; intros i AT v Hi; try omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        destruct (zeq i (Z.of_nat n + 1)); subst; zmap_simpl.
        - rewrite unused_pages_AT_outside; try omega.
          destruct (ZMap.get (Z.of_nat n + 1) AT) as [[|] [| |]|]; omega.
        - rewrite IHn; auto; omega.
      Qed.

      Lemma unused_pages_AT_set :
        forall n i ati AT,
          unused_pages_AT (ZMap.set i ati AT) n =
          unused_pages_AT AT n + 
          if zle i 0 then 0 else
            if zlt (Z.of_nat n) i then 0 else
              match ati with
                | ATValid false ATNorm _ => 
                  match ZMap.get i AT with
                    | ATValid false ATNorm _ => 0
                    | _ => 1 
                  end
                | _ =>
                  match ZMap.get i AT with
                    | ATValid false ATNorm _ => -1
                    | _ => 0 
                  end
              end.
      Proof.
        intros; destruct (zle i 0).
        rewrite unused_pages_AT_outside_small; omega.
        destruct (zlt (Z.of_nat n) i).
        rewrite unused_pages_AT_outside; omega.
        destruct ati as [[|] [| |] v|];
          try solve [rewrite unused_pages_AT_inside; auto; try omega;
                     destruct (ZMap.get i AT) as [[|] [| |]|]; omega].
        rewrite unused_pages_AT_inside_false; auto; omega.
      Qed.

      Lemma single_quota_bounded_aux :
        forall ac, Container_valid ac ->
                   forall n i, 
                     0 <= i <= Z_of_nat n ->
                     cused (ZMap.get i ac) = true ->
                     cusage (ZMap.get i ac) < cquota (ZMap.get i ac) ->
                     0 < sum_quotas ac n.
      Proof.
        intros ac Hinv; induction n; simpl; intros.
        assert (i = 0) by omega; subst; rewrites; omega.
        change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        destruct (zeq i (Z.of_nat n + 1)); subst.
        rewrites; assert (Hpos:= sum_quotas_pos _ Hinv n); omega.
        assert (0 < sum_quotas ac n) by (eapply IHn; eauto; omega).      
        destruct (cused (ZMap.get (Z.of_nat n + 1) ac)) eqn:Hused; try omega.
        destruct Hinv; specialize (cvalid_usage0 _ Hused); omega.
      Qed.

      Lemma single_quota_bounded_AT :
        forall ac AT nps i,
          Container_valid ac -> quota_bounded_AT ac AT nps ->
          cused (ZMap.get i ac) = true ->
          cusage (ZMap.get i ac) < cquota (ZMap.get i ac) -> 
          0 < unused_pages_AT AT (nat_of_Z (nps - 1)).
      Proof.
        unfold quota_bounded_AT; intros.
        cut (0 < sum_quotas ac (nat_of_Z (num_id - 1))); try omega.
        eapply single_quota_bounded_aux; eauto.
        rewrite nat_of_Z_eq; try omega.
        destruct H; specialize (cvalid_id0 _ H1); omega.
      Qed.

      Lemma unused_pages_AT_first_free_aux :
        forall AT n,
          (forall p, 0 < p <= Z_of_nat n -> match ZMap.get p AT with
                                              | ATValid false ATNorm _ => False
                                              | _ => True end) ->
          unused_pages_AT AT n = 0.
      Proof.
        induction n; simpl; intros; auto.
        change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
        rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
        rewrite IHn.
        destruct (ZMap.get (Z.of_nat n + 1) AT) eqn:Hat; auto.
        destruct b; destruct t; auto.
        specialize (H (Z.of_nat n + 1)); rewrites; contradiction H; omega.
        intros; eapply H; eauto; omega.
      Qed.

      Lemma unused_pages_AT_first_free :
        forall AT nps,
          0 < unused_pages_AT AT (nat_of_Z (nps - 1)) ->
          exists pf, first_free AT nps = inleft pf.
      Proof.
        intros.
        destruct (first_free AT nps); eauto.
        rewrite unused_pages_AT_first_free_aux in H; try omega.
        intros p Hp; destruct (ZMap.get p AT) eqn:Hat; auto.
        destruct b; destruct t; auto.
        assert (Hcases: nps - 1 >= 0 \/ nps - 1 < 0) by omega; destruct Hcases.      
        rewrite nat_of_Z_eq in Hp; try omega.
        contradiction (n p); try omega; eauto.
        rewrite nat_of_Z_neg in Hp; simpl in *; omega.
      Qed.

      Lemma quota_bounded_AT_first_free :
        forall ac AT nps i,
          Container_valid ac -> quota_bounded_AT ac AT nps ->
          cused (ZMap.get i ac) = true ->
          cusage (ZMap.get i ac) < cquota (ZMap.get i ac) -> 
          exists pf, first_free AT nps = inleft pf.
      Proof.
        intros; apply unused_pages_AT_first_free; eapply single_quota_bounded_AT; eauto.
      Qed.

    End QUOTA_BOUNDED_AT_LEMMAS.

    (* Abstraction of quota_bounded to LAT *)

    Fixpoint unused_pages lat p :=
      match p with
      | O => 0
      | S p' => match ZMap.get (Z_of_nat p) lat with
                | LATValid false ATNorm _ => 1
                | _ => 0
                end + unused_pages lat p'
      end.

    Definition quota_bounded ac lat nps := 
      sum_quotas ac (nat_of_Z (num_id - 1)) <= unused_pages lat (nat_of_Z (nps - 1)).

    Lemma unused_pages_relate :
      forall p AT lat,
        relate_LATable AT lat -> unused_pages lat p = unused_pages_AT AT p.
    Proof.
      induction p; intros AT lat Hrel; simpl; auto.
      rewrite (IHp AT); auto.
      specialize (Hrel (Z.pos (Pos.of_succ_nat p))); inv Hrel; rewrites; omega.
    Qed.

    Lemma quota_bounded_relate :
      forall ac AT lat nps,        
        relate_LATable AT lat -> 
        (quota_bounded ac lat nps <-> quota_bounded_AT ac AT nps).
    Proof.
      unfold quota_bounded, quota_bounded_AT; intros.
      rewrite (unused_pages_relate _ AT); tauto.
    Qed.

    (* Canonical relation between LAT and AT *)

    Let build_AT_elt s :=
      match s with
        | LATUndef => ATUndef
        | LATValid b t l => ATValid b t (Z.of_nat (length l))
      end.

    Let build_AT lat := ZMap.map build_AT_elt lat.

    Let build_AT_elt_relate :
      forall s, relate_LATInfo (build_AT_elt s) s.
    Proof.
      destruct s; constructor; auto.
    Qed.

    Let build_AT_relate : 
      forall lat, relate_LATable (build_AT lat) lat.
    Proof.
      intros lat i; unfold build_AT; rewrite ZMap.gmap; auto.
    Qed.

    Lemma unused_pages_build_AT_set : 
      forall n i sl sa lat,
        relate_LATInfo sa sl ->
        unused_pages_AT (build_AT (ZMap.set i sl lat)) n = 
        unused_pages_AT (ZMap.set i sa (build_AT lat)) n.
    Proof.
      induction n; simpl; intros i sl sa lat Hrel; auto.
      rewrite (IHn _ _ sa); auto.
      unfold build_AT at 1; unfold build_AT_elt; rewrite ZMap.gmap.
      zmap_solve; subst.
      destruct Hrel; omega.
      destruct (build_AT_relate lat (Z.pos (Pos.of_succ_nat n))); omega.
    Qed.

    Section QUOTA_BOUNDED_LAT_LEMMAS.

      Lemma unused_pages_outside :
        forall n i lat l,
          Z_of_nat n < i ->
          unused_pages (ZMap.set i l lat) n = unused_pages lat n.
      Proof.
        intros; rewrite (unused_pages_relate _ (build_AT (ZMap.set i l lat))); auto.
        rewrite (unused_pages_build_AT_set _ _ _ (build_AT_elt l)); auto.
        rewrite unused_pages_AT_outside; auto.
        rewrite (unused_pages_relate _ (build_AT lat)); auto.
      Qed.

      Lemma unused_pages_outside_small :
        forall n i lat l,
          i <= 0 ->
          unused_pages (ZMap.set i l lat) n = unused_pages lat n.
      Proof.
        intros; rewrite (unused_pages_relate _ (build_AT (ZMap.set i l lat))); auto.
        rewrite (unused_pages_build_AT_set _ _ _ (build_AT_elt l)); auto.
        rewrite unused_pages_AT_outside_small; auto.
        rewrite (unused_pages_relate _ (build_AT lat)); auto.
      Qed.

      Lemma unused_pages_inside :
        forall n i lat ati,
          0 < i <= Z.of_nat n -> 
          match ati with
            | LATValid false ATNorm _ => False
            | _ => True 
          end ->
          unused_pages (ZMap.set i ati lat) n =
          unused_pages lat n - match ZMap.get i lat with
                                   | LATValid false ATNorm _ => 1
                                   | _ => 0 end.
      Proof.
        intros; rewrite (unused_pages_relate _ (build_AT (ZMap.set i ati lat))); auto.
        rewrite (unused_pages_build_AT_set _ _ _ (build_AT_elt ati)); auto.
        rewrite unused_pages_AT_inside; auto.
        rewrite (unused_pages_relate _ (build_AT lat)); auto.
        destruct (build_AT_relate lat i); omega.
        destruct (build_AT_elt_relate ati); auto.
      Qed.

      Lemma unused_pages_inside_false :
        forall n i lat v,
          0 < i <= Z.of_nat n -> 
          unused_pages (ZMap.set i (LATValid false ATNorm v) lat) n =
          unused_pages lat n + match ZMap.get i lat with
                                   | LATValid false ATNorm _ => 0
                                   | _ => 1 end.
      Proof.
        intros; rewrite (unused_pages_relate _ 
                  (build_AT (ZMap.set i (LATValid false ATNorm v) lat))); auto.
        rewrite (unused_pages_build_AT_set _ _ _ 
                  (build_AT_elt (LATValid false ATNorm v))); auto.
        simpl; rewrite unused_pages_AT_inside_false; auto.
        rewrite (unused_pages_relate _ (build_AT lat)); auto.
        destruct (build_AT_relate lat i); omega.
      Qed.

      Lemma unused_pages_set :
        forall n i ati lat,
          unused_pages (ZMap.set i ati lat) n =
          unused_pages lat n + 
          if zle i 0 then 0 else
            if zlt (Z.of_nat n) i then 0 else
              match ati with
                | LATValid false ATNorm _ => 
                  match ZMap.get i lat with
                    | LATValid false ATNorm _ => 0
                    | _ => 1 
                  end
                | _ =>
                  match ZMap.get i lat with
                    | LATValid false ATNorm _ => -1
                    | _ => 0 
                  end
              end.
      Proof.
        intros; destruct (zle i 0).
        rewrite unused_pages_outside_small; omega.
        destruct (zlt (Z.of_nat n) i).
        rewrite unused_pages_outside; omega.
        destruct ati as [[|] [| |] v|];
          try solve [rewrite unused_pages_inside; auto; try omega;
                     destruct (ZMap.get i lat) as [[|] [| |]|]; omega].
        rewrite unused_pages_inside_false; auto; omega.
      Qed.

      Lemma single_quota_bounded :
        forall ac lat nps i,
          Container_valid ac -> quota_bounded ac lat nps ->
          cused (ZMap.get i ac) = true ->
          cusage (ZMap.get i ac) < cquota (ZMap.get i ac) -> 
          0 < unused_pages lat (nat_of_Z (nps - 1)).
      Proof.
        unfold quota_bounded; intros.
        cut (0 < sum_quotas ac (nat_of_Z (num_id - 1))); try omega.
        eapply single_quota_bounded_aux; eauto.
        rewrite nat_of_Z_eq; try omega.
        destruct H; specialize (cvalid_id0 _ H1); omega.
      Qed.

      Lemma unused_pages_first_free_aux :
        forall lat n,
          (forall p, 0 < p <= Z_of_nat n -> match ZMap.get p lat with
                                              | LATValid false ATNorm _ => False
                                              | _ => True end) ->
          unused_pages lat n = 0.
      Proof.
        intros; rewrite (unused_pages_relate _ (build_AT lat)); auto.
        rewrite unused_pages_AT_first_free_aux; auto.
        intro p; specialize (H p); destruct (build_AT_relate lat p); auto.
      Qed.

      Lemma unused_pages_first_free :
        forall lat nps,
          (forall i l, ZMap.get i lat = LATValid false ATNorm l -> l = nil) ->
          0 < unused_pages lat (nat_of_Z (nps - 1)) ->         
          exists pf, Lfirst_free lat nps = inleft pf.
      Proof.
        intros.
        destruct (Lfirst_free lat nps); eauto.
        rewrite unused_pages_first_free_aux in H0; try omega.
        intros p Hp; destruct (ZMap.get p lat) eqn:Hat; auto.
        destruct b; destruct t; auto.
        assert (Hcases: nps - 1 >= 0 \/ nps - 1 < 0) by omega; destruct Hcases.      
        rewrite nat_of_Z_eq in Hp; try omega.
        specialize (H p l Hat); contradiction (n p); try omega; rewrites; subst; auto.
        rewrite nat_of_Z_neg in Hp; simpl in *; omega.
      Qed.

      Lemma quota_bounded_first_free :
        forall ac lat nps i,
          (forall i l, ZMap.get i lat = LATValid false ATNorm l -> l = nil) ->
          Container_valid ac -> quota_bounded ac lat nps ->
          cused (ZMap.get i ac) = true ->
          cusage (ZMap.get i ac) < cquota (ZMap.get i ac) -> 
          exists pf, Lfirst_free lat nps = inleft pf.
      Proof.
        intros; apply unused_pages_first_free; auto; eapply single_quota_bounded; eauto.
      Qed.

    End QUOTA_BOUNDED_LAT_LEMMAS.

  End QUOTA_BOUNDED_INV.

  (** Physical Page Info *)
  (*Inductive PPgColor:=
    | PGFreeable
    | PGLoadable.*)

  (** Pg Onwership*)
  Inductive PPgOnwer :=
  | PGPMap (n i: Z).

  Inductive PPgInfo :=
  | PGUndef
  | PGAlloc (*(i: PPgColor)*)
  | PGHide (o: PPgOnwer).

  (* physical page permission *)
  Definition PPermT := ZMap.t PPgInfo.

  Section PPgInfo_Property.
    
    Inductive PPgInfo_leq: PPgInfo -> PPgInfo -> Prop :=
    | PGLE_REFL: forall i, PPgInfo_leq i i
    | PGLE_ALLOC_BUSY: forall o, PPgInfo_leq (PGHide o) (PGAlloc (*PGFreeable*))
    (*| PGLE_ALLOC_FREE: PPgInfo_leq (PGAlloc PGLoadable) (PGAlloc PGFreeable)*).
 
    Definition PPermT_les (c1 c2: PPermT) :=
      forall i, PPgInfo_leq (ZMap.get i c1) (ZMap.get i c2).

    Definition consistent_ppage (att: ATable) (ppt: PPermT) (nps: Z): Prop :=
      forall i, 
        0<= i < nps ->
        (~ (ZMap.get i ppt = PGUndef) 
         -> exists n, 
              ZMap.get i att = ATValid true ATNorm n)
        /\ (forall n, ZMap.get i att = ATValid true ATNorm n
                      -> ~ (ZMap.get i ppt = PGUndef)).

    Lemma consistent_ppage_init:
      forall nps,
      consistent_ppage (ZMap.init ATUndef) (ZMap.init PGUndef) nps.
    Proof.
      split; repeat rewrite ZMap.gi; intros.
      - elim H0. reflexivity.
      - discriminate.
    Qed.

    Definition Lconsistent_ppage (att: LATable) (ppt: PPermT) (nps: Z): Prop :=
      forall i, 
        0<= i < nps ->
        (~ (ZMap.get i ppt = PGUndef) 
         -> exists n, 
              ZMap.get i att = LATValid true ATNorm n)
        /\ (forall n, ZMap.get i att = LATValid true ATNorm n
                      -> ~ (ZMap.get i ppt = PGUndef)).

    Lemma Lconsistent_ppage_init:
      forall nps,
      Lconsistent_ppage (ZMap.init LATUndef) (ZMap.init PGUndef) nps.
    Proof.
      split; repeat rewrite ZMap.gi; intros.
      - elim H0. reflexivity.
      - discriminate.
    Qed.

    Remark PPgOwner_dec (o o1: PPgOnwer):
      { o = o1 } + {~ o = o1 }.
    Proof.
      decide equality; apply zeq.
    Qed.

    (*Remark PPgOwnerList_dec (o o1: list PPgOnwer):
      { o = o1 } + {~ o = o1 }.
    Proof.
      decide equality. apply PPgOwner_dec.
    Qed.*)

    Remark PPgInfo_dec (pperm pperm1: PPgInfo):
      {pperm = pperm1} + {~ pperm = pperm1}.
    Proof.
      decide equality.
      eapply PPgOwner_dec.
    Qed.

  End PPgInfo_Property.

  Inductive PTPerm: Type :=
  | PTP
  | PTU 
  | PTK (b: bool).
  
  Function ZtoPerm (i:Z): option PTPerm:=
    match i with
      | PT_PERM_P => Some PTP
      | PT_PERM_PTKF => Some (PTK false) (*kern: >1G, PTE_P|_W *)
      | PT_PERM_PTKT => Some (PTK true) (*kern: <1G, PTE_P|_W|_G *)
      | PT_PERM_PTU => Some PTU (*usr: >1G, PTE_P|_W|_U*)
      | _ => None
    end.
  
  Function PermtoZ (p: PTPerm): Z :=
    match p with
      | PTP => PT_PERM_P
      | PTU => PT_PERM_PTU
      | PTK false => PT_PERM_PTKF
      | PTK true => PT_PERM_PTKT
    end.
  
  Lemma PermZ_eq: 
    forall v p, ZtoPerm v = Some p -> v = PermtoZ p.
  Proof.
    functional inversion 1; trivial.
  Qed.
  
  Lemma PermZ_eq_r: forall p, ZtoPerm (PermtoZ p) = Some p.
  Proof.
    intros.
    destruct p; trivial.
    destruct b; trivial.
  Qed.

  Lemma ZtoPerm_range: forall i p,  ZtoPerm (i) = Some p -> 0<= i < 260.
  Proof.
    functional inversion 1; omega.
  Qed.

  (** Page Table*)
  Inductive PTEInfo:=
  | PTEValid (v: Z) (p: PTPerm)
  | PTEUnPresent
  | PTEUndef.
  
  Definition PTE := ZMap.t PTEInfo.

  Inductive PDE :=
  | PDEValid (pi: Z) (pte: PTE)
  | PDEID
  | PDEUnPresent
  | PDEUndef.

  Inductive IDPTEInfo:=
  | IDPTEValid (p: PTPerm)
  | IDPTEUndef.

  Definition IDPTE := ZMap.t IDPTEInfo.
  Definition IDPDE := ZMap.t IDPTE.

  (*Function ZtoPDE (i:Z) :=
    match i with
      | PT_PERM_UP => Some PDEUnPresent
      | PT_PERM_PTKT => Some PDEKern
      | _ => None
    end.
  
  Function PDEtoZ (p: PDE) :=
    match p with
      | PDEUnPresent => Some PT_PERM_UP
      | PDEKern => Some PT_PERM_PTKT
      | _ => None
    end.
  
  Lemma PDEZ_eq: 
    forall v p, ZtoPDE v = Some p -> PDEtoZ p = Some v.
  Proof.
    functional inversion 1; trivial.
  Qed.
  
  Lemma PDEZ_eq_r: forall v p, PDEtoZ p = Some v -> ZtoPDE v = Some p.
  Proof.
    functional inversion 1; trivial.
  Qed.

  Lemma ZtoPDE_range: forall i p,  ZtoPDE i = Some p -> 0 <= i <= PT_PERM_PTKT.
  Proof.
    functional inversion 1; omega.
  Qed.*)

  Definition PMap := ZMap.t PDE.

  Section PT_Property.

    Definition PDE_kern (pmap: PMap) (i: Z):=
      ZMap.get (PDX (i * PgSize)) pmap = PDEID.

    Definition PDE_kern_range (pmap: PMap) (lo high: Z) :=
      forall i , lo <= i < high -> PDE_kern pmap i.
    
    Definition PMap_common (pmap: PMap) :=   
      forall i, 0<= i < kern_low \/ kern_high <= i < maxpage
                -> PDE_kern pmap i.

    Definition PMap_kern (pmap: PMap) :=   
      forall i, kern_low <= i < kern_high
                -> PDE_kern pmap i.

    Remark PDE_kern_dec:
      forall pt i, {PDE_kern pt i} + {~ PDE_kern pt i}.
    Proof.
      intros; unfold PDE_kern.
      destruct (ZMap.get (PDX (i * PgSize)) pt) eqn: HPDX.
      + right; red; intros. discriminate.
      + left; trivial.
      + right; red; intros. discriminate.
      + right; red; intros. discriminate.
    Qed.

    Remark PDE_kern_range_dec:
      forall pt lo high, {PDE_kern_range pt lo high} + {~PDE_kern_range pt lo high}.
    Proof.
      intros. unfold PDE_kern_range.
      eapply general_range_dec. intros.
      apply PDE_kern_dec.
    Qed.

    Remark PMap_common_dec:
      forall pt, {PMap_common pt } + { ~ PMap_common pt}.
    Proof.
      intros; unfold PMap_common.
      destruct (PDE_kern_range_dec pt 0 kern_low).
      + destruct (PDE_kern_range_dec pt kern_high maxpage).
        * left; unfold PDE_kern_range in *; intros.
          destruct H; auto.
        * right; red; intros.
          unfold PDE_kern_range in *; auto.
      + right; red; intros.
        apply n; unfold PDE_kern_range; auto.
    Qed.

    Remark PMap_kern_dec:
      forall pt, {PMap_kern pt } + { ~ PMap_kern pt}.
    Proof.
      intros. apply (PDE_kern_range_dec pt kern_low kern_high).
    Qed.

    Definition PDE_usr (pmap: PMap) (i: Z):=
      ZMap.get (PDX (i * PgSize)) pmap = PDEUnPresent
      \/ ZMap.get (PDX (i * PgSize)) pmap = PDEID
      \/ (exists pte pi, ZMap.get (PDX (i * PgSize)) pmap = PDEValid pi pte
                         /\ ~ (ZMap.get (PTX (i * PgSize)) pte = PTEUndef)).

    Definition PDE_usr_range (pmap: PMap) (lo high: Z) :=
      forall i , lo <= i < high -> PDE_usr pmap i.
    
    Definition PMap_usr (pmap: PMap) :=   
      forall i, kern_low <= i < kern_high
                -> PDE_usr pmap i.

    Remark PDE_usr_dec:
      forall pt i, {PDE_usr pt i} + {~ PDE_usr pt i}.
    Proof.
      intros; unfold PDE_usr.
      destruct (ZMap.get (PDX (i * PgSize)) pt) eqn: HPDX.
      - destruct (ZMap.get (PTX (i * 4096)) pte) eqn: HPTX.
        + left; intros. right. right. 
          esplit; esplit. split; trivial.
          rewrite HPTX. red; intros HF; inv HF.
        + left; intros. right. right.
          esplit; esplit. split; trivial.
          rewrite HPTX. red; intros HF; inv HF.
        + right; red; intros. destruct H.
          * discriminate.
          * destruct H; try discriminate.
            destruct H as (? & ? & HW & HF).
            inv HW. elim HF; assumption.
      - left. right. left. reflexivity.
      - left. left. reflexivity.
      - right; red; intros. destruct H.
        + discriminate.
        + destruct H; try discriminate.
          destruct H as (? & ? & HW & HF). inv HW.
    Qed.

    Remark PDE_usr_range_dec:
      forall pt lo high, {PDE_usr_range pt lo high} + {~PDE_usr_range pt lo high}.
    Proof.
      intros. unfold PDE_usr_range.
      eapply general_range_dec. intros.
      apply PDE_usr_dec.
    Qed.

    Remark PMap_usr_dec:
      forall pt, {PMap_usr pt } + { ~ PMap_usr pt}.
    Proof.
      intros; unfold PMap_usr.
      destruct (PDE_usr_range_dec pt kern_low kern_high ).
      - left; unfold PDE_usr_range in *; intros. eauto.
      - right; red; intros.
        apply n; unfold PDE_usr_range; auto.
    Qed.

    Definition PMap_valid (pmap: PMap) :=   
      PMap_common pmap /\ PMap_usr pmap.

    Remark PMap_valid_dec:
      forall pt, {PMap_valid pt } + { ~ PMap_valid pt}.
    Proof.
      intros; unfold PMap_valid.
      destruct (PMap_common_dec pt).
      destruct (PMap_usr_dec pt).
      - left. eauto.
      - right; red; intros.
        apply n. apply H.
      - right; red; intros.
        apply n. apply H.
    Qed.
    
  End PT_Property.

  Function pt_Arg' (n vadr: Z) : bool :=
    if zlt_lt 0 n num_proc then
      if zle_lt adr_low vadr adr_high then
        true
      else false
    else false.      

  Function pt_Arg (n vadr padr np: Z) : bool :=
    if pt_Arg' n vadr then
      if zlt_lt 0 padr np then
        true
      else false
    else false.

  Section IDPMap_Property.

    Definition IDPTE_valid (pte: IDPTE) (i: Z) (b: bool):=
      ZMap.get i pte = IDPTEValid (PTK b).

    Definition IDPTE_valid_range (pte: IDPTE) (lo high: Z) (b: bool):=
      forall i , lo <= i < high -> IDPTE_valid pte i b.

    Definition IDPTE_valid_page (pte: IDPTE) (b: bool):=
      forall i , 0 <= i < one_k -> IDPTE_valid pte i b.

    Definition IDPDE_range (pde: IDPDE) (lo high: Z) (b: bool):=
      forall i , lo <= i < high -> IDPTE_valid_page (ZMap.get (PDX (i * PgSize)) pde) b.
    
    Definition IDPDE_common (pde: IDPDE) :=   
      forall i, 0<= i < kern_low \/ kern_high <= i < maxpage
                -> IDPTE_valid_page (ZMap.get (PDX (i * PgSize)) pde) true.

    Definition IDPDE_kern (pde: IDPDE) :=   
      forall i, kern_low <= i < kern_high
                -> IDPTE_valid_page (ZMap.get (PDX (i * PgSize)) pde) false.

    Definition IDPDE_init (pde: IDPDE) :=   
      IDPDE_common pde /\ IDPDE_kern pde.

    Remark IDPTE_valid_dec:
      forall pte i b, {IDPTE_valid pte i b} + {~ IDPTE_valid pte i b}.
    Proof.
      intros; unfold IDPTE_valid.
      repeat (decide equality).
    Qed.

    Remark IDPTE_valid_range_dec:
      forall pte lo high b, {IDPTE_valid_range pte lo high b} + {~ IDPTE_valid_range pte lo high b}.
    Proof.
      intros. unfold IDPTE_valid_range.
      eapply general_range_dec. intros.
      apply IDPTE_valid_dec.
    Qed.

    Remark IDPTE_valid_page_dec:
      forall pte b, {IDPTE_valid_page pte b} + {~ IDPTE_valid_page pte b}.
    Proof.
      intros. eapply IDPTE_valid_range_dec.
    Qed.

    Remark IDPDE_range_dec:
      forall pde lo high b, {IDPDE_range pde lo high b} + {~ IDPDE_range pde lo high b}.
    Proof.
      intros. unfold IDPDE_range.
      eapply general_range_dec. intros.
      apply IDPTE_valid_page_dec.
    Qed.

    Remark IDPDE_common_dec:
      forall pde, {IDPDE_common pde } + { ~ IDPDE_common pde}.
    Proof.
      intros; unfold IDPDE_common.
      destruct (IDPDE_range_dec pde 0 kern_low true).
      destruct (IDPDE_range_dec pde kern_high maxpage true).
      - left; unfold IDPDE_range in *; intros.
        destruct H; auto.
      - right; red; intros.
        unfold IDPDE_range in *; auto.
      - right; red; intros.
        apply n; unfold IDPDE_range; auto.
    Qed.

    Remark IDPDE_kern_dec:
      forall pde, {IDPDE_kern pde } + { ~ IDPDE_kern pde}.
    Proof.
      intros. apply IDPDE_range_dec.
    Qed.

    Remark IDPDE_init_dec:
      forall pde, {IDPDE_init pde } + { ~ IDPDE_init pde}.
    Proof.
      intros. 
      destruct (IDPDE_common_dec pde).
      destruct (IDPDE_kern_dec pde).
      - left; split; assumption.
      - right; red; intros; elim n. apply H.
      - right; red; intros; elim n. apply H.
    Qed.

  End IDPMap_Property.

  Definition PMapPool := ZMap.t PMap.

  Section PTP_Property.

    Definition consistent_pmap (ptp: PMapPool) (ppt: PPermT) (At: LATable) (nps: Z): Prop :=
      forall i,
        0 <= i < num_proc ->
        forall j,
          0<= j < adr_max ->
          forall pte pi,
            ZMap.get (PDX j) (ZMap.get i ptp) = PDEValid pi pte ->
            0 < pi < nps
            /\ ZMap.get pi ppt = PGHide (PGPMap i (PDX j))
            /\ ZMap.get pi At = LATValid true ATNorm nil.
    
    Lemma consistent_pmap_init:
      forall pg a nps,
      consistent_pmap (ZMap.init (ZMap.init PDEUndef)) pg a nps.
    Proof.
      unfold consistent_pmap.
      intros. repeat rewrite ZMap.gi in H1. inv H1.
    Qed.

    Definition consistent_pmap_domain (ptp: PMapPool) (ppt: PPermT) (At: LATable) (nps: Z): Prop :=
      forall i,
        0 <= i < num_proc ->
        forall j,
          0<= j < adr_max ->
          forall pte pi,
            ZMap.get (PDX j) (ZMap.get i ptp) = PDEValid pi pte ->
            forall v p,
              ZMap.get (PTX j) pte = PTEValid v p ->
              0 < v < nps
              /\ ZMap.get v ppt = PGAlloc (*PGLoadable*)
              /\ exists l, ZMap.get v At = LATValid true ATNorm l
                           /\ count_occ LATOwner_dec l (LATO i (PDX j) (PTX j)) = 1%nat.

    Lemma consistent_pmap_domain_init:
      forall pg At nps,
        consistent_pmap_domain (ZMap.init (ZMap.init PDEUndef)) pg At nps.
    Proof.
      unfold consistent_pmap_domain.
      intros. repeat rewrite ZMap.gi in H1. inv H1.
    Qed.

    Definition consistent_lat_domain (ptp: PMapPool) (At: LATable) (nps: Z): Prop :=
      forall v,
        0 < v < nps ->
        forall l, 
          ZMap.get v At = LATValid true ATNorm l ->
          forall n pdi pti,        
            In (LATO n pdi pti) l ->
            0 <= pti <= PTX (Int.max_unsigned)
            /\ exists pi pte,
                 ZMap.get pdi (ZMap.get n ptp) = PDEValid pi pte 
                 /\ exists p,
                      ZMap.get pti pte = PTEValid v p.
    
    Lemma consistent_lat_domain_init:
      forall ptp nps,
        consistent_lat_domain ptp (ZMap.init LATUndef) nps.
    Proof.
      unfold consistent_lat_domain.
      intros. repeat rewrite ZMap.gi in H0. inv H0.
    Qed.

    Definition PDE_unp (pmap: PMap) (i: Z) :=
      ZMap.get (PDX (i * PgSize)) pmap = PDEUnPresent.
    
    Definition PDE_unp_range (pmap: PMap) (lo high: Z) :=
      forall i , lo <= i < high -> PDE_unp pmap i.

    Definition PMap_init (pmap: PMap) :=
      PMap_common pmap
      /\ PDE_unp_range pmap kern_low kern_high.

    (*Definition PTP_init (pt: PTPool) (lo high: Z) :=
      forall i , lo <= i < high -> PT_init (ZMap.get i pt).*)

    (*Lemma PT_kern_PDT_valid:
      forall pt,
        PT_kern pt -> PDT_usr pt.
    Proof.
      unfold PT_kern, PDT_usr.
      unfold PT_pos, PDT_valid.
      intros. destruct (H _ H0) as [pte[HT1 HT2]].
      eauto.
    Qed.*)

    Lemma PMap_init_common_usr:
      forall pmap,
        PMap_init pmap -> PMap_valid pmap.
    Proof.
      unfold PMap_valid, PMap_init, PMap_usr, PDE_unp_range. intros.
      destruct H as [HT1 HT2]. 
      split; [assumption|].
      intros. exploit HT2; eauto.
      unfold PDE_unp, PDE_usr.
      left; assumption.
    Qed.

    Function ZtoBool (i:Z): option bool :=
     match i with
       | 0 => Some false
       | 1 => Some true
       | _ => None
     end.
 
   Function BooltoZ (b:bool): Z :=
     match b with
       | true => 1
       | _ => 0
     end.

  End PTP_Property.  

End MemoryManagement.

Section ProcessManagement.

  Definition KContext := regset.
  Definition KContextPool := ZMap.t KContext.
  
  Lemma register_type_load:
    forall (rs: regset)  r v f,
      Val.has_type (rs r) Tint
      -> val_inject f (Val.load_result Mint32 (rs r)) v
      -> val_inject f (rs r) v.
  Proof.
    intros.
    unfold Val.has_type in *.
    destruct (rs r); inv H; inv H0; try econstructor; eauto.
  Qed.
  
  Definition PregtoZ (r: preg) : option Z :=
    match r with 
      | ESP => Some 0
      | EDI => Some 1
      | ESI => Some 2
      | EBX => Some 3
      | EBP => Some 4
      | RA => Some 5
      | _ => None
    end.

  Function ZtoPreg (i: Z) : option preg :=
    match i with
      | 0 => Some (IR ESP)
      | 1 => Some (IR EDI)
      | 2 => Some (IR ESI)
      | 3 => Some (IR EBX) 
      | 4 => Some (IR EBP)
      | 5 => Some RA
      | _ => None
    end.
  
  Definition kctxt_inj (f:meminj) (range:Z) (kctxtp kctxtp': KContextPool) :=
    forall i n r,
      0<= n < range
      -> ZtoPreg i = Some r
      -> val_inject f (Pregmap.get r (ZMap.get n kctxtp)) (Pregmap.get r (ZMap.get n kctxtp')).

  Definition kctxt_inject_neutral (kp: KContextPool) (n: block) :=
    forall ofs, 
      0 <= ofs < num_proc -> 
      let rs := ZMap.get ofs kp in
      forall v r, ZtoPreg v = Some r -> 
                  Val.has_type (rs r) Tint
                  /\ val_inject (Mem.flat_inj n) (rs r) (rs r).

  Lemma PregToZ_correct:
    forall r i, PregtoZ r = Some i -> ZtoPreg i = Some r.
  Proof.      
    intros.
    induction r; inv H; auto.
    induction i0; inv H1; auto.
  Qed.

  Lemma ZtoPreg_correct:
    forall r i, ZtoPreg i = Some r -> PregtoZ r = Some i.
  Proof.
    functional inversion 1; trivial.
  Qed.

  Lemma ZtoPreg_range:
    forall n r, 
      ZtoPreg n = Some r -> 0<= n <= 5.
  Proof.
    functional inversion 1; omega.
  Qed.

  Lemma ZtoPreg_range_correct:
    forall n, 
      0<= n <= 5 -> exists r, ZtoPreg n = Some r.
  Proof.
    intros.
    destruct (zeq n 0). subst; simpl; eauto.
    destruct (zeq n 1). subst; simpl; eauto.
    destruct (zeq n 2). subst; simpl; eauto.
    destruct (zeq n 3). subst; simpl; eauto.
    destruct (zeq n 4). subst; simpl; eauto.
    destruct (zeq n 5). subst; simpl; eauto.    
    omega.
  Qed.

  Lemma ZtoPreg_type:
    forall v r,
      ZtoPreg v = Some r -> Tint = typ_of_preg r.
  Proof.
    functional inversion 1; trivial.
  Qed.

  Definition is_valid_context_reg (v: val) :=
    match v with
      | Vfloat _ => false
      | _ => true
    end.
  
  Inductive ThreadState :=
  | READY
  | RUN
  | SLEEP
  | DEAD.

  Remark ThreadState_dec: forall ts ts': ThreadState, {ts = ts'} + {~ ts = ts'}.
  Proof.
    intros; decide equality.
  Qed.

  Function ZtoThreadState (i:Z) :=
    match i with
      | 0 => Some READY
      | 1 => Some RUN
      | 2 => Some SLEEP
      | 3 => Some DEAD
      | _ => None
    end.
  
  Definition ThreadStatetoZ (tds: ThreadState) :=
    match tds with
      | READY => 0
      | RUN => 1
      | SLEEP => 2
      | DEAP => 3
    end.

  Lemma ZtoThreadState_correct: 
    forall i tds, ZtoThreadState i = Some tds -> ThreadStatetoZ tds = i.
  Proof.  
    functional inversion 1; trivial.
  Qed.

  Lemma ThreadStatetoZ_correct: 
    forall tds, ZtoThreadState (ThreadStatetoZ tds) = Some tds.
  Proof.  
    destruct tds; trivial.
  Qed.

  Lemma ZtoThreadState_range:
    forall i tds, ZtoThreadState i = Some tds -> 0 <= i <= 3.
  Proof.
    functional inversion 1; omega.
  Qed.

  Lemma ZtoThreadState_range_correct:
    forall i, 0<= i <= 3 -> exists tds, ZtoThreadState i = Some tds. 
  Proof.
    intros.
    destruct (zeq i 0). subst; simpl; eauto.
    destruct (zeq i 1). subst; simpl; eauto.
    destruct (zeq i 2). subst; simpl; eauto.
    destruct (zeq i 3). subst; simpl; eauto.
    omega.
  Qed.

  Inductive TCB :=
  | TCBUndef
  | TCBValid (tds: ThreadState) (prev: Z) (next: Z).

  Remark TCB_dec: forall tcb tcb': TCB, {tcb = tcb'} + {~ tcb = tcb'}.
  Proof.
    intros.
    decide equality.
    apply Z_eq_dec.
    apply Z_eq_dec.
    apply ThreadState_dec.
  Qed.
  
  Definition TCBPool := ZMap.t TCB.

  Definition TCBCorrect (tcb: TCB) (high:Z) :=
    exists s prev next, tcb = TCBValid s prev next /\ 0<= prev <= high /\ 0<= next <= high.

  Definition TCBCorrect_range' (tcb: TCBPool) (lo high num_proc: Z) :=
    forall i , lo <= i < high -> TCBCorrect (ZMap.get i tcb) num_proc. 
  
  Definition TCBCorrect_range (tcb: TCBPool) :=
    forall i , 0 <= i < num_proc -> TCBCorrect (ZMap.get i tcb) num_proc. 

  Definition TCBInit' (tcb: TCBPool) (lo high num_proc: Z) :=
    forall i , lo <= i < high -> ZMap.get i tcb = TCBValid DEAD num_proc num_proc. 

  Definition TCBInit (tcb: TCBPool) :=
    forall i , 0 <= i < num_proc -> ZMap.get i tcb = TCBValid DEAD num_proc num_proc. 

  Inductive TDQueue :=
  | TDQUndef
  | TDQValid (head tail: Z).

  Definition TDQueuePool := ZMap.t TDQueue.

  Definition TDQCorrect (tdq: TDQueue) (high:Z) :=
    exists head tail, tdq = TDQValid head tail /\ 0<= head <= high /\ 0<= tail <= high.

  Definition TDQCorrect_range (tdq: TDQueuePool) :=
    forall i , 0 <= i <= num_chan -> TDQCorrect (ZMap.get i tdq) num_proc. 
  
  Definition TDQInit (tdq: TDQueuePool) :=
    forall i , 0 <= i <= num_chan -> ZMap.get i tdq = TDQValid num_proc num_proc. 

  Inductive AbQueue :=
  | AbQUndef
  | AbQValid (l: list Z).

  Definition AbQueuePool := ZMap.t AbQueue.
  
  (* [inQ] below is the index of the queue the process is in:

      -1             no queue
      0..num_proc-1  the queue associated with thread n
      num_proc       the ready queue
   *)
  Inductive AbTCB :=
  | AbTCBUndef
  | AbTCBValid (tds: ThreadState) (inQ: Z).

  Definition AbTCBPool := ZMap.t AbTCB.

  Definition AbTCBCorrect (tcb: AbTCB):=
    exists s b, tcb = AbTCBValid s b /\ (-1 <= b <= num_chan).
  
  Definition AbTCBStrong (tcb: AbTCB):=
    exists s b, tcb = AbTCBValid s b /\ ((s = RUN \/ s = DEAD) -> b = -1) 
                /\ (s = SLEEP -> 0 <= b < num_chan)
                /\ (s = READY -> b = num_chan).

  Definition AbQCorrect (tdq: AbQueue) :=
    exists l, tdq = AbQValid l /\ (forall x, In x l -> 0 <= x < num_proc).

  Definition AbTCBInit (tcb: AbTCBPool) :=
    forall i , 0 <= i < num_proc -> ZMap.get i tcb = AbTCBValid DEAD (-1). 

  Definition AbQInit (tdq: AbQueuePool) :=
    forall i , 0 <= i <= num_proc -> ZMap.get i tdq = AbQValid nil. 

  Definition AbTCBCorrect_range t :=
    forall i, 0 <= i < num_proc -> AbTCBCorrect (ZMap.get i t).

  Definition AbTCBStrong_range t:=
    forall i, 0 <= i < num_proc -> 
              AbTCBStrong (ZMap.get i t).

  Definition AbQCorrect_range q :=
    forall i, 0 <= i <= num_chan ->  AbQCorrect (ZMap.get i q).

  Definition NotInQ c t :=
    forall i s b, 
      0 <= i < num_proc
      -> cused (ZMap.get i c) = false
      -> ZMap.get i t = AbTCBValid s b
      -> b = -1.

  Definition QCount t q :=
    forall i s b, 
      0 <= i < num_proc
      -> ZMap.get i t = AbTCBValid s b
      -> 0 <= b <= num_chan
      -> exists l, 
           ZMap.get b q = AbQValid l
           /\ count_occ zeq l i = 1%nat.

  Definition InQ t q :=
    forall i j l, 
      0 <= i < num_proc
      -> 0 <= j <= num_chan
      -> ZMap.get j q = AbQValid l
      -> In i l
      -> exists s, ZMap.get i t = AbTCBValid s j.

  Definition CurIDValid i c t :=
    cused (ZMap.get i c) = true
    /\ (ZMap.get i t = AbTCBValid RUN (-1)).

  Definition SingleRun c t :=
    forall i s b,
      0 <= i < num_proc
      -> i <> c
      -> ZMap.get i t = AbTCBValid s b
      -> s <> RUN.

  Function Queue_arg (n i: Z) :=
    if zle_le 0 n num_chan then
      if zle_lt 0 i num_proc then
        true
      else false
    else false. 

  Section AbTCB_TDQ_Property.

    Lemma AbTCBInit_valid:
      forall tcbp,
        AbTCBInit tcbp
        -> (forall i, 0 <= i < num_proc ->
                      AbTCBCorrect (ZMap.get i tcbp)).
    Proof.
      unfold AbTCBInit, AbTCBCorrect; intros.
      esplit; esplit. split.
      eapply H; eauto. omega.
    Qed.

    Lemma AbTCBInit_notInQ:
      forall tcbp,
        AbTCBInit tcbp ->
        (forall i s b, 0 <= i < num_proc ->
                       ZMap.get i tcbp = AbTCBValid s b ->
                       b = -1).
    Proof.
      unfold AbTCBInit; intros.
      specialize (H _ H0). rewrite H1 in H; inv H. trivial.
    Qed.

    Lemma AbTDQInit_valid:
      forall tdqp,
        AbQInit tdqp
        -> (forall i, 0 <= i <= num_proc ->
                      AbQCorrect (ZMap.get i tdqp)).
    Proof.
      unfold AbQInit, AbQCorrect; intros.
      esplit. split.
      eapply H; eauto. intros. inv H1.
    Qed.

  End AbTCB_TDQ_Property.

  Definition UContext := ZMap.t val.
  
  Definition UContextPool := ZMap.t UContext.

  Definition uctxt_inj (f:meminj) (uctxtp uctxtp': UContextPool) :=
    forall i j,
      0<= i < num_proc ->
      0<= j < UCTXT_SIZE -> 
      val_inject f (ZMap.get j (ZMap.get i uctxtp))
                 (ZMap.get j (ZMap.get i uctxtp')).

  Definition uctxt_inject_neutral (up: UContextPool) (n: block) :=
    forall ii ii', 
      0<= ii < num_proc ->
      0<= ii' < UCTXT_SIZE ->
      let v:= (ZMap.get ii' (ZMap.get ii up)) in
      Val.has_type v AST.Tint
      /\ val_inject (Mem.flat_inj n) v v.

(*
  typedef
    struct pushregs {
      uint32_t edi;
      uint32_t esi;
      uint32_t ebp;
      uint32_t oesp;		/* Useless */
      uint32_t ebx;
      uint32_t edx;
      uint32_t ecx;
      uint32_t eax;
    } pushregs;

    typedef
      struct tf_t {
	/* registers and other info we push manually in trapasm.S */
	                                                          pushregs regs;
	uint16_t es;		uint16_t padding_es;
	uint16_t ds;		uint16_t padding_ds;
	uint32_t trapno;

	/* format from here on determined by x86 hardware architecture */
	uint32_t err;
	uintptr_t eip;
	uint16_t cs;		uint16_t padding_cs;
	uint32_t eflags;

	/* rest included only when crossing rings, e.g., user to kernel */
	uintptr_t esp;
        uint16_t ss;		uint16_t padding_ss;
      } tf_t;
*)

  Function is_UCTXT_ptr (ofs : Z): bool :=
    match ofs with
      | U_EDI => false
      | U_ESI => false
      | U_EBX => false
      | U_EDX => false
      | U_ECX => false
      | U_EAX => false
      | U_ES => false
      | U_DS => false
      | U_ERR => false
      | U_TRAPNO => false
      | U_CS => false
      | U_EFLAGS => false
      | U_ESP => false
      | U_SS => false
      | _ => true
    end.

  Lemma is_UCTXT_ptr_range:
    forall i, is_UCTXT_ptr i = false -> 0<= i < UCTXT_SIZE.
  Proof.
    intros.
    functional inversion H; omega.
  Qed.

  Function UCtxt_Reg (r: preg) : bool :=
    match r with
      | IR _ => true
      | RA => true
      | _ => false
    end.

  (* Sync IPC Channel *)
  Inductive SyncChannel :=
  | SyncChanUndef
  | SyncChanValid (to senderpaddr count: int).

  Definition SyncChanPool := ZMap.t SyncChannel.

  Definition SyncChannel_Valid (ch: SyncChannel) :=
    exists t p c, ch = SyncChanValid t p c.

  Definition SyncChanPool_Valid (chp: SyncChanPool) :=
    forall i, 0 <= i < num_chan -> SyncChannel_Valid (ZMap.get i chp).

  Definition SyncChannel_Init (ch: SyncChannel) :=
    ch = SyncChanValid (Int.repr num_chan) Int.zero Int.zero.

  Definition SyncChanPool_Init (chp: SyncChanPool) :=
    forall i, 0 <= i < num_chan -> SyncChannel_Init (ZMap.get i chp).

  Lemma SyncChannel_Init_Correct:
    forall chp,
      SyncChanPool_Init chp -> SyncChanPool_Valid chp.
  Proof.
    unfold SyncChanPool_Init, SyncChanPool_Valid.
    unfold SyncChannel_Init, SyncChannel_Valid.
    eauto.
  Qed.

  (*Inductive Channel :=
    | ChanUndef
    | ChanValid (isbusy content: int).

    Definition ChanPool := ZMap.t Channel.
    
    Definition Channel_Valid  (ch: Channel) := 
      exists ib ct, ch = ChanValid ib ct.
    
    Definition ChanPool_Valid (chp: ChanPool) :=
      forall i , 0 <= i < num_chan -> Channel_Valid (ZMap.get i chp).

    Definition Channel_Init  (ch: Channel) := 
      ch = ChanValid Int.zero Int.zero.
    
    Definition ChanPool_Init (chp: ChanPool) :=
      forall i , 0 <= i < num_chan -> Channel_Init (ZMap.get i chp).

    Lemma ChanPool_Init_Correct:
      forall chp,
        ChanPool_Init chp -> ChanPool_Valid chp.
    Proof.
      unfold ChanPool_Init, ChanPool_Valid.
      unfold Channel_Init, Channel_Valid.
      eauto.
    Qed.*)

  Inductive SharedMemInfo :=
  | SHRDREADY  | SHRDPEND  | SHRDDEAD.

  Remark SharedMemInfo_dec:
    forall x y: SharedMemInfo,
      {x = y} + {x <> y}.
  Proof.
    intros. repeat progress (decide equality).
  Qed.

  Inductive SharedMemState :=
  | SHRDValid (info: SharedMemInfo) (seen: bool) (vadr: Z) 
  | SHRDUndef.

  Definition SharedMemSTPool :=
    ZMap.t (ZMap.t SharedMemState).

  Function SharedMemInfo2Z (i: SharedMemInfo) :=
    match i with      
      | SHRDREADY => SHARED_MEM_READY
      | SHRDPEND => SHARED_MEM_PEND
      | SHRDDEAD => SHARED_MEM_DEAD
    end.

  Function Z2SharedMemInfo (i: Z) :=
    match i with
      | SHARED_MEM_READY => Some SHRDREADY
      | SHARED_MEM_PEND => Some SHRDPEND
      | SHARED_MEM_DEAD => Some SHRDDEAD
      | _ => None
    end.

  Lemma Z2SharedMemInfo_correct:
    forall st i,
      Z2SharedMemInfo st = Some i ->
      SharedMemInfo2Z i = st.
  Proof.
    functional inversion 1; reflexivity.
  Qed.

  Lemma SharedMemInfo2Z_correct:
    forall st i,
      SharedMemInfo2Z i = st ->
      Z2SharedMemInfo st = Some i.
  Proof.
    functional inversion 1; reflexivity.
  Qed.

  Lemma SharedMemInfo2Z_range:
    forall st i,
      SharedMemInfo2Z i = st ->
      SHARED_MEM_READY <= st <= SHARED_MEM_DEAD.
  Proof.
    functional inversion 1; omega.
  Qed.

  Definition SharedMemST_Valid (st: SharedMemState) := 
    exists i s vadr, st = SHRDValid i s vadr.
  
  Definition SharedMemSTPool_Init (smsp: SharedMemSTPool) :=
    forall i, 
      0 <= i < num_proc -> 
      forall j, 0 <= j < num_proc ->
                SharedMemST_Valid (ZMap.get j (ZMap.get i smsp)).
 
End ProcessManagement.

Section VirtManagement.

  Inductive NPTPerm :=
  | ALL_PERM.

  Definition NPTPerm2Z (perm : NPTPerm) : Z :=
    match perm with
      | ALL_PERM => 39
    end.

  Inductive NPTE:=
  | NPTEValid (hpa: Z)
  | NPTEUndef.

  Definition NPTab := ZMap.t NPTE.

  Inductive NPDE :=
  | NPDEValid (nptab : NPTab)
  | NPDEUndef.

  Definition NPT := ZMap.t NPDE.

  Definition NPDE_valid (npt: NPT) (i:Z) :=
    exists npte, ZMap.get (PDX i) npt = NPDEValid npte.

  (*Remark NPDE_valid_dec (npt: NPT)(i:Z):
    {NPDE_valid npt i} + {~ NPDE_valid npt i}.
  Proof.
    unfold NPDE_valid.
    destruct (ZMap.get (PDX i) npt).
    left.
    exists nptab.
    trivial.
    right.
    red; intros.
    destruct H as [pte HF].
    inv HF.
  Qed.*)

  Definition NPT_valid (npt: NPT) (lo high: Z):=
    forall i , lo <= i < high -> NPDE_valid npt i.

  (*Remark NPT_valid_dec:
    forall npt lo high, {NPT_valid npt lo high} + {~ NPT_valid npt lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {NPT_valid npt lo (lo+n)} + {~NPT_valid npt lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    destruct (NPDE_valid_dec npt (lo+z)).
    left.
    unfold NPT_valid in *.
    intros.
    destruct (zeq i (lo + z)).
    congruence.
    apply n.
    omega.
    right; red; intro.
    elim n0.
    apply H0.
    omega.
    right; red; intro.
    elim n.
    red; intros.
    apply H0.
    omega.

    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction.
  Qed.*)

  Definition PregtoZ_Host (r: preg) : option Z :=
    match r with
      | ECX => Some 0
      | EDI => Some 1
      | ESI => Some 2
      | EBX => Some 3
      | EBP => Some 4
      | EDX => Some 5
      | ESP => Some 6
      | RA => Some 7
      | _ => None
    end.

  Function ZtoPreg_Host (i: Z) : option preg :=
    match i with
      | 0 => Some (IR ECX)
      | 1 => Some (IR EDI)
      | 2 => Some (IR ESI)
      | 3 => Some (IR EBX)
      | 4 => Some (IR EBP)
      | 5 => Some (IR EDX)
      | 6 => Some (IR ESP)
      | 7 => Some RA
      | _ => None
    end.

  Lemma PregToZ_Host_correct:
    forall r i, PregtoZ_Host r = Some i -> ZtoPreg_Host i = Some r.
  Proof.
    intros. destruct r; inv H.
    destruct i0; inv H1; reflexivity.
    reflexivity.
  Qed.

  Lemma ZtoPreg_Host_correct:
    forall r i, ZtoPreg_Host i = Some r -> PregtoZ_Host r = Some i.
  Proof.
    intros. functional inversion H; reflexivity.
  Qed.

  Lemma ZtoPreg_Host_range:
    forall n r,
      ZtoPreg_Host n = Some r -> 0<= n <= 7.
  Proof.
    intros. functional inversion H; omega.
  Qed.

  Lemma ZtoPreg_range_Host_correct:
    forall n,
      0<= n <= 7 -> exists r, ZtoPreg_Host n = Some r.
  Proof.
    intros.
    destruct (zeq n 0); subst. simpl; eauto.
    destruct (zeq n 1); subst. simpl; eauto.
    destruct (zeq n 2); subst. simpl; eauto.
    destruct (zeq n 3); subst. simpl; eauto.
    destruct (zeq n 4); subst. simpl; eauto.
    destruct (zeq n 5); subst. simpl; eauto.
    destruct (zeq n 6); subst. simpl; eauto.
    destruct (zeq n 7); subst. simpl; eauto.
    omega.
  Qed.

  Lemma ZtoPreg_Host_type:
    forall n r,
      ZtoPreg_Host n = Some r ->
      typ_of_preg r = Tint.
  Proof.
    intros. functional inversion H; reflexivity.
  Qed.

  Definition hctx_inj (f:meminj)(hctxt hctxt': regset) :=
    forall i r,
      ZtoPreg_Host i = Some r
      -> val_inject f (Pregmap.get r hctxt) (Pregmap.get r hctxt').

  Definition addr_valid (addr : Z) :=
    if zle_le 0 addr (Int.max_unsigned + 1 - PgSize) then
      if Zdivide_dec PgSize addr HPS then
        true
      else
        false
    else
      false.

  Function is_VMCB_Z_ofs (v:Z) : bool :=
    if zle_lt 0 v 16 then
      true
    else
      if zle_lt 18 v 44 then
        true
      else
        if zle_lt 46 v 338 then
          true
        else
          if zle_lt 344 v 348 then
            true
          else
            if zle_lt 352 v 374 then
              true
            else
              if zle_lt 376 v 382 then
                true
              else
                if zle_lt 384 v 400 then
                  true
                else
                  if zle_lt 402 v 1024 then
                    true
                  else
                    false.

  Lemma VMCB_Z_ofs_range:
    forall v, is_VMCB_Z_ofs v = true -> 0 <= v <= 1023.
  Proof.
    intros.
    functional inversion H; omega.
  Qed.

  Function is_VMCB_V_ofs (v:Z) : bool :=
    match v with
      | VMCB_V_CR4_LO_OFFSET         => true
      | VMCB_V_CR3_LO_OFFSET         => true
      | VMCB_V_CR0_LO_OFFSET         => true
      | VMCB_V_RFLAGS_LO_OFFSET      => true
      | VMCB_V_RIP_LO_OFFSET         => true
      | VMCB_V_RSP_LO_OFFSET         => true
      | VMCB_V_RAX_LO_OFFSET         => true
      | VMCB_V_CR2_LO_OFFSET         => true
      | _ => false
    end.

  Lemma VMCB_V_ofs_range:
    forall v, is_VMCB_V_ofs v = true -> VMCB_V_CR4_LO_OFFSET <= v <= VMCB_V_CR2_LO_OFFSET.
  Proof.
    intros.
    functional inversion H; omega.
  Qed.

  Lemma VMCB_V_ofs_correct:
    forall v, is_VMCB_V_ofs v = true -> is_VMCB_Z_ofs v = false.
  Proof.
    intros. 
    functional inversion H; trivial.    
  Qed.

  Lemma VMCB_Z_ofs_correct:
    forall v, is_VMCB_Z_ofs v = true -> is_VMCB_V_ofs v = false.
  Proof.
    intros.
    functional induction (is_VMCB_V_ofs v); trivial; inv H.
  Qed.

  Inductive valid_val: val -> Prop :=
  | valid_val_int: forall n, valid_val (Vint n)
  | valid_val_vptr: forall b ofs, valid_val (Vptr b ofs)
  | valid_val_undef: valid_val Vundef.

  Definition VMCB_Val := ZMap.t val.

  Inductive VMCB_Entry_Z :=
  | VMCBEntryZValid (v : Z)
  | VMCBEntryZUndef.

  Definition VMCB_Z := ZMap.t VMCB_Entry_Z.

  Definition VMCB_Entry_Z_Valid (vmcb_z : VMCB_Z) (ofs : Z) : Prop :=
    exists v, ZMap.get ofs vmcb_z = VMCBEntryZValid v /\ 0 <= v <= Int.max_unsigned.

  (*Remark VMCB_Entry_Z_Valid_dec :
    forall vmcb_z ofs,
      { VMCB_Entry_Z_Valid vmcb_z ofs } + { ~ VMCB_Entry_Z_Valid vmcb_z ofs }.
  Proof.
    intros.
    unfold VMCB_Entry_Z_Valid.
    destruct (ZMap.get ofs vmcb_z).
    destruct (zle 0 v).
    destruct (zle v Int.max_unsigned).

    left.
    exists v. split; auto.

    right.
    intro H.
    destruct H as [v' [H_0 H_1]].
    inv H_0.
    omega.

    right.
    intro H.
    destruct H as [v' [H_0 H_1]].
    inv H_0.
    omega.

    right.
    intro H.
    destruct H as [v' [H_0 H_1]].
    inv H_0.
  Qed.*)

  Definition VMCB_Z_Range_Valid (vmcb_z : VMCB_Z) (lo high: Z):=
    forall i , lo <= i < high -> VMCB_Entry_Z_Valid vmcb_z i.

  (*Remark VMCB_Z_Range_Valid_dec:
    forall vmcb_z lo high, {VMCB_Z_Range_Valid vmcb_z lo high} + {~ VMCB_Z_Range_Valid vmcb_z lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {VMCB_Z_Range_Valid vmcb_z lo (lo+n)} + {~VMCB_Z_Range_Valid vmcb_z lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    destruct (VMCB_Entry_Z_Valid_dec vmcb_z (lo+z)).
    left.
    unfold VMCB_Z_Range_Valid in *.
    intros.
    destruct (zeq i (lo + z)).
    congruence.
    apply v.
    omega.
    right; red; intro.
    elim n.
    apply H0.
    omega.
    right; red; intro.
    elim n.
    red; intros.
    apply H0.
    omega.

    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction.
  Qed.*)

  Definition VMCB_Z_Valid (vmcb_z : VMCB_Z) :=
    forall ofs, is_VMCB_Z_ofs ofs = true -> VMCB_Entry_Z_Valid vmcb_z ofs.

  Ltac simpl_if :=
    repeat match goal with
             | [ |- context [if ?a then _ else _]] => destruct a
           end; trivial; try omega.

  (*Remark VMCB_Z_Valid_dec (vmcb_z : VMCB_Z) :
    { VMCB_Z_Valid vmcb_z } + { ~ VMCB_Z_Valid vmcb_z }.
  Proof.
    unfold VMCB_Z_Valid.
    destruct (VMCB_Z_Range_Valid_dec vmcb_z 0 16);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    destruct (VMCB_Z_Range_Valid_dec vmcb_z 18 44);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    destruct (VMCB_Z_Range_Valid_dec vmcb_z 46 338);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    destruct (VMCB_Z_Range_Valid_dec vmcb_z 344 348);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    destruct (VMCB_Z_Range_Valid_dec vmcb_z 352 374);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    destruct (VMCB_Z_Range_Valid_dec vmcb_z 376 382);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    destruct (VMCB_Z_Range_Valid_dec vmcb_z 384 400);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    destruct (VMCB_Z_Range_Valid_dec vmcb_z 402 1024);
      [|right; red; intros; elim n; unfold VMCB_Z_Range_Valid; intros;
        apply H; unfold is_VMCB_Z_ofs;
        destruct H0 as [HT1 HT2]; simpl; simpl_if].

    left.
    intros.
    unfold VMCB_Z_Range_Valid in *.
    functional inversion H; auto.

  Qed.*)

  Definition XVMState := ZMap.t val.

  Definition bit_not (n : Z) : Z := Z.lxor n (Int.unsigned Int.mone).

  Lemma Z_lxor_range :
    forall x y,
      0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
      0 <= Z.lxor x y <= Int.max_unsigned.
  Proof.
    unfold Int.max_unsigned. simpl.
    intros.
    split.
    rewrite Z.lxor_nonneg.
    split; omega.
    assert(Z.lxor x y < 4294967296).
    apply Z.log2_lt_cancel.
    assert(Z.log2 (Z.lxor x y) <= Z.max (Z.log2 x) (Z.log2 y)).
    apply Z.log2_lxor.
    omega.
    omega.
    apply Z.le_lt_trans with (m := Z.max (Z.log2 x) (Z.log2 y)); auto.
    rewrite Zmax_spec in *.
    destruct (zlt (Z.log2 y) (Z.log2 x)).
    assert(Z.log2 x <= Z.log2 4294967295).
    apply Z.log2_le_mono.
    omega.
    simpl in *.
    omega.
    assert(Z.log2 y <= Z.log2 4294967295).
    apply Z.log2_le_mono.
    omega.
    simpl in *.
    omega.
    omega.
  Qed.

  Lemma bit_not_range :
    forall n,
      0 <= n <= Int.max_unsigned ->
      0 <= bit_not n <= Int.max_unsigned.
  Proof.
    unfold bit_not. intros.
    apply Z_lxor_range; auto.
    unfold Int.mone.
    destruct (Int.repr (-1)).
    simpl.
    unfold Int.max_unsigned in *.
    omega.
  Qed.

  (** Primitives: get the information of VMEXIT
                    idx = 0 : get the lower 32-bit of EXITCODE;
                    idx = 1 : get the lower 32-bit of EXITINFO1;
                    idx = 2 : get the lower 32-bit of EXITINFO2;
                    idx = 3 : get the lower 32-bit of EXITINTINFO;
                    idx = 4 : get the higher 32-bit of EXITINTINFO. *)

  Function id2exitcode (idx: Z) :=
    match idx with
      | 0 => Some VMCB_Z_EXITCODE_LO_OFFSET
      | 1 => Some VMCB_Z_EXITINFO1_LO_OFFSET
      | 2 => Some VMCB_Z_EXITINFO2_LO_OFFSET
      | 3 => Some VMCB_Z_EXITINTINFO_LO_OFFSET
      | 4 => Some VMCB_Z_EXITINTINFO_HI_OFFSET
      | _ => None
    end.

  (* Primitive: write the guest segment registers
                  seg = 0 : CS;
                  seg = 1 : DS;
                  seg = 2 : ES;
                  seg = 3 : FS;
                  seg = 4 : GS;
                  seg = 5 : SS;
                  seg = 6 : LDTR;
                  seg = 7 : TR;
                  seg = 8 : GDTR;
                  seg = 9 : IDTR *)
  Function seg2offset (seg : Z) : Z :=
    match seg with
      | G_CS => VMCB_Z_CS_OFFSET
      | G_DS => VMCB_Z_DS_OFFSET
      | G_ES => VMCB_Z_ES_OFFSET
      | G_FS => VMCB_Z_FS_OFFSET
      | G_GS => VMCB_Z_GS_OFFSET
      | G_SS => VMCB_Z_SS_OFFSET
      | G_LDTR => VMCB_Z_LDTR_OFFSET
      | G_TR => VMCB_Z_TR_OFFSET
      | G_GDTR => VMCB_Z_GDTR_OFFSET
      | _ => VMCB_Z_IDTR_OFFSET
    end.

  (* Primitive: write the guest registers
                  reg =  0: EAX;
                  reg =  7: ESP;
                  reg =  8: EIP;
                  reg =  9: EFLAGS;
                  reg = 10: CR0;
                  reg = 11: CR2;
                  reg = 12: CR3;
                  reg = 13: CR4 *)

  Function reg2offset (reg : Z) : option Z :=
    match reg with
      | G_EAX => Some VMCB_V_RAX_LO_OFFSET
      | G_ESP => Some VMCB_V_RSP_LO_OFFSET
      | G_EIP => Some VMCB_V_RIP_LO_OFFSET
      | G_EFLAGS => Some VMCB_V_RFLAGS_LO_OFFSET
      | G_CR0 => Some VMCB_V_CR0_LO_OFFSET
      | G_CR2 => Some VMCB_V_CR2_LO_OFFSET
      | G_CR3 => Some VMCB_V_CR3_LO_OFFSET
      | G_CR4 => Some VMCB_V_CR4_LO_OFFSET
      | _ => None
    end.

  Lemma reg2offset_correct:
    forall r n, reg2offset r = Some n -> is_VMCB_V_ofs n = true.
  Proof.
    intros.
    functional inversion H;
      trivial.
  Qed.

  Function xreg2offset (reg : Z) : option Z :=
    match reg with
      | G_EBX => Some XVMST_EBX_OFFSET
      | G_ECX => Some XVMST_ECX_OFFSET
      | G_EDX => Some XVMST_EDX_OFFSET
      | G_ESI => Some XVMST_ESI_OFFSET
      | G_EDI => Some XVMST_EDI_OFFSET
      | G_EBP => Some XVMST_EBP_OFFSET
      | _ => None
    end.

  Lemma xreg2offset_correct:
    forall r n, xreg2offset r = Some n -> 0<= n < XVMST_SIZE.
  Proof.
    intros.
    functional inversion H;
      omega.
  Qed.

  (* Primitive: write the guest registers
                  reg =  0: EAX;
                  reg =  1: EBX;
                  reg =  2: ECX;
                  reg =  3: EDX;
                  reg =  4: ESI;
                  reg =  5: EDI;
                  reg =  6: EBP;
                  reg =  7: ESP;
                  reg =  8: EIP;
                  reg =  9: EFLAGS;
                  reg = 10: CR0;
                  reg = 11: CR2;
                  reg = 12: CR3;
                  reg = 13: CR4 *)

  Function hreg2offset (reg : Z) : Z :=
    match reg with
      | G_EAX => VMCB_V_RAX_LO_OFFSET
      | G_EBX => XVMST_EBX_OFFSET
      | G_ECX => XVMST_ECX_OFFSET
      | G_EDX => XVMST_EDX_OFFSET
      | G_ESI => XVMST_ESI_OFFSET
      | G_EDI => XVMST_EDI_OFFSET
      | G_EBP => XVMST_EBP_OFFSET
      | G_ESP => VMCB_V_RSP_LO_OFFSET
      (*| G_EIP => VMCB_V_RIP_LO_OFFSET*)
      | _ => VMCB_V_RIP_LO_OFFSET
    end.

End VirtManagement.

Ltac inv_uctx_primitive HVV:=
  repeat match goal with
           | [ |- context[Pregmap.elt_eq ?a ?b]] 
             => destruct (Pregmap.elt_eq a b);
               [try (eapply HVV; eauto; try omega; try (apply PregToZ_correct; compute;trivial))|]
         end.

Ltac inv_hctx_primitive HVV:=
        repeat match goal with
                 | [ |- context[Pregmap.elt_eq ?a ?b]]
                   => destruct (Pregmap.elt_eq a b);
                     [try (eapply HVV; eauto; try omega; try (apply PregToZ_Host_correct; compute;trivial))|]
               end.

Notation Lremove := (remove LATOwner_dec).

Section IntelVirtManagement.

  Section EPTDEF.

    Definition EPT_PTAB_INDEX (i:Z) := (i/PgSize) mod five_one_two.
    Definition EPT_PDIR_INDEX (i:Z) := (i/ (PgSize * five_one_two)) mod five_one_two.
    Definition EPT_PDPT_INDEX (i:Z) := (i/ (PgSize * five_one_two * five_one_two))
                                         mod five_one_two.
    Definition EPT_PML4_INDEX (i:Z) := (i/ (PgSize * five_one_two * five_one_two *
                                            five_one_two)) mod five_one_two.
    Definition EPTADDR (i:Z) (ofs:Z) := (i * PgSize) + (ofs mod PgSize).

    Inductive EPTPerm :=
    | ALL_EPERM.

    Definition EPTPerm2Z (perm : EPTPerm) : Z := 7.

    (* PTab entry *)
    Inductive EPTE:=
    | EPTEValid (hpa: Z)
    | EPTEUndef.

    Definition EPTAB := ZMap.t EPTE.

    (* PDT entry *)
    Inductive EPDTE :=
    | EPDTEValid (eptab : EPTAB)
    | EPDTEUndef.

    Definition EPDT := ZMap.t EPDTE.

    (* Definition EPDTE_valid (epdt: EPDT) (i:Z) :=
    exists eptab, ZMap.get (EPT_PDIR_INDEX i) epdt = EPDTEValid eptab.

  Definition EPDT_valid (epdt: EPDT) (lo high: Z):=
    forall i , lo <= i < high -> EPDTE_valid epdt i. *)

    (* PDPT entry *)
    Inductive EPDPTE :=
    | EPDPTEValid (epdt: EPDT)
    | EPDPTEUndef.

    Definition EPDPT := ZMap.t EPDPTE.

    (* Definition EPDPTE_valid (epdpt: EPDPT) (i:Z) := 
    exists epdt, ((ZMap.get i epdpt = EPDPTEValid epdt) /\
    EPDT_valid epdt 0 Int.max_unsigned).

  Definition EPDPT_valid (epdpt: EPDPT) (lo high: Z) :=
    forall i, lo <= i < high -> EPDPTE_valid epdpt i. *)

    (* PML4 entry *)

    Inductive EPML4E :=
    | EPML4EValid (epdpt: EPDPT)
    | EPML4EUndef.

    Definition EPT := ZMap.t EPML4E.

    Definition EPT_valid (ept: EPT) :=
      exists epdpt, ((ZMap.get 0 ept = EPML4EValid epdpt) /\
                     (forall i2, 0 <= i2 < 4 -> 
                                 exists epdt, ((ZMap.get i2 epdpt = EPDPTEValid epdt) /\
                                               (forall i3, 0 <= i3 < 512 -> exists eptab, (ZMap.get i3 epdt = EPDTEValid eptab))))).
  
  End EPTDEF.

  Section VMCSDEF.

    Inductive VMCS_Encoding : Type :=
    | VMCS_VPID
    | VMCS_GUEST_ES_SELECTOR
    | VMCS_GUEST_CS_SELECTOR
    | VMCS_GUEST_SS_SELECTOR
    | VMCS_GUEST_DS_SELECTOR
    | VMCS_GUEST_FS_SELECTOR
    | VMCS_GUEST_GS_SELECTOR
    | VMCS_GUEST_LDTR_SELECTOR
    | VMCS_GUEST_TR_SELECTOR
    | VMCS_HOST_ES_SELECTOR
    | VMCS_HOST_CS_SELECTOR
    | VMCS_HOST_SS_SELECTOR
    | VMCS_HOST_DS_SELECTOR
    | VMCS_HOST_FS_SELECTOR
    | VMCS_HOST_GS_SELECTOR
    | VMCS_HOST_TR_SELECTOR
    | VMCS_IO_BITMAP_A
    | VMCS_IO_BITMAP_A_HI
    | VMCS_IO_BITMAP_B
    | VMCS_IO_BITMAP_B_HI
    | VMCS_MSR_BITMAP
    | VMCS_MSR_BITMAP_HI
    | VMCS_EXIT_MSR_STORE
    | VMCS_EXIT_MSR_LOAD
    | VMCS_ENTRY_MSR_LOAD
    | VMCS_EXECUTIVE_VMCS
    | VMCS_TSC_OFFSET
    | VMCS_VIRTUAL_APIC
    | VMCS_APIC_ACCESS
    | VMCS_EPTP
    | VMCS_EPTP_HI
    | VMCS_GUEST_PHYSICAL_ADDRESS
    | VMCS_LINK_POINTER
    | VMCS_GUEST_IA32_DEBUGCTL
    | VMCS_GUEST_IA32_PAT
    | VMCS_GUEST_IA32_EFER
    | VMCS_GUEST_IA32_PERF_GLOBAL_CTRL 
    | VMCS_GUEST_PDPTE0
    | VMCS_GUEST_PDPTE1
    | VMCS_GUEST_PDPTE2
    | VMCS_GUEST_PDPTE3
    | VMCS_HOST_IA32_PAT
    | VMCS_HOST_IA32_EFER
    | VMCS_HOST_IA32_PERF_GLOBAL_CTRL
    | VMCS_PIN_BASED_CTLS
    | VMCS_PRI_PROC_BASED_CTLS
    | VMCS_EXCEPTION_BITMAP
    | VMCS_PF_ERROR_MASK
    | VMCS_PF_ERROR_MATCH
    | VMCS_CR3_TARGET_COUNT
    | VMCS_EXIT_CTLS
    | VMCS_EXIT_MSR_STORE_COUNT
    | VMCS_EXIT_MSR_LOAD_COUNT
    | VMCS_ENTRY_CTLS
    | VMCS_ENTRY_MSR_LOAD_COUNT
    | VMCS_ENTRY_INTR_INFO
    | VMCS_ENTRY_EXCEPTION_ERROR
    | VMCS_ENTRY_INST_LENGTH
    | VMCS_TPR_THRESHOLD
    | VMCS_SEC_PROC_BASED_CTLS
    | VMCS_PLE_GAP
    | VMCS_PLE_WINDOW
    | VMCS_INSTRUCTION_ERROR
    | VMCS_EXIT_REASON
    | VMCS_EXIT_INTERRUPTION_INFO
    | VMCS_EXIT_INTERRUPTION_ERROR
    | VMCS_IDT_VECTORING_INFO
    | VMCS_IDT_VECTORING_ERROR
    | VMCS_EXIT_INSTRUCTION_LENGTH
    | VMCS_EXIT_INSTRUCTION_INFO
    | VMCS_GUEST_ES_LIMIT
    | VMCS_GUEST_CS_LIMIT
    | VMCS_GUEST_SS_LIMIT
    | VMCS_GUEST_DS_LIMIT
    | VMCS_GUEST_FS_LIMIT
    | VMCS_GUEST_GS_LIMIT
    | VMCS_GUEST_LDTR_LIMIT
    | VMCS_GUEST_TR_LIMIT
    | VMCS_GUEST_GDTR_LIMIT
    | VMCS_GUEST_IDTR_LIMIT
    | VMCS_GUEST_ES_ACCESS_RIGHTS
    | VMCS_GUEST_CS_ACCESS_RIGHTS
    | VMCS_GUEST_SS_ACCESS_RIGHTS
    | VMCS_GUEST_DS_ACCESS_RIGHTS
    | VMCS_GUEST_FS_ACCESS_RIGHTS
    | VMCS_GUEST_GS_ACCESS_RIGHTS
    | VMCS_GUEST_LDTR_ACCESS_RIGHTS
    | VMCS_GUEST_TR_ACCESS_RIGHTS
    | VMCS_GUEST_INTERRUPTIBILITY
    | VMCS_GUEST_ACTIVITY
    | VMCS_GUEST_SMBASE
    | VMCS_GUEST_IA32_SYSENTER_CS
    | VMCS_PREEMPTION_TIMER_VALUE
    | VMCS_HOST_IA32_SYSENTER_CS
    | VMCS_CR0_MASK
    | VMCS_CR4_MASK
    | VMCS_CR0_SHADOW
    | VMCS_CR4_SHADOW
    | VMCS_CR3_TARGET0
    | VMCS_CR3_TARGET1
    | VMCS_CR3_TARGET2
    | VMCS_CR3_TARGET3
    | VMCS_EXIT_QUALIFICATION
    | VMCS_IO_RCX
    | VMCS_IO_RSI
    | VMCS_IO_RDI
    | VMCS_IO_RIP
    | VMCS_GUEST_LINEAR_ADDRESS
    | VMCS_GUEST_CR0
    | VMCS_GUEST_CR3
    | VMCS_GUEST_CR4
    | VMCS_GUEST_ES_BASE
    | VMCS_GUEST_CS_BASE
    | VMCS_GUEST_SS_BASE
    | VMCS_GUEST_DS_BASE
    | VMCS_GUEST_FS_BASE
    | VMCS_GUEST_GS_BASE
    | VMCS_GUEST_LDTR_BASE
    | VMCS_GUEST_TR_BASE
    | VMCS_GUEST_GDTR_BASE
    | VMCS_GUEST_IDTR_BASE
    | VMCS_GUEST_DR7
    | VMCS_GUEST_RSP
    | VMCS_GUEST_RIP
    | VMCS_GUEST_RFLAGS
    | VMCS_GUEST_PENDING_DBG_EXCEPTIONS
    | VMCS_GUEST_IA32_SYSENTER_ESP
    | VMCS_GUEST_IA32_SYSENTER_EIP
    | VMCS_HOST_CR0
    | VMCS_HOST_CR3
    | VMCS_HOST_CR4
    | VMCS_HOST_FS_BASE
    | VMCS_HOST_GS_BASE
    | VMCS_HOST_TR_BASE
    | VMCS_HOST_GDTR_BASE
    | VMCS_HOST_IDTR_BASE
    | VMCS_HOST_IA32_SYSENTER_ESP
    | VMCS_HOST_IA32_SYSENTER_EIP
    | VMCS_HOST_RSP
    | VMCS_HOST_RIP.
    
    Function vmcs_ZtoEncoding (z:Z) : option VMCS_Encoding :=
      match z with
        | C_VMCS_VPID => Some VMCS_VPID
        | C_VMCS_GUEST_ES_SELECTOR => Some VMCS_GUEST_ES_SELECTOR
        | C_VMCS_GUEST_CS_SELECTOR => Some VMCS_GUEST_CS_SELECTOR
        | C_VMCS_GUEST_SS_SELECTOR => Some VMCS_GUEST_SS_SELECTOR
        | C_VMCS_GUEST_DS_SELECTOR => Some VMCS_GUEST_DS_SELECTOR
        | C_VMCS_GUEST_FS_SELECTOR => Some VMCS_GUEST_FS_SELECTOR
        | C_VMCS_GUEST_GS_SELECTOR => Some VMCS_GUEST_GS_SELECTOR
        | C_VMCS_GUEST_LDTR_SELECTOR => Some VMCS_GUEST_LDTR_SELECTOR
        | C_VMCS_GUEST_TR_SELECTOR => Some VMCS_GUEST_TR_SELECTOR
        | C_VMCS_HOST_ES_SELECTOR => Some VMCS_HOST_ES_SELECTOR
        | C_VMCS_HOST_CS_SELECTOR => Some VMCS_HOST_CS_SELECTOR
        | C_VMCS_HOST_SS_SELECTOR => Some VMCS_HOST_SS_SELECTOR
        | C_VMCS_HOST_DS_SELECTOR => Some VMCS_HOST_DS_SELECTOR
        | C_VMCS_HOST_FS_SELECTOR => Some VMCS_HOST_FS_SELECTOR
        | C_VMCS_HOST_GS_SELECTOR => Some VMCS_HOST_GS_SELECTOR
        | C_VMCS_HOST_TR_SELECTOR => Some VMCS_HOST_TR_SELECTOR
        | C_VMCS_IO_BITMAP_A => Some VMCS_IO_BITMAP_A
        | C_VMCS_IO_BITMAP_A_HI => Some VMCS_IO_BITMAP_A_HI
        | C_VMCS_IO_BITMAP_B => Some VMCS_IO_BITMAP_B
        | C_VMCS_IO_BITMAP_B_HI => Some VMCS_IO_BITMAP_B_HI
        | C_VMCS_MSR_BITMAP => Some VMCS_MSR_BITMAP
        | C_VMCS_MSR_BITMAP_HI => Some VMCS_MSR_BITMAP_HI
        | C_VMCS_EXIT_MSR_STORE => Some VMCS_EXIT_MSR_STORE
        | C_VMCS_EXIT_MSR_LOAD => Some VMCS_EXIT_MSR_LOAD
        | C_VMCS_ENTRY_MSR_LOAD => Some VMCS_ENTRY_MSR_LOAD
        | C_VMCS_EXECUTIVE_VMCS => Some VMCS_EXECUTIVE_VMCS
        | C_VMCS_TSC_OFFSET => Some VMCS_TSC_OFFSET
        | C_VMCS_VIRTUAL_APIC => Some VMCS_VIRTUAL_APIC
        | C_VMCS_APIC_ACCESS => Some VMCS_APIC_ACCESS
        | C_VMCS_EPTP => Some VMCS_EPTP
        | C_VMCS_EPTP_HI => Some VMCS_EPTP_HI
        | C_VMCS_GUEST_PHYSICAL_ADDRESS => Some VMCS_GUEST_PHYSICAL_ADDRESS
        | C_VMCS_LINK_POINTER => Some VMCS_LINK_POINTER
        | C_VMCS_GUEST_IA32_DEBUGCTL => Some VMCS_GUEST_IA32_DEBUGCTL
        | C_VMCS_GUEST_IA32_PAT => Some VMCS_GUEST_IA32_PAT
        | C_VMCS_GUEST_IA32_EFER => Some VMCS_GUEST_IA32_EFER
        | C_VMCS_GUEST_IA32_PERF_GLOBAL_CTRL  => Some VMCS_GUEST_IA32_PERF_GLOBAL_CTRL 
        | C_VMCS_GUEST_PDPTE0 => Some VMCS_GUEST_PDPTE0
        | C_VMCS_GUEST_PDPTE1 => Some VMCS_GUEST_PDPTE1
        | C_VMCS_GUEST_PDPTE2 => Some VMCS_GUEST_PDPTE2
        | C_VMCS_GUEST_PDPTE3 => Some VMCS_GUEST_PDPTE3
        | C_VMCS_HOST_IA32_PAT => Some VMCS_HOST_IA32_PAT
        | C_VMCS_HOST_IA32_EFER => Some VMCS_HOST_IA32_EFER
        | C_VMCS_HOST_IA32_PERF_GLOBAL_CTRL => Some VMCS_HOST_IA32_PERF_GLOBAL_CTRL
        | C_VMCS_PIN_BASED_CTLS => Some VMCS_PIN_BASED_CTLS
        | C_VMCS_PRI_PROC_BASED_CTLS => Some VMCS_PRI_PROC_BASED_CTLS
        | C_VMCS_EXCEPTION_BITMAP => Some VMCS_EXCEPTION_BITMAP
        | C_VMCS_PF_ERROR_MASK => Some VMCS_PF_ERROR_MASK
        | C_VMCS_PF_ERROR_MATCH => Some VMCS_PF_ERROR_MATCH
        | C_VMCS_CR3_TARGET_COUNT => Some VMCS_CR3_TARGET_COUNT
        | C_VMCS_EXIT_CTLS => Some VMCS_EXIT_CTLS
        | C_VMCS_EXIT_MSR_STORE_COUNT => Some VMCS_EXIT_MSR_STORE_COUNT
        | C_VMCS_EXIT_MSR_LOAD_COUNT => Some VMCS_EXIT_MSR_LOAD_COUNT
        | C_VMCS_ENTRY_CTLS => Some VMCS_ENTRY_CTLS
        | C_VMCS_ENTRY_MSR_LOAD_COUNT => Some VMCS_ENTRY_MSR_LOAD_COUNT
        | C_VMCS_ENTRY_INTR_INFO => Some VMCS_ENTRY_INTR_INFO
        | C_VMCS_ENTRY_EXCEPTION_ERROR => Some VMCS_ENTRY_EXCEPTION_ERROR
        | C_VMCS_ENTRY_INST_LENGTH => Some VMCS_ENTRY_INST_LENGTH
        | C_VMCS_TPR_THRESHOLD => Some VMCS_TPR_THRESHOLD
        | C_VMCS_SEC_PROC_BASED_CTLS => Some VMCS_SEC_PROC_BASED_CTLS
        | C_VMCS_PLE_GAP => Some VMCS_PLE_GAP
        | C_VMCS_PLE_WINDOW => Some VMCS_PLE_WINDOW
        | C_VMCS_INSTRUCTION_ERROR => Some VMCS_INSTRUCTION_ERROR
        | C_VMCS_EXIT_REASON => Some VMCS_EXIT_REASON
        | C_VMCS_EXIT_INTERRUPTION_INFO => Some VMCS_EXIT_INTERRUPTION_INFO
        | C_VMCS_EXIT_INTERRUPTION_ERROR => Some VMCS_EXIT_INTERRUPTION_ERROR
        | C_VMCS_IDT_VECTORING_INFO => Some VMCS_IDT_VECTORING_INFO
        | C_VMCS_IDT_VECTORING_ERROR => Some VMCS_IDT_VECTORING_ERROR
        | C_VMCS_EXIT_INSTRUCTION_LENGTH => Some VMCS_EXIT_INSTRUCTION_LENGTH
        | C_VMCS_EXIT_INSTRUCTION_INFO => Some VMCS_EXIT_INSTRUCTION_INFO
        | C_VMCS_GUEST_ES_LIMIT => Some VMCS_GUEST_ES_LIMIT
        | C_VMCS_GUEST_CS_LIMIT => Some VMCS_GUEST_CS_LIMIT
        | C_VMCS_GUEST_SS_LIMIT => Some VMCS_GUEST_SS_LIMIT
        | C_VMCS_GUEST_DS_LIMIT => Some VMCS_GUEST_DS_LIMIT
        | C_VMCS_GUEST_FS_LIMIT => Some VMCS_GUEST_FS_LIMIT
        | C_VMCS_GUEST_GS_LIMIT => Some VMCS_GUEST_GS_LIMIT
        | C_VMCS_GUEST_LDTR_LIMIT => Some VMCS_GUEST_LDTR_LIMIT
        | C_VMCS_GUEST_TR_LIMIT => Some VMCS_GUEST_TR_LIMIT
        | C_VMCS_GUEST_GDTR_LIMIT => Some VMCS_GUEST_GDTR_LIMIT
        | C_VMCS_GUEST_IDTR_LIMIT => Some VMCS_GUEST_IDTR_LIMIT
        | C_VMCS_GUEST_ES_ACCESS_RIGHTS => Some VMCS_GUEST_ES_ACCESS_RIGHTS
        | C_VMCS_GUEST_CS_ACCESS_RIGHTS => Some VMCS_GUEST_CS_ACCESS_RIGHTS
        | C_VMCS_GUEST_SS_ACCESS_RIGHTS => Some VMCS_GUEST_SS_ACCESS_RIGHTS
        | C_VMCS_GUEST_DS_ACCESS_RIGHTS => Some VMCS_GUEST_DS_ACCESS_RIGHTS
        | C_VMCS_GUEST_FS_ACCESS_RIGHTS => Some VMCS_GUEST_FS_ACCESS_RIGHTS
        | C_VMCS_GUEST_GS_ACCESS_RIGHTS => Some VMCS_GUEST_GS_ACCESS_RIGHTS
        | C_VMCS_GUEST_LDTR_ACCESS_RIGHTS => Some VMCS_GUEST_LDTR_ACCESS_RIGHTS
        | C_VMCS_GUEST_TR_ACCESS_RIGHTS => Some VMCS_GUEST_TR_ACCESS_RIGHTS
        | C_VMCS_GUEST_INTERRUPTIBILITY => Some VMCS_GUEST_INTERRUPTIBILITY
        | C_VMCS_GUEST_ACTIVITY => Some VMCS_GUEST_ACTIVITY
        | C_VMCS_GUEST_SMBASE => Some VMCS_GUEST_SMBASE
        | C_VMCS_GUEST_IA32_SYSENTER_CS => Some VMCS_GUEST_IA32_SYSENTER_CS
        | C_VMCS_PREEMPTION_TIMER_VALUE => Some VMCS_PREEMPTION_TIMER_VALUE
        | C_VMCS_HOST_IA32_SYSENTER_CS => Some VMCS_HOST_IA32_SYSENTER_CS
        | C_VMCS_CR0_MASK => Some VMCS_CR0_MASK
        | C_VMCS_CR4_MASK => Some VMCS_CR4_MASK
        | C_VMCS_CR0_SHADOW => Some VMCS_CR0_SHADOW
        | C_VMCS_CR4_SHADOW => Some VMCS_CR4_SHADOW
        | C_VMCS_CR3_TARGET0 => Some VMCS_CR3_TARGET0
        | C_VMCS_CR3_TARGET1 => Some VMCS_CR3_TARGET1
        | C_VMCS_CR3_TARGET2 => Some VMCS_CR3_TARGET2
        | C_VMCS_CR3_TARGET3 => Some VMCS_CR3_TARGET3
        | C_VMCS_EXIT_QUALIFICATION => Some VMCS_EXIT_QUALIFICATION
        | C_VMCS_IO_RCX => Some VMCS_IO_RCX
        | C_VMCS_IO_RSI => Some VMCS_IO_RSI
        | C_VMCS_IO_RDI => Some VMCS_IO_RDI
        | C_VMCS_IO_RIP => Some VMCS_IO_RIP
        | C_VMCS_GUEST_LINEAR_ADDRESS => Some VMCS_GUEST_LINEAR_ADDRESS
        | C_VMCS_GUEST_CR0 => Some VMCS_GUEST_CR0
        | C_VMCS_GUEST_CR3 => Some VMCS_GUEST_CR3
        | C_VMCS_GUEST_CR4 => Some VMCS_GUEST_CR4
        | C_VMCS_GUEST_ES_BASE => Some VMCS_GUEST_ES_BASE
        | C_VMCS_GUEST_CS_BASE => Some VMCS_GUEST_CS_BASE
        | C_VMCS_GUEST_SS_BASE => Some VMCS_GUEST_SS_BASE
        | C_VMCS_GUEST_DS_BASE => Some VMCS_GUEST_DS_BASE
        | C_VMCS_GUEST_FS_BASE => Some VMCS_GUEST_FS_BASE
        | C_VMCS_GUEST_GS_BASE => Some VMCS_GUEST_GS_BASE
        | C_VMCS_GUEST_LDTR_BASE => Some VMCS_GUEST_LDTR_BASE
        | C_VMCS_GUEST_TR_BASE => Some VMCS_GUEST_TR_BASE
        | C_VMCS_GUEST_GDTR_BASE => Some VMCS_GUEST_GDTR_BASE
        | C_VMCS_GUEST_IDTR_BASE => Some VMCS_GUEST_IDTR_BASE
        | C_VMCS_GUEST_DR7 => Some VMCS_GUEST_DR7
        | C_VMCS_GUEST_RSP => Some VMCS_GUEST_RSP
        | C_VMCS_GUEST_RIP => Some VMCS_GUEST_RIP
        | C_VMCS_GUEST_RFLAGS => Some VMCS_GUEST_RFLAGS
        | C_VMCS_GUEST_PENDING_DBG_EXCEPTIONS => Some VMCS_GUEST_PENDING_DBG_EXCEPTIONS
        | C_VMCS_GUEST_IA32_SYSENTER_ESP => Some VMCS_GUEST_IA32_SYSENTER_ESP
        | C_VMCS_GUEST_IA32_SYSENTER_EIP => Some VMCS_GUEST_IA32_SYSENTER_EIP
        | C_VMCS_HOST_CR0 => Some VMCS_HOST_CR0
        | C_VMCS_HOST_CR3 => Some VMCS_HOST_CR3
        | C_VMCS_HOST_CR4 => Some VMCS_HOST_CR4
        | C_VMCS_HOST_FS_BASE => Some VMCS_HOST_FS_BASE
        | C_VMCS_HOST_GS_BASE => Some VMCS_HOST_GS_BASE
        | C_VMCS_HOST_TR_BASE => Some VMCS_HOST_TR_BASE
        | C_VMCS_HOST_GDTR_BASE => Some VMCS_HOST_GDTR_BASE
        | C_VMCS_HOST_IDTR_BASE => Some VMCS_HOST_IDTR_BASE
        | C_VMCS_HOST_IA32_SYSENTER_ESP => Some VMCS_HOST_IA32_SYSENTER_ESP
        | C_VMCS_HOST_IA32_SYSENTER_EIP => Some VMCS_HOST_IA32_SYSENTER_EIP
        | C_VMCS_HOST_RSP => Some VMCS_HOST_RSP
        | C_VMCS_HOST_RIP => Some VMCS_HOST_RIP
        | _ => None
      end.
 
    Definition vmcs_EncodingtoZ (e: VMCS_Encoding) : Z :=
      match e with
        | VMCS_VPID => C_VMCS_VPID
        | VMCS_GUEST_ES_SELECTOR => C_VMCS_GUEST_ES_SELECTOR
        | VMCS_GUEST_CS_SELECTOR => C_VMCS_GUEST_CS_SELECTOR
        | VMCS_GUEST_SS_SELECTOR => C_VMCS_GUEST_SS_SELECTOR
        | VMCS_GUEST_DS_SELECTOR => C_VMCS_GUEST_DS_SELECTOR
        | VMCS_GUEST_FS_SELECTOR => C_VMCS_GUEST_FS_SELECTOR
        | VMCS_GUEST_GS_SELECTOR => C_VMCS_GUEST_GS_SELECTOR
        | VMCS_GUEST_LDTR_SELECTOR => C_VMCS_GUEST_LDTR_SELECTOR
        | VMCS_GUEST_TR_SELECTOR => C_VMCS_GUEST_TR_SELECTOR
        | VMCS_HOST_ES_SELECTOR => C_VMCS_HOST_ES_SELECTOR
        | VMCS_HOST_CS_SELECTOR => C_VMCS_HOST_CS_SELECTOR
        | VMCS_HOST_SS_SELECTOR => C_VMCS_HOST_SS_SELECTOR
        | VMCS_HOST_DS_SELECTOR => C_VMCS_HOST_DS_SELECTOR
        | VMCS_HOST_FS_SELECTOR => C_VMCS_HOST_FS_SELECTOR
        | VMCS_HOST_GS_SELECTOR => C_VMCS_HOST_GS_SELECTOR
        | VMCS_HOST_TR_SELECTOR => C_VMCS_HOST_TR_SELECTOR
        | VMCS_IO_BITMAP_A => C_VMCS_IO_BITMAP_A
        | VMCS_IO_BITMAP_A_HI => C_VMCS_IO_BITMAP_A_HI
        | VMCS_IO_BITMAP_B => C_VMCS_IO_BITMAP_B
        | VMCS_IO_BITMAP_B_HI => C_VMCS_IO_BITMAP_B_HI
        | VMCS_MSR_BITMAP => C_VMCS_MSR_BITMAP
        | VMCS_MSR_BITMAP_HI => C_VMCS_MSR_BITMAP_HI
        | VMCS_EXIT_MSR_STORE => C_VMCS_EXIT_MSR_STORE
        | VMCS_EXIT_MSR_LOAD => C_VMCS_EXIT_MSR_LOAD
        | VMCS_ENTRY_MSR_LOAD => C_VMCS_ENTRY_MSR_LOAD
        | VMCS_EXECUTIVE_VMCS => C_VMCS_EXECUTIVE_VMCS
        | VMCS_TSC_OFFSET => C_VMCS_TSC_OFFSET
        | VMCS_VIRTUAL_APIC => C_VMCS_VIRTUAL_APIC
        | VMCS_APIC_ACCESS => C_VMCS_APIC_ACCESS
        | VMCS_EPTP => C_VMCS_EPTP
        | VMCS_EPTP_HI => C_VMCS_EPTP_HI
        | VMCS_GUEST_PHYSICAL_ADDRESS => C_VMCS_GUEST_PHYSICAL_ADDRESS
        | VMCS_LINK_POINTER => C_VMCS_LINK_POINTER
        | VMCS_GUEST_IA32_DEBUGCTL => C_VMCS_GUEST_IA32_DEBUGCTL
        | VMCS_GUEST_IA32_PAT => C_VMCS_GUEST_IA32_PAT
        | VMCS_GUEST_IA32_EFER => C_VMCS_GUEST_IA32_EFER
        | VMCS_GUEST_IA32_PERF_GLOBAL_CTRL  => C_VMCS_GUEST_IA32_PERF_GLOBAL_CTRL 
        | VMCS_GUEST_PDPTE0 => C_VMCS_GUEST_PDPTE0
        | VMCS_GUEST_PDPTE1 => C_VMCS_GUEST_PDPTE1
        | VMCS_GUEST_PDPTE2 => C_VMCS_GUEST_PDPTE2
        | VMCS_GUEST_PDPTE3 => C_VMCS_GUEST_PDPTE3
        | VMCS_HOST_IA32_PAT => C_VMCS_HOST_IA32_PAT
        | VMCS_HOST_IA32_EFER => C_VMCS_HOST_IA32_EFER
        | VMCS_HOST_IA32_PERF_GLOBAL_CTRL => C_VMCS_HOST_IA32_PERF_GLOBAL_CTRL
        | VMCS_PIN_BASED_CTLS => C_VMCS_PIN_BASED_CTLS
        | VMCS_PRI_PROC_BASED_CTLS => C_VMCS_PRI_PROC_BASED_CTLS
        | VMCS_EXCEPTION_BITMAP => C_VMCS_EXCEPTION_BITMAP
        | VMCS_PF_ERROR_MASK => C_VMCS_PF_ERROR_MASK
        | VMCS_PF_ERROR_MATCH => C_VMCS_PF_ERROR_MATCH
        | VMCS_CR3_TARGET_COUNT => C_VMCS_CR3_TARGET_COUNT
        | VMCS_EXIT_CTLS => C_VMCS_EXIT_CTLS
        | VMCS_EXIT_MSR_STORE_COUNT => C_VMCS_EXIT_MSR_STORE_COUNT
        | VMCS_EXIT_MSR_LOAD_COUNT => C_VMCS_EXIT_MSR_LOAD_COUNT
        | VMCS_ENTRY_CTLS => C_VMCS_ENTRY_CTLS
        | VMCS_ENTRY_MSR_LOAD_COUNT => C_VMCS_ENTRY_MSR_LOAD_COUNT
        | VMCS_ENTRY_INTR_INFO => C_VMCS_ENTRY_INTR_INFO
        | VMCS_ENTRY_EXCEPTION_ERROR => C_VMCS_ENTRY_EXCEPTION_ERROR
        | VMCS_ENTRY_INST_LENGTH => C_VMCS_ENTRY_INST_LENGTH
        | VMCS_TPR_THRESHOLD => C_VMCS_TPR_THRESHOLD
        | VMCS_SEC_PROC_BASED_CTLS => C_VMCS_SEC_PROC_BASED_CTLS
        | VMCS_PLE_GAP => C_VMCS_PLE_GAP
        | VMCS_PLE_WINDOW => C_VMCS_PLE_WINDOW
        | VMCS_INSTRUCTION_ERROR => C_VMCS_INSTRUCTION_ERROR
        | VMCS_EXIT_REASON => C_VMCS_EXIT_REASON
        | VMCS_EXIT_INTERRUPTION_INFO => C_VMCS_EXIT_INTERRUPTION_INFO
        | VMCS_EXIT_INTERRUPTION_ERROR => C_VMCS_EXIT_INTERRUPTION_ERROR
        | VMCS_IDT_VECTORING_INFO => C_VMCS_IDT_VECTORING_INFO
        | VMCS_IDT_VECTORING_ERROR => C_VMCS_IDT_VECTORING_ERROR
        | VMCS_EXIT_INSTRUCTION_LENGTH => C_VMCS_EXIT_INSTRUCTION_LENGTH
        | VMCS_EXIT_INSTRUCTION_INFO => C_VMCS_EXIT_INSTRUCTION_INFO
        | VMCS_GUEST_ES_LIMIT => C_VMCS_GUEST_ES_LIMIT
        | VMCS_GUEST_CS_LIMIT => C_VMCS_GUEST_CS_LIMIT
        | VMCS_GUEST_SS_LIMIT => C_VMCS_GUEST_SS_LIMIT
        | VMCS_GUEST_DS_LIMIT => C_VMCS_GUEST_DS_LIMIT
        | VMCS_GUEST_FS_LIMIT => C_VMCS_GUEST_FS_LIMIT
        | VMCS_GUEST_GS_LIMIT => C_VMCS_GUEST_GS_LIMIT
        | VMCS_GUEST_LDTR_LIMIT => C_VMCS_GUEST_LDTR_LIMIT
        | VMCS_GUEST_TR_LIMIT => C_VMCS_GUEST_TR_LIMIT
        | VMCS_GUEST_GDTR_LIMIT => C_VMCS_GUEST_GDTR_LIMIT
        | VMCS_GUEST_IDTR_LIMIT => C_VMCS_GUEST_IDTR_LIMIT
        | VMCS_GUEST_ES_ACCESS_RIGHTS => C_VMCS_GUEST_ES_ACCESS_RIGHTS
        | VMCS_GUEST_CS_ACCESS_RIGHTS => C_VMCS_GUEST_CS_ACCESS_RIGHTS
        | VMCS_GUEST_SS_ACCESS_RIGHTS => C_VMCS_GUEST_SS_ACCESS_RIGHTS
        | VMCS_GUEST_DS_ACCESS_RIGHTS => C_VMCS_GUEST_DS_ACCESS_RIGHTS
        | VMCS_GUEST_FS_ACCESS_RIGHTS => C_VMCS_GUEST_FS_ACCESS_RIGHTS
        | VMCS_GUEST_GS_ACCESS_RIGHTS => C_VMCS_GUEST_GS_ACCESS_RIGHTS
        | VMCS_GUEST_LDTR_ACCESS_RIGHTS => C_VMCS_GUEST_LDTR_ACCESS_RIGHTS
        | VMCS_GUEST_TR_ACCESS_RIGHTS => C_VMCS_GUEST_TR_ACCESS_RIGHTS
        | VMCS_GUEST_INTERRUPTIBILITY => C_VMCS_GUEST_INTERRUPTIBILITY
        | VMCS_GUEST_ACTIVITY => C_VMCS_GUEST_ACTIVITY
        | VMCS_GUEST_SMBASE => C_VMCS_GUEST_SMBASE
        | VMCS_GUEST_IA32_SYSENTER_CS => C_VMCS_GUEST_IA32_SYSENTER_CS
        | VMCS_PREEMPTION_TIMER_VALUE => C_VMCS_PREEMPTION_TIMER_VALUE
        | VMCS_HOST_IA32_SYSENTER_CS => C_VMCS_HOST_IA32_SYSENTER_CS
        | VMCS_CR0_MASK => C_VMCS_CR0_MASK
        | VMCS_CR4_MASK => C_VMCS_CR4_MASK
        | VMCS_CR0_SHADOW => C_VMCS_CR0_SHADOW
        | VMCS_CR4_SHADOW => C_VMCS_CR4_SHADOW
        | VMCS_CR3_TARGET0 => C_VMCS_CR3_TARGET0
        | VMCS_CR3_TARGET1 => C_VMCS_CR3_TARGET1
        | VMCS_CR3_TARGET2 => C_VMCS_CR3_TARGET2
        | VMCS_CR3_TARGET3 => C_VMCS_CR3_TARGET3
        | VMCS_EXIT_QUALIFICATION => C_VMCS_EXIT_QUALIFICATION
        | VMCS_IO_RCX => C_VMCS_IO_RCX
        | VMCS_IO_RSI => C_VMCS_IO_RSI
        | VMCS_IO_RDI => C_VMCS_IO_RDI
        | VMCS_IO_RIP => C_VMCS_IO_RIP
        | VMCS_GUEST_LINEAR_ADDRESS => C_VMCS_GUEST_LINEAR_ADDRESS
        | VMCS_GUEST_CR0 => C_VMCS_GUEST_CR0
        | VMCS_GUEST_CR3 => C_VMCS_GUEST_CR3
        | VMCS_GUEST_CR4 => C_VMCS_GUEST_CR4
        | VMCS_GUEST_ES_BASE => C_VMCS_GUEST_ES_BASE
        | VMCS_GUEST_CS_BASE => C_VMCS_GUEST_CS_BASE
        | VMCS_GUEST_SS_BASE => C_VMCS_GUEST_SS_BASE
        | VMCS_GUEST_DS_BASE => C_VMCS_GUEST_DS_BASE
        | VMCS_GUEST_FS_BASE => C_VMCS_GUEST_FS_BASE
        | VMCS_GUEST_GS_BASE => C_VMCS_GUEST_GS_BASE
        | VMCS_GUEST_LDTR_BASE => C_VMCS_GUEST_LDTR_BASE
        | VMCS_GUEST_TR_BASE => C_VMCS_GUEST_TR_BASE
        | VMCS_GUEST_GDTR_BASE => C_VMCS_GUEST_GDTR_BASE
        | VMCS_GUEST_IDTR_BASE => C_VMCS_GUEST_IDTR_BASE
        | VMCS_GUEST_DR7 => C_VMCS_GUEST_DR7
        | VMCS_GUEST_RSP => C_VMCS_GUEST_RSP
        | VMCS_GUEST_RIP => C_VMCS_GUEST_RIP
        | VMCS_GUEST_RFLAGS => C_VMCS_GUEST_RFLAGS
        | VMCS_GUEST_PENDING_DBG_EXCEPTIONS => C_VMCS_GUEST_PENDING_DBG_EXCEPTIONS
        | VMCS_GUEST_IA32_SYSENTER_ESP => C_VMCS_GUEST_IA32_SYSENTER_ESP
        | VMCS_GUEST_IA32_SYSENTER_EIP => C_VMCS_GUEST_IA32_SYSENTER_EIP
        | VMCS_HOST_CR0 => C_VMCS_HOST_CR0
        | VMCS_HOST_CR3 => C_VMCS_HOST_CR3
        | VMCS_HOST_CR4 => C_VMCS_HOST_CR4
        | VMCS_HOST_FS_BASE => C_VMCS_HOST_FS_BASE
        | VMCS_HOST_GS_BASE => C_VMCS_HOST_GS_BASE
        | VMCS_HOST_TR_BASE => C_VMCS_HOST_TR_BASE
        | VMCS_HOST_GDTR_BASE => C_VMCS_HOST_GDTR_BASE
        | VMCS_HOST_IDTR_BASE => C_VMCS_HOST_IDTR_BASE
        | VMCS_HOST_IA32_SYSENTER_ESP => C_VMCS_HOST_IA32_SYSENTER_ESP
        | VMCS_HOST_IA32_SYSENTER_EIP => C_VMCS_HOST_IA32_SYSENTER_EIP
        | VMCS_HOST_RSP => C_VMCS_HOST_RSP
        | VMCS_HOST_RIP => C_VMCS_HOST_RIP
      end.

    Definition vmcs_encoding_beq (a b: VMCS_Encoding): bool :=
      match (a, b) with
        | (VMCS_VPID, VMCS_VPID) => true
        | (VMCS_GUEST_ES_SELECTOR, VMCS_GUEST_ES_SELECTOR) => true
        | (VMCS_GUEST_CS_SELECTOR, VMCS_GUEST_CS_SELECTOR) => true
        | (VMCS_GUEST_SS_SELECTOR, VMCS_GUEST_SS_SELECTOR) => true
        | (VMCS_GUEST_DS_SELECTOR, VMCS_GUEST_DS_SELECTOR) => true
        | (VMCS_GUEST_FS_SELECTOR, VMCS_GUEST_FS_SELECTOR) => true
        | (VMCS_GUEST_GS_SELECTOR, VMCS_GUEST_GS_SELECTOR) => true
        | (VMCS_GUEST_LDTR_SELECTOR, VMCS_GUEST_LDTR_SELECTOR) => true
        | (VMCS_GUEST_TR_SELECTOR, VMCS_GUEST_TR_SELECTOR) => true
        | (VMCS_HOST_ES_SELECTOR, VMCS_HOST_ES_SELECTOR) => true
        | (VMCS_HOST_CS_SELECTOR, VMCS_HOST_CS_SELECTOR) => true
        | (VMCS_HOST_SS_SELECTOR, VMCS_HOST_SS_SELECTOR) => true
        | (VMCS_HOST_DS_SELECTOR, VMCS_HOST_DS_SELECTOR) => true
        | (VMCS_HOST_FS_SELECTOR, VMCS_HOST_FS_SELECTOR) => true
        | (VMCS_HOST_GS_SELECTOR, VMCS_HOST_GS_SELECTOR) => true
        | (VMCS_HOST_TR_SELECTOR, VMCS_HOST_TR_SELECTOR) => true
        | (VMCS_IO_BITMAP_A, VMCS_IO_BITMAP_A) => true
        | (VMCS_IO_BITMAP_A_HI, VMCS_IO_BITMAP_A_HI) => true
        | (VMCS_IO_BITMAP_B, VMCS_IO_BITMAP_B) => true
        | (VMCS_IO_BITMAP_B_HI, VMCS_IO_BITMAP_B_HI) => true
        | (VMCS_MSR_BITMAP, VMCS_MSR_BITMAP) => true
        | (VMCS_MSR_BITMAP_HI, VMCS_MSR_BITMAP_HI) => true
        | (VMCS_EXIT_MSR_STORE, VMCS_EXIT_MSR_STORE) => true
        | (VMCS_EXIT_MSR_LOAD, VMCS_EXIT_MSR_LOAD) => true
        | (VMCS_ENTRY_MSR_LOAD, VMCS_ENTRY_MSR_LOAD) => true
        | (VMCS_EXECUTIVE_VMCS, VMCS_EXECUTIVE_VMCS) => true
        | (VMCS_TSC_OFFSET, VMCS_TSC_OFFSET) => true
        | (VMCS_VIRTUAL_APIC, VMCS_VIRTUAL_APIC) => true
        | (VMCS_APIC_ACCESS, VMCS_APIC_ACCESS) => true
        | (VMCS_EPTP, VMCS_EPTP) => true
        | (VMCS_EPTP_HI, VMCS_EPTP_HI) => true
        | (VMCS_GUEST_PHYSICAL_ADDRESS, VMCS_GUEST_PHYSICAL_ADDRESS) => true
        | (VMCS_LINK_POINTER, VMCS_LINK_POINTER) => true
        | (VMCS_GUEST_IA32_DEBUGCTL, VMCS_GUEST_IA32_DEBUGCTL) => true
        | (VMCS_GUEST_IA32_PAT, VMCS_GUEST_IA32_PAT) => true
        | (VMCS_GUEST_IA32_EFER, VMCS_GUEST_IA32_EFER) => true
        | (VMCS_GUEST_IA32_PERF_GLOBAL_CTRL , VMCS_GUEST_IA32_PERF_GLOBAL_CTRL ) => true
        | (VMCS_GUEST_PDPTE0, VMCS_GUEST_PDPTE0) => true
        | (VMCS_GUEST_PDPTE1, VMCS_GUEST_PDPTE1) => true
        | (VMCS_GUEST_PDPTE2, VMCS_GUEST_PDPTE2) => true
        | (VMCS_GUEST_PDPTE3, VMCS_GUEST_PDPTE3) => true
        | (VMCS_HOST_IA32_PAT, VMCS_HOST_IA32_PAT) => true
        | (VMCS_HOST_IA32_EFER, VMCS_HOST_IA32_EFER) => true
        | (VMCS_HOST_IA32_PERF_GLOBAL_CTRL, VMCS_HOST_IA32_PERF_GLOBAL_CTRL) => true
        | (VMCS_PIN_BASED_CTLS, VMCS_PIN_BASED_CTLS) => true
        | (VMCS_PRI_PROC_BASED_CTLS, VMCS_PRI_PROC_BASED_CTLS) => true
        | (VMCS_EXCEPTION_BITMAP, VMCS_EXCEPTION_BITMAP) => true
        | (VMCS_PF_ERROR_MASK, VMCS_PF_ERROR_MASK) => true
        | (VMCS_PF_ERROR_MATCH, VMCS_PF_ERROR_MATCH) => true
        | (VMCS_CR3_TARGET_COUNT, VMCS_CR3_TARGET_COUNT) => true
        | (VMCS_EXIT_CTLS, VMCS_EXIT_CTLS) => true
        | (VMCS_EXIT_MSR_STORE_COUNT, VMCS_EXIT_MSR_STORE_COUNT) => true
        | (VMCS_EXIT_MSR_LOAD_COUNT, VMCS_EXIT_MSR_LOAD_COUNT) => true
        | (VMCS_ENTRY_CTLS, VMCS_ENTRY_CTLS) => true
        | (VMCS_ENTRY_MSR_LOAD_COUNT, VMCS_ENTRY_MSR_LOAD_COUNT) => true
        | (VMCS_ENTRY_INTR_INFO, VMCS_ENTRY_INTR_INFO) => true
        | (VMCS_ENTRY_EXCEPTION_ERROR, VMCS_ENTRY_EXCEPTION_ERROR) => true
        | (VMCS_ENTRY_INST_LENGTH, VMCS_ENTRY_INST_LENGTH) => true
        | (VMCS_TPR_THRESHOLD, VMCS_TPR_THRESHOLD) => true
        | (VMCS_SEC_PROC_BASED_CTLS, VMCS_SEC_PROC_BASED_CTLS) => true
        | (VMCS_PLE_GAP, VMCS_PLE_GAP) => true
        | (VMCS_PLE_WINDOW, VMCS_PLE_WINDOW) => true
        | (VMCS_INSTRUCTION_ERROR, VMCS_INSTRUCTION_ERROR) => true
        | (VMCS_EXIT_REASON, VMCS_EXIT_REASON) => true
        | (VMCS_EXIT_INTERRUPTION_INFO, VMCS_EXIT_INTERRUPTION_INFO) => true
        | (VMCS_EXIT_INTERRUPTION_ERROR, VMCS_EXIT_INTERRUPTION_ERROR) => true
        | (VMCS_IDT_VECTORING_INFO, VMCS_IDT_VECTORING_INFO) => true
        | (VMCS_IDT_VECTORING_ERROR, VMCS_IDT_VECTORING_ERROR) => true
        | (VMCS_EXIT_INSTRUCTION_LENGTH, VMCS_EXIT_INSTRUCTION_LENGTH) => true
        | (VMCS_EXIT_INSTRUCTION_INFO, VMCS_EXIT_INSTRUCTION_INFO) => true
        | (VMCS_GUEST_ES_LIMIT, VMCS_GUEST_ES_LIMIT) => true
        | (VMCS_GUEST_CS_LIMIT, VMCS_GUEST_CS_LIMIT) => true
        | (VMCS_GUEST_SS_LIMIT, VMCS_GUEST_SS_LIMIT) => true
        | (VMCS_GUEST_DS_LIMIT, VMCS_GUEST_DS_LIMIT) => true
        | (VMCS_GUEST_FS_LIMIT, VMCS_GUEST_FS_LIMIT) => true
        | (VMCS_GUEST_GS_LIMIT, VMCS_GUEST_GS_LIMIT) => true
        | (VMCS_GUEST_LDTR_LIMIT, VMCS_GUEST_LDTR_LIMIT) => true
        | (VMCS_GUEST_TR_LIMIT, VMCS_GUEST_TR_LIMIT) => true
        | (VMCS_GUEST_GDTR_LIMIT, VMCS_GUEST_GDTR_LIMIT) => true
        | (VMCS_GUEST_IDTR_LIMIT, VMCS_GUEST_IDTR_LIMIT) => true
        | (VMCS_GUEST_ES_ACCESS_RIGHTS, VMCS_GUEST_ES_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_CS_ACCESS_RIGHTS, VMCS_GUEST_CS_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_SS_ACCESS_RIGHTS, VMCS_GUEST_SS_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_DS_ACCESS_RIGHTS, VMCS_GUEST_DS_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_FS_ACCESS_RIGHTS, VMCS_GUEST_FS_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_GS_ACCESS_RIGHTS, VMCS_GUEST_GS_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_LDTR_ACCESS_RIGHTS, VMCS_GUEST_LDTR_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_TR_ACCESS_RIGHTS, VMCS_GUEST_TR_ACCESS_RIGHTS) => true
        | (VMCS_GUEST_INTERRUPTIBILITY, VMCS_GUEST_INTERRUPTIBILITY) => true
        | (VMCS_GUEST_ACTIVITY, VMCS_GUEST_ACTIVITY) => true
        | (VMCS_GUEST_SMBASE, VMCS_GUEST_SMBASE) => true
        | (VMCS_GUEST_IA32_SYSENTER_CS, VMCS_GUEST_IA32_SYSENTER_CS) => true
        | (VMCS_PREEMPTION_TIMER_VALUE, VMCS_PREEMPTION_TIMER_VALUE) => true
        | (VMCS_HOST_IA32_SYSENTER_CS, VMCS_HOST_IA32_SYSENTER_CS) => true
        | (VMCS_CR0_MASK, VMCS_CR0_MASK) => true
        | (VMCS_CR4_MASK, VMCS_CR4_MASK) => true
        | (VMCS_CR0_SHADOW, VMCS_CR0_SHADOW) => true
        | (VMCS_CR4_SHADOW, VMCS_CR4_SHADOW) => true
        | (VMCS_CR3_TARGET0, VMCS_CR3_TARGET0) => true
        | (VMCS_CR3_TARGET1, VMCS_CR3_TARGET1) => true
        | (VMCS_CR3_TARGET2, VMCS_CR3_TARGET2) => true
        | (VMCS_CR3_TARGET3, VMCS_CR3_TARGET3) => true
        | (VMCS_EXIT_QUALIFICATION, VMCS_EXIT_QUALIFICATION) => true
        | (VMCS_IO_RCX, VMCS_IO_RCX) => true
        | (VMCS_IO_RSI, VMCS_IO_RSI) => true
        | (VMCS_IO_RDI, VMCS_IO_RDI) => true
        | (VMCS_IO_RIP, VMCS_IO_RIP) => true
        | (VMCS_GUEST_LINEAR_ADDRESS, VMCS_GUEST_LINEAR_ADDRESS) => true
        | (VMCS_GUEST_CR0, VMCS_GUEST_CR0) => true
        | (VMCS_GUEST_CR3, VMCS_GUEST_CR3) => true
        | (VMCS_GUEST_CR4, VMCS_GUEST_CR4) => true
        | (VMCS_GUEST_ES_BASE, VMCS_GUEST_ES_BASE) => true
        | (VMCS_GUEST_CS_BASE, VMCS_GUEST_CS_BASE) => true
        | (VMCS_GUEST_SS_BASE, VMCS_GUEST_SS_BASE) => true
        | (VMCS_GUEST_DS_BASE, VMCS_GUEST_DS_BASE) => true
        | (VMCS_GUEST_FS_BASE, VMCS_GUEST_FS_BASE) => true
        | (VMCS_GUEST_GS_BASE, VMCS_GUEST_GS_BASE) => true
        | (VMCS_GUEST_LDTR_BASE, VMCS_GUEST_LDTR_BASE) => true
        | (VMCS_GUEST_TR_BASE, VMCS_GUEST_TR_BASE) => true
        | (VMCS_GUEST_GDTR_BASE, VMCS_GUEST_GDTR_BASE) => true
        | (VMCS_GUEST_IDTR_BASE, VMCS_GUEST_IDTR_BASE) => true
        | (VMCS_GUEST_DR7, VMCS_GUEST_DR7) => true
        | (VMCS_GUEST_RSP, VMCS_GUEST_RSP) => true
        | (VMCS_GUEST_RIP, VMCS_GUEST_RIP) => true
        | (VMCS_GUEST_RFLAGS, VMCS_GUEST_RFLAGS) => true
        | (VMCS_GUEST_PENDING_DBG_EXCEPTIONS, VMCS_GUEST_PENDING_DBG_EXCEPTIONS) => true
        | (VMCS_GUEST_IA32_SYSENTER_ESP, VMCS_GUEST_IA32_SYSENTER_ESP) => true
        | (VMCS_GUEST_IA32_SYSENTER_EIP, VMCS_GUEST_IA32_SYSENTER_EIP) => true
        | (VMCS_HOST_CR0, VMCS_HOST_CR0) => true
        | (VMCS_HOST_CR3, VMCS_HOST_CR3) => true
        | (VMCS_HOST_CR4, VMCS_HOST_CR4) => true
        | (VMCS_HOST_FS_BASE, VMCS_HOST_FS_BASE) => true
        | (VMCS_HOST_GS_BASE, VMCS_HOST_GS_BASE) => true
        | (VMCS_HOST_TR_BASE, VMCS_HOST_TR_BASE) => true
        | (VMCS_HOST_GDTR_BASE, VMCS_HOST_GDTR_BASE) => true
        | (VMCS_HOST_IDTR_BASE, VMCS_HOST_IDTR_BASE) => true
        | (VMCS_HOST_IA32_SYSENTER_ESP, VMCS_HOST_IA32_SYSENTER_ESP) => true
        | (VMCS_HOST_IA32_SYSENTER_EIP, VMCS_HOST_IA32_SYSENTER_EIP) => true
        | (VMCS_HOST_RSP, VMCS_HOST_RSP) => true
        | (VMCS_HOST_RIP, VMCS_HOST_RIP) => true    
        |(_, _) => false
      end.
  
    Lemma vmcs_encoding_Z_eq:
      forall z e, vmcs_ZtoEncoding z = Some e <->
                  z = vmcs_EncodingtoZ e.
    Proof.
      split.
      - functional inversion 1; trivial.
      - induction e; intros; subst; trivial.
    Qed.

    Lemma vmcs_encoding_Z_eq_r:
      forall e, vmcs_ZtoEncoding (vmcs_EncodingtoZ e) = Some e.
    Proof.
      intros. destruct e; trivial.
    Qed.

    Lemma vmcs_ZtoEncoding_range:
      forall z e, vmcs_ZtoEncoding z = Some e ->
                  (0 <= z <= 27670)%Z.
    Proof.
      functional inversion 1; omega.
    Qed.
    
    Inductive VMCS :=
    | VMCSValid (revid: val) (abrtid: val) (data: ZMap.t val).

    Inductive VMCS_inj : meminj -> VMCS -> VMCS -> Prop :=
    | VMCS_INJ_INTRO:
        forall f r a v v',
          (forall i,
            (*vmcs_ZtoEncoding i = Some e*)
            val_inject f (ZMap.get i v) (ZMap.get i v'))
          -> VMCS_inj f (VMCSValid r a v) (VMCSValid r a v').

    Inductive VMCS_inject_neutral :VMCS -> block -> Prop :=
    | VMCS_inject_neutral_INTRO:
      forall r a d n, 
        (forall ofs,
           let v := ZMap.get ofs d in
           Val.has_type v Tint
           /\ val_inject (Mem.flat_inj n) v v)
        -> VMCS_inject_neutral (VMCSValid r a d) n.

    Inductive FieldWidth :=
      W16 | W32 | W64.

    Function field_width_beq (a b: FieldWidth) :=
      match (a, b) with
        | (W16, W16) => true
        | (W32, W32) => true
        | (W64, W64) => true
        | (_, _) => false
      end.

    Definition vmcs_filed_width_by_encoding (encoding: VMCS_Encoding): FieldWidth :=
      match encoding with
        | VMCS_VPID => W16
        | VMCS_GUEST_ES_SELECTOR => W16
        | VMCS_GUEST_CS_SELECTOR => W16
        | VMCS_GUEST_SS_SELECTOR => W16
        | VMCS_GUEST_DS_SELECTOR => W16
        | VMCS_GUEST_FS_SELECTOR => W16
        | VMCS_GUEST_GS_SELECTOR => W16
        | VMCS_GUEST_LDTR_SELECTOR => W16
        | VMCS_GUEST_TR_SELECTOR => W16
        | VMCS_HOST_ES_SELECTOR => W16
        | VMCS_HOST_CS_SELECTOR => W16
        | VMCS_HOST_SS_SELECTOR => W16
        | VMCS_HOST_DS_SELECTOR => W16
        | VMCS_HOST_FS_SELECTOR => W16
        | VMCS_HOST_GS_SELECTOR => W16
        | VMCS_HOST_TR_SELECTOR => W16
        | VMCS_IO_BITMAP_A => W64
        | VMCS_IO_BITMAP_A_HI => W64
        | VMCS_IO_BITMAP_B => W64
        | VMCS_IO_BITMAP_B_HI => W64
        | VMCS_MSR_BITMAP => W64
        | VMCS_MSR_BITMAP_HI => W64
        | VMCS_EXIT_MSR_STORE => W16
        | VMCS_EXIT_MSR_LOAD => W16
        | VMCS_ENTRY_MSR_LOAD => W16
        | VMCS_EXECUTIVE_VMCS => W16
        | VMCS_TSC_OFFSET => W16
        | VMCS_VIRTUAL_APIC => W16
        | VMCS_APIC_ACCESS => W16
        | VMCS_EPTP => W64
        | VMCS_EPTP_HI => W64
        | VMCS_GUEST_PHYSICAL_ADDRESS => W64
        | VMCS_LINK_POINTER => W64
        | VMCS_GUEST_IA32_DEBUGCTL => W64
        | VMCS_GUEST_IA32_PAT => W64
        | VMCS_GUEST_IA32_EFER => W64
        | VMCS_GUEST_IA32_PERF_GLOBAL_CTRL  => W64
        | VMCS_GUEST_PDPTE0 => W64
        | VMCS_GUEST_PDPTE1 => W64
        | VMCS_GUEST_PDPTE2 => W64
        | VMCS_GUEST_PDPTE3 => W64
        | VMCS_HOST_IA32_PAT => W64
        | VMCS_HOST_IA32_EFER => W64
        | VMCS_HOST_IA32_PERF_GLOBAL_CTRL => W64
        | VMCS_PIN_BASED_CTLS => W32
        | VMCS_PRI_PROC_BASED_CTLS => W32
        | VMCS_EXCEPTION_BITMAP => W32
        | VMCS_PF_ERROR_MASK => W32
        | VMCS_PF_ERROR_MATCH => W32
        | VMCS_CR3_TARGET_COUNT => W32
        | VMCS_EXIT_CTLS => W32
        | VMCS_EXIT_MSR_STORE_COUNT => W32
        | VMCS_EXIT_MSR_LOAD_COUNT => W32
        | VMCS_ENTRY_CTLS => W32
        | VMCS_ENTRY_MSR_LOAD_COUNT => W32
        | VMCS_ENTRY_INTR_INFO => W32
        | VMCS_ENTRY_EXCEPTION_ERROR => W32
        | VMCS_ENTRY_INST_LENGTH => W32
        | VMCS_TPR_THRESHOLD => W32
        | VMCS_SEC_PROC_BASED_CTLS => W32
        | VMCS_PLE_GAP => W32
        | VMCS_PLE_WINDOW => W32
        | VMCS_INSTRUCTION_ERROR => W32
        | VMCS_EXIT_REASON => W32
        | VMCS_EXIT_INTERRUPTION_INFO => W32
        | VMCS_EXIT_INTERRUPTION_ERROR => W32
        | VMCS_IDT_VECTORING_INFO => W32
        | VMCS_IDT_VECTORING_ERROR => W32
        | VMCS_EXIT_INSTRUCTION_LENGTH => W32
        | VMCS_EXIT_INSTRUCTION_INFO => W32
        | VMCS_GUEST_ES_LIMIT => W32
        | VMCS_GUEST_CS_LIMIT => W32
        | VMCS_GUEST_SS_LIMIT => W32
        | VMCS_GUEST_DS_LIMIT => W32
        | VMCS_GUEST_FS_LIMIT => W32
        | VMCS_GUEST_GS_LIMIT => W32
        | VMCS_GUEST_LDTR_LIMIT => W32
        | VMCS_GUEST_TR_LIMIT => W32
        | VMCS_GUEST_GDTR_LIMIT => W32
        | VMCS_GUEST_IDTR_LIMIT => W32
        | VMCS_GUEST_ES_ACCESS_RIGHTS => W32
        | VMCS_GUEST_CS_ACCESS_RIGHTS => W32
        | VMCS_GUEST_SS_ACCESS_RIGHTS => W32
        | VMCS_GUEST_DS_ACCESS_RIGHTS => W32
        | VMCS_GUEST_FS_ACCESS_RIGHTS => W32
        | VMCS_GUEST_GS_ACCESS_RIGHTS => W32
        | VMCS_GUEST_LDTR_ACCESS_RIGHTS => W32
        | VMCS_GUEST_TR_ACCESS_RIGHTS => W32
        | VMCS_GUEST_INTERRUPTIBILITY => W32
        | VMCS_GUEST_ACTIVITY => W32
        | VMCS_GUEST_SMBASE => W32
        | VMCS_GUEST_IA32_SYSENTER_CS => W32
        | VMCS_PREEMPTION_TIMER_VALUE => W32
        | VMCS_HOST_IA32_SYSENTER_CS => W32
        | VMCS_CR0_MASK => W32
        | VMCS_CR4_MASK => W32
        | VMCS_CR0_SHADOW => W32
        | VMCS_CR4_SHADOW => W32
        | VMCS_CR3_TARGET0 => W32
        | VMCS_CR3_TARGET1 => W32
        | VMCS_CR3_TARGET2 => W32
        | VMCS_CR3_TARGET3 => W32
        | VMCS_EXIT_QUALIFICATION => W32
        | VMCS_IO_RCX => W32
        | VMCS_IO_RSI => W32
        | VMCS_IO_RDI => W32
        | VMCS_IO_RIP => W32
        | VMCS_GUEST_LINEAR_ADDRESS => W32
        | VMCS_GUEST_CR0 => W32
        | VMCS_GUEST_CR3 => W32
        | VMCS_GUEST_CR4 => W32
        | VMCS_GUEST_ES_BASE => W32
        | VMCS_GUEST_CS_BASE => W32
        | VMCS_GUEST_SS_BASE => W32
        | VMCS_GUEST_DS_BASE => W32
        | VMCS_GUEST_FS_BASE => W32
        | VMCS_GUEST_GS_BASE => W32
        | VMCS_GUEST_LDTR_BASE => W32
        | VMCS_GUEST_TR_BASE => W32
        | VMCS_GUEST_GDTR_BASE => W32
        | VMCS_GUEST_IDTR_BASE => W32
        | VMCS_GUEST_DR7 => W32
        | VMCS_GUEST_RSP => W32
        | VMCS_GUEST_RIP => W32
        | VMCS_GUEST_RFLAGS => W32
        | VMCS_GUEST_PENDING_DBG_EXCEPTIONS => W32
        | VMCS_GUEST_IA32_SYSENTER_ESP => W32
        | VMCS_GUEST_IA32_SYSENTER_EIP => W32
        | VMCS_HOST_CR0 => W32
        | VMCS_HOST_CR3 => W32
        | VMCS_HOST_CR4 => W32
        | VMCS_HOST_FS_BASE => W32
        | VMCS_HOST_GS_BASE => W32
        | VMCS_HOST_TR_BASE => W32
        | VMCS_HOST_GDTR_BASE => W32
        | VMCS_HOST_IDTR_BASE => W32
        | VMCS_HOST_IA32_SYSENTER_ESP => W32
        | VMCS_HOST_IA32_SYSENTER_EIP => W32
        | VMCS_HOST_RSP => W32
        | VMCS_HOST_RIP => W32
      end.

    Inductive FieldPerm :=
      ReadOnly | WriteOnly | ReadWrite.

    Definition vmcs_wr_permission_by_encoding (encoding: VMCS_Encoding): FieldPerm :=
      match encoding with
        | VMCS_VPID => ReadWrite
        | VMCS_GUEST_ES_SELECTOR => ReadWrite
        | VMCS_GUEST_CS_SELECTOR => ReadWrite
        | VMCS_GUEST_SS_SELECTOR => ReadWrite
        | VMCS_GUEST_DS_SELECTOR => ReadWrite
        | VMCS_GUEST_FS_SELECTOR => ReadWrite
        | VMCS_GUEST_GS_SELECTOR => ReadWrite
        | VMCS_GUEST_LDTR_SELECTOR => ReadWrite
        | VMCS_GUEST_TR_SELECTOR => ReadWrite
        | VMCS_HOST_ES_SELECTOR => ReadWrite
        | VMCS_HOST_CS_SELECTOR => ReadWrite
        | VMCS_HOST_SS_SELECTOR => ReadWrite
        | VMCS_HOST_DS_SELECTOR => ReadWrite
        | VMCS_HOST_FS_SELECTOR => ReadWrite
        | VMCS_HOST_GS_SELECTOR => ReadWrite
        | VMCS_HOST_TR_SELECTOR => ReadWrite
        | VMCS_IO_BITMAP_A => ReadWrite
        | VMCS_IO_BITMAP_A_HI => ReadWrite
        | VMCS_IO_BITMAP_B => ReadWrite
        | VMCS_IO_BITMAP_B_HI => ReadWrite
        | VMCS_MSR_BITMAP => ReadWrite
        | VMCS_MSR_BITMAP_HI => ReadWrite
        | VMCS_EXIT_MSR_STORE => ReadWrite
        | VMCS_EXIT_MSR_LOAD => ReadWrite
        | VMCS_ENTRY_MSR_LOAD => ReadWrite
        | VMCS_EXECUTIVE_VMCS => ReadWrite
        | VMCS_TSC_OFFSET => ReadWrite
        | VMCS_VIRTUAL_APIC => ReadWrite
        | VMCS_APIC_ACCESS => ReadWrite
        | VMCS_EPTP => ReadWrite
        | VMCS_EPTP_HI => ReadWrite
        | VMCS_GUEST_PHYSICAL_ADDRESS => ReadOnly
        | VMCS_LINK_POINTER => ReadWrite
        | VMCS_GUEST_IA32_DEBUGCTL => ReadWrite
        | VMCS_GUEST_IA32_PAT => ReadWrite
        | VMCS_GUEST_IA32_EFER => ReadWrite
        | VMCS_GUEST_IA32_PERF_GLOBAL_CTRL  => ReadWrite
        | VMCS_GUEST_PDPTE0 => ReadWrite
        | VMCS_GUEST_PDPTE1 => ReadWrite
        | VMCS_GUEST_PDPTE2 => ReadWrite
        | VMCS_GUEST_PDPTE3 => ReadWrite
        | VMCS_HOST_IA32_PAT => ReadWrite
        | VMCS_HOST_IA32_EFER => ReadWrite
        | VMCS_HOST_IA32_PERF_GLOBAL_CTRL => ReadWrite
        | VMCS_PIN_BASED_CTLS => ReadWrite
        | VMCS_PRI_PROC_BASED_CTLS => ReadWrite
        | VMCS_EXCEPTION_BITMAP => ReadWrite
        | VMCS_PF_ERROR_MASK => ReadWrite
        | VMCS_PF_ERROR_MATCH => ReadWrite
        | VMCS_CR3_TARGET_COUNT => ReadWrite
        | VMCS_EXIT_CTLS => ReadWrite
        | VMCS_EXIT_MSR_STORE_COUNT => ReadWrite
        | VMCS_EXIT_MSR_LOAD_COUNT => ReadWrite
        | VMCS_ENTRY_CTLS => ReadWrite
        | VMCS_ENTRY_MSR_LOAD_COUNT => ReadWrite
        | VMCS_ENTRY_INTR_INFO => ReadWrite
        | VMCS_ENTRY_EXCEPTION_ERROR => ReadWrite
        | VMCS_ENTRY_INST_LENGTH => ReadWrite
        | VMCS_TPR_THRESHOLD => ReadWrite
        | VMCS_SEC_PROC_BASED_CTLS => ReadWrite
        | VMCS_PLE_GAP => ReadWrite
        | VMCS_PLE_WINDOW => ReadWrite
        | VMCS_INSTRUCTION_ERROR => ReadOnly
        | VMCS_EXIT_REASON => ReadOnly
        | VMCS_EXIT_INTERRUPTION_INFO => ReadOnly
        | VMCS_EXIT_INTERRUPTION_ERROR => ReadOnly
        | VMCS_IDT_VECTORING_INFO => ReadOnly
        | VMCS_IDT_VECTORING_ERROR => ReadOnly
        | VMCS_EXIT_INSTRUCTION_LENGTH => ReadOnly
        | VMCS_EXIT_INSTRUCTION_INFO => ReadOnly
        | VMCS_GUEST_ES_LIMIT => ReadWrite
        | VMCS_GUEST_CS_LIMIT => ReadWrite
        | VMCS_GUEST_SS_LIMIT => ReadWrite
        | VMCS_GUEST_DS_LIMIT => ReadWrite
        | VMCS_GUEST_FS_LIMIT => ReadWrite
        | VMCS_GUEST_GS_LIMIT => ReadWrite
        | VMCS_GUEST_LDTR_LIMIT => ReadWrite
        | VMCS_GUEST_TR_LIMIT => ReadWrite
        | VMCS_GUEST_GDTR_LIMIT => ReadWrite
        | VMCS_GUEST_IDTR_LIMIT => ReadWrite
        | VMCS_GUEST_ES_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_CS_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_SS_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_DS_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_FS_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_GS_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_LDTR_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_TR_ACCESS_RIGHTS => ReadWrite
        | VMCS_GUEST_INTERRUPTIBILITY => ReadWrite
        | VMCS_GUEST_ACTIVITY => ReadWrite
        | VMCS_GUEST_SMBASE => ReadWrite
        | VMCS_GUEST_IA32_SYSENTER_CS => ReadWrite
        | VMCS_PREEMPTION_TIMER_VALUE => ReadWrite
        | VMCS_HOST_IA32_SYSENTER_CS => ReadWrite
        | VMCS_CR0_MASK => ReadWrite
        | VMCS_CR4_MASK => ReadWrite
        | VMCS_CR0_SHADOW => ReadWrite
        | VMCS_CR4_SHADOW => ReadWrite
        | VMCS_CR3_TARGET0 => ReadWrite
        | VMCS_CR3_TARGET1 => ReadWrite
        | VMCS_CR3_TARGET2 => ReadWrite
        | VMCS_CR3_TARGET3 => ReadWrite
        | VMCS_EXIT_QUALIFICATION => ReadOnly
        | VMCS_IO_RCX => ReadOnly
        | VMCS_IO_RSI => ReadOnly
        | VMCS_IO_RDI => ReadOnly
        | VMCS_IO_RIP => ReadOnly
        | VMCS_GUEST_LINEAR_ADDRESS => ReadOnly
        | VMCS_GUEST_CR0 => ReadWrite
        | VMCS_GUEST_CR3 => ReadWrite
        | VMCS_GUEST_CR4 => ReadWrite
        | VMCS_GUEST_ES_BASE => ReadWrite
        | VMCS_GUEST_CS_BASE => ReadWrite
        | VMCS_GUEST_SS_BASE => ReadWrite
        | VMCS_GUEST_DS_BASE => ReadWrite
        | VMCS_GUEST_FS_BASE => ReadWrite
        | VMCS_GUEST_GS_BASE => ReadWrite
        | VMCS_GUEST_LDTR_BASE => ReadWrite
        | VMCS_GUEST_TR_BASE => ReadWrite
        | VMCS_GUEST_GDTR_BASE => ReadWrite
        | VMCS_GUEST_IDTR_BASE => ReadWrite
        | VMCS_GUEST_DR7 => ReadWrite
        | VMCS_GUEST_RSP => ReadWrite
        | VMCS_GUEST_RIP => ReadWrite
        | VMCS_GUEST_RFLAGS => ReadWrite
        | VMCS_GUEST_PENDING_DBG_EXCEPTIONS => ReadWrite
        | VMCS_GUEST_IA32_SYSENTER_ESP => ReadWrite
        | VMCS_GUEST_IA32_SYSENTER_EIP => ReadWrite
        | VMCS_HOST_CR0 => ReadWrite
        | VMCS_HOST_CR3 => ReadWrite
        | VMCS_HOST_CR4 => ReadWrite
        | VMCS_HOST_FS_BASE => ReadWrite
        | VMCS_HOST_GS_BASE => ReadWrite
        | VMCS_HOST_TR_BASE => ReadWrite
        | VMCS_HOST_GDTR_BASE => ReadWrite
        | VMCS_HOST_IDTR_BASE => ReadWrite
        | VMCS_HOST_IA32_SYSENTER_ESP => ReadWrite
        | VMCS_HOST_IA32_SYSENTER_EIP => ReadWrite
        | VMCS_HOST_RSP => ReadWrite
        | VMCS_HOST_RIP => ReadWrite
      end.

  End VMCSDEF.

  Section VMXDEF.

    Definition VMX := ZMap.t val.

    Inductive VMX_inj : meminj -> VMX -> VMX -> Prop :=
    | VMX_INJ_INTRO:
        forall f v v',
          (forall i,
            val_inject f (ZMap.get i v) (ZMap.get i v'))
          -> VMX_inj f v v'.

    Inductive VMX_inject_neutral :VMX -> block -> Prop :=
    | VMX_inject_neutral_INTRO:
      forall d n, 
        (forall ofs,
           let v := ZMap.get ofs d in
           Val.has_type v Tint
           /\ val_inject (Mem.flat_inj n) v v)
        -> VMX_inject_neutral d n.

  End VMXDEF.

End IntelVirtManagement.

Notation "a {quota i := b }" := (update_cquota a i b) (at level 1).
Notation "a {usage i := b }" := (update_cusage a i b) (at level 1).
Notation "a {parent i := b }" := (update_cparent a i b) (at level 1).
Notation "a {children i := b }" := (update_cchildren a i b) (at level 1).
Notation "a {used i := b }" := (update_cused a i b) (at level 1).
