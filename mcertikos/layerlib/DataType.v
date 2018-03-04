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
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide some [data types] that will be used in the layer definitions and refinement proofs*)
Require Import Coq.ZArith.BinInt.  
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import AsmExtra.
Require Import AST.
Require Import XOmega.

Notation PT_PERM_UP := 0.
Notation PT_PERM_P := 1. (**r kern: >1G, PTE_P *)
Notation PT_PERM_PTKF := 3. (**r kern: >1G, PTE_P|_W *)
Notation PT_PERM_PTKT := 259. (**r kern: <1G, PTE_P|_W|_G *)
Notation PT_PERM_PTU := 7. (**r usr: >1G, PTE_P|_W|_U *)

Section DataType.
  
  Context `{PgSize:Z}.
  Context `{kern_low:Z}.
  Context `{kern_high:Z}.
  Context `{maxpage: Z}.
    
  (** *Data types for abstract data*)

  (** Physical memory intromation table*)
  Inductive MMPerm:=
  | MMUsable
  | MMResv.
  
  Inductive MMInfo:=
  | MMValid (s l:Z) (p: MMPerm)
  | MMUndef.
  
  Definition MMTable := ZMap.t MMInfo.

  Definition trapinfo := prod int val.
  
  Definition init_trap_info : trapinfo := (Int.zero, Vundef).  

  Inductive globalpointer :=
  | GLOBP (b: ident) (ofs: int)
  | GLOBUndef.

  Inductive PTPerm: Type :=
  | PTP
  | PTU 
  | PTK (b: bool).
  
  Definition ZtoPerm (i:Z): option PTPerm:=
    if zeq i PT_PERM_P then
      Some PTP
    else if zeq i PT_PERM_PTKF then (*kern: >1G, PTE_P|_W *)
           Some (PTK false)
         else if zeq i PT_PERM_PTKT then (*kern: <1G, PTE_P|_W|_G *)
                Some (PTK true)
              else if zeq i PT_PERM_PTU then (*usr: >1G, PTE_P|_W|_U*)
                     Some PTU
                   else None.
  
  Definition PermtoZ (p: PTPerm): Z :=
    match p with
      | PTP => PT_PERM_P
      | PTU => PT_PERM_PTU
      | PTK false => PT_PERM_PTKF
      | PTK true => PT_PERM_PTKT
    end.
  
  Lemma PermZ_eq: 
    forall v p, ZtoPerm v = Some p -> v = PermtoZ p.
  Proof.
    intros.
    unfold ZtoPerm, PermtoZ in *.
    destruct (zeq v PT_PERM_P).
    inv H.
    trivial.
    destruct (zeq v PT_PERM_PTKF).
    inv H.
    trivial.
    destruct (zeq v PT_PERM_PTKT).
    inv H.
    trivial.
    destruct (zeq v PT_PERM_PTU).
    inv H.
    trivial.
    inv H.

  Qed.
  
  Lemma PermZ_eq_r: forall p, ZtoPerm (PermtoZ p) = Some p.
  Proof.
    intros.
    unfold ZtoPerm, PermtoZ.
    destruct p; simpl; trivial.
    destruct b; simpl; trivial.
  Qed.

  (** Page Table*)
  Inductive PTInfo:=
  | PTValid (v: block) (p: PTPerm)
  | PTUnPresent
  | PTUndef.
  
  Definition PTE := ZMap.t PTInfo.

  Inductive PDTInfo :=
  | PDTValid (pte: PTE)
  | PDTUndef.

  Definition PTable := ZMap.t PDTInfo.

  Definition PTPool := ZMap.t PTable.

  (** Allocation table*)
  Inductive ATType: Type :=
  | ATKern 
  | ATResv 
  | ATNorm.

  Inductive ATInfo :=
  | ATValid (b: bool) (t: ATType)
  | ATUndef.

  Definition ATable := ZMap.t ATInfo.

  Definition ZtoATType (i: Z) : option ATType :=
    if zeq i 0
    then Some ATResv
    else if zeq i 1
         then Some ATKern
         else if zeq i 2
              then Some ATNorm
              else None.
  
 Definition IntToATTypeZ (n: int) : int :=
    if zeq (Int.unsigned n) 0 then Int.zero
    else if zeq (Int.unsigned n) 1 then Int.zero
         else (Int.repr 1).

  Definition IntToBoolZ (n: int) : int :=
    if zeq (Int.unsigned n) 0 then Int.zero
    else (Int.repr 1).

  (** page table bit map*)
  Inductive PTBit :=
  | PTBUndef
  | PTTrue
  | PTFalse.
  
  Definition PTBitMap := ZMap.t PTBit.
  
  Definition ZtoPTBit (i:Z): option PTBit:=
    if zeq i 1 then
      Some PTTrue
    else if zeq i 0 then
           Some PTFalse
         else None.
  
  Definition ZtoBool (i:Z): option bool :=
    if zeq i 0
    then Some false
    else if zeq i 1
         then Some true
         else None.

  Definition BooltoZ (b:bool): Z :=
    match b with
      | true => 1
      | _ => 0
    end.

 
  (** * [Decidability] of data types*)
  Lemma eq_bool_dec : forall a b : bool, {a = b} +{~ a = b}.
  Proof.
    intros.
    decide equality.
  Qed.

  Remark Z_le_lt_dec (a b c :Z) :
    {a <= b < c } +{~ a <= b < c}.
  Proof.
    destruct (Z_le_dec a b).
    destruct (Z_lt_dec b c).
    left.
    omega.
    right.
    omega.
    right.
    omega.
  Qed.
  
  (** ** Decidability of physical memory information table*)
  Remark MM_dec (mm: MMTable) (i:Z):
    { exists s l p,  ZMap.get i mm = MMValid s l p} +{~exists s l  p, ZMap.get i mm = MMValid s l p}.
  Proof.
    induction (ZMap.get i mm). 
    left.
    exists s.
    exists l.
    exists p.
    trivial.
    right.
    red.
    intros.
    destruct H as [s[l[p H]]].
    inversion H.
  Qed.
  
  (** ** Decidability of physical memory information table*)
  Remark MM'_dec (mm: MMTable) (i:Z):
    { exists s l p,  ZMap.get i mm = MMValid s l p /\ s >= 0 /\ l > 0 /\ s + l < Int.max_unsigned} 
    +{~exists s l  p, ZMap.get i mm = MMValid s l p /\ s >= 0 /\ l > 0 /\ s + l < Int.max_unsigned}.
  Proof.
    induction (ZMap.get i mm). 
    destruct (zle 0 s).
    destruct (zlt 0 l).
    destruct (zlt (s + l) Int.max_unsigned).
    left.
    exists s.
    exists l.
    exists p.
    split; trivial.
    split; omega.
    right.
    red.
    intros [s'[l'[p' [HT [_[_ HF]]]]]].
    inv HT; omega.

    right.
    red.
    intros [s'[l'[p' [HT [_[HF _]]]]]].
    inv HT; omega.

    right.
    red.
    intros [s'[l'[p' [HT [HF _]]]]].
    inv HT; omega.

    right.
    red.
    intros [s'[l'[p' [HT _]]]].
    inv HT.

  Qed.

  Definition MM_range (mm: MMTable) (lo high: Z) :=
    forall i , lo <= i < high -> exists s l p, (ZMap.get i mm = MMValid s l p /\ s >= 0 /\ l > 0 /\ s + l < Int.max_unsigned).

  Remark MM_range_dec:
    forall mm lo high, {MM_range mm lo high} + {~MM_range mm lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {MM_range mm lo (lo+n)} + {~MM_range mm lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    
    destruct (MM'_dec mm (lo+z)).
    left.
    unfold MM_range in *.
    intros.
    destruct e as [s[l[p HT]]].
    destruct (zeq i (lo + z)).
    exists s.
    exists l.
    exists p.
    subst.
    trivial.
    apply m. 
    omega. 
    right; red; intro. 
    unfold MM_range in H0.
    assert (HL: lo <= (lo+z) < lo + Z.succ z).
    omega.
    specialize (H0 (lo+z) HL).
    elim n.
    trivial.

    right; red; intro. 
    elim n.
    clear n.
    unfold MM_range in *.    
    intros.
    assert (HL: lo <= i < lo + Z.succ z).
    omega.
    specialize (H0 i HL).   
    trivial.
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
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
    assert(HP1: {p1 = p2} + {~p1 = p2}).
    decide equality.
    destruct HP1.
    left.
    auto.
    right.
    unfold not.
    intros.
    apply n.
    auto.
    left.
    intros.
    omegaContradiction.
    left.
    intros.
    omega.
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
    destruct (ZMap.get i mm).
    destruct (ZMap.get j mm).
    unfold perm_consist. 
    destruct (MMPerm_dec p p0).
    left.
    intros.
    inv H; inv H0.
    trivial.
    destruct (zlt s (s0 + l0)).
    destruct (zlt s0 (s + l)).
    
    right.
    red; intros.
    elim n.
    specialize (H _ _ _ _ _ _ refl_equal refl_equal).
    apply H; trivial.

    left.
    intros.
    inv H; inv H0.
    omega.

    left.
    intros.
    inv H; inv H0.
    omega.

    left.
    intros.
    inv H0.

    left.
    intros.
    inv H.

  Qed.
  
  Definition MM_correct1 (mm: MMTable) (i size: Z) :=
    forall j, 0<= j < size -> MM_correct_pos mm i j.
  
  Remark MM_correct1_dec (mm: MMTable) (i size:Z) :
    {MM_correct1 mm i size} + {~ MM_correct1 mm i size}.
  Proof.
    assert(HQ: forall n, 0<= n -> {MM_correct1 mm i n} +{~ MM_correct1 mm i n}).
    unfold MM_correct1.
    apply natlike_rec2.
    left.
    intros.
    omega.
    
    intros.
    destruct H0.
    destruct (MM_correct_pos_dec mm i z).
    left.
    intros.    
    destruct (zeq j z).
    subst j.
    trivial.
    unfold MM_correct_pos in *.
    intros.
    apply m with j; trivial.
    omega.

    right; red; intro. 
    apply n.
    apply H0.
    omega.
    
    right; red; intro.
    apply n.
    intros.
    apply H0.
    omega.
    
    destruct (Z_le_dec size 0).
    left.
    unfold MM_correct1.
    intros.
    omega.

    apply HQ.
    omega.
  Qed.

  Definition MM_correct2 (mm: MMTable) (size size2: Z) :=
    forall i, 0<= i < size -> MM_correct1 mm i size2.
  
  Remark MM_correct2_dec (mm: MMTable) (size size2:Z) :
    {MM_correct2 mm size size2} + {~ MM_correct2 mm size size2}.
  Proof.
    assert(HQ: forall n, 0<= n -> {MM_correct2 mm n size2} +{~ MM_correct2 mm n size2}).
    unfold MM_correct2.
    apply natlike_rec2.
    left.
    intros.
    omega.
    
    intros.
    destruct H0.
    destruct (MM_correct1_dec mm z size2).
    left.
    intros.    
    destruct (zeq i z).
    subst i.
    trivial.
    unfold MM_correct1 in *.
    intros.
    assert(HL: 0<= i < z).
    omega.
    specialize (m i HL j H1).
    trivial.

    right; red; intro. 
    apply n.
    apply H0.
    omega.
    
    right; red; intro.
    apply n.
    intros.
    apply H0.
    omega.
    
    destruct (Z_le_dec size 0).
    left.
    unfold MM_correct2.
    intros.
    omega.
    
    apply HQ.
    omega.
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
    left.
    unfold MM_correct2 in m.
    unfold MM_correct.
    intros.
    specialize (m i H).
    unfold MM_correct1 in m.
    specialize (m j H0).
    unfold MM_correct_pos in m.
    specialize (m s1 s2 l1 l2 p1 p2 H1 H2).
    trivial.
    
    right;red;intro.
    apply n.
    unfold MM_correct2.
    unfold MM_correct1.
    unfold MM_correct_pos.
    intros.
    unfold MM_correct in H.
    apply H with i j; trivial.
  Qed.

  Definition MM_kern_valid (mm: MMTable)(n size:Z):=
    exists i s l, 
      0<= i < size /\ ZMap.get i mm = MMValid s l MMUsable /\ s<= n * PgSize /\ l + s >= ((n+1)* PgSize).

  Remark MM_kern_valid_dec (mm:MMTable) (n size:Z) :
    {MM_kern_valid mm n size} +{~MM_kern_valid mm n size}.
  Proof.
    assert(HQ: forall k, 0<= k -> {MM_kern_valid mm n k} +{~MM_kern_valid mm n k}).
    unfold MM_kern_valid.
    apply natlike_rec2.
    right.
    red.
    intros.
    destruct H as [i[_[_[HI _]]]].
    omega.
    
    intros.
    destruct H0.
    left.
    destruct e as [i [s[l[HI[HM[HS HL]]]]]].
    exists i.
    exists s.
    exists l.
    repeat (split;trivial).
    omega.
    omega.

    caseEq (ZMap.get z mm); intros.
    destruct (MMPerm_dec p MMUsable).
    destruct (zle s (n * PgSize)).
    destruct (zle ((n+1)*PgSize) (l + s)).
    
    left.
    exists z.
    exists s.
    exists l.
    rewrite e in H0.
    repeat(split;trivial);
    omega. 
    
    right.
    red; intros.
    destruct H1 as [i'[s'[l' HM]]].
    destruct (zeq i' z).
    subst i'.
    destruct HM as [_ [HM [_ HF]]].
    rewrite H0 in HM.
    inv HM.
    omega.
    elim n0.
    exists i'.
    exists s'.
    exists l'.
    destruct HM as [HM1 HM2].
    split; trivial.
    omega.

    right.
    red; intros.
    destruct H1 as [i'[s'[l' HM]]].
    destruct (zeq i' z).
    subst i'.
    destruct HM as [_ [HM [HF _]]].
    rewrite H0 in HM.
    inv HM.
    omega.
    elim n0.
    exists i'.
    exists s'.
    exists l'.
    destruct HM as [HM1 HM2].
    split; trivial.
    omega.

    right.
    red; intros.
    destruct H1 as [i'[s'[l' HM]]].
    destruct (zeq i' z).
    subst i'.
    destruct HM as [_ [HM _]].
    rewrite H0 in HM.
    inv HM.
    elim n1; trivial.
    elim n0.
    exists i'.
    exists s'.
    exists l'.
    destruct HM as [HM1 HM2].
    split; trivial.
    omega.

    right.
    red; intros.
    destruct H1 as [i'[s'[l' HM]]].
    destruct (zeq i' z).
    subst i'.
    destruct HM as [_ [HM _]].
    rewrite H0 in HM.
    inv HM.
    elim n0.
    exists i'.
    exists s'.
    exists l'.
    destruct HM as [HM1 HM2].
    split; trivial.
    omega.
    
    destruct (Z_le_dec size 0).
    right.
    red.
    unfold MM_kern_valid.
    intro.
    destruct H as [i[_[_[HI _]]]].
    omega.
    
    apply HQ.
    omega.
  Qed.
  
  Definition MM_kern_range (mm:MMTable) (n size: Z):=
    forall i, 0<= i < n -> MM_kern_valid mm i size.
  
  Remark MM_kern_range_dec (mm: MMTable) (k size: Z) :
    {MM_kern_range mm k size} + {~ MM_kern_range mm k size}.
  Proof.
    assert(HQ: forall n, 0<= n -> {MM_kern_range mm n size} + {~ MM_kern_range mm n size}).
    apply natlike_rec2.
    left.
    unfold MM_kern_range.
    intros.
    omega.
    
    intros.
    destruct H0.
    destruct (MM_kern_valid_dec mm z size).
    left.
    unfold MM_kern_range in *.
    intros.
    destruct (zeq i z).
    subst i.
    trivial.
    
    apply m.
    omega.
    
    right.
    unfold MM_kern_range.
    red. intro.
    apply n.
    apply H0.
    omega.
    
    right.
    red. intro.
    unfold MM_kern_range in *.
    apply n.
    intros.
    apply H0.
    omega.
    
    destruct (Z_le_dec 0 k).
    apply HQ.
    trivial.
    
    left.
    unfold MM_kern_range.
    intros.
    omega.
  Qed.
  
  Definition MM_kern_l (mm:MMTable) (size: Z):=
    MM_kern_range mm kern_low size.
  
  Remark MM_kern_l_dec (mm: MMTable) (size: Z) :
    {MM_kern_l mm size} + {~ MM_kern_l mm size}.
  Proof.
    unfold MM_kern_l.
    apply MM_kern_range_dec.
  Qed.

  (** ** Decidability of allocation table*)
  Remark AT_info_dec (t0 t: ATType) : {t0 = t } + {~ t0 =  t}.
  Proof.
    intros.
    decide equality.
  Qed.
  
  Remark AT_dec (info: ATInfo) (b: bool) (t: ATType):
    {info = ATValid b t} + {~info = ATValid b t}.
  Proof.
    decide equality.
    decide equality.
    decide equality.
  Qed.

  Remark AT_dec_e (info: ATInfo):
    {exists b, info = ATValid b ATNorm \/ info = ATValid b ATResv} 
    + {~exists b, info = ATValid b ATNorm \/ info = ATValid b ATResv}.
  Proof.
    destruct info.  
    destruct (AT_info_dec t ATNorm).
    rewrite e.
    left.
    exists b.
    left.
    trivial.

    destruct (AT_info_dec t ATResv).
    rewrite e.
    left.
    exists b. right. trivial.

    right.
    unfold not.
    intros.
    destruct H as [b0 [HP1|HP2]].
    inversion HP1.
    congruence.
    
    inversion HP2.
    congruence.
    
    right.
    unfold not.
    intros.
    destruct H as [b [HP1|HP2]].
    inversion HP1; trivial.
    inversion HP2; trivial.
  Qed.

  Definition AT_range (At: ATable) (lo high: Z) (b: bool) (t: ATType):=
    forall i , lo <= i < high -> ZMap.get i At = ATValid b t.
  
  Definition AT_range_not (At: ATable) (lo high: Z) (b: bool) (t: ATType):=
    forall i , lo <= i < high -> ZMap.get i At <> ATValid b t.

  Definition AT_range_e (At: ATable) (lo high: Z) :=
    forall i , lo <= i < high 
               -> exists b, ZMap.get i At = ATValid b ATNorm
                            \/ ZMap.get i At = ATValid b ATResv.

  Remark AT_range_dec:
    forall At lo high b t, {AT_range At lo high b t} + {~AT_range At lo high b t}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {AT_range At lo (lo+n) b t} + {~AT_range At lo (lo+n) b t}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    
    destruct (AT_dec (ZMap.get (lo+z) At)  b t).
    left.
    unfold AT_range in *.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply a. 
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
  Qed.

  Remark AT_range_not_dec:
    forall At lo high b t, {AT_range_not At lo high b t} + {~AT_range_not At lo high b t}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {AT_range_not At lo (lo+n) b t} + {~AT_range_not At lo (lo+n) b t}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    
    destruct (AT_dec (ZMap.get (lo+z) At)  b t).
    right;red;intro.
    unfold AT_range_not in *.
    specialize (H0 (lo+z)).
    assert(HA: lo <= lo + z < lo + Z.succ z).
    omega.
    specialize (H0 HA e).
    apply H0.
    
    left.
    unfold AT_range_not in *.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply a. 
    omega. 
    
    unfold AT_range_not in *.
    right; red; intro. 
    elim n.
    intros.
    apply H0. 
    omega. 
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.

  Remark AT_range_dec_e:
    forall At lo high, {AT_range_e At lo high} + {~AT_range_e At lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {AT_range_e At lo (lo+n)} + {~AT_range_e At lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    
    destruct (AT_dec_e (ZMap.get (lo+z) At)).
    left.
    unfold AT_range_e in *.
    intros.
    destruct (zeq i (lo + z)).
    rewrite e0.
    apply e.
    apply a.
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
  Qed.

  Definition AT_kern_l (AT: ATable) (nps: Z) :=   
    forall i, 0<= i < kern_low \/ kern_high <= i < nps
              -> ZMap.get i AT = ATValid false ATKern.

  Definition AT_usr_l (AT: ATable) (nps: Z):= 
    forall i,  kern_low <= i < Z.min kern_high nps
               -> exists b, ZMap.get i AT = ATValid b ATNorm 
                            \/ ZMap.get i AT = ATValid b ATResv.

  Definition AT_aloc_fail (AT: ATable) (nps: Z) :=   
    forall i, 0<= i < nps
              -> ZMap.get i AT <> ATValid false ATNorm.

  Remark AT_kern_l_dec:
    forall AT nps, { AT_kern_l AT nps} + { ~ AT_kern_l AT nps}.
  Proof.
    intros.
    unfold AT_kern_l.
    destruct (AT_range_dec AT 0 kern_low false ATKern).
    destruct (AT_range_dec AT kern_high nps false ATKern).
    left.
    unfold AT_range in *.
    intros.
    destruct H.
    specialize (a i H).
    trivial.
    specialize (a0 i H).
    trivial.
    right.
    unfold not.
    intros.
    unfold AT_range in *.
    apply n.
    intros.
    apply H.
    right; trivial.
    right.
    unfold not.
    intros.
    apply n.
    unfold AT_range.
    intros.
    apply H.
    left.
    trivial.
  Qed.

  Remark AT_aloc_fail_dec:
    forall AT nps, { AT_aloc_fail AT nps} + { ~ AT_aloc_fail AT nps}.
  Proof.
    intros.
    unfold AT_aloc_fail.
    specialize (AT_range_not_dec AT 0 nps false ATNorm).
    unfold AT_range_not in *.
    trivial.
  Qed.


  Remark AT_usr_l_dec:
    forall AT nps, { AT_usr_l AT nps } + { ~ AT_usr_l AT nps}.
  Proof.
    intros.
    unfold AT_usr_l.
    specialize (AT_range_dec_e AT kern_low (Z.min kern_high nps)).
    intros HP.
    destruct HP.
    left.
    intros.
    specialize (a i H).
    destruct a as [b a].
    exists b.
    trivial.

    right.
    unfold not.
    intros HP.
    apply n.    
    unfold AT_range_e in *.
    trivial.
  Qed.
  
  (** ** Decidability of page table*)
  Remark PTPerm_dec (p1 p2: PTPerm):
    {p1 = p2} +{~p1 = p2}.
  Proof.
    decide equality.
    decide equality.
  Qed.

  Remark PTInfo_dec (pt1 pt2: PTInfo) :
    {pt1 = pt2} +{~ pt1 = pt2}.
  Proof.
    decide equality.
    apply PTPerm_dec.
    apply  (Z_eq_dec).
  Qed.

  Scheme tree_rect := Induction for PTree.tree Sort Type.

  Theorem PTree_eq : 
    forall A:Type,
      (forall (x y: A), {x=y} + {x<>y}) ->
      forall (a b : PTree.t A), {a = b} + {a <> b}.
  Proof.
    intros A eqA.
    decide equality.
    generalize o o0; decide equality.
  Qed.
  
  Theorem ZMap_eq: 
    forall A:Type,               
      (forall (x y: A), {x=y} + {x<>y}) ->
      forall (a b : ZMap.t A), {a = b} + {a <> b}.
  Proof.
    intros A eqA.
    decide equality.
    apply PTree_eq.
    trivial.
  Qed.

  Remark PDT_dec (pt: PTable) (i: Z) (p: PTE) :
    {ZMap.get i pt = PDTValid p} + {~ZMap.get i pt = PDTValid p}.
  Proof.
    decide equality.
    apply ZMap_eq.
    apply PTInfo_dec.
  Qed.
  
  (** *** Lemmas about the parameters related to page table*)
  Definition one_k := PgSize/4.
  Definition PDX (i:Z) := i/(PgSize * one_k).
  Definition PTX (i:Z) := (i/PgSize) mod one_k.
  Definition PTADDR (i:Z) (ofs:Z) := (i * PgSize) + (ofs mod PgSize).
  
  Section PT_Lemma.
    Context {HPS: PgSize >= 4}.

    Lemma PgS_Pos:  PgSize * one_k > 0.     
    Proof.
      unfold one_k.
      apply Zmult_gt_0_compat.
      omega.
      assert (1 <= PgSize/4).
      apply Zdiv_le_lower_bound; omega.
      omega.
    Qed.

    Lemma Div_mult:
      forall a, (PgSize * one_k | a) -> a = (a/ (PgSize * one_k)) *  (PgSize * one_k).
    Proof.
      intros.
      rewrite Z.mul_comm.
      apply Z_div_exact_2.
      apply PgS_Pos.
      apply Zdivide_mod; trivial.
    Qed.
    
    Lemma Div_Diff:
      forall a b c, (PgSize * one_k | a) -> b < a -> a <= c -> PDX b < PDX c.
    Proof.
      intros.
      unfold PDX.
      specialize (Div_mult _ H).
      intro HW.
      rewrite HW in H0.
      specialize (PgS_Pos).
      intro HP.
      assert(HW1: b / (PgSize * one_k) < a / (PgSize * one_k)).
      apply Zdiv_lt_upper_bound;
        omega.
      assert(HW2:  a / (PgSize * one_k) <= c / (PgSize * one_k)).
      apply Z_div_le; trivial.
      omega.   
    Qed.
    
    Lemma pgs_pos: PgSize / 4 > 0.
    Proof.
      assert(HW: PgSize/4 >= 1).
      rewrite <- (Z_div_same_full 4).
      apply Z_div_ge; omega.
      omega.
      omega.
    Qed.
    
    Lemma onek_pos: one_k > 0.
    Proof.
      unfold one_k.
      apply (pgs_pos).
    Qed.
    
    Lemma onek_pgs_pos: PgSize * (one_k) > 0.
    Proof.
      assert(HW: PgSize > 0) by
          omega.
      apply Zmult_gt_0_compat; trivial.
      apply onek_pos.
    Qed.

    Lemma PDX_le_trans: 
      forall a b, a <= b ->  PDX a <= PDX b.
    Proof.  
      intros.
      unfold PDX.
      apply Z_div_le; trivial.
      apply onek_pgs_pos.
    Qed.
    
    Lemma PDX_0: PDX 0 = 0.
    Proof.
      unfold PDX.
      apply Zdiv_0_l.
    Qed.
    
    Lemma PTX_pos: forall a, 0 <= PTX a. 
    Proof.
      intros.
      unfold PTX.
      specialize (Z_mod_lt (a / PgSize) one_k onek_pos).
      intros.
      omega.
    Qed.

    Section PDT_MAX.

      Context `{Hmax: (PgSize * one_k) < Int.max_unsigned}.

      Lemma PDX_max_pos: PDX (Int.max_unsigned) > 0.
      Proof.  
        unfold PDX.
        assert (HW:  Int.max_unsigned / (PgSize * one_k) >= 1).
        specialize onek_pgs_pos;  intro Hone.
        erewrite <- (Z_div_same_full  (PgSize * one_k)).
        apply Z_div_ge; trivial.
        omega.
        omega.
        omega.
      Qed.
      
    End PDT_MAX.

    Section PT_Lemma4.

      Context `{HDIV4: (4 | PgSize)}.

      Lemma onek_le: 4 * one_k = PgSize.
      Proof.
        unfold one_k.
        erewrite <- Zdivide_Zdiv_eq; trivial; try omega.
      Qed.
      
      Section PTX_MAX.

        Context `{HPTX: PTX Int.max_unsigned = one_k - 1}.

        Lemma PTX_le: 4 * PTX (Int.max_unsigned) <= PgSize -4.
        Proof. 
          rewrite HPTX.
          specialize onek_le.
          intros.
          omega.
        Qed.
        
        Lemma PTX_max: forall a, PTX a <= PTX Int.max_unsigned.
        Proof.
          intros.
          rewrite HPTX.
          unfold PTX.
          specialize (Z_mod_lt (a / PgSize) one_k onek_pos).
          intros.
          omega.
        Qed.

      End PTX_MAX.
    End PT_Lemma4.
  End PT_Lemma.

  Definition adr_low := kern_low * PgSize.
  Definition adr_high := kern_high * PgSize.
  Definition adr_max := maxpage * PgSize.

  Definition PT_valid (pt: globalpointer) := exists b ofs, pt = GLOBP b ofs. 

  Remark PT_valid_dec (pt: globalpointer) :
    {PT_valid pt } + { ~ PT_valid pt}.
  Proof.
    unfold PT_valid.
    destruct pt.
    left.
    eauto.
    right.
    red; intros.
    destruct H as [b0 [ofs0 HG]].
    inv HG.

  Qed.

  Remark PT_dec (pte: PTE) (i: Z) (b: bool) :
    {ZMap.get (PTX (i * PgSize)) pte = PTValid (i * PgSize) (PTK b)} + {~ZMap.get (PTX (i * PgSize)) pte = PTValid (i * PgSize) (PTK b)}.
  Proof.
    decide equality.
    apply PTPerm_dec.
    apply Z_eq_dec.
  Qed.
  
  Definition PT_pos (pt: PTable) (i: Z) (b: bool) :=
    exists pte, ZMap.get (PDX (i * PgSize)) pt = PDTValid pte /\ ZMap.get (PTX (i * PgSize)) pte = PTValid (i * PgSize) (PTK b).
  
  Remark PT_pos_dec:
    forall pt i b, {PT_pos pt i b}+{~PT_pos pt i b}.
  Proof.
    intros.
    unfold PT_pos.
    induction (ZMap.get (PDX (i * PgSize)) pt).
    destruct (PT_dec pte i b).
    left.
    exists pte.
    split;trivial.
    right.
    unfold not.
    intros.
    destruct H as [pte0[HP1 HP2]].
    inv HP1.
    apply n.
    trivial.
    
    right.
    unfold not.
    intros.
    destruct H as [pte[HP _]].
    inv HP.
  Qed.

  Definition PT_range (ptv: PTable) (lo high: Z) (b: bool) :=
    forall i , lo <= i < high -> PT_pos ptv i b.

  Remark PT_range_dec:
    forall pt lo high b, {PT_range pt lo high b} + {~PT_range pt lo high b}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {PT_range pt lo (lo+n) b} + {~PT_range pt lo (lo+n) b}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    destruct (PT_pos_dec pt (lo+z) b).
    left.
    unfold PT_range in *.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply p. 
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
  Qed.

  Definition PDT_valid (pt:PTable)(i:Z) :=
    exists pte, ZMap.get (PDX (i * PgSize)) pt = PDTValid pte.
  
  Remark PDT_valid_dec (pt:PTable)(i:Z):
    {PDT_valid pt i} + {~PDT_valid pt i}.
  Proof.
    unfold PDT_valid.
    destruct (ZMap.get (PDX (i * PgSize)) pt).
    left.
    exists pte.
    trivial.
    right.
    red; intros.
    destruct H as [pte HF].
    inv HF.
  Qed.

  Definition PDT_valid_range (pt: PTable) (lo high: Z):=
    forall i , lo <= i < high -> PDT_valid pt i.

  Remark PDT_valid_range_dec:
    forall pt lo high, {PDT_valid_range pt lo high} + {~PDT_valid_range pt lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {PDT_valid_range pt lo (lo+n)} + {~PDT_valid_range pt lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    destruct (PDT_valid_dec pt (lo+z)).
    left.
    unfold PDT_valid_range in *.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply p. 
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
  Qed.

  Definition PT_common_l (pt: PTable) :=   
    forall i, 0<= i < kern_low \/ kern_high <= i < maxpage
              -> PT_pos pt i true.

  Definition PT_kern_l (pt: PTable) := 
    forall i, kern_low <= i < kern_high-> PT_pos pt i false.
  
  Definition PDT_usr_l (pt: PTable) :=
    forall i, kern_low <= i < kern_high -> PDT_valid pt i.

  Remark PT_common_l_dec:
    forall pt, { PT_common_l pt } + { ~ PT_common_l pt}.
  Proof.
    intros.
    unfold PT_common_l.
    destruct (PT_range_dec pt 0 kern_low true).
    destruct (PT_range_dec pt kern_high maxpage true).
    left.
    unfold PT_range in *.
    intros.
    destruct H.
    specialize (p i H).
    trivial.
    specialize (p0 i H).
    trivial.
    right.
    unfold not.
    intros.
    unfold PT_range in *.
    apply n.
    intros.
    apply H.
    right; trivial.
    right.
    unfold not.
    intros.
    apply n.
    unfold PT_range.
    intros.
    apply H.
    left.
    trivial.
  Qed.

  Remark PT_kern_l_dec:
    forall pt, { PT_kern_l pt } + { ~ PT_kern_l pt}.
  Proof.
    intros.
    unfold PT_kern_l.
    specialize (PT_range_dec pt kern_low kern_high false).
    intros.
    unfold PT_range in *.
    trivial.
  Qed.

  Remark PDT_usr_l_dec:
    forall pt, { PDT_usr_l pt } + { ~ PDT_usr_l pt}.
  Proof.
    intros.
    unfold PDT_usr_l.
    specialize (PDT_valid_range_dec pt kern_low kern_high).
    intros.
    unfold PDT_valid_range in *.
    trivial.
  Qed.

  Definition PT_unp (pt: PTable) (i: Z) :=
    exists pte, ZMap.get (PDX (i * PgSize)) pt = PDTValid pte /\ ZMap.get (PTX (i * PgSize)) pte = PTUnPresent.
  
  Remark PT_unp_dec:
    forall pt i, {PT_unp pt i}+{~PT_unp pt i}.
  Proof.
    intros.
    unfold PT_unp.
    induction (ZMap.get (PDX (i * PgSize)) pt).
    caseEq (ZMap.get (PTX (i * PgSize)) pte); intros.
    right.
    red; intros.
    destruct H0 as [pte0 [PT1 PT2]].
    inv PT1.
    rewrite H in PT2.
    inv PT2.
    left.
    exists pte.
    auto.
    right.
    red.
    intros.
    destruct H0 as [pte0[HP HM]].
    inv HP.
    rewrite HM in H.
    inv H.
    right.
    red.
    intros.
    destruct H as [pte[HP _]].
    inv HP.
  Qed.

  Definition PT_unp_range (ptv: PTable) (lo high: Z) :=
    forall i , lo <= i < high -> PT_unp ptv i.

  Remark PT_unp_range_dec:
    forall pt lo high, {PT_unp_range pt lo high} + {~PT_unp_range pt lo high }.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {PT_unp_range pt lo (lo+n)} + {~PT_unp_range pt lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    destruct (PT_unp_dec pt (lo+z)).
    left.
    unfold PT_unp_range in *.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply p. 
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
  Qed.

  Definition PT_init (pt: PTable) :=
    PT_common_l pt
    /\ (forall i, kern_low <= i < kern_high
                  -> PT_unp pt i).

  Remark PT_init_dec:
    forall pt, { PT_init pt } + { ~ PT_init pt}.
  Proof.
    intros.
    unfold PT_init.
    destruct (PT_common_l_dec pt).
    destruct (PT_unp_range_dec pt kern_low kern_high).
    left.
    unfold PT_unp_range in *.
    split; trivial.
    right.
    red.
    intros.
    destruct H as [_ HP].
    elim n.
    unfold PT_unp_range in *.
    trivial.
    right.
    red.
    intros.
    elim n.
    destruct H as [HP _].
    trivial.
  Qed.
  
  Lemma PT_init_common:
    forall pt, PT_init pt -> PT_common_l pt.
  Proof.
    intros.
    unfold PT_init in H.
    destruct H as [HP _].
    auto.
  Qed.

  Definition PTP_init (pt: PTPool) (lo high: Z) :=
    forall i , lo <= i < high -> PT_init (ZMap.get i pt).

  Remark PTP_init_dec:
    forall pt lo high, {PTP_init pt lo high} + {~PTP_init pt lo high }.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {PTP_init pt lo (lo+n)} + {~PTP_init pt lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    destruct (PT_init_dec (ZMap.get (lo+z) pt)).
    left.
    unfold PTP_init in *.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply p. 
    omega. 
    right; red; intro. 
    elim n. 
    unfold PTP_init in H0.
    apply H0. 
    omega. 
    right; red; intro. 
    elim n. 
    unfold PTP_init in *.
    intros.
    apply H0. 
    omega. 
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.

  (** ** Decidability of page table bit map*)  
  Remark PTBitT_dec: forall ptb, {ptb = PTTrue} + {~ ptb = PTTrue}.
  Proof.
    intros.
    decide equality.
  Qed.

  Remark PTBitF_dec: forall ptb, {ptb = PTFalse} + {~ ptb = PTFalse}.
  Proof.
    intros.
    decide equality.
  Qed.

  Remark PTBitU_dec: forall ptb, {ptb = PTBUndef} + {~ ptb = PTBUndef}.
  Proof.
    intros.
    decide equality.
  Qed.

  Definition PTB_false (ptb: PTBitMap) (lo high: Z) :=
    forall i , lo <= i < high -> (ZMap.get i ptb = PTFalse).

  Remark PTB_false_dec:
    forall ptb lo high, {PTB_false ptb lo high} + {~PTB_false ptb lo high }.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {PTB_false ptb lo (lo+n)} + {~PTB_false ptb lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    destruct (PTBitF_dec (ZMap.get (lo+z) ptb)).
    left.
    unfold PTB_false in *.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply p. 
    omega. 
    right; red; intro. 
    elim n. 
    unfold PTB_false in H0.
    apply H0. 
    omega. 
    right; red; intro. 
    elim n. 
    unfold PTB_false in *.
    intros.
    apply H0. 
    omega. 
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.

  Definition PTB_defined (ptb: PTBitMap) (lo high: Z) :=
    forall i , lo <= i < high -> ~ (ZMap.get i ptb = PTBUndef).

  Remark PTB_defined_dec:
    forall ptb lo high, {PTB_defined ptb lo high} + {~PTB_defined ptb lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {PTB_defined ptb lo (lo+n)} + {~PTB_defined ptb lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    unfold PTB_defined in *.
    destruct (PTBitU_dec (ZMap.get (lo+z) ptb)).
    right; red; intro.
    assert (Hofs: lo <= (lo + z) < lo + Z.succ z) by omega.
    specialize (H0 _ Hofs).
    elim H0.
    trivial.

    left.
    intros.
    destruct (zeq i (lo + z)). 
    congruence. 
    apply p. 
    omega. 

    right; red; intro. 
    elim n. 
    unfold PTB_defined in *.
    intros.
    apply H0. 
    omega. 
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.
  
  Definition PTBMap_init (ptb: PTBitMap) (n:Z):=
    (ZMap.get 0 ptb = PTTrue) /\ PTB_false ptb 1 n.
  
  Remark PTBMap_init_dec:
    forall ptb n, {PTBMap_init ptb n} + {~PTBMap_init ptb n}.
  Proof.
    intros.
    unfold PTBMap_init.
    destruct (PTBitT_dec (ZMap.get 0 ptb)).
    destruct (PTB_false_dec ptb 1 n).
    left.
    auto.
    right.
    red; intros.
    elim n0.
    inversion H.
    auto.
    right.
    red; intros.
    elim n0.
    inversion H.
    trivial.
  Qed.

  (** * Correctness of algorithms to calculate data types*)
  (** ** Correctness of calculate allocation table*)
  Fixpoint Calculate_AT (n:nat) (nps: Z) (mm:MMTable) (size:Z) (At: ATable) : ATable :=
    match n with
      | O => ZMap.set (Z.of_nat n) (ATValid false ATKern) At
      | S k => if Z_le_dec kern_low (Z.of_nat (S k))
               then if Z_lt_dec (Z.of_nat (S k)) (Z.min kern_high nps)
                    then if MM_kern_valid_dec mm (Z.of_nat (S k)) size
                         then ZMap.set (Z.of_nat (S k)) (ATValid false ATNorm) (Calculate_AT k nps mm size At)
                         else ZMap.set (Z.of_nat (S k)) (ATValid false ATResv) (Calculate_AT k nps mm size At)
                    else  ZMap.set (Z.of_nat (S k)) (ATValid false ATKern) (Calculate_AT k nps mm size At)
               else  ZMap.set (Z.of_nat (S k)) (ATValid false ATKern) (Calculate_AT k nps mm size At)
    end.
  
  Definition Cal_at_Well (x:Z) :=
    forall n m i nps mm size,
      0<= i
      -> i<= n <= m
      -> m - n = x
      -> ZMap.get i (Calculate_AT (Z.to_nat n) nps mm size (ZMap.init ATUndef))
         =ZMap.get i (Calculate_AT (Z.to_nat (m)) nps mm size (ZMap.init ATUndef)).

  
  Lemma cal_at_correct':
    forall x, 0<= x-> Cal_at_Well x.
  Proof.
    apply natlike_rec2.
    unfold Cal_at_Well.
    intros.
    assert(HP: m = n).
    omega.
    subst m.
    trivial.
    
    intros.
    unfold Cal_at_Well in *.
    intros.
    specialize (H0 n (Z.pred m) i nps mm size).
    assert(HM: i <= n <= m-1).
    omega.
    assert(HN: Z.pred m -n = z).
    omega.
    specialize (H0 H1 HM HN).
    rewrite H0.
    unfold Calculate_AT.
    case_eq (Z.to_nat m).
    intros.
    assert(HZM: (Z.to_nat (Z.pred m)) = 0%nat).
    rewrite Z2Nat.inj_pred.
    omega.
    rewrite HZM.
    trivial.
    fold Calculate_AT.
    
    intros.
    assert(HZM: Z.to_nat (Z.pred m) = n0).
    rewrite Z2Nat.inj_pred.
    omega.
    rewrite HZM.
    assert(HNOT:   i <> Z.of_nat (S n0)).
    red.
    rewrite <- H4.
    erewrite Z2Nat.id.
    intros.
    omega.
    omega.

    destruct ( Z_le_dec kern_low (Z.of_nat (S n0))).
    destruct ( Z_lt_dec (Z.of_nat (S n0)) (Z.min kern_high nps)).
    destruct (MM_kern_valid_dec mm (Z.of_nat (S n0)) size).
    erewrite ZMap.gso; trivial.
    
    erewrite ZMap.gso; trivial.

    erewrite ZMap.gso; trivial.

    erewrite ZMap.gso; trivial.
  Qed.  
  
  Lemma cal_at_correct_kern: 
    forall nps mm size,
      0< kern_low <= nps -> kern_low < kern_high -> AT_kern_l (Calculate_AT (Z.to_nat (nps-1)) nps mm size (ZMap.init ATUndef)) nps.
  Proof.
    intros.
    unfold AT_kern_l.
    intros.
    specialize (cal_at_correct' (nps-1 -i)).
    intros.
    assert(HT: 0 <= nps - 1 - i).
    omega.
    specialize (H2 HT).
    unfold Cal_at_Well in H2.
    specialize (H2 i (nps -1) i nps mm size).

    destruct H1 as [HH |HH].
    rewrite <- H2; try omega.
    clear H2.
    unfold Calculate_AT.
    case_eq (Z.to_nat i).
    intros.
    assert(HI: i = 0).
    case_eq (Z_eq_dec i 0).
    intros.
    trivial.
    intros.
    assert(HI: 0< i).
    omega.
    specialize (Z2Nat.inj_lt 0 i).
    intros.
    assert(HI1: 0<=0).
    omega.
    assert(HI2:0<=i).
    omega.
    specialize (H3 HI1 HI2).
    inv H3.
    specialize (H4 HI).
    rewrite H1 in H4.
    omega.
    
    subst i.
    rewrite Nat2Z.inj_0.
    apply ZMap.gss.
    
    fold Calculate_AT.
    intros.
    rewrite <- H1.
    rewrite Z2Nat.id; try omega.
    case_eq (Z_le_dec kern_low i).
    intros.
    omega.
    intros.
    apply ZMap.gss.    
    
    rewrite <- H2; try omega.
    clear H2.
    unfold Calculate_AT.
    case_eq (Z.to_nat i).
    intros.
    specialize (Z2Nat.inj_lt 0 i).
    intros.
    assert(HI1: 0<=0).
    omega.
    assert(HI2:0<=i).
    omega.
    specialize (H2 HI1 HI2).
    inv H2.
    assert(HI: 0< i).
    omega.
    specialize (H3 HI).
    rewrite H1 in H3.
    omega.
    
    fold Calculate_AT.
    intros.
    rewrite <- H1.
    rewrite Z2Nat.id; try omega.
    case_eq (Z_le_dec kern_low i).
    intros.
    case_eq (Z_lt_dec i (Z.min kern_high nps)).
    intros.
    case_eq (Z_le_dec kern_high nps).
    intros.
    assert(HP: Z.min kern_high nps = kern_high).
    rewrite Z.min_l; trivial.
    omega.
    
    intros.
    omega.
    
    intros.
    apply ZMap.gss.
    
    intros.
    omega.
  Qed.

  Lemma cal_at_correct_usr: 
    forall nps mm size,
      0< kern_low <= nps -> kern_low < kern_high -> AT_usr_l (Calculate_AT (Z.to_nat (nps-1)) nps mm size (ZMap.init ATUndef)) nps.
  Proof.
    intros.
    unfold AT_usr_l.
    intros.
    assert(HIN: i < nps).
    case_eq (Z_le_dec kern_high nps).
    intros.
    rewrite Z.min_l in H1; trivial.
    omega.
    
    intros.
    rewrite Z.min_r in H1; omega.

    specialize (cal_at_correct' (nps-1 -i)).
    intros.
    assert(HT: 0 <= nps - 1 - i).
    omega.
    specialize (H2 HT).
    unfold Cal_at_Well in H2.
    specialize (H2 i (nps -1) i nps mm size).

    rewrite <- H2; try omega.
    clear H2.
    exists false.
    unfold Calculate_AT.
    case_eq (Z.to_nat i).
    intros.
    specialize (Z2Nat.inj_lt 0 i).
    intros.
    assert(HI1: 0<=0).
    omega.
    assert(HI2:0<=i).
    omega.
    specialize (H3 HI1 HI2).
    inv H3.
    assert(HI: 0< i).
    omega.
    specialize (H4 HI).
    rewrite H2 in H4.
    omega.
    
    fold Calculate_AT.
    intros.
    rewrite <- H2.
    rewrite Z2Nat.id; try omega.
    case_eq (Z_le_dec kern_low i).
    intros.
    case_eq (Z_lt_dec i (Z.min kern_high nps)).
    intros.
    destruct ( MM_kern_valid_dec mm i size).
    left.
    apply ZMap.gss.
    right.
    apply ZMap.gss.
    
    intros.
    omega.
    intros.
    omega.
  Qed.

  Lemma min_ex: forall (P: Z -> Prop) lo hi,
                  (forall n, {P n} + {~ P n}) ->
                  {n : Z | lo <= n < hi /\ P n /\ forall n', lo <= n' < n -> ~ P n'} +
                  {forall n, lo <= n < hi -> ~ P n}.
  Proof.
    intros.
    assert(HP: forall k, 
                 0 <= k -> {n : Z | lo <= n < lo + k /\ P n /\ (forall n' : Z, lo <= n' < n -> ~ P n')} +
                          {(forall n : Z, lo <= n < lo + k -> ~ P n)}).
    apply natlike_rec2.
    right.
    intros.
    omega.

    intros z HR HT.
    destruct HT.
    left.
    destruct s as [n[HT HM]].
    exists n.
    split; trivial.
    omega.
    
    specialize (H (lo + z)).
    destruct H.
    left.
    exists (lo + z).
    split; auto.
    omega.

    right.
    intros.
    destruct (zeq n1 (lo + z)).
    subst.
    trivial.
    apply n.
    omega.

    destruct (zlt lo hi).
    replace hi with (lo + (hi - lo)) by omega. apply HP. omega.
    right; intros. omegaContradiction. 

  Qed.

  (** ** Find the first free page*)  
  Definition first_free (At: ATable) (size: Z) :
    {n| 0<= n < size /\ ZMap.get n At = ATValid false ATNorm /\ forall x, 0 <= x< n -> ~ ZMap.get x At = ATValid false ATNorm }
    + {forall x, 0 <= x < size -> ~ ZMap.get x At = ATValid false ATNorm}.
  Proof.
    eapply min_ex.
    intros.
    apply AT_dec.
  Defined.
  
  (** ** Find the first free page table*)  
  Definition first_free_PT (pb: PTBitMap) (size: Z) :
    {n| 0<= n < size /\ ~ (ZMap.get n pb = PTTrue) /\ forall x, 0 <= x< n -> ZMap.get x pb = PTTrue }
    + {forall x, 0 <= x < size -> ZMap.get x pb = PTTrue}.
  Proof.
    specialize (min_ex (fun n:Z => ~ ZMap.get n pb = PTTrue) 0 size).
    intros HT.
    assert (HDEC: forall n : Z, {ZMap.get n pb <> PTTrue} + {~ ZMap.get n pb <> PTTrue}).
    intros.
    destruct (PTBitT_dec (ZMap.get n pb)).
    rewrite e.
    right.
    red; intros.
    elim H.
    trivial.
    left; trivial.
    specialize (HT HDEC).
    destruct HT.
    left.
    destruct s as [n[HT1[HT2 HT3]]].
    exists n.
    split; trivial.
    split; trivial.
    intros.
    specialize (HT3 _ H).
    destruct (ZMap.get x pb).
    elim HT3.
    red; intros.
    inv H0.
    trivial.
    elim HT3.
    red; intros.
    inv H0.

    right.
    intros.
    specialize (n _ H).
    destruct (ZMap.get x pb).
    elim n.
    red; intros.
    inv H0.
    trivial.
    elim n.
    red; intros.
    inv H0.
  Defined.
  
End DataType.

Definition max_unsigned_value :=
  Eval compute in Int.max_unsigned.

Ltac xomega :=
  change Int.max_unsigned with max_unsigned_value in *;
  unfold max_unsigned_value in *;
  unfold PDX in *;
  unfold PTX in *;
  unfold adr_low in *;
  unfold adr_high in *;
  change one_k with 1024 in *;
  XOmega.xomega.
