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
(*              Definition of FlatMeory                                *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the flat memory model (the high memory [from 1G to 3G]) definition and its operations.*)

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Export Memdata.
Require Import AST.
Require Import Values.
Require Import AuxStateDataType.
Require Import Constant.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (ZMap.get b a) (at level 1).

Module FlatMem.

  (** * Flatmem definition and operations*)
  Inductive flatmem_val :=
  | HUndef
  | HByte: byte -> flatmem_val.

  Definition flatmem := ZMap.t flatmem_val. 

  (** empty flatmem*)
  Definition empty_flatmem : flatmem := ZMap.init HUndef.

  (** ** Memory reads. *)
  (** Convert the flatmem_val to mem_val*)
  Definition FlatMem2MemVal (hv: flatmem_val): memval :=
    match hv with
      | HUndef => Undef
      | HByte b => Byte b
    end.

  (** Reading N adjacent bytes in the flatmem start from address [p]. *)
  Fixpoint getN (n: nat) (p: Z) (c: flatmem) {struct n}: list memval :=
    match n with
      | O => nil
      | S n' => (FlatMem2MemVal c#p) :: getN n' (p + 1) c
    end.

  (** [load chunk h addr] perform a read in flatmem state [h], at address
  [addr].  It returns the value of the memory chunk
  at that address. [None] is returned if the accessed bytes
  are not readable. *)
  Definition load (chunk: memory_chunk) (h: flatmem) (addr: Z): val :=
    (decode_val chunk (getN (size_chunk_nat chunk) addr h)).

  (** [loadv chunk h addr] is similar, but the address [addr] must be a pure address (int value). *)
  Definition loadv (chunk: memory_chunk) (h: flatmem) (addr: val) : option val :=
    match addr with
      | Vint n => Some (load chunk h (Int.unsigned n))
      | _ => None
    end.

  (** [loadbytes h addr n] reads [n] consecutive bytes starting at
  location [addr].  Returns [None] if the accessed locations are
  not readable. *)
  Definition loadbytes (h: flatmem) (addr n: Z): (list memval) :=
    (getN (nat_of_Z n) addr h).

  (** ** Memory stores. *)
  (** Convert the mem_val to flatmem_val*)
  Definition Mem2FlatMemVal (mv: memval): flatmem_val :=
    match mv with
      | Byte b => (HByte b)
      | _ => HUndef
    end.

  (** Writing N adjacent bytes in the flatmem start from address [p]. *)
  Fixpoint setN (vl: list memval) (p: Z) (c: flatmem) {struct vl}: flatmem :=
    match vl with
      | nil => c
      | v :: vl' => setN vl' (p + 1) (ZMap.set p (Mem2FlatMemVal v) c)
    end.

  (** [store chunk h addr v] perform a write in flatmem state [h].
  Value [v] is stored at address [addr].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)
  Definition store (chunk: memory_chunk) (h: flatmem) (addr: Z) (v: val): flatmem :=
    setN (encode_val chunk v) addr h.

  (** [storev chunk h addr v] is similar, but the address [addr] must be a pure address (int vaule). *)
  Definition storev (chunk: memory_chunk) (h: flatmem) (addr v: val) : option flatmem :=
    match addr with
      | Vint n => Some (store chunk h (Int.unsigned n) v)
      | _ => None
    end.

  (** [storebytes h addr bytes] stores the given list of bytes [bytes]
  starting at location [addr].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
  Definition storebytes (h: flatmem) (addr: Z) (bytes: list memval) : flatmem :=
    (setN bytes addr h).

  (** ** Properties related to [load] *)
  Lemma load_result:
    forall chunk h addr v,
      load chunk h addr = v ->
      v = decode_val chunk (getN (size_chunk_nat chunk) addr h).
  Proof.
    intros until v. unfold load. 
    intros.
    congruence.
  Qed.
  
  Theorem load_type:
    forall h chunk addr v,
      load chunk h addr = v ->
      Val.has_type v (type_of_chunk chunk).
  Proof.
    intros. exploit load_result; eauto; intros. rewrite H0. 
    apply decode_val_type. 
  Qed.

  Theorem load_cast:
    forall h chunk addr v,
      load chunk h addr = v ->
      match chunk with
        | Mint8signed => v = Val.sign_ext 8 v
        | Mint8unsigned => v = Val.zero_ext 8 v
        | Mint16signed => v = Val.sign_ext 16 v
        | Mint16unsigned => v = Val.zero_ext 16 v
        | Mfloat32 => v = Val.singleoffloat v
        | _ => True
      end.
  Proof.
    intros. exploit load_result; eauto.
    set (l := getN (size_chunk_nat chunk) addr h).
    intros. subst v. apply decode_val_cast. 
  Qed.

  Theorem load_int8_signed_unsigned:
    forall h addr,
      load Mint8signed h addr = (Val.sign_ext 8) (load Mint8unsigned h addr).
  Proof.
    intros. unfold load.
    change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
    set (cl := getN (size_chunk_nat Mint8unsigned) addr h).
    unfold decode_val. 
    destruct (proj_bytes cl); auto.
    simpl. decEq.
    rewrite Int.sign_ext_zero_ext. 
    trivial.
    omega.
  Qed.

  Theorem load_int16_signed_unsigned:
    forall m ofs,
      load Mint16signed m ofs = (Val.sign_ext 16) (load Mint16unsigned m ofs).
  Proof.
    intros. unfold load.
    change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
    set (cl := getN (size_chunk_nat Mint16unsigned) ofs m).
    unfold decode_val. 
    destruct (proj_bytes cl); auto.
    simpl. decEq.  rewrite Int.sign_ext_zero_ext. auto. 
    omega.
  Qed.

(*
  Theorem load_float64al32:
    forall m ofs v,
      load Mfloat64 m ofs = v -> load Mfloat64al32 m ofs = v.
  Proof.
    unfold load; intros. 
    unfold decode_val in *.
    change  (size_chunk_nat Mfloat64al32) with (size_chunk_nat Mfloat64).
    set (cl:= (getN (size_chunk_nat Mfloat64) ofs m)) in *.
    destruct (proj_bytes cl); auto.
  Qed.

  Theorem loadv_float64al32:
    forall m a v,
      loadv Mfloat64 m a = Some v -> loadv Mfloat64al32 m a = Some v.
  Proof.
    unfold loadv; intros. destruct a; auto. 
  Qed.
*)

  (** ** Properties related to [loadbytes] *)
  Theorem loadbytes_load:
    forall chunk m  ofs bytes,
      loadbytes m ofs (size_chunk chunk) = bytes ->
      (align_chunk chunk | ofs) ->
      load chunk m ofs = (decode_val chunk bytes).
  Proof.
    unfold loadbytes, load; intros. 
    auto.

    unfold size_chunk.
    unfold size_chunk_nat.
    rewrite H.
    trivial.
  Qed.

  Theorem load_loadbytes:
    forall chunk m ofs v,
      load chunk m ofs = v ->
      exists bytes, loadbytes m ofs (size_chunk chunk) = bytes
                    /\ v = decode_val chunk bytes.
  Proof.
    intros. 
    unfold load in H.
    exists (getN (size_chunk_nat chunk) ofs m); split.
    unfold loadbytes. 
    unfold size_chunk_nat.
    trivial.
    auto.
  Qed.

  Lemma getN_length:
    forall c n p, length (getN n p c) = n.
  Proof.
    induction n; simpl; intros. auto. decEq; auto.
  Qed.

  Theorem loadbytes_length:
    forall m ofs n bytes,
      loadbytes m ofs n = bytes ->
      length bytes = nat_of_Z n.
  Proof.
    unfold loadbytes; intros.
    inv H.
    apply getN_length.
  Qed.

  Theorem loadbytes_empty:
    forall m ofs n,
      n <= 0 -> loadbytes m ofs n = nil.
  Proof.
    intros. unfold loadbytes.  rewrite nat_of_Z_neg; auto.
  Qed.

  Lemma getN_emptymem:
    forall n ofs,
      getN n ofs empty_flatmem = list_repeat n Undef.
  Proof.
    induction n; intros; simpl.
    - reflexivity.
    - decEq.
      + unfold empty_flatmem.
        rewrite ZMap.gi. reflexivity.
      + eauto.      
  Qed.

  Lemma loadbytes_emptymem:
    forall ofs len,
      loadbytes empty_flatmem ofs len = (list_repeat (nat_of_Z len) Undef).
  Proof.
    intros. 
    unfold loadbytes.
    eapply getN_emptymem.
  Qed.
  
  Lemma getN_concat:
    forall c n1 n2 p,
      getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z_of_nat n1) c.
  Proof.
    induction n1; intros.
    simpl. decEq. omega.
    rewrite inj_S. simpl. decEq.
    replace (p + Zsucc (Z_of_nat n1)) with ((p + 1) + Z_of_nat n1) by omega.
    auto. 
  Qed.

  Theorem loadbytes_concat:
    forall m ofs n1 n2 bytes1 bytes2,
      loadbytes m ofs n1 = bytes1 ->
      loadbytes m (ofs + n1) n2 = bytes2 ->
      n1 >= 0 -> n2 >= 0 ->
      loadbytes m ofs (n1 + n2) = (bytes1 ++ bytes2).
  Proof.
    unfold loadbytes; intros.
    inv H.
    rewrite Z2Nat.inj_add; try omega.
    rewrite getN_concat. rewrite nat_of_Z_eq; auto.
  Qed.

  Theorem loadbytes_split:
    forall m ofs n1 n2 bytes,
      loadbytes m ofs (n1 + n2) = bytes ->
      n1 >= 0 -> n2 >= 0 ->
      exists bytes1, exists bytes2,
                       loadbytes m ofs n1 = bytes1 
                       /\ loadbytes m (ofs + n1) n2 = bytes2
                       /\ bytes = bytes1 ++ bytes2.
  Proof.
    unfold loadbytes; intros. 
    rewrite nat_of_Z_plus in H; auto. rewrite getN_concat in H.
    rewrite nat_of_Z_eq in H; auto.
    econstructor; econstructor.
    split. reflexivity. split. reflexivity. congruence.
  Qed.

  Theorem load_rep:
    forall ch m1 m2 ofs v1 v2, 
      (forall z, 0 <= z < size_chunk ch -> m1#(ofs+z) = m2#(ofs+z)) ->
      load ch m1 ofs = v1 ->
      load ch m2 ofs = v2 ->
      v1 = v2.
  Proof.
    intros.
    apply load_result in H0.
    apply load_result in H1.
    subst.
    f_equal.
    rewrite size_chunk_conv in H.
    remember (size_chunk_nat ch) as n; clear Heqn.
    revert ofs H; induction n; intros; simpl; auto.
    f_equal.
    rewrite inj_S in H.
    replace ofs with (ofs+0) by omega.
    rewrite  H; try omega.
    trivial.
    apply IHn.
    intros.
    rewrite <- Zplus_assoc.
    apply H.
    rewrite inj_S. omega.
  Qed.

  Theorem load_rep':
    forall ch m1 m2 ofs1 ofs2 v1 v2, 
      (forall z, 0 <= z < size_chunk ch -> m1#(ofs1+z) = m2#(ofs2+z)) ->
      load ch m1 ofs1 = v1 ->
      load ch m2 ofs2 = v2 ->
      v1 = v2.
  Proof.
    intros.
    apply load_result in H0.
    apply load_result in H1.
    subst.
    f_equal.
    rewrite size_chunk_conv in H.
    remember (size_chunk_nat ch) as n; clear Heqn.
    revert ofs1 ofs2 H; induction n; intros; simpl; auto.
    f_equal.
    rewrite inj_S in H.
    replace ofs1 with (ofs1+0) by omega.
    replace ofs2 with (ofs2+0) by omega.
    rewrite H; try omega.
    trivial.
    apply IHn.
    intros.
    repeat rewrite <- Zplus_assoc.
    apply H.
    rewrite inj_S. omega.
  Qed.

  Lemma proj_pointer_undef: 
    forall n addr h,
      proj_pointer (getN n addr h) = Vundef.
  Proof.
    intros.
    unfold proj_pointer.
    destruct n.
    simpl.
    trivial.
    
    unfold getN.
    unfold FlatMem2MemVal.
    destruct (ZMap.get addr h); trivial.
  Qed.

  Lemma load_valid: 
    forall h t addr b ofs,
      (load t h addr) = Vptr b ofs
      -> False.
  Proof.
    intros.
    unfold load in H.
    unfold decode_val in H.
    rewrite proj_pointer_undef in H.
    destruct (proj_bytes (getN (size_chunk_nat t) addr h)).
    destruct t; inv H.
    destruct t; inv H.
  Qed.

  Lemma load_inject:
    forall j chunk h l,
      val_inject j (load chunk h l) (load chunk h l).
  Proof.
    intros.
    destruct (load chunk h l) as [] eqn:VAL; auto.
    exfalso; eapply load_valid; eauto.
  Qed.

  Remark setN_other:
    forall vl c p q,
      (forall r, p <= r < p + Z_of_nat (length vl) -> r <> q) ->
      ZMap.get q (setN vl p c) = ZMap.get q c.
  Proof.
    induction vl; intros; simpl.
    auto. 
    simpl length in H. rewrite inj_S in H.
    transitivity (ZMap.get q (ZMap.set p (Mem2FlatMemVal a) c)).
    apply IHvl. intros. apply H. omega.
    apply ZMap.gso. apply not_eq_sym. apply H. omega. 
  Qed.

  Remark setN_outside:
    forall vl c p q,
      q < p \/ q >= p + Z_of_nat (length vl) ->
      ZMap.get q (setN vl p c) = ZMap.get q c.
  Proof.
    intros. apply setN_other. 
    intros. omega. 
  Qed.

  (*Remark FlatMem_correct:
    forall a,
      FlatMem2MemVal (Mem2FlatMemVal a) = a.
  Proof.
    unfold FlatMem2MemVal, Mem2FlatMemVal.
    destruct a.*)

  Lemma getN_setN_list_undef:
    forall n p c,
      getN (length (list_repeat n Undef)) p
           (setN (list_repeat n Undef) p c) =
      list_repeat (length (list_repeat n Undef)) Undef.
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. intros.
      decEq.
      + rewrite setN_outside. 
        * rewrite ZMap.gss. reflexivity.
        * left. omega.
      + apply IHn.
  Qed.

  Lemma getN_setN_list_bytes:
    forall vl p c,
      getN (length (inj_bytes vl)) p
      (setN (inj_bytes vl) p c) = inj_bytes vl.
  Proof.
    induction vl.
    - simpl. reflexivity.
    - simpl. intros.
      decEq.
      + rewrite setN_outside. 
        * rewrite ZMap.gss. reflexivity.
        * left. omega.
      + apply IHvl.
  Qed.

  Lemma getN_setN_list_pointer:
    forall n b i p c,
      getN (length (inj_pointer n b i)) p (setN (inj_pointer n b i) p c) =
      list_repeat (length (inj_pointer n b i)) Undef.
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. intros.
      decEq.
      + rewrite setN_outside. 
        * rewrite ZMap.gss. reflexivity.
        * left. omega.
      + apply IHn.
  Qed.

  Remark getN_setN_same:
    forall v p c chunk,
      getN (length (encode_val chunk v)) p (setN (encode_val chunk v) p c) = (encode_val chunk v) \/
      getN (length (encode_val chunk v)) p (setN (encode_val chunk v) p c) = list_repeat (length (encode_val chunk v)) Undef.
  Proof.
    Opaque list_repeat inj_pointer inj_bytes.
    destruct chunk; destruct v; simpl;
    try (right; apply getN_setN_list_undef);
    try (left; apply getN_setN_list_bytes).
    right. apply getN_setN_list_pointer.
  Qed.

  (*Remark getN_setN_disjoint:
    forall vl q c n p,
      Intv.disjoint (p, p + Z_of_nat n) (q, q + Z_of_nat (length vl)) ->
      getN n p (setN vl q c) = getN n p c.
  Proof.
    intros. apply getN_exten. intros. apply setN_other.
    intros; red; intros; subst r. eelim H; eauto. 
  Qed.*)

  Remark getN_exten:
    forall c1 c2 n p,
      (forall i, p <= i < p + Z_of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
      getN n p c1 = getN n p c2.
  Proof.
    induction n; intros. 
    - auto. 
    - rewrite inj_S in H. simpl. decEq.
      + assert (HW: c1 # p = c2 # p).
        {
          apply H. omega. 
        }
        rewrite HW. reflexivity.
      + apply IHn. intros. apply H. omega.
  Qed.
 
  Remark getN_setN_outside:
    forall vl q c n p,
      p + Z_of_nat n <= q \/ q + Z_of_nat (length vl) <= p ->
      getN n p (setN vl q c) = getN n p c.
  Proof.
    intros. apply getN_exten.
    intros. apply setN_other.
    red; intros; subst.
    eelim H; intros; omega.
  Qed.

  Remark getN_setN_same_int:
    forall v p c chunk,
      getN (length (encode_val chunk (Vint v))) p (setN (encode_val chunk (Vint v)) p c) = 
      (encode_val chunk (Vint v)).
  Proof.
    Opaque list_repeat inj_pointer inj_bytes.
    destruct chunk; simpl;
    try (apply getN_setN_list_bytes);
    try (apply getN_setN_list_undef).
  Qed.

  (** ** Properties related to [store] *)
  Section STORE.

    Variable chunk: memory_chunk.
    Variable m1: flatmem.
    Variable ofs: Z.
    Variable v: val.
    Variable m2: flatmem.
    Hypothesis STORE: store chunk m1 ofs v = m2.

    Lemma store_flatmem_contents: 
      m2 = (setN (encode_val chunk v) ofs m1).
    Proof.
      unfold store in STORE. 
      auto.
    Qed.

    Lemma loadbytes_store_same:
      loadbytes m2 ofs (size_chunk chunk) = encode_val chunk v
      \/ loadbytes m2 ofs (size_chunk chunk) = list_repeat (length (encode_val chunk v)) Undef.
    Proof.
      intros.
      unfold loadbytes. rewrite store_flatmem_contents; simpl. 
      replace (nat_of_Z (size_chunk chunk)) with (length (encode_val chunk v)).
      - eapply getN_setN_same.
      - rewrite encode_val_length. auto.
    Qed.

    Lemma loadbytes_store_other:
      forall ofs' n,
        n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
        loadbytes m2 ofs' n = loadbytes m1 ofs' n.
    Proof.
      intros. unfold loadbytes. 
      rewrite store_flatmem_contents; simpl.
      destruct (zle n 0).
      - rewrite (nat_of_Z_neg _ l). auto.
      - destruct H. 
        + omega.
        + apply getN_setN_outside. rewrite encode_val_length.
          rewrite <- size_chunk_conv.
          rewrite nat_of_Z_eq. assumption. 
          omega. 
    Qed.

    Lemma load_store_same:
      forall h ofs i,
        load Mint32 (store Mint32 h ofs (Vint i)) ofs = Vint i.
    Proof.
      intros. unfold load, store. 
      replace (size_chunk_nat Mint32) with (length (encode_val Mint32 (Vint i))).                          
      - rewrite getN_setN_same_int.
        specialize (decode_encode_val_general (Vint i) Mint32 Mint32).
        simpl. trivial.
      - rewrite encode_val_length. reflexivity.
    Qed.

    Lemma load_store_other:
      forall chunk m1 m2 ofs v chunk' ofs',
        store chunk m1 ofs v = m2 ->
        ofs' + (size_chunk chunk') <= ofs \/ ofs + size_chunk chunk <= ofs' ->
        load chunk' m2 ofs' = load chunk' m1 ofs'.
    Proof.
      unfold load, store. intros. rewrite <- H.
      rewrite getN_setN_outside. reflexivity. 
      rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
      assumption.
    Qed.

  End STORE.

  (** * Flatmem injection *)
  Inductive flatmem_val_inject  : flatmem_val -> flatmem_val -> Prop :=
    flatmemval_inject_byte : forall n : byte, flatmem_val_inject (HByte n) (HByte n)
  | flatmemval_inject_undef : forall mv : flatmem_val, flatmem_val_inject HUndef mv.

  Definition flatmem_inj (h1 h2: flatmem) :=
    forall addr, flatmem_val_inject h1#addr h2#addr.

  (*Definition flatmem_pperm_inj (p: PPermT) (h1 h2: flatmem) :=
    forall addr, 
      (forall o, ZMap.get (PageI addr) p <> PGHide o) ->
      FlatMem.flatmem_val_inject h1#addr h2#addr.*)

  Lemma getN_inj:
    forall f m1 m2,
      flatmem_inj m1 m2 ->
      forall n ofs,
        list_forall2 (memval_inject f) 
                     (getN n ofs m1)
                     (getN n ofs m2).
  Proof.
    induction n; intros; simpl.
    constructor.
    constructor.
    unfold flatmem_inj in H.
    specialize (H ofs).
    destruct (m1 # ofs).
    constructor.
    inv H.
    constructor.
    specialize (IHn (ofs +1)).
    trivial.
  Qed.

  (*Lemma getN_pperm_inj:
    forall f m1 m2 p,
      flatmem_pperm_inj p m1 m2 ->
      forall n ofs,
        (forall ofs',
           ofs <= ofs' < ofs + (Z_of_nat n) ->
           forall o,
             ZMap.get (PageI ofs') p <> PGHide o) ->
        list_forall2 (memval_inject f) 
                     (getN n ofs m1)
                     (getN n ofs m2).
  Proof.
    induction n; intros; simpl.
    - constructor.
    - constructor.
      + unfold flatmem_pperm_inj in H.
        assert (HOS: ofs <= ofs < ofs + Z.of_nat (S n)). 
        {
          rewrite Nat2Z.inj_succ. omega.
        }
        specialize (H0 _ HOS).
        specialize (H _ H0).
        destruct (m1 # ofs).
        * constructor.
        * inv H. constructor.
      + eapply IHn. intros. eapply H0.
        rewrite Nat2Z.inj_succ. omega.
  Qed.*)

  Lemma load_inj:
    forall m1 m2 chunk ofs v1 f,
      flatmem_inj  m1 m2 ->
      load chunk m1 ofs = v1 ->
      exists v2, load chunk m2 ofs = v2 /\ val_inject f v1 v2.
  Proof.
    intros.
    unfold load in *.
    exists (decode_val chunk (getN (size_chunk_nat chunk) ofs m2)).
    split; trivial.
    rewrite <- H0.
    apply decode_val_inject. apply getN_inj; auto. 
  Qed.

  (*Lemma load_pperm_inj:
    forall m1 m2 chunk ofs v1 f p,
      flatmem_pperm_inj p m1 m2 ->
      load chunk m1 ofs = v1 ->
      (forall ofs',
         ofs <= ofs' < ofs + (size_chunk chunk) ->
         forall o,
           ZMap.get (PageI ofs') p <> PGHide o) ->      
      exists v2, load chunk m2 ofs = v2 /\ val_inject f v1 v2.
  Proof.
    intros.
    unfold load in *.
    exists (decode_val chunk (getN (size_chunk_nat chunk) ofs m2)).
    split; trivial.
    rewrite <- H0.
    apply decode_val_inject. eapply getN_pperm_inj; eauto. 
    rewrite <- size_chunk_conv. assumption.
  Qed.*)

  Lemma setN_inj:
    forall f vl1 vl2,
      list_forall2 (memval_inject f) vl1 vl2 ->
      forall p c1 c2,
        (forall q, flatmem_val_inject (c1#q) (c2#(q))) ->
        (forall q, flatmem_val_inject ((setN vl1 p c1)#q) 
                                     ((setN vl2 (p) c2)#(q))).
  Proof.
    induction 1; intros; simpl. 
    auto.
    apply IHlist_forall2; auto. 
    intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
    rewrite ZMap.gss. 
    destruct a1.
    constructor.
    inv H.
    constructor.
    constructor.
    rewrite ZMap.gso. auto. 
    trivial.
  Qed.

  Lemma store_mapped_inj:
    forall f chunk m1 ofs v1 n1 n2 m2 v2,
      flatmem_inj m1 m2 ->
      store chunk m1 ofs v1 = n1 ->
      val_inject f v1 v2 ->
      store chunk m2 (ofs) v2 = n2 ->
      flatmem_inj n1 n2.
  Proof.
    intros.
    unfold store in *.
    rewrite <- H0.
    rewrite <- H2.
    unfold flatmem_inj in *.
    
    apply setN_inj with f; trivial.
    apply encode_val_inject; auto. 
  Qed.

  (*Lemma setN_pperm_inj:
    forall f vl1 vl2,
      list_forall2 (memval_inject f) vl1 vl2 ->
      forall p c1 c2 pp,
        (forall q, 
           (forall o, ZMap.get (PageI q) pp <> PGHide o) ->
           flatmem_val_inject (c1#q) (c2#(q))) ->
        (forall q, 
           (forall o, ZMap.get (PageI q) pp <> PGHide o) ->
           flatmem_val_inject ((setN vl1 p c1)#q) 
                              ((setN vl2 (p) c2)#(q))).
  Proof.
    induction 1; intros; simpl. 
    auto.
    eapply IHlist_forall2; eauto. 
    intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
    rewrite ZMap.gss. 
    destruct a1.
    constructor.
    inv H.
    constructor.
    constructor.
    rewrite ZMap.gso. auto. 
    trivial.
  Qed.

  Lemma store_mapped_pperm_inj:
    forall f chunk m1 ofs v1 n1 n2 m2 v2 p,
      flatmem_pperm_inj p m1 m2 ->
      store chunk m1 ofs v1 = n1 ->
      val_inject f v1 v2 ->
      store chunk m2 (ofs) v2 = n2 ->
      flatmem_pperm_inj p n1 n2.
  Proof.
    intros.
    unfold store in *.
    rewrite <- H0.
    rewrite <- H2.
    unfold flatmem_pperm_inj in *.
    intros.
    apply setN_pperm_inj with f p; auto.
    apply encode_val_inject; auto. 
  Qed.

  Lemma setN_pperm_unmapped_inj:
    forall vl2,
      forall p c1 c2 pp,
        (forall ofs', 
           p <= ofs' < p + Z.of_nat (length vl2) ->
           exists o, ZMap.get (PageI ofs') pp = PGHide o) ->
        (forall q, 
           (forall o, ZMap.get (PageI q) pp <> PGHide o) ->
           flatmem_val_inject (c1#q) (c2#(q))) ->
        (forall q, 
           (forall o, ZMap.get (PageI q) pp <> PGHide o) ->
           flatmem_val_inject (c1#q) 
                              ((setN vl2 p c2)#(q))).
  Proof.
    induction vl2; intros; simpl. 
    - eauto.
    - eapply IHvl2; eauto. 
      + intros. eapply H. Local Opaque Z.of_nat. simpl.
        rewrite Nat2Z.inj_succ. omega.
      + intros.
        destruct (zeq q0 p); subst.
        * rewrite ZMap.gss.
          exploit (H p). simpl.
          rewrite Nat2Z.inj_succ. omega.
          intros (o & HF). specialize (H2 o). congruence.
        * rewrite ZMap.gso; auto. 
  Qed.

  Lemma store_unmapped_pperm_inj:
    forall chunk m1 ofs n2 m2 v2 p,
      flatmem_pperm_inj p m1 m2 ->
      store chunk m2 (ofs) v2 = n2 ->
      (forall ofs',
         ofs <= ofs' < ofs + size_chunk chunk ->
         exists o, ZMap.get (PageI ofs') p = PGHide o) ->
      flatmem_pperm_inj p m1 n2.
  Proof.
    intros.
    unfold store in *.
    rewrite <- H0.
    unfold flatmem_pperm_inj in *.
    intros.
    apply setN_pperm_unmapped_inj with p; auto.
    rewrite encode_val_length.
    rewrite <- size_chunk_conv. assumption.
  Qed.*)

  Lemma flatmem_empty_inj: flatmem_inj empty_flatmem empty_flatmem.
  Proof.
    unfold flatmem_inj.
    intros.
    unfold empty_flatmem.
    rewrite ZMap.gi.
    constructor.
  Qed.

  (*Lemma flatmem_empty_pperm_inj: forall p, flatmem_pperm_inj p empty_flatmem empty_flatmem.
  Proof.
    unfold flatmem_pperm_inj.
    intros.
    unfold empty_flatmem.
    rewrite ZMap.gi.
    constructor.
  Qed.*)

  Definition free_page (i: Z) (c: flatmem) :=
    setN (list_repeat (Z.to_nat PgSize) Undef) (i * PgSize) c.

  Lemma setN_free_get:
    forall n i ofs c,
      i <= ofs < i + (Z.of_nat n) ->
      (setN (list_repeat n Undef) i c) # ofs = HUndef.
  Proof.
    induction n; intros.
    - Local Transparent Z.of_nat.
      simpl in H. omega.
    - Local Opaque Z.of_nat.
      rewrite Nat2Z.inj_succ in *.
      Local Transparent list_repeat. simpl.
      destruct (zeq ofs i); subst.
      + rewrite setN_other.
        * rewrite ZMap.gss. reflexivity.
        * intros. red; intros HF; subst. omega.
      + eapply IHn. omega.
  Qed.

  Lemma free_page_gss:
    forall addr h,
      ZMap.get addr (free_page (PageI addr) h) = HUndef.
  Proof.
    unfold free_page. intros.
    eapply setN_free_get.
    rewrite Z2Nat.id; [|omega].
    unfold PageI. 
    exploit (Z_div_mod_eq addr PgSize). omega.
    rewrite Zmult_comm.
    intros Hrange.
    exploit (Z_mod_lt addr PgSize). omega.
    intros Hrange'. omega.
  Qed.

  Lemma free_page_gso:
    forall addr i h,
      i <> PageI addr ->
      ZMap.get addr (free_page i h) = ZMap.get addr h.
  Proof.
    unfold free_page. intros.
    apply setN_other.
    rewrite length_list_repeat.
    rewrite Z2Nat.id; [|omega].
    red; intros; subst. elim H. clear H.
    unfold PageI. 
    assert (HP: exists a, addr = i * PgSize + a /\ 0 <= a < PgSize).
    {
      exists (addr - i * PgSize).
      split; omega.
    }
    clear H0. destruct HP as (a & Heq & Hrange).
    rewrite Heq. clear Heq.
    rewrite Z_div_plus_full_l; [| omega].
    rewrite Zdiv_small; trivial. omega. 
  Qed.    

  (*Lemma free_page_pperm_inj:
    forall pp h h',
    flatmem_pperm_inj pp h h' ->
    forall i p,
      flatmem_pperm_inj (ZMap.set i p pp) (free_page i h) h'.
  Proof.
    intros. unfold flatmem_pperm_inj in *.
    intros. destruct (zeq i (PageI addr)); subst.
    - rewrite free_page_gss.
      constructor.
    - rewrite ZMap.gso in H0; auto.
      rewrite free_page_gso; auto.
  Qed.*)

  Lemma free_page_inj:
    forall h h',
      flatmem_inj h h' ->
      forall i,
        flatmem_inj (free_page i h) h'.
  Proof.
    intros. unfold flatmem_inj in *.
    intros. destruct (zeq i (PageI addr)); subst.
    - rewrite free_page_gss.
      constructor.
    - rewrite free_page_gso; auto.
  Qed.

  Lemma free_page_inj':
    forall h h',
      flatmem_inj h h' ->
      forall i,
        flatmem_inj (free_page i h) (free_page i h').
  Proof.
    intros. unfold flatmem_inj in *.
    intros. destruct (zeq i (PageI addr)); subst.
    - rewrite free_page_gss.
      constructor.
    - repeat rewrite free_page_gso; auto.
  Qed.

  Lemma store_unmapped_inj:
    forall chunk m1 ofs n2 m2 v2 i,
      flatmem_inj m1 m2 ->
      store chunk m2 ofs v2 = n2 ->
      i * PgSize <= ofs <= i * PgSize + PgSize - (size_chunk chunk) ->
      flatmem_inj (free_page i m1) n2.
  Proof.
    intros. unfold flatmem_inj in *. intros.
    unfold store in *.
    rewrite <- H0. 
    destruct (zeq i (PageI addr)); subst.
    - rewrite free_page_gss. constructor.
    - rewrite free_page_gso; auto.
      rewrite setN_other; auto.
      intros. red; intros; subst. elim n.
      revert H0 H1. clear; intros.
      assert (HW: exists a, addr = i * PgSize + a
                            /\ 0 <= a < PgSize).
      {
        exists (addr - i * PgSize).
        specialize (size_chunk_range chunk); intros.
        rewrite encode_val_length in H0.
        rewrite <- size_chunk_conv in H0. 
        unfold ZIndexed.t in *.
        split; omega. 
      }
      revert HW; clear; intros.
      destruct HW as (a & Heq & Hrange). subst.
      unfold PageI. 
      rewrite Z_div_plus_full_l; [|omega].
      rewrite Zdiv_small. omega. assumption.
  Qed.

End FlatMem.

Notation flatmem := FlatMem.flatmem.

Section DirtyPPage.

Definition dirty_ppage (pperm: PPermT) (hp: flatmem) :=
  forall i o, ZMap.get i pperm = PGHide o -> 
              forall adr,
                ZMap.get adr hp = ZMap.get adr (FlatMem.free_page i hp).

Lemma dirty_ppage_init:
  forall h,
    dirty_ppage (ZMap.init PGUndef) h.
Proof.
  unfold dirty_ppage. intros. 
  rewrite ZMap.gi in H. congruence.
Qed.

Lemma dirty_ppage_gso:
  forall pp h,
    dirty_ppage pp h ->
    forall p,
      (forall o, p <> PGHide o) ->
      forall n,
        dirty_ppage (ZMap.set n p pp) h.
Proof.
  unfold dirty_ppage; intros.
  destruct (zeq i n); subst.
  - rewrite ZMap.gss in H1. subst.
    elim (H0 o). reflexivity.
  - rewrite ZMap.gso in H1; eauto 2.
Qed.

Lemma dirty_ppage_store_unmaped':
  forall pp h,
    dirty_ppage pp h ->
    forall i,
      ZMap.get (PageI i) pp = PGAlloc (*o*) ->
      forall v h' chunk,
        FlatMem.store chunk h i v = h' ->
        i mod PgSize <= PgSize - size_chunk chunk ->
        dirty_ppage pp h'.
Proof.
  unfold dirty_ppage in *. intros. subst.
  destruct (zeq i0 (PageI adr)); subst.
  - rewrite FlatMem.free_page_gss.
    unfold FlatMem.store.
    erewrite FlatMem.setN_other.
    + erewrite H; try apply H3.
      rewrite FlatMem.free_page_gss.
      reflexivity.
    + rewrite encode_val_length. rewrite <- size_chunk_conv.
      red; intros; subst.
      assert (HW: PageI adr = PageI i).
      {
        unfold PageI.
        assert (HW: exists a, adr = i + a
                              /\ 0 <= a < size_chunk chunk).
        {
          exists (adr - i).
          unfold ZIndexed.t in *.
          split; omega.
        }
        destruct HW as (a & Heq & Hrange); subst.
        assert (HW: exists b c, i = b * PgSize + c
                                /\ 0 <= c <= PgSize - size_chunk chunk).
        {
          rewrite (Z_div_mod_eq i PgSize); [|omega].
          rewrite (Zmult_comm PgSize (i/ PgSize)).
          esplit; esplit; split. reflexivity.
          exploit  (Z_mod_lt i PgSize). omega.
          intros (HP & _).
          split; try assumption. 
        }
        destruct HW as (b & c & Heq & Hrange'). rewrite Heq.
        replace (b * PgSize + c + a) with (b * PgSize + (c + a)) by omega.
        repeat rewrite Z_div_plus_full_l; try omega.
        repeat rewrite Zdiv_small; omega.
      }            
      congruence.
  - rewrite FlatMem.free_page_gso; trivial.
Qed.

Lemma dirty_ppage_store_unmaped:
  forall pp h,
    dirty_ppage pp h ->
    forall i,
      ZMap.get (PageI (i * 4)) pp = PGAlloc ->
      forall v h',
        FlatMem.store Mint32 h (i * 4) v = h' ->
        dirty_ppage pp h'.
Proof.
  intros. eapply dirty_ppage_store_unmaped'; try eassumption. 
  clear. simpl.
  change 4096 with (1024 * 4).
  rewrite Zmult_mod_distr_r.
  apply mod_chunk.
Qed.

Lemma dirty_ppage_gss:
  forall pp h,
    dirty_ppage pp h ->
    forall o n,
      dirty_ppage (ZMap.set n (PGHide o) pp) (FlatMem.free_page n h).
Proof.
  unfold dirty_ppage; intros.
  destruct (zeq i n); subst.
  - destruct (zeq n (PageI adr)); subst.
    + repeat rewrite FlatMem.free_page_gss.
      reflexivity.
    + repeat rewrite FlatMem.free_page_gso; auto.
  - rewrite ZMap.gso in H0; [|assumption].
    destruct (zeq n (PageI adr)); subst.
    + repeat rewrite FlatMem.free_page_gss.
      rewrite FlatMem.free_page_gso; auto.
      rewrite FlatMem.free_page_gss.               
      reflexivity.
    + destruct (zeq i (PageI adr)); subst.
      * rewrite FlatMem.free_page_gso.
        rewrite FlatMem.free_page_gss.               
        erewrite H; [| eassumption].
        rewrite FlatMem.free_page_gss.               
        reflexivity. auto.
      * repeat rewrite FlatMem.free_page_gso; auto.
Qed.

End DirtyPPage.

Section DirtyPPage'.

Definition dirty_ppage' (pperm: PPermT) (hp: flatmem) :=
  forall i, ZMap.get i pperm <> PGAlloc ->
              forall adr,
                ZMap.get adr hp = ZMap.get adr (FlatMem.free_page i hp).

Lemma dirty_ppage'_init:
  dirty_ppage' (ZMap.init PGUndef) FlatMem.empty_flatmem.
Proof.
  unfold dirty_ppage'; intros; unfold FlatMem.empty_flatmem.
  destruct (zeq (PageI adr) i); subst.
  rewrite ZMap.gi; rewrite FlatMem.free_page_gss; auto.
  rewrite FlatMem.free_page_gso; auto.
Qed.

Lemma dirty_ppage'_gso:
  forall pp h,
    dirty_ppage' pp h ->
      forall n,
        dirty_ppage' (ZMap.set n PGAlloc pp) h.
Proof.
  unfold dirty_ppage'; intros.
  destruct (zeq i n); subst.
  - rewrite ZMap.gss in H0. contradict H0; auto.
  - rewrite ZMap.gso in H0; auto.
Qed.

Lemma dirty_ppage'_store_unmapped':
  forall pp h,
    dirty_ppage' pp h ->
    forall i,
      ZMap.get (PageI i) pp = PGAlloc ->
      forall v h' chunk,
        FlatMem.store chunk h i v = h' ->
        i mod PgSize <= PgSize - size_chunk chunk ->
        dirty_ppage' pp h'.
Proof.
  unfold dirty_ppage' in *. intros. subst.
  destruct (zeq i0 (PageI adr)); subst.
  - rewrite FlatMem.free_page_gss.
    unfold FlatMem.store.
    erewrite FlatMem.setN_other.
    + erewrite H; try apply H3.
      rewrite FlatMem.free_page_gss.
      reflexivity.
    + rewrite encode_val_length. rewrite <- size_chunk_conv.
      red; intros; subst.
      assert (HW: PageI adr = PageI i).
      {
        unfold PageI.
        assert (HW: exists a, adr = i + a
                              /\ 0 <= a < size_chunk chunk).
        {
          exists (adr - i).
          unfold ZIndexed.t in *.
          split; omega.
        }
        destruct HW as (a & Heq & Hrange); subst.
        assert (HW: exists b c, i = b * PgSize + c
                                /\ 0 <= c <= PgSize - size_chunk chunk).
        {
          rewrite (Z_div_mod_eq i PgSize); [|omega].
          rewrite (Zmult_comm PgSize (i/ PgSize)).
          esplit; esplit; split. reflexivity.
          exploit  (Z_mod_lt i PgSize). omega.
          intros (HP & _).
          split; try assumption. 
        }
        destruct HW as (b & c & Heq & Hrange'). rewrite Heq.
        replace (b * PgSize + c + a) with (b * PgSize + (c + a)) by omega.
        repeat rewrite Z_div_plus_full_l; try omega.
        repeat rewrite Zdiv_small; omega.
      }            
      congruence.
  - rewrite FlatMem.free_page_gso; trivial.
Qed.

Lemma dirty_ppage'_store_unmapped:
  forall pp h,
    dirty_ppage' pp h ->
    forall i,
      ZMap.get (PageI (i * 4)) pp = PGAlloc ->
      forall v h',
        FlatMem.store Mint32 h (i * 4) v = h' ->
        dirty_ppage' pp h'.
Proof.
  intros. eapply dirty_ppage'_store_unmapped'; try eassumption. 
  clear. simpl.
  change 4096 with (1024 * 4).
  rewrite Zmult_mod_distr_r.
  apply mod_chunk.
Qed.

Lemma dirty_ppage'_gss:
  forall pp h,
    dirty_ppage' pp h ->
    forall p n,
      dirty_ppage' (ZMap.set n p pp) (FlatMem.free_page n h).
Proof.
  unfold dirty_ppage'; intros.
  destruct (zeq i n); subst.
  - destruct (zeq n (PageI adr)); subst.
    + repeat rewrite FlatMem.free_page_gss.
      reflexivity.
    + repeat rewrite FlatMem.free_page_gso; auto.
  - rewrite ZMap.gso in H0; [|assumption].
    destruct (zeq n (PageI adr)); subst.
    + repeat rewrite FlatMem.free_page_gss.
      rewrite FlatMem.free_page_gso; auto.
      rewrite FlatMem.free_page_gss.               
      reflexivity.
    + destruct (zeq i (PageI adr)); subst.
      * rewrite FlatMem.free_page_gso.
        rewrite FlatMem.free_page_gss.               
        erewrite H; [| eassumption].
        rewrite FlatMem.free_page_gss.               
        reflexivity. auto.
      * repeat rewrite FlatMem.free_page_gso; auto.
Qed.

Lemma dirty_ppage_strengthen:
  forall pp h, dirty_ppage' pp h -> dirty_ppage pp h.
Proof.
  unfold dirty_ppage', dirty_ppage; intros.
  apply H; rewrite H0; discriminate.
Qed.

End DirtyPPage'.