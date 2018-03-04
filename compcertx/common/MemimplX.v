Require compcert.common.Memimpl.
Require MemoryX.

Import Coqlib.
Import Values.
Import Memimpl.
Import MemoryX.

(** Because we need the additional [storebytes_empty] property, we
have to modify the implementation of [storebytes]... *)

Definition is_empty {A: Type} (l: list A):
  {l = nil} + {l <> nil}.
Proof.
  destruct l; (left; congruence) || (right; congruence).
Defined.

Definition storebytes m b o l :=
  if is_empty l then Some m else Memimpl.storebytes m b o l.

(** ... and we have to again prove every property of [storebytes]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Ltac storebytes_tac thm :=
  simpl; intros;
  match goal with
    | H: storebytes ?m1 _ _ ?l = Some ?m2 |- _ =>
      unfold storebytes in H;
        destruct (is_empty l);
        [ | eapply thm; eassumption ];
        subst l;
        replace m2 with m1 in * by congruence;
        clear H;
        try congruence;
        unfold Mem.range_perm, range_perm, Mem.valid_access, valid_access;
        intuition (simpl in *; omega)
  end.

Lemma range_perm_storebytes:
   forall (m1 : mem) (b : block) (ofs : Z) (bytes : list memval),
   Mem.range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
   exists m2 : mem, storebytes m1 b ofs bytes = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using range_perm_storebytes.
Qed.

Lemma encode_val_not_empty chunk v:
  encode_val chunk v <> nil.
Proof.
  generalize (encode_val_length chunk v). generalize (encode_val chunk v).
  destruct chunk; destruct l; compute; congruence.
Qed.

Lemma storebytes_store:
   forall (m1 : mem) (b : block) (ofs : Z) (chunk : AST.memory_chunk)
     (v : val) (m2 : mem),
   storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
   (align_chunk chunk | ofs) -> Mem.store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty (encode_val chunk v)); eauto using storebytes_store.
  edestruct encode_val_not_empty; eauto.
Qed.

Lemma store_storebytes:
   forall (m1 : mem) (b : block) (ofs : Z) (chunk : AST.memory_chunk)
     (v : val) (m2 : mem),
   Mem.store chunk m1 b ofs v = Some m2 ->
   storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes. intros.
  destruct (is_empty (encode_val chunk v)); eauto using store_storebytes.
  edestruct encode_val_not_empty; eauto.
Qed.

Lemma loadbytes_storebytes_same:
   forall (m1 : mem) (b : block) (ofs : Z) (bytes : list memval) (m2 : mem),
   storebytes m1 b ofs bytes = Some m2 ->
   Mem.loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using loadbytes_storebytes_same.
  subst; simpl.
  unfold loadbytes. simpl. destruct (range_perm_dec m2 b ofs (ofs + 0) Cur Readable); try reflexivity.
  destruct n. unfold range_perm. intros; omega.
Qed.

Lemma storebytes_concat: forall (m : mem) (b : block) (ofs : Z) (bytes1 : list memval)
         (m1 : mem) (bytes2 : list memval) (m2 : mem),
       storebytes m b ofs bytes1 = Some m1 ->
       storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 =
       Some m2 -> storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  unfold storebytes at 1.
  intros until m2.
  case_eq (is_empty bytes1).
  {
    intros.
    subst. inv H0.
    simpl in *.
    replace (ofs + 0) with ofs in * by omega.
    assumption.
  }
  intros.
  unfold storebytes in *.
  destruct (is_empty bytes2).
  {
    inv H1.
    rewrite <- app_nil_end.
    rewrite H.
    assumption.
  }
  exploit (Memimpl.storebytes_concat m b ofs bytes1 m1 bytes2 m2); eauto.
  intros.
  destruct bytes1; try congruence. (** HERE transparently use is_empty *)
  assumption.
Qed.

Lemma storebytes_split:
   forall (m : mem) (b : block) (ofs : Z) (bytes1 bytes2 : list memval)
     (m2 : mem),
   storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
   exists m1 : mem,
     storebytes m b ofs bytes1 = Some m1 /\
     storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 = Some m2.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty (bytes1 ++ bytes2)).
  {
    subst.
    inv H.
    destruct (app_eq_nil _ _ e). subst. simpl. eauto.
  }
  destruct (is_empty bytes1).
  {
    subst; simpl. replace (ofs + 0) with ofs in * by omega.
    simpl in *.
    destruct (is_empty bytes2); eauto.
    contradiction.
  }
  destruct (is_empty bytes2).
  {
    subst.
    rewrite <- app_nil_end in H. eauto.
  }
  eauto using storebytes_split.
Qed.

Lemma is_empty_list_forall2:
  forall (A B: Type) (P: A -> B -> Prop) l1 l2,
    list_forall2 P l1 l2 ->
    (l1 = nil <-> l2 = nil).
Proof.
  intros.
  inversion H; subst.
   tauto.
   split; discriminate.
Qed.

Lemma storebytes_within_extends:
   forall (m1 m2 : mem) (b : block) (ofs : Z) (bytes1 : list memval)
     (m1' : mem) (bytes2 : list memval),
   Mem.extends m1 m2 ->
   storebytes m1 b ofs bytes1 = Some m1' ->
   list_forall2 memval_lessdef bytes1 bytes2 ->
   exists m2' : mem,
     storebytes m2 b ofs bytes2 = Some m2' /\ Mem.extends m1' m2'.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty bytes1); destruct (is_empty bytes2); eauto using storebytes_within_extends.
  * inv H0. eauto.
  * apply is_empty_list_forall2 in H1. exfalso; tauto.
  * apply is_empty_list_forall2 in H1. exfalso; tauto.
Qed.

Lemma storebytes_mapped_inject:
   forall (f : meminj) (m1 : mem) (b1 : block) (ofs : Z)
     (bytes1 : list memval) (n1 m2 : mem) (b2 : block) 
     (delta : Z) (bytes2 : list memval),
   Mem.inject f m1 m2 ->
   storebytes m1 b1 ofs bytes1 = Some n1 ->
   f b1 = Some (b2, delta) ->
   list_forall2 (memval_inject f) bytes1 bytes2 ->
   exists n2 : mem,
     storebytes m2 b2 (ofs + delta) bytes2 = Some n2 /\
     Mem.inject f n1 n2.
Proof.
  unfold storebytes.
  intros.
  destruct (is_empty bytes1); destruct (is_empty bytes2); eauto using storebytes_mapped_inject.
  * inv H0. eauto.
  * apply is_empty_list_forall2 in H2. exfalso; tauto.
  * apply is_empty_list_forall2 in H2. exfalso; tauto.
Qed.

Lemma storebytes_empty_inject:
   forall (f : meminj) (m1 : mem) (b1 : block) (ofs1 : Z) 
     (m1' m2 : mem) (b2 : block) (ofs2 : Z) (m2' : mem),
   Mem.inject f m1 m2 ->
   storebytes m1 b1 ofs1 nil = Some m1' ->
   storebytes m2 b2 ofs2 nil = Some m2' -> Mem.inject f m1' m2'.
Proof.
  unfold storebytes; simpl; congruence.
Qed.

Lemma storebytes_unchanged_on:
   forall (P : block -> Z -> Prop) (m : mem) (b : block) 
     (ofs : Z) (bytes : list memval) (m' : mem),
   storebytes m b ofs bytes = Some m' ->
   (forall i : Z, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
   Mem.unchanged_on P m m'.
Proof.
  unfold storebytes. intros.
  destruct (is_empty bytes); eauto using Mem.storebytes_unchanged_on.
  inv H. eapply Mem.unchanged_on_refl.
Qed.

(** Additional proof not present in CompCert *)

Lemma storebytes_empty:
  forall m b ofs m',
    storebytes m b ofs nil = Some m'
    -> m' = m.
Proof.
  unfold storebytes. intros.
  destruct (is_empty nil); congruence.
Qed.

(** Because we need the additional [free_range] property, we
have to modify the implementation of [free]... *)

Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if zle hi lo then Some m else Memimpl.free m b lo hi.

(** ... and we have to again prove every property of [free]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Ltac free_tac thm :=
  simpl;
  intros;
  match goal with
    | H: free ?m1 _ ?lo ?hi = Some ?m2 |- _ =>
      unfold free in H;
        destruct (zle hi lo);
        try (eapply thm; eassumption);
        replace m2 with m1 in * by congruence;
        clear H;
        try congruence;
        unfold Mem.range_perm, range_perm, Mem.valid_access, valid_access;
        intuition omega
  end.

Lemma range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  exists m2: mem, free m1 b lo hi = Some m2.
Proof.
  unfold free. intros.
  destruct (zle hi lo); eauto using Memimpl.range_perm_free.
Qed.

Lemma free_parallel_extends:
   forall (m1 m2 : mem) (b : block) (lo hi : Z) (m1' : mem),
   extends m1 m2 ->
   free m1 b lo hi = Some m1' ->
   exists m2' : mem, free m2 b lo hi = Some m2' /\ extends m1' m2'.
Proof.
  unfold free. intros until 1.
  destruct (zle hi lo); eauto using free_parallel_extends.
  inversion 1; subst; eauto.
Qed.

(** Additional proof not present in CompCert *)

Lemma free_range:
  forall m1 m1' b lo hi,
    free m1 b lo hi = Some m1' ->
    (lo < hi)%Z \/ m1' = m1.
Proof.
  unfold free. intros.
  destruct (zle hi lo).
   right; congruence.
  left; omega.
Qed.

(** Because we need the additional [inject_neutral_incr] property, we
have to modify the implementation of [inject_neutral]... *)

Definition inject_neutral (thr: block) (m: mem) :=
  Memimpl.inject_neutral thr m /\  (forall b, Ple thr b -> forall o k p, ~ perm m b o k p).

(** ... and we have to again prove every property of [inject_neutral]
(fortunately, we can reuse the proofs in Memimpl, we just need to extend them)... *)

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) m m.
Proof.
  destruct 1; eauto using Memimpl.neutral_inject.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  split; eauto using Memimpl.empty_inject_neutral, perm_empty.
Qed.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Memimpl.alloc_inject_neutral.
  intros.
  intro. eapply perm_valid_block in H5. unfold valid_block in *. apply nextblock_alloc in H. rewrite H in H5. xomega.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  val_inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Memimpl.store_inject_neutral.
  intros. intro. eapply H2. eassumption. eauto using perm_store_2.
Qed.

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  inversion 2; subst.
  split; eauto using Memimpl.drop_inject_neutral.
  intros. intro. eapply H2. eassumption. eauto using perm_drop_4.
Qed.  

(** Additional proof not present in CompCert *)

Theorem inject_neutral_incr:
  forall m thr, inject_neutral thr m -> forall thr', Ple thr thr' -> inject_neutral thr' m.
Proof.
  intros ? ? [[] PERM].
  split.
  split.
   unfold flat_inj. intros until p. destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro. eapply mi_perm. 2: eassumption. unfold flat_inj. destruct (plt b2 thr). reflexivity. edestruct PERM. 2: eassumption. xomega.
   unfold flat_inj. intros until p. destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro. exists 0; omega.
   unfold flat_inj. intros until delta. destruct (plt b1 thr'); try discriminate. injection 1; intros until 2; subst. intro.
   intros. eapply memval_inject_incr. eapply mi_memval. 2: assumption. unfold flat_inj. destruct (plt b2 thr). reflexivity. edestruct PERM. 2: eassumption. xomega.
   unfold inject_incr. unfold flat_inj. intros until delta. destruct (plt b thr); try discriminate. injection 1; intros until 2; subst. destruct (plt b' thr'); try reflexivity. xomega.
   intros. eapply PERM. xomega.
Qed.

Theorem free_inject_neutral':
  forall m b lo hi m' thr,
  Memimpl.free m b lo hi = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  intros until 1. intros [? PERM]. intros.
  exploit free_left_inj; eauto. intro. 
  exploit free_right_inj; eauto.
  intros until p. unfold flat_inj. destruct (plt b' thr); try discriminate. injection 1; intros until 2; subst. replace (ofs + 0) with ofs by omega. intros. eapply Memimpl.perm_free_2; eauto.
  split.
   assumption.
  intros. intro. eapply PERM. eassumption. eauto using Memimpl.perm_free_3.
Qed.

Theorem storebytes_inject_neutral':
  forall m b o l m' thr,
  Memimpl.storebytes m b o l = Some m' ->
  list_forall2 (memval_inject (Mem.flat_inj thr)) l l ->
  Plt b thr ->
  inject_neutral thr m ->
  inject_neutral thr m'.
Proof.
  inversion 4; subst.
  unfold Memimpl.inject_neutral in H3.
  generalize H. intro STORE.
  eapply storebytes_mapped_inj in STORE; eauto.
  Focus 3.
   unfold flat_inj. destruct (plt b thr); try reflexivity. contradiction.
  destruct STORE as (m2 & STORE & INJ).
  replace (o + 0) with o in * by omega.
  replace m2 with m' in * by congruence.
  split; auto.
  intros; intro. eapply Memimpl.perm_storebytes_2 in H6; eauto. eapply H4; eauto.
  unfold meminj_no_overlap.
  unfold flat_inj. intros.
  destruct (plt b1 thr); try discriminate.
  destruct (plt b2 thr); try discriminate.
  left; congruence.
Qed.

(** Extra properties about drop_perm and extends *)

Theorem drop_perm_right_extends:
  forall m1 m2 b lo hi p m2',
  extends m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_drop _ _ _ _ _ _ H0). auto.
  eapply drop_outside_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. omega.
Qed. 

Theorem drop_perm_parallel_extends:
  forall m1 m2 b lo hi p m1',
  extends m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  exists m2',
     drop_perm m2 b lo hi p = Some m2'
  /\ extends m1' m2'.
Proof.
  intros.
  inv H.
  exploit drop_mapped_inj; eauto.
  unfold meminj_no_overlap. unfold inject_id. intros; left; congruence.
  reflexivity.
  replace (lo + 0) with lo by omega.
  replace (hi + 0) with hi by omega.
  destruct 1 as [m2' [FREE INJ]]. exists m2'; split; auto.
  constructor; auto.
  rewrite (nextblock_drop _ _ _ _ _ _ H0).
  rewrite (nextblock_drop _ _ _ _ _ _ FREE). auto.
Qed.

(** ... and we need to repackage instances for the CompCert memory model. *)

Lemma perm_free_2:
   forall (m1 : mem) (bf : block) (lo hi : Z) (m2 : mem),
   free m1 bf lo hi = Some m2 ->
   forall (ofs : Z) (k : perm_kind) (p : permission),
   lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  free_tac Memimpl.perm_free_2.
Qed.

Lemma perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  free_tac Memimpl.perm_free_3.
Qed.

Global Instance memory_model_ops: Mem.MemoryModelOps mem.
Proof.
  constructor.
  exact empty.
  exact alloc.
  exact free.
  exact load.
  exact store.
  exact loadbytes.
  exact storebytes.
  exact drop_perm.
  exact nextblock.
  exact perm.
  exact valid_pointer.
  exact extends.
  exact inject.
  exact inject_neutral.
  exact unchanged_on.
Defined. (** Qed does not work here, need transparent definitions for MemoryModel* *)

Lemma perm_free_list:
  forall l m m' b ofs k p,
  Mem.free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\ 
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  Opaque free.
  induction l; simpl; intros.
  inv H. auto. 
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split.  eapply perm_free_3; eauto.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
  Transparent free.
Qed.

Lemma free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2.
Proof.
  free_tac free_left_inject.
Qed.

Lemma free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  Mem.free_list m1 l = Some m1' ->
  inject f m1' m2.
Proof.
  Opaque free.
  induction l; simpl; intros. 
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
  Transparent free.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  free_tac free_right_inject.
Qed.

Lemma free_inject:
   forall (f : meminj) (m1 : mem) (l : list (block * Z * Z)) 
     (m1' m2 : mem) (b : block) (lo hi : Z) (m2' : mem),
   Mem.inject f m1 m2 ->
   Mem.free_list m1 l = Some m1' ->
   Mem.free m2 b lo hi = Some m2' ->
   (forall (b1 : block) (delta ofs : Z) (k : perm_kind) (p : permission),
    f b1 = Some (b, delta) ->
    Mem.perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi ->
    exists lo1 hi1 : Z, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
   Mem.inject f m1' m2'.
Proof.
  intros. 
  eapply free_right_inject; eauto. 
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Lemma free_unchanged_on:
   forall (P : block -> Z -> Prop) (m : mem) (b : block) 
     (lo hi : Z) (m' : mem),
     free m b lo hi = Some m' ->
   (forall i : Z, lo <= i < hi -> ~ P b i) -> unchanged_on P m m'.
Proof.
  unfold free. intros.
  destruct (zle hi lo); eauto using Memimpl.free_unchanged_on.
  inv H. apply Memimpl.unchanged_on_refl.
Qed.

Global Instance memory_model: Mem.MemoryModel mem.
Proof.
  constructor.
  exact  valid_not_valid_diff.
exact  perm_implies.
exact  perm_cur_max.
exact  perm_cur.
exact  perm_max.
exact  perm_valid_block.
exact  range_perm_implies.
exact  range_perm_cur.
exact  range_perm_max.
exact  valid_access_implies.
exact  valid_access_valid_block.
exact  valid_access_perm.
exact  valid_pointer_nonempty_perm.
exact  valid_pointer_valid_access.
exact  weak_valid_pointer_spec.
exact  valid_pointer_implies.
exact  nextblock_empty.
exact  perm_empty.
exact  valid_access_empty.
exact  valid_access_load.
exact  load_valid_access.
exact  load_type.
exact  load_cast.
exact  load_int8_signed_unsigned.
exact  load_int16_signed_unsigned.
exact  loadv_int64_split.
exact  range_perm_loadbytes.
exact  loadbytes_range_perm.
exact  loadbytes_load.
exact  load_loadbytes.
exact  loadbytes_length.
exact  loadbytes_empty.
exact  loadbytes_concat.
exact  loadbytes_split.
exact  nextblock_store.
exact  store_valid_block_1.
exact  store_valid_block_2.
exact  perm_store_1.
exact  perm_store_2.
exact  store_valid_access_1.
exact  store_valid_access_2.
exact  store_valid_access_3.
exact  valid_access_store.
exact  load_store_similar.
exact  load_store_similar_2.
exact  load_store_same.
exact  load_store_other.
exact  load_store_pointer_overlap.
exact  load_store_pointer_mismatch.
exact  load_pointer_store.
exact  loadbytes_store_same.
exact  loadbytes_store_other.
exact  store_signed_unsigned_8.
exact  store_signed_unsigned_16.
exact  store_int8_zero_ext.
exact  store_int8_sign_ext.
exact  store_int16_zero_ext.
exact  store_int16_sign_ext.
exact  store_float32_truncate.
exact  storev_int64_split.
now storebytes_tac storebytes_range_perm.
now storebytes_tac perm_storebytes_1.
now storebytes_tac perm_storebytes_2.
now storebytes_tac storebytes_valid_access_1.
now storebytes_tac storebytes_valid_access_2.
now storebytes_tac nextblock_storebytes.
now storebytes_tac storebytes_valid_block_1.
now storebytes_tac storebytes_valid_block_2.
exact  range_perm_storebytes.
exact  storebytes_store.
exact  store_storebytes.
exact  loadbytes_storebytes_same.
now storebytes_tac loadbytes_storebytes_other.
now storebytes_tac load_storebytes_other.
now storebytes_tac loadbytes_storebytes_disjoint.
exact  storebytes_concat.
exact  storebytes_split.
exact  alloc_result.
exact  nextblock_alloc.
exact  valid_block_alloc.
exact  fresh_block_alloc.
exact  valid_new_block.
exact  valid_block_alloc_inv.
exact  perm_alloc_1.
exact  perm_alloc_2.
exact  perm_alloc_3.
exact  perm_alloc_4.
exact  perm_alloc_inv.
exact  valid_access_alloc_other.
exact  valid_access_alloc_same.
exact  valid_access_alloc_inv.
exact  load_alloc_unchanged.
exact  load_alloc_other.
exact  load_alloc_same.
exact  load_alloc_same'.
exact  loadbytes_alloc_unchanged.
exact  loadbytes_alloc_same.
now free_tac free_range_perm.
exact  range_perm_free.
now free_tac nextblock_free.
now free_tac valid_block_free_1.
now free_tac valid_block_free_2.
now free_tac perm_free_1.
exact  perm_free_2.
exact  perm_free_3.
exact  perm_free_list.
now free_tac valid_access_free_1.
now free_tac valid_access_free_2.
now free_tac valid_access_free_inv_1.
now free_tac valid_access_free_inv_2.
now free_tac load_free.
now free_tac loadbytes_free.
now free_tac loadbytes_free_2.
exact  nextblock_drop.
exact  drop_perm_valid_block_1.
exact  drop_perm_valid_block_2.
exact  range_perm_drop_1.
exact  range_perm_drop_2.
exact  perm_drop_1.
exact  perm_drop_2.
exact  perm_drop_3.
exact  perm_drop_4.
exact  load_drop.
exact  loadbytes_drop.
exact  mext_next.
exact  extends_refl.
exact  load_extends.
exact  loadv_extends.
exact  loadbytes_extends.
exact  store_within_extends.
exact  store_outside_extends.
exact  storev_extends.
exact  storebytes_within_extends.
now storebytes_tac storebytes_outside_extends.
exact  alloc_extends.
now free_tac free_left_extends.
now free_tac free_right_extends.
exact  free_parallel_extends.
exact  valid_block_extends.
exact  perm_extends.
exact  valid_access_extends.
exact  valid_pointer_extends.
exact  weak_valid_pointer_extends.
exact  mi_freeblocks.
exact  mi_mappedblocks.
exact  mi_no_overlap.
exact  valid_block_inject_1.
exact  valid_block_inject_2.
exact  perm_inject.
exact  range_perm_inject.
exact  valid_access_inject.
exact  valid_pointer_inject.
exact  weak_valid_pointer_inject.
exact  address_inject.
exact  valid_pointer_inject_no_overflow.
exact  weak_valid_pointer_inject_no_overflow.
exact  valid_pointer_inject_val.
exact  weak_valid_pointer_inject_val.
exact  inject_no_overlap.
exact  different_pointers_inject.
exact  disjoint_or_equal_inject.
exact  aligned_area_inject.
exact  load_inject.
exact  loadv_inject.
exact  loadbytes_inject.
exact  store_mapped_inject.
exact  store_unmapped_inject.
exact  store_outside_inject.
exact  storev_mapped_inject.
exact  storebytes_mapped_inject.
now storebytes_tac storebytes_unmapped_inject.
now storebytes_tac storebytes_outside_inject.
exact  storebytes_empty_inject.
exact  alloc_right_inject.
exact  alloc_left_unmapped_inject.
exact  alloc_left_mapped_inject.
exact  alloc_parallel_inject.
exact  free_inject.
exact  free_left_inject.
exact  free_list_left_inject.
exact  free_right_inject.
exact  drop_outside_inject.
exact  neutral_inject.
exact  empty_inject_neutral.
exact  alloc_inject_neutral.
exact  store_inject_neutral.
exact  drop_inject_neutral.
exact  unchanged_on_refl .
exact  perm_unchanged_on .
exact  perm_unchanged_on_2 .
exact  loadbytes_unchanged_on_1 .
exact  loadbytes_unchanged_on .
exact  load_unchanged_on_1 .
exact  load_unchanged_on .
exact  store_unchanged_on .
exact  storebytes_unchanged_on .
exact  alloc_unchanged_on .
exact  free_unchanged_on .
exact  unchanged_on_empty .
exact  unchanged_on_trans .
exact  unchanged_on_weak .
exact  unchanged_on_or .
exact  unchanged_on_exists .
Qed.

(** Here we expose the additional properties that we need, and most of
which are actually already proved in the original CompCert
implementation. *)

Global Instance memory_model_x: Mem.MemoryModelX mem.
Proof.
  constructor.
  typeclasses eauto.
  exact extends_extends_compose.
  exact inject_extends_compose.
  exact inject_compose.
  exact extends_inject_compose.
  apply inject_neutral_incr.
  now free_tac free_inject_neutral'.
  apply drop_perm_right_extends.
  apply drop_perm_parallel_extends.
  now storebytes_tac storebytes_inject_neutral'.
  exact free_range.
  exact storebytes_empty.
Qed.
