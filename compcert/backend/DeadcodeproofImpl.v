Require Import Coqlib.
Require Import Maps.
Require Import Values.
Require Import Memory.
Require Memimpl.
Require Import Deadcodeproof.
Require Import NeedDomain.

(** * Relating the memory states *)

(** The [magree] predicate is a variant of [Mem.extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation. *)

(** [CompCertX:test-compcert-param-memory] [magree] used to be defined in [Deadcodeproof].
  However, this definition is based on the
  concrete implementation of the memory model.
  We now specify it abstractly in [Deadcodeproof], and we moved
  the concrete implementation and its proofs here,
  relying on the new [Memimpl]. *)

Record magree (m1 m2: Memimpl.mem) (P: locset) : Prop := mk_magree {
  ma_perm:
    forall b ofs k p,
    Memimpl.perm m1 b ofs k p ->
    Memimpl.perm m2 b ofs k p;
  ma_memval:
    forall b ofs,
    Memimpl.perm m1 b ofs Cur Readable ->
    P b ofs ->
    memval_lessdef (ZMap.get ofs (PMap.get b (Memimpl.mem_contents m1)))
                   (ZMap.get ofs (PMap.get b (Memimpl.mem_contents m2)));
  ma_nextblock:
    Memimpl.nextblock m2 = Memimpl.nextblock m1
}.

Lemma magree_monotone:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q.
Proof.
  intros. destruct H. constructor; auto.
Qed.

Lemma mextends_agree:
  forall m1 m2 P, Memimpl.extends m1 m2 -> magree m1 m2 P.
Proof.
  intros. destruct H. destruct mext_inj. constructor; intros.
- replace ofs with (ofs + 0) by omega. eapply mi_perm; eauto. auto.
- exploit mi_memval; eauto. unfold inject_id; eauto. 
  rewrite Zplus_0_r. auto. 
- auto.
Qed.

Lemma magree_extends:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> Memimpl.extends m1 m2.
Proof.
  intros. destruct H0. constructor; auto. constructor; unfold inject_id; intros.
- inv H0. rewrite Zplus_0_r. simpl in *; eauto. 
- inv H0. apply Zdivide_0. 
- inv H0. rewrite Zplus_0_r. eapply ma_memval0; eauto.
Qed.

Lemma magree_loadbytes:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  Memimpl.loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', Memimpl.loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes'.
Proof.
  assert (GETN: forall c1 c2 n ofs,
    (forall i, ofs <= i < ofs + Z.of_nat n -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    list_forall2 memval_lessdef (Memimpl.getN n ofs c1) (Memimpl.getN n ofs c2)).
  {
    induction n; intros; simpl. 
    constructor.
    rewrite inj_S in H. constructor.
    apply H. omega. 
    apply IHn. intros; apply H; omega.
  }
  unfold Memimpl.loadbytes; intros. destruct H. 
  destruct (Memimpl.range_perm_dec m1 b ofs (ofs + n) Cur Readable); inv H0.
  rewrite pred_dec_true. econstructor; split; eauto.
  apply GETN. intros. rewrite nat_of_Z_max in H.
  assert (ofs <= i < ofs + n) by xomega. 
  apply ma_memval0; auto.
  red; intros; eauto. 
Qed.

Lemma magree_load:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  Memimpl.load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', Memimpl.load chunk m2 b ofs = Some v' /\ Val.lessdef v v'.
Proof.
  intros. exploit Memimpl.load_valid_access; eauto. intros [A B]. 
  exploit Memimpl.load_loadbytes; eauto. intros [bytes [C D]].
  exploit magree_loadbytes; eauto. intros [bytes' [E F]].
  exists (decode_val chunk bytes'); split. 
  apply Memimpl.loadbytes_load; auto. 
  apply val_inject_id. subst v. apply decode_val_inject; auto. 
Qed.

Lemma magree_storebytes_parallel:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  Memimpl.storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z_of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', Memimpl.storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q.
Proof.
  assert (SETN: forall (access: Z -> Prop) bytes1 bytes2,
    list_forall2 memval_lessdef bytes1 bytes2 ->
    forall p c1 c2,
    (forall i, access i -> i < p \/ p + Z.of_nat (length bytes1) <= i -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    forall q, access q ->
    memval_lessdef (ZMap.get q (Memimpl.setN bytes1 p c1))
                   (ZMap.get q (Memimpl.setN bytes2 p c2))).
  {
    induction 1; intros; simpl.
  - apply H; auto. simpl. omega.
  - simpl length in H1; rewrite inj_S in H1. 
    apply IHlist_forall2; auto. 
    intros. rewrite ! ZMap.gsspec. destruct (ZIndexed.eq i p). auto. 
    apply H1; auto. unfold ZIndexed.t in *; omega. 
  }
  intros. 
  destruct (Memimpl.range_perm_storebytes m2 b ofs bytes2) as [m2' ST2].
  { erewrite <- list_forall2_length by eauto. red; intros.
    eapply ma_perm; eauto. 
    eapply Memimpl.storebytes_range_perm; eauto. }
  exists m2'; split; auto. 
  constructor; intros.
- eapply Memimpl.perm_storebytes_1; eauto. eapply ma_perm; eauto.
  eapply Memimpl.perm_storebytes_2; eauto. 
- rewrite (Memimpl.storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (Memimpl.storebytes_mem_contents _ _ _ _ _ ST2).
  rewrite ! PMap.gsspec. destruct (peq b0 b).
+ subst b0. apply SETN with (access := fun ofs => Memimpl.perm m1' b ofs Cur Readable /\ Q b ofs); auto.
  intros. destruct H5. eapply ma_memval; eauto.
  eapply Memimpl.perm_storebytes_2; eauto.
  apply H1; auto.
+ eapply ma_memval; eauto. eapply Memimpl.perm_storebytes_2; eauto. apply H1; auto.
- rewrite (Memimpl.nextblock_storebytes _ _ _ _ _ H0).
  rewrite (Memimpl.nextblock_storebytes _ _ _ _ _ ST2).
  eapply ma_nextblock; eauto. 
Qed.

Lemma magree_store_parallel:
  forall m1 m2 (P Q: locset) chunk b ofs v1 m1' v2,
  magree m1 m2 P ->
  Memimpl.store chunk m1 b ofs v1 = Some m1' ->
  vagree v1 v2 (store_argument chunk) ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + size_chunk chunk <= i ->
                P b' i) ->
  exists m2', Memimpl.store chunk m2 b ofs v2 = Some m2' /\ magree m1' m2' Q.
Proof.
  intros. 
  exploit Memimpl.store_valid_access_3; eauto. intros [A B]. 
  exploit Memimpl.store_storebytes; eauto. intros SB1.
  exploit magree_storebytes_parallel. eauto. eauto. 
  instantiate (1 := Q). intros. rewrite encode_val_length in H4.
  rewrite <- size_chunk_conv in H4. apply H2; auto. 
  eapply store_argument_sound; eauto. 
  intros [m2' [SB2 AG]]. 
  exists m2'; split; auto.
  apply Memimpl.storebytes_store; auto. 
Qed.

Lemma magree_storebytes_left:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  Memimpl.storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. constructor; intros.
- eapply ma_perm; eauto. eapply Memimpl.perm_storebytes_2; eauto. 
- rewrite (Memimpl.storebytes_mem_contents _ _ _ _ _ H0).
  rewrite PMap.gsspec. destruct (peq b0 b).
+ subst b0. rewrite Memimpl.setN_outside. eapply ma_memval; eauto. eapply Memimpl.perm_storebytes_2; eauto.
  destruct (zlt ofs0 ofs); auto. destruct (zle (ofs + Z.of_nat (length bytes1)) ofs0); try omega.
  elim (H1 ofs0). omega. auto. 
+ eapply ma_memval; eauto. eapply Memimpl.perm_storebytes_2; eauto.
- rewrite (Memimpl.nextblock_storebytes _ _ _ _ _ H0).
  eapply ma_nextblock; eauto. 
Qed.

Lemma magree_store_left:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  Memimpl.store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. eapply magree_storebytes_left; eauto.
  eapply Memimpl.store_storebytes; eauto. 
  intros. rewrite encode_val_length in H2.
  rewrite <- size_chunk_conv in H2. apply H1; auto. 
Qed.

Lemma magree_free:
  forall m1 m2 (P Q: locset) b lo hi m1',
  magree m1 m2 P ->
  Memimpl.free m1 b lo hi = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ ~(lo <= i < hi) ->
                P b' i) ->
  exists m2', Memimpl.free m2 b lo hi = Some m2' /\ magree m1' m2' Q.
Proof.
  intros. 
  destruct (Memimpl.range_perm_free m2 b lo hi) as [m2' FREE].
  red; intros. eapply ma_perm; eauto. eapply Memimpl.free_range_perm; eauto. 
  exists m2'; split; auto.
  constructor; intros.
- (* permissions *)
  assert (Memimpl.perm m2 b0 ofs k p). { eapply ma_perm; eauto. eapply Memimpl.perm_free_3; eauto. }
  exploit Memimpl.perm_free_inv; eauto. intros [[A B] | A]; auto.
  subst b0. eelim Memimpl.perm_free_2. eexact H0. eauto. eauto. 
- (* contents *)
  rewrite (Memimpl.free_result _ _ _ _ _ H0).
  rewrite (Memimpl.free_result _ _ _ _ _ FREE). 
  simpl. eapply ma_memval; eauto. eapply Memimpl.perm_free_3; eauto.
  apply H1; auto. destruct (eq_block b0 b); auto.
  subst b0. right. red; intros. eelim Memimpl.perm_free_2. eexact H0. eauto. eauto. 
- (* nextblock *)
  rewrite (Memimpl.free_result _ _ _ _ _ H0).
  rewrite (Memimpl.free_result _ _ _ _ _ FREE).
  simpl. eapply ma_nextblock; eauto.
Qed.

Global Instance magree_ops: Deadcodeproof.MAgreeOps Memimpl.mem :=
  {|
    magree := magree
  |}.

Global Instance magree_prf: Deadcodeproof.MAgree Memimpl.mem.
Proof.
  constructor.
  exact ma_perm.
  exact magree_monotone.
  exact mextends_agree.
  exact magree_extends.
  exact magree_loadbytes.
  exact magree_load.
  exact magree_storebytes_parallel.
  exact magree_store_parallel.
  exact magree_storebytes_left.
  exact magree_store_left.
  exact magree_free.
Qed.
