Require Import Coqlib.
Require Import Zwf.
Require Import Maps.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Kildall.
Require Import Registers.
Require Import RTL.
Require Import ValueDomain.

(** [CompCertX:test-compcert-param-memory] The following property cannot be proved solely based on the
    specification of the memory model. It is now abstractly specified
    in [ValueDomain], and its original proof based on the concrete
    implementation [Memimpl] of the memory model, is moved here.
*)

Section WITHMEM.
Context `{memory_model: Mem.MemoryModel}.

Section WITHBC.

Variable (bc: block_classification).

Record mmatch (m: mem) (am: amem) : Prop := mk_mem_match {
  mmatch_stack: forall b,
    bc b = BCstack ->
    bmatch bc m b am.(am_stack);
  mmatch_glob: forall id ab b,
    bc b = BCglob id -> 
    am.(am_glob)!id = Some ab ->
    bmatch bc m b ab;
  mmatch_nonstack: forall b,
    bc b <> BCstack -> bc b <> BCinvalid ->
    smatch bc m b am.(am_nonstack);
  mmatch_top: forall b,
    bc b <> BCinvalid ->
    smatch bc m b am.(am_top);
  mmatch_below:
    bc_below bc (Mem.nextblock m)
}.

Theorem load_sound:
  forall chunk m b ofs v rm am p,
  Mem.load chunk m b (Int.unsigned ofs) = Some v ->
  romatch bc m rm ->
  mmatch m am ->
  pmatch bc b ofs p ->
  vmatch bc v (ValueDomain.load chunk rm am p).
Proof.
  intros. unfold ValueDomain.load. inv H2. 
- (* Gl id ofs *)
  destruct (rm!id) as [ab|] eqn:RM. 
  eapply ablock_load_sound; eauto. eapply H0; eauto. 
  destruct (am_glob am)!id as [ab|] eqn:AM.
  eapply ablock_load_sound; eauto. eapply mmatch_glob; eauto. 
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto; congruence.
- (* Glo id *)
  destruct (rm!id) as [ab|] eqn:RM. 
  eapply ablock_load_anywhere_sound; eauto. eapply H0; eauto. 
  destruct (am_glob am)!id as [ab|] eqn:AM.
  eapply ablock_load_anywhere_sound; eauto. eapply mmatch_glob; eauto. 
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto; congruence.
- (* Glob *)
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto. congruence. congruence.
- (* Stk ofs *)
  eapply ablock_load_sound; eauto. eapply mmatch_stack; eauto.
- (* Stack *)
  eapply ablock_load_anywhere_sound; eauto. eapply mmatch_stack; eauto.
- (* Nonstack *)
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto. 
- (* Top *)
  eapply vnormalize_cast; eauto. eapply mmatch_top; eauto.
Qed.

Theorem store_sound:
  forall chunk m b ofs v m' am p av,
  Mem.store chunk m b (Int.unsigned ofs) v = Some m' ->
  mmatch m am ->
  pmatch bc b ofs p ->
  vmatch bc v av ->
  mmatch m' (ValueDomain.store chunk am p av).
Proof.
  intros until av; intros STORE MM PM VM.
  unfold store; constructor; simpl; intros.
- (* Stack *)
  assert (DFL: bc b <> BCstack -> bmatch bc m' b0 (am_stack am)).
  { intros. apply bmatch_inv with m. eapply mmatch_stack; eauto. 
    intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. }
  inv PM; try (apply DFL; congruence).
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_store_sound; eauto. eapply mmatch_stack; eauto. 
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_store_anywhere_sound; eauto. eapply mmatch_stack; eauto. 
  + eapply ablock_store_anywhere_sound; eauto. eapply mmatch_stack; eauto.

- (* Globals *)
  rename b0 into b'.
  assert (DFL: bc b <> BCglob id -> (am_glob am)!id = Some ab -> 
               bmatch bc m' b' ab).
  { intros. apply bmatch_inv with m. eapply mmatch_glob; eauto.
    intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. }
  inv PM. 
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_store_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_store_anywhere_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + eapply DFL; eauto. congruence.
  + eapply DFL; eauto. congruence. 
  + rewrite PTree.gempty in H0; congruence.
  + rewrite PTree.gempty in H0; congruence.

- (* Nonstack *)
  assert (DFL: smatch bc m' b0 (vplub av (am_nonstack am))).
  { eapply smatch_store; eauto. eapply mmatch_nonstack; eauto. }
  assert (STK: bc b = BCstack -> smatch bc m' b0 (am_nonstack am)).
  { intros. apply smatch_inv with m. eapply mmatch_nonstack; eauto; congruence.
    intros. eapply Mem.loadbytes_store_other; eauto. left. congruence.
  }
  inv PM; (apply DFL || apply STK; congruence).

- (* Top *)
  eapply smatch_store; eauto. eapply mmatch_top; eauto.

- (* Below *)
  erewrite Mem.nextblock_store by eauto. eapply mmatch_below; eauto.
Qed.

Theorem loadbytes_sound:
  forall m b ofs sz bytes am rm p,
  Mem.loadbytes m b (Int.unsigned ofs) sz = Some bytes ->
  romatch bc m rm ->
  mmatch m am ->
  pmatch bc b ofs p ->
  forall  b' ofs' i, In (Pointer b' ofs' i) bytes -> pmatch bc b' ofs' (ValueDomain.loadbytes am rm p).
Proof.
  intros. unfold ValueDomain.loadbytes; inv H2.
- (* Gl id ofs *)
  destruct (rm!id) as [ab|] eqn:RM.
  exploit H0; eauto. intros (A & B & C). eapply ablock_loadbytes_sound; eauto.
  destruct (am_glob am)!id as [ab|] eqn:GL.
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_glob; eauto. 
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Glo id *)
  destruct (rm!id) as [ab|] eqn:RM.
  exploit H0; eauto. intros (A & B & C). eapply ablock_loadbytes_sound; eauto.
  destruct (am_glob am)!id as [ab|] eqn:GL.
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_glob; eauto. 
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Glob *)
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Stk ofs *)
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_stack; eauto. 
- (* Stack *)
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_stack; eauto.
- (* Nonstack *) 
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Top *)
  eapply smatch_loadbytes; eauto. eapply mmatch_top; eauto with va.
Qed.

Theorem storebytes_sound:
  forall m b ofs bytes m' am p sz q,
  Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
  mmatch m am ->
  pmatch bc b ofs p ->
  length bytes = nat_of_Z sz ->
  (forall b' ofs' i, In (Pointer b' ofs' i) bytes -> pmatch bc b' ofs' q) ->
  mmatch m' (ValueDomain.storebytes am p sz q).
Proof.
  intros until q; intros STORE MM PM LENGTH BYTES.
  unfold ValueDomain.storebytes; constructor; simpl; intros.
- (* Stack *)
  assert (DFL: bc b <> BCstack -> bmatch bc m' b0 (am_stack am)).
  { intros. apply bmatch_inv with m. eapply mmatch_stack; eauto. 
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. }
  inv PM; try (apply DFL; congruence).
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_storebytes_sound; eauto. eapply mmatch_stack; eauto. 
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0. 
    eapply ablock_storebytes_anywhere_sound; eauto. eapply mmatch_stack; eauto. 
  + eapply ablock_storebytes_anywhere_sound; eauto. eapply mmatch_stack; eauto.

- (* Globals *)
  rename b0 into b'.
  assert (DFL: bc b <> BCglob id -> (am_glob am)!id = Some ab -> 
               bmatch bc m' b' ab).
  { intros. apply bmatch_inv with m. eapply mmatch_glob; eauto.
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. }
  inv PM. 
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_storebytes_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_storebytes_anywhere_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL. 
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + eapply DFL; eauto. congruence.
  + eapply DFL; eauto. congruence. 
  + rewrite PTree.gempty in H0; congruence.
  + rewrite PTree.gempty in H0; congruence.

- (* Nonstack *)
  assert (DFL: smatch bc m' b0 (plub q (am_nonstack am))).
  { eapply smatch_storebytes; eauto. eapply mmatch_nonstack; eauto. }
  assert (STK: bc b = BCstack -> smatch bc m' b0 (am_nonstack am)).
  { intros. apply smatch_inv with m. eapply mmatch_nonstack; eauto; congruence.
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left. congruence.
  }
  inv PM; (apply DFL || apply STK; congruence).

- (* Top *)
  eapply smatch_storebytes; eauto. eapply mmatch_top; eauto.

- (* Below *)
  erewrite Mem.nextblock_storebytes by eauto. eapply mmatch_below; eauto.
Qed.

Lemma mmatch_ext:
  forall m am m',
  mmatch m am ->
  (forall b ofs n bytes, bc b <> BCinvalid -> n >= 0 -> Mem.loadbytes m' b ofs n = Some bytes -> Mem.loadbytes m b ofs n = Some bytes) ->
  Ple (Mem.nextblock m) (Mem.nextblock m') ->
  mmatch m' am.
Proof.
  intros. inv H. constructor; intros.
- apply bmatch_ext with m; auto with va.
- apply bmatch_ext with m; eauto with va.
- apply smatch_ext with m; auto with va.
- apply smatch_ext with m; auto with va.
- red; intros. exploit mmatch_below0; eauto. xomega. 
Qed.

Lemma mmatch_free:
  forall m b lo hi m' am,
  Mem.free m b lo hi = Some m' ->
  mmatch m am ->
  mmatch m' am.
Proof.
  intros. apply mmatch_ext with m; auto. 
  intros. eapply Mem.loadbytes_free_2; eauto. 
  erewrite <- Mem.nextblock_free by eauto. xomega. 
Qed.

Lemma mmatch_top':
  forall m am, mmatch m am -> mmatch m mtop.
Proof.
  intros. constructor; simpl; intros.
- apply ablock_init_sound. apply smatch_ge with (ab_summary (am_stack am)). 
  eapply mmatch_stack; eauto. constructor.
- rewrite PTree.gempty in H1; discriminate.
- eapply smatch_ge. eapply mmatch_nonstack; eauto. constructor.
- eapply smatch_ge. eapply mmatch_top; eauto. constructor.
- eapply mmatch_below; eauto.
Qed.

Lemma mbeq_sound:
  forall m1 m2, mbeq m1 m2 = true -> forall m, mmatch m m1 <-> mmatch m m2.
Proof.
  unfold mbeq; intros. InvBooleans. rewrite PTree.beq_correct in H1.
  split; intros M; inv M; constructor; intros.
- erewrite <- bbeq_sound; eauto. 
- specialize (H1 id). rewrite H4 in H1. destruct (am_glob m1)!id eqn:G; try contradiction. 
  erewrite <- bbeq_sound; eauto. 
- rewrite <- H; eauto. 
- rewrite <- H0; eauto.
- auto.
- erewrite bbeq_sound; eauto. 
- specialize (H1 id). rewrite H4 in H1. destruct (am_glob m2)!id eqn:G; try contradiction. 
  erewrite bbeq_sound; eauto. 
- rewrite H; eauto. 
- rewrite H0; eauto.
- auto.
Qed.

Lemma mmatch_lub_l:
  forall m x y, mmatch m x -> mmatch m (mlub x y).
Proof.
  intros. inv H. constructor; simpl; intros. 
- apply bmatch_lub_l; auto. 
- rewrite PTree.gcombine in H0 by auto. unfold combine_ablock in H0. 
  destruct (am_glob x)!id as [b1|] eqn:G1;
  destruct (am_glob y)!id as [b2|] eqn:G2;
  inv H0.
  apply bmatch_lub_l; eauto. 
- apply smatch_lub_l; auto. 
- apply smatch_lub_l; auto.
- auto.
Qed.

Lemma mmatch_lub_r:
  forall m x y, mmatch m y -> mmatch m (mlub x y).
Proof.
  intros. inv H. constructor; simpl; intros. 
- apply bmatch_lub_r; auto. 
- rewrite PTree.gcombine in H0 by auto. unfold combine_ablock in H0. 
  destruct (am_glob x)!id as [b1|] eqn:G1;
  destruct (am_glob y)!id as [b2|] eqn:G2;
  inv H0.
  apply bmatch_lub_r; eauto. 
- apply smatch_lub_r; auto. 
- apply smatch_lub_r; auto.
- auto.
Qed.

Lemma mmatch_inj_top:
  forall m m', Mem.inject (inj_of_bc bc) m m' -> mmatch m mtop.
Proof.
  intros. 
  assert (SM: forall b, bc b <> BCinvalid -> smatch bc m b Ptop).
  {
    intros; split; intros. 
    - exploit Mem.load_inject. eauto. eauto. apply inj_of_bc_valid; auto. 
      intros (v' & A & B). eapply vmatch_inj_top; eauto. 
    - exploit Mem.loadbytes_inject. eauto. eauto. apply inj_of_bc_valid; auto. 
      intros (bytes' & A & B). inv B. inv H4. eapply pmatch_inj_top; eauto. 
  }
  constructor; simpl; intros. 
  - apply ablock_init_sound. apply SM. congruence.
  - rewrite PTree.gempty in H1; discriminate.
  - apply SM; auto.
  - apply SM; auto.
  - red; intros. eapply Mem.valid_block_inject_1. eapply inj_of_bc_valid; eauto. eauto.  
Qed.

End WITHBC.

End WITHMEM.

Global Instance mmatch_ops
 {mem}
 {memory_model_ops: Mem.MemoryModelOps mem}
: ValueDomain.MMatchOps mem :=
  {|
    mmatch := mmatch
  |}.

Require Memimpl.

Lemma mmatch_inj:
  forall bc m am, mmatch bc m am -> bc_below bc (Mem.nextblock m) -> Mem.inject (inj_of_bc bc) m m.
Proof.
  intros. constructor. constructor.
- (* perms *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst. 
  rewrite Zplus_0_r. auto. 
- (* alignment *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst. 
  apply Zdivide_0. 
- (* contents *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst. 
  rewrite Zplus_0_r. 
  set (mv := ZMap.get ofs (Memimpl.mem_contents m)#b1).
  assert (Mem.loadbytes m b1 ofs 1 = Some (mv :: nil)).
  {
    simpl.
    Local Transparent Memimpl.loadbytes.
    unfold Memimpl.loadbytes. rewrite pred_dec_true. reflexivity. 
    red; intros. replace ofs0 with ofs by omega. auto.
  }
  destruct mv; econstructor.
  apply inj_of_bc_valid.
  assert (PM: pmatch bc b i Ptop).
  { exploit mmatch_top; eauto. intros [P Q].
    eapply pmatch_top'. eapply Q; eauto. }
  inv PM; auto.
  rewrite Int.add_zero; auto.
- (* free blocks *)
  intros. unfold inj_of_bc. erewrite bc_below_invalid; eauto. 
- (* mapped blocks *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst.
  apply H0; auto.
- (* overlap *)
  red; intros. 
  exploit inj_of_bc_inv. eexact H2. intros (A1 & B & C); subst.
  exploit inj_of_bc_inv. eexact H3. intros (A2 & B & C); subst.
  auto.
- (* overflow *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst. 
  rewrite Zplus_0_r. split. omega. apply Int.unsigned_range_2.
Qed.

Global Instance mmatch_prf: ValueDomain.MMatch Memimpl.mem.
Proof.
  constructor.
  exact mmatch_stack.
  exact mmatch_glob.
  exact mmatch_nonstack.
  exact mmatch_top.
  exact mmatch_below.
  exact load_sound.
  exact store_sound.
  exact loadbytes_sound.
  exact storebytes_sound.
  exact mmatch_ext.
  exact mmatch_free.
  exact mmatch_top'.
  exact mbeq_sound.
  exact mmatch_lub_l.
  exact mmatch_lub_r.
  exact mmatch_inj.
  exact mmatch_inj_top.
Qed.
