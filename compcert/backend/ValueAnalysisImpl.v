Require Import Coqlib.
Require Import Maps.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import RTL.
Require Import ValueDomain.
Require Import ValueDomainImpl.
Require Import ValueAnalysis.

Section WITHMEM.
Context `{Hmem: Mem.MemoryModel}.
Context `{mmatch_prf: !ValueDomain.MMatch mem}.

Section NOSTACK.

Variable bc: block_classification.
Hypothesis NOSTACK: bc_nostack bc.

Lemma mmatch_no_stack: forall m am astk,
  mmatch bc m am -> mmatch bc m {| am_stack := astk; am_glob := PTree.empty _; am_nonstack := Nonstack; am_top := Nonstack |}.
Proof.
  intros. destruct H. constructor; simpl; intros.
- elim (NOSTACK b); auto. 
- rewrite PTree.gempty in H0; discriminate.
- eapply smatch_no_stack; eauto. 
- eapply smatch_no_stack; eauto. 
- auto.
Qed.

End NOSTACK.

Theorem allocate_stack:
  forall m sz m' sp bc ge rm am,
  Mem.alloc m 0 sz = (m', sp) ->
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ bc' sp = BCstack
  /\ genv_match bc' ge
  /\ romatch bc' m' rm
  /\ mmatch bc' m' mfunction_entry
  /\ (forall b, Plt b sp -> bc' b = bc b)
  /\ (forall v x, vmatch bc v x -> vmatch bc' v (Ifptr Nonstack)).
Proof.
  intros until am; intros ALLOC GENV RO MM NOSTACK. 
  exploit Mem.nextblock_alloc; eauto. intros NB. 
  exploit Mem.alloc_result; eauto. intros SP.
  assert (SPINVALID: bc sp = BCinvalid).
  { rewrite SP. eapply bc_below_invalid. apply Plt_strict. eapply ValueDomain.mmatch_below; eauto. }
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCstack else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob bc); eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (BC'EQ: forall b, bc b <> BCinvalid -> bc' b = bc b).
  { intros; simpl. apply dec_eq_false. congruence. }
  assert (INCR: bc_incr bc bc').
  { red; simpl; intros. apply BC'EQ; auto. }
(* Part 2: invariance properties *)
  assert (SM: forall b p, bc b <> BCinvalid -> smatch bc m b p -> smatch bc' m' b Nonstack).
  {
    intros. 
    apply smatch_incr with bc; auto.
    apply smatch_inv with m. 
    apply smatch_no_stack with p; auto.
    intros. eapply Mem.loadbytes_alloc_unchanged; eauto. eapply mmatch_below; eauto. 
  }
  assert (SMSTACK: smatch bc' m' sp Pbot).
  {
    split; intros. 
    exploit Mem.load_alloc_same; eauto. intros EQ. subst v. constructor.
    exploit Mem.loadbytes_alloc_same; eauto with coqlib. congruence.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  assumption.
- (* sp is BCstack *)
  simpl; apply dec_eq_true. 
- (* genv match *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence. 
- (* romatch *)
  apply romatch_exten with bc. 
  eapply romatch_alloc; eauto. eapply mmatch_below; eauto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. apply SMSTACK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp).
    subst b. apply smatch_ge with Pbot. apply SMSTACK. constructor.  
    eapply SM; auto. eapply mmatch_top; eauto.
  + (* below *)
    red; simpl; intros. rewrite NB. destruct (eq_block b sp). 
    subst b; rewrite SP; xomega. 
    exploit mmatch_below; eauto. simpl. xomega. 
- (* unchanged *)
  simpl; intros. apply dec_eq_false. apply Plt_ne. auto.
- (* values *)
  intros. apply vmatch_incr with bc; auto. eapply vmatch_no_stack; eauto. 
Qed.

(** Construction 2: turn the stack into an "other" block, at public calls or function returns *)

Theorem anonymize_stack:
  forall m sp bc ge rm am,
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc sp = BCstack ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCother
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, vmatch bc v x -> vmatch bc' v Vtop)
  /\ genv_match bc' ge
  /\ romatch bc' m rm
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros GENV RO MM SP.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCother else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_stack; eauto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_glob; eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall b ofs p, pmatch bc b ofs p -> pmatch bc' b ofs Ptop).
  {
    intros. assert (pmatch bc b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl. destruct (eq_block b sp); congruence. 
  }
  assert (VM: forall v x, vmatch bc v x -> vmatch bc' v Vtop).
  {
    induction 1; constructor; eauto.
  }
  assert (SM: forall b p, smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H as [S1 S2]. split; intros.
    eapply VM. eapply S1; eauto.
    eapply PM. eapply S2; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence. 
  red; intros. elim n. eapply bc_stack; eauto. 
- (* bc' sp is BCother *)
  simpl; apply dec_eq_true. 
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto. 
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); auto.
- (* romatch *)
  apply romatch_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch top *)
  constructor; simpl; intros. 
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_nonstack; eauto. 
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_top; eauto.
  + red; simpl; intros. destruct (eq_block b sp). 
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
Qed.

(** Construction 3: turn the stack into an invalid block, at private calls *)

Theorem hide_stack:
  forall m sp bc ge rm am,
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc sp = BCstack ->
  pge Nonstack am.(am_nonstack) ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCinvalid
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, vge (Ifptr Nonstack) x -> vmatch bc v x -> vmatch bc' v Vtop)
  /\ genv_match bc' ge
  /\ romatch bc' m rm
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros GENV RO MM SP NOLEAK.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCinvalid else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_stack; eauto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_glob; eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall b ofs p, pge Nonstack p -> pmatch bc b ofs p -> pmatch bc' b ofs Ptop).
  {
    intros. assert (pmatch bc b ofs Nonstack) by (eapply pmatch_ge; eauto).
    inv H1. constructor; simpl; destruct (eq_block b sp); congruence. 
  }
  assert (VM: forall v x, vge (Ifptr Nonstack) x -> vmatch bc v x -> vmatch bc' v Vtop).
  {
    intros. apply vmatch_ifptr; intros. subst v. 
    inv H0; inv H; eapply PM; eauto.
  }
  assert (SM: forall b p, pge Nonstack p -> smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H0 as [S1 S2]. split; intros.
    eapply VM with (x := Ifptr p). constructor; auto. eapply S1; eauto.
    eapply PM. eauto. eapply S2; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence. 
  red; intros. elim n. eapply bc_stack; eauto. 
- (* bc' sp is BCinvalid *)
  simpl; apply dec_eq_true. 
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto. 
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* romatch *)
  apply romatch_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch top *)
  constructor; simpl; intros. 
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto. 
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto. 
    red; intros; elim n. eapply bc_stack; eauto. 
  + red; simpl; intros. destruct (eq_block b sp). congruence. 
    eapply mmatch_below; eauto.
Qed.

(** Construction 4: restore the stack after a public call *)

Theorem return_from_public_call:
  forall (caller callee: block_classification) bound sp ge e ae v m rm,
  bc_below caller bound ->
  callee sp = BCother ->
  caller sp = BCstack ->
  (forall b, Plt b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller e ae ->
  Ple bound (Mem.nextblock m) ->
  vmatch callee v Vtop ->
  romatch callee m rm ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      vmatch bc v Vtop
   /\ ematch bc e ae
   /\ romatch bc m rm
   /\ mmatch bc m mafter_public_call
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, Plt b sp -> bc b = caller b).
Proof.
  intros until rm; intros BELOW SP1 SP2 SAME GE1 EM BOUND RESM RM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto. 
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. 
    symmetry; apply SAME; auto. 
  }
(* Invariance properties *)
  assert (PM: forall b ofs p, pmatch callee b ofs p -> pmatch bc b ofs Ptop).  
  {
    intros. assert (pmatch callee b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl. destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vmatch callee v x -> vmatch bc v Vtop).
  {
    intros. assert (vmatch callee v0 Vtop) by (eapply vmatch_top; eauto). 
    inv H0; constructor; eauto.
  }
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Ptop).
  {
    intros. destruct H; split; intros. eapply VM; eauto. eapply PM; eauto.
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto. 
- (* romem *)
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_nonstack; eauto. congruence. 
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    eapply SM. eapply mmatch_top; eauto. 
    destruct (eq_block b sp); congruence.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp). 
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten with caller; eauto.
  simpl; intros. destruct (eq_block b sp). intuition congruence. 
  split; intros. rewrite SAME in H by eauto with va. auto.
  apply <- (proj1 GE2) in H. apply (proj1 GE1) in H. auto.
  simpl; intros. destruct (eq_block b sp). congruence. 
  rewrite <- SAME; eauto with va.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence. 
  symmetry. apply SAME; auto. eapply Plt_trans. eauto. apply BELOW. congruence.
Qed.

(** Construction 5: restore the stack after a private call *)

Theorem return_from_private_call:
  forall (caller callee: block_classification) bound sp ge e ae v m rm am,
  bc_below caller bound ->
  callee sp = BCinvalid ->
  caller sp = BCstack ->
  (forall b, Plt b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller e ae ->
  bmatch caller m sp am.(am_stack) ->
  Ple bound (Mem.nextblock m) ->
  vmatch callee v Vtop ->
  romatch callee m rm ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      vmatch bc v (Ifptr Nonstack)
   /\ ematch bc e ae
   /\ romatch bc m rm
   /\ mmatch bc m (mafter_private_call am)
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, Plt b sp -> bc b = caller b).
Proof.
  intros until am; intros BELOW SP1 SP2 SAME GE1 EM CONTENTS BOUND RESM RM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto. 
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR1: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. 
    symmetry; apply SAME; auto. 
  }
  assert (INCR2: bc_incr callee bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. auto.
  }

(* Invariance properties *)
  assert (PM: forall b ofs p, pmatch callee b ofs p -> pmatch bc b ofs Nonstack).  
  {
    intros. assert (pmatch callee b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl; destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vmatch callee v x -> vmatch bc v (Ifptr Nonstack)).
  {
    intros. assert (vmatch callee v0 Vtop) by (eapply vmatch_top; eauto). 
    inv H0; constructor; eauto.
  }
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Nonstack).
  {
    intros. destruct H; split; intros. eapply VM; eauto. eapply PM; eauto.
  }
  assert (BSTK: bmatch bc m sp (am_stack am)).
  {
    apply bmatch_incr with caller; eauto. 
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto. 
- (* romem *)
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    destruct (eq_block b sp). 
    subst b. exact BSTK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp). 
    subst. apply smatch_ge with (ab_summary (am_stack am)). apply BSTK. apply pge_lub_l. 
    apply smatch_ge with Nonstack. eapply SM. eapply mmatch_top; eauto. apply pge_lub_r.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp). 
    subst b. apply Plt_le_trans with bound. apply BELOW. congruence. auto. 
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence. 
  symmetry. apply SAME; auto. eapply Plt_trans. eauto. apply BELOW. congruence.
Qed.

(** Construction 6: external call *)

Theorem external_call_match':
  forall (ge: genv),
  forall vargs m vres m' bc rm am,
    genv_match bc ge ->
    (forall v, In v vargs -> vmatch bc v Vtop) ->
    romatch bc m rm ->
    mmatch bc m am ->
    bc_nostack bc ->
    forall (external_call_inject:
                        meminj_preserves_globals ge (inj_of_bc bc) ->
                        Mem.inject (inj_of_bc bc) m m ->
                        val_list_inject (inj_of_bc bc) vargs vargs ->
                        exists f', exists vres', exists m2',
                                                   val_inject f' vres vres'
                                                   /\ Mem.inject f' m' m2'
                                                   /\ Mem.unchanged_on (loc_unmapped (inj_of_bc bc)) m m'
                                                   /\ inject_incr (inj_of_bc bc) f'
                                                   /\ inject_separated (inj_of_bc bc) f' m m)
           (external_call_readonly:
                          Mem.unchanged_on (loc_not_writable m) m m')
           (external_call_max_perm: forall (b : block) (ofs : Z)
                               (p : Memtype.permission),
                          Mem.valid_block m b ->
                          Mem.perm m' b ofs Memtype.Max p ->
                          Mem.perm m b ofs Memtype.Max p)
           (external_call_nextblock:
                           Ple (Mem.nextblock m) (Mem.nextblock m'))
    ,
    exists bc',
      bc_incr bc bc'
      /\ (forall b, Plt b (Mem.nextblock m) -> bc' b = bc b)
      /\ vmatch bc' vres Vtop
      /\ genv_match bc' ge
      /\ romatch bc' m' rm
      /\ mmatch bc' m' mtop
      /\ bc_nostack bc'
      /\ (forall b ofs n, Mem.valid_block m b -> bc b = BCinvalid -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n)
.
Proof.
  intros until am; intros GENV ARGS RO MM NOSTACK. intros.
  (* Part 1: using ec_mem_inject *)
 (** [CompCertX:test-compcert-param-memory] This function now depends also on the memory model,
  so we have to provide those additional arguments. *)
 (** [CompCertX:test-compcert-param-extcall] Idem with external function semantics. *)
 (** [CompCertX:test-compcert-protect-stack-arg] Idem with writable block predicate. *)
  exploit (external_call_inject).
  apply inj_of_bc_preserves_globals; auto. 
  eapply ValueDomain.mmatch_inj; eauto. eapply mmatch_below; eauto.
  revert ARGS. generalize vargs. 
  induction vargs0; simpl; intros; constructor.
  eapply vmatch_inj; eauto. auto. 
  intros (j' & vres' & m'' & IRES & IMEM & UNCH1 & IINCR & ISEP).
  assert (JBELOW: forall b, Plt b (Mem.nextblock m) -> j' b = inj_of_bc bc b).
  {
    intros. destruct (inj_of_bc bc b) as [[b' delta] | ] eqn:EQ.
    eapply IINCR; eauto. 
    destruct (j' b) as [[b'' delta'] | ] eqn:EQ'; auto.
    exploit ISEP; eauto. tauto. 
  }
  (* Part 2: constructing bc' from j' *)
  set (f := fun b => if plt b (Mem.nextblock m)
                     then bc b
                     else match j' b with None => BCinvalid | Some _ => BCother end).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> bc b = BCstack).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (j' b); discriminate. }
    intros. apply (bc_stack bc); auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (j' b); discriminate. }
    intros. eapply (bc_glob bc); eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (INCR: bc_incr bc bc').
  {
    red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
  }
  assert (BC'INV: forall b, bc' b <> BCinvalid -> exists b' delta, j' b = Some(b', delta)).
  {
    simpl; intros. destruct (plt b (Mem.nextblock m)). 
    exists b, 0. rewrite JBELOW by auto. apply inj_of_bc_valid; auto.
    destruct (j' b) as [[b' delta] | ]. 
    exists b', delta; auto. 
    congruence.
  }

  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. simpl; unfold f. 
    destruct (plt b (Mem.nextblock m)).
    rewrite JBELOW in H by auto. eapply inj_of_bc_inv; eauto. 
    rewrite H; congruence.
  }
  assert (VMTOP: forall v v', val_inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H; constructor. eapply PMTOP; eauto. 
  }
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m' b Ptop).
  {
    intros; split; intros.
  - exploit BC'INV; eauto. intros (b' & delta & J'). 
    exploit Mem.load_inject. eexact IMEM. eauto. eauto. intros (v' & A & B). 
    eapply VMTOP; eauto.
  - exploit BC'INV; eauto. intros (b'' & delta & J'). 
    exploit Mem.loadbytes_inject. eexact IMEM. eauto. eauto. intros (bytes & A & B).
    inv B. inv H3. eapply PMTOP; eauto. 
  }
  (* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  exact INCR.
- (* unchanged *)
  simpl; intros. apply pred_dec_true; auto.
- (* vmatch res *)
  eapply VMTOP; eauto.
- (* genv match *)
  apply genv_match_exten with bc; auto.
  simpl; intros; split; intros.
  rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
  destruct (plt b (Mem.nextblock m)). auto. destruct (j' b); congruence.
  simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
- (* romatch m' *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)).
  exploit RO; eauto. intros (R & P & Q).
  split; auto.
  split. apply bmatch_incr with bc; auto. apply bmatch_inv with m; auto.
  intros. eapply Mem.loadbytes_unchanged_on_1. eapply external_call_readonly; eauto.
  auto. intros; red. apply Q. 
  intros; red; intros; elim (Q ofs). 
  eapply external_call_max_perm; eauto.
  destruct (j' b); congruence.
- (* mmatch top *)
  constructor; simpl; intros.
  + apply ablock_init_sound. apply SMTOP. simpl; congruence. 
  + rewrite PTree.gempty in H0; discriminate.
  + apply SMTOP; auto.
  + apply SMTOP; auto. 
  + red; simpl; intros. destruct (plt b (Mem.nextblock m)). 
    eapply Plt_le_trans. eauto. eapply external_call_nextblock; eauto. 
    destruct (j' b) as [[bx deltax] | ] eqn:J'. 
    eapply Mem.valid_block_inject_1; eauto. 
    congruence.
- (* nostack *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)). 
  apply NOSTACK; auto.
  destruct (j' b); congruence.
- (* unmapped blocks are invariant *)
  intros. eapply Mem.loadbytes_unchanged_on_1; auto.
  apply UNCH1; auto. intros; red. unfold inj_of_bc; rewrite H0; auto. 
Qed.

Global Instance mmatch_constructions: MMatchConstructions mem.
Proof.
  constructor.
  typeclasses eauto.
  exact allocate_stack.
  exact anonymize_stack.
  exact hide_stack.
  exact return_from_public_call.
  exact return_from_private_call.
  exact external_call_match'.
Qed.

End WITHMEM.
