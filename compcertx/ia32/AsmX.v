Require compcert.ia32.Asm.
Require MemoryX.

Import Coqlib.
Import Integers.
Import Floats.
Import AST.
Import Values.
Import MemoryX.
Import Globalenvs.
Import Events.
Import Smallstep.
Import Locations.
Import Conventions.
Export Asm.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

(** Execution of Asm functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state (lm: regset) (p: Asm.program) (i: ident) (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state'_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    (Hpc: lm PC = Vptr b Int.zero)
    (Hargs: extcall_arguments lm m sg args)    
  :
      initial_state lm p i sg args m (State lm m)
.

Inductive final_state (lm: regset) (sg: signature) : state -> (list val * mem) -> Prop :=
  | final_state_intro:
      forall rs,
        eq (lm # RA) (rs # PC) ->
        eq (lm # ESP) (rs # ESP) ->
        forall v,
          v = List.map rs (loc_external_result sg) ->
          (** We need the following condition to make sure that Asm takes at least one step. *)
          forall
            RA_VUNDEF: rs # RA = Vundef,
            (** Callee-save registers.
                We use Val.lessdef instead of eq because the Stacking and Asmgen passes do not exactly preserve their values. *)
          forall
            (CALLEE_SAVE: forall r,
                            ~ In r destroyed_at_call ->
                            Val.lessdef (lm (preg_of r)) (rs (preg_of r))),
          forall m_,
            final_state lm sg (State rs m_) (v, m_)
.

(** [CompCertiKOS:test-compcert-param-mem-accessors] CompcertX does not
care about kernel vs. user mode, and uses its memory model to define
its memory accessors. *)
Section WITH_MEM_ACCESSORS_DEFAULT.
Local Existing Instance mem_accessors_default.

Definition semantics  (lm: regset) (p: Asm.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
  Semantics (step) (initial_state lm p i sg args m) (final_state lm sg) (Genv.globalenv p).

End WITH_MEM_ACCESSORS_DEFAULT.

(** Properties of arguments *)

Lemma extcall_args_type_decode_longs:
  forall init_asm_rs,
  forall m tl z vl,
  list_forall2 (Asm.extcall_arg init_asm_rs m) (loc_arguments_rec tl z) vl ->
  Val.has_type_list (decode_longs tl vl) tl.
Proof.
  induction tl; simpl.
   clear; tauto.
  destruct a.
  {
    inversion 1; subst.
    inv H2.
    destruct (init_asm_rs ESP); try discriminate.
    unfold Val.add, Mem.loadv in H6.
    constructor. 
    change (AST.Tint) with (AST.type_of_chunk (AST.chunk_of_type AST.Tint)).
    eapply Mem.load_type. eassumption.
    eauto.
  }
  {
    inversion 1; subst.
    inv H2.
    destruct (init_asm_rs ESP); try discriminate.
    unfold Val.add, Mem.loadv in H6.
    constructor. 
    change (AST.Tfloat) with (AST.type_of_chunk (AST.chunk_of_type AST.Tfloat)).
    eapply Mem.load_type. eassumption.
    eauto.
  }
  {
    inversion 1; subst.
    inv H4.
    constructor.
    destruct b1; destruct b0; simpl; trivial.
    eauto.
  }
  {
    inversion 1; subst.
    inv H2.
    destruct (init_asm_rs ESP); try discriminate.
    unfold Val.add, Mem.loadv in H6.
    constructor. 
    simpl. change (AST.Tsingle) with (AST.type_of_chunk (AST.chunk_of_type AST.Tsingle)).
    eapply Mem.load_type. eassumption.
    eauto.
  }
Qed.

Lemma extcall_args_inject_neutral:
  forall init_asm_rs,
  forall m,
    Mem.inject_neutral (Mem.nextblock m) m ->
    forall tl z vl,
      list_forall2 (Asm.extcall_arg init_asm_rs m) (loc_arguments_rec tl z) vl ->
      val_list_inject (Mem.flat_inj (Mem.nextblock m)) vl vl.
Proof.
  induction tl; simpl.
   inversion 2; subst. constructor.
  destruct a.
  {
    inversion 1; subst.
    inv H3.
    constructor.
     eapply Mem.loadv_inject_neutral; eauto.
    eauto.
  }
  {
    inversion 1; subst.
    inv H3.
    constructor.
     eapply Mem.loadv_inject_neutral; eauto.
    eauto.
  }
  {
    inversion 1; subst.
    inv H3.
    inv H5.
    inv H3.
    constructor.
     eapply Mem.loadv_inject_neutral; eauto.
    constructor.
     eapply Mem.loadv_inject_neutral; eauto.
    eauto.
  }
  {
    inversion 1; subst.
    inv H3.
    constructor.
     eapply Mem.loadv_inject_neutral; eauto.
    eauto.
  }
Qed.

(** Invariants *)

Function typ_of_preg (r: preg): typ :=
  match r with
    | FR _ => Tfloat
    | ST0 => Tfloat
    | _ => Tint
  end.

Definition wt_regset (rs: regset) :=
  forall r, Val.has_type (rs # r) (typ_of_preg r).

Record inject_neutral_invariant {F V: Type} (ge: Genv.t F V) (rs: regset) (m: mem): Prop :=
  {
    inv_mem_valid:
      (Genv.genv_next ge <= Mem.nextblock m)%positive;
    inv_mem_inject_neutral:
      Mem.inject_neutral (Mem.nextblock m) m;
    inv_reg_inject_neutral r:
      val_inject (Mem.flat_inj (Mem.nextblock m)) (rs # r) (rs # r)
  }.

Record asm_invariant {F V: Type} (ge: Genv.t F V) (rs: regset) (m: mem): Prop :=
  {
    inv_inject_neutral :> inject_neutral_invariant ge rs m;
    inv_reg_wt: wt_regset rs
  }.

(** Proof that the invariants are preserved by Asm steps. *)

(** For the proof of [exec_instr_inject_neutral] below, we need
[MemoryX.inject_neutral_incr] for [Pallocframe]. *)
Context `{memory_model_x: !Mem.MemoryModelX mem}.

Class MemAccessorsInvariant
      exec_load exec_store
      `{mem_acc: !MemAccessors exec_load exec_store} := 
  {
    exec_load_invariant {F V} ge chunk m a rs rv rs' m':
      exec_load F V ge chunk m a rs rv = Next rs' m' ->
      subtype (type_of_chunk chunk) (typ_of_preg rv) = true ->
      asm_invariant ge rs m ->
      asm_invariant ge rs' m'
    ;

    exec_store_invariant {F V} ge chunk m a rs rv rvl rs' m':
      exec_store F V ge chunk m a rs rv rvl = Next rs' m' ->
      asm_invariant ge rs m ->
      asm_invariant ge rs' m'
  }.

(** Typing invariant on registers *)

Lemma set_reg_wt: 
 forall v r',
   Val.has_type v (typ_of_preg r') ->
   forall rs,
     wt_regset rs ->
     wt_regset (rs # r' <- v)
.
Proof.
  red. intros. destruct (preg_eq r r').
   subst. repeat rewrite Pregmap.gss. assumption.
  repeat rewrite Pregmap.gso; eauto.
Qed.

Lemma set_regs_wt': 
  forall vl tl,
    Val.has_type_list vl tl ->
    forall rs,
      wt_regset rs ->
      forall res, subtype_list tl (map Asm.typ_of_preg res) = true ->
                  wt_regset (set_regs res vl rs).
Proof.
  change Asm.typ_of_preg with typ_of_preg.
  induction vl; destruct tl; try contradiction.
  + simpl. destruct res; try discriminate. simpl; auto.
  + destruct 1. destruct res; simpl; try discriminate.
    destruct (subtype t (typ_of_preg p)) eqn:?; try discriminate.
    simpl. intros.
    eapply IHvl; eauto.
    eapply set_reg_wt; eauto.
    eapply Val.has_subtype; eauto.
Qed.

Lemma set_regs_wt: 
  forall sg vl,
    Val.has_type_list vl (proj_sig_res' sg) ->
    forall rs,
      wt_regset rs ->
      wt_regset (set_regs (loc_external_result sg) vl rs).
Proof.
  destruct sg. unfold proj_sig_res'.
  destruct sig_res.
  - destruct t; simpl; destruct vl; intros Hinv; inv Hinv; try(eapply set_reg_wt; eauto).
    destruct vl; inv H0. intros. repeat eapply set_reg_wt; eauto.
    simpl. destruct v; inv H. constructor. constructor.
  - simpl. intros. destruct vl; auto.
    inv H. eapply set_reg_wt; eauto.
Qed.

Lemma undef_reg_wt:
  forall rs,
    wt_regset rs ->
    forall r',
    wt_regset (rs # r' <- Vundef).
Proof.
  intros; eapply set_reg_wt; simpl; eauto.
Qed.

Lemma undef_regs_wt:
  forall rs,
    wt_regset rs ->
    forall l, wt_regset (undef_regs l rs).
Proof.
  intros until l. revert rs H. induction l; simpl; eauto using undef_reg_wt.
Qed.

Lemma nextinstr_wt:
  forall rs,
    wt_regset rs ->
    wt_regset (nextinstr rs).
Proof.
  unfold nextinstr.  intros.
  apply set_reg_wt; eauto.
  simpl. generalize (H PC); simpl.
  destruct (rs PC); simpl; clear; tauto.
Qed.

Lemma nextinstr_nf_wt:
  forall rs,
    wt_regset rs ->
    wt_regset (nextinstr_nf rs).
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_wt.
  apply undef_regs_wt.
  assumption.
Qed.


(** Inject_neutral *)

Lemma set_reg_inject: 
 forall j v v',
   val_inject j v v' ->
   forall rs rs',
     (forall r, val_inject j (rs#r) (rs'#r)) ->
     forall r' r, val_inject j ((rs#r' <- v)#r) ((rs'#r' <- v')#r)
.
Proof.
  intros. destruct (preg_eq r r').
   subst. repeat rewrite Pregmap.gss. assumption.
  repeat rewrite Pregmap.gso; eauto.
Qed.

Lemma set_regs_inject: 
  forall f rl vl rs,
    (forall r, val_inject f (rs r) (rs r))
    -> val_list_inject f vl vl 
    -> forall r, val_inject f ((set_regs rl vl rs) r) ((set_regs rl vl rs) r).
Proof.
  induction rl; simpl. auto.
  intros. destruct vl. auto.
  inv H0. eapply IHrl; eauto.
  eapply set_reg_inject; eauto.
Qed.

Lemma undef_reg_inject:
  forall j rs rs',
    (forall r, val_inject j (rs#r) (rs'#r)) ->
    forall r' r, val_inject j ((rs#r' <- Vundef)#r) ((rs'#r' <- Vundef)#r).
Proof.
  intros; apply set_reg_inject; auto.
Qed.

Lemma undef_regs_inject:
  forall j rs rs',
    (forall r, val_inject j (rs#r) (rs'#r)) ->
    forall l r, val_inject j ((undef_regs l rs)#r) ((undef_regs l rs')#r).
Proof.
  intros until l. revert rs rs' H. induction l; simpl; eauto using undef_reg_inject.
Qed.

Lemma nextinstr_inject:
  forall j rs rs',
    (forall r, val_inject j (rs#r) (rs'#r)) ->
    forall r, val_inject j ((nextinstr rs)#r) ((nextinstr rs')#r).
Proof.
  unfold nextinstr.  intros.
  apply set_reg_inject; eauto.
  eapply val_add_inject; eauto.
  constructor.
Qed.

Lemma nextinstr_nf_inject:
  forall j rs rs',
    (forall r, val_inject j (rs#r) (rs'#r)) ->
    forall r, val_inject j ((nextinstr_nf rs)#r) ((nextinstr_nf rs')#r).
Proof.
  unfold nextinstr_nf.
  intros.
  apply nextinstr_inject.
  apply undef_regs_inject.
  assumption.
Qed.

Lemma regs_inject_map:
  forall j rs rs',
    (forall r: preg, val_inject j (rs#r) (rs'#r)) ->
    forall args,
  list_forall2 (val_inject j) (map rs args) (map rs' args).
Proof.
  induction args; simpl; constructor; auto.
Qed.

Lemma val_inject_neutral_incr: forall thr v, val_inject (Mem.flat_inj thr) v v -> forall thr', Ple thr thr' -> val_inject (Mem.flat_inj thr') v v.
Proof.
  inversion 1; try constructor.
  clear H4. subst. unfold Mem.flat_inj in *. destruct (plt b1 thr); try discriminate. inv H3.
  econstructor. destruct (plt b1 thr'); try xomega. reflexivity. rewrite Int.add_zero. reflexivity.
Qed.

Lemma extcall_arg_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         l v,
    extcall_arg rs m l v ->
    val_inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  induction 3; auto.
  generalize H0. unfold Mem.loadv. case_eq (rs ESP); try discriminate. simpl. intros. eapply Mem.loadv_inject_neutral; eauto.
Qed.

Lemma extcall_args_inject_neutral':
  forall m rs
         (Hinj_reg: forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         sg args,
    extcall_arguments rs m sg args ->
    list_forall2 (val_inject (Mem.flat_inj (Mem.nextblock m))) args args.
Proof.
  unfold extcall_arguments. intros until sg. generalize (loc_arguments sg). clear sg.
  induction 1; constructor; eauto using extcall_arg_inject_neutral'.
Qed.

Lemma annot_arg_inject_neutral:
  forall m rs
         (Hinj_reg: forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         l v,
    annot_arg rs m l v ->
    val_inject (Mem.flat_inj (Mem.nextblock m)) v v.
Proof.
  induction 3; auto.
  exploit Mem.neutral_inject; eauto.
  intro.
  eapply Mem.load_inject_neutral; eauto.
Qed.

Lemma annot_args_inject_neutral:
  forall m rs
         (Hinj_reg: forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r))
         (Hinj_mem: Mem.inject_neutral (Mem.nextblock m) m)
         sg args,
    annot_arguments rs m sg args ->
    list_forall2 (val_inject (Mem.flat_inj (Mem.nextblock m))) args args.
Proof.
  induction 3; constructor; eauto using annot_arg_inject_neutral.
Qed.

Lemma shl_inject_neutral:
  forall f v1 v2,
    val_inject f (Val.shl v1 v2) (Val.shl v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shr_inject_neutral:
  forall f v1 v2,
    val_inject f (Val.shr v1 v2) (Val.shr v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shru_inject_neutral:
  forall f v1 v2,
    val_inject f (Val.shru v1 v2) (Val.shru v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma ror_inject_neutral:
  forall f v1 v2,
    val_inject f (Val.ror v1 v2) (Val.ror v1 v2).
Proof.
  destruct v1; destruct v2; try constructor.
  simpl.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma of_bool_inject_neutral:
  forall f b,
    val_inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  destruct b; simpl; constructor.
Qed.

Lemma compare_floats_inject_neutral:
  forall f rs,
    (forall r: preg, val_inject f (rs r) (rs r)) ->
    forall a b r,
      val_inject f (compare_floats a b rs r) (compare_floats a b rs r).
Proof with (simpl;
            repeat apply undef_reg_inject;
            auto using of_bool_inject_neutral).
  intros. unfold compare_floats. destruct a...
  destruct b...
  repeat apply set_reg_inject...
Qed.

Lemma cmpu_inject_neutral:
  forall f p c a b,
    val_inject f (Val.cmpu p c a b) (Val.cmpu p c a b).
Proof.
  intros.
  unfold Val.cmpu. destruct (Val.cmpu_bool p c a b); simpl; auto.
  destruct b0; constructor.
Qed.

Lemma cmp_inject_neutral:
  forall f p c a,
    val_inject f (Val.cmp p c a) (Val.cmp p c a).
Proof.
  intros.
  unfold Val.cmp. destruct (Val.cmp_bool p c a); simpl; auto.
  destruct b; constructor.
Qed.

Lemma sub_overflow_inject_neutral:
  forall f a b,
    val_inject f (Val.sub_overflow a b) (Val.sub_overflow a b).
Proof.
  intros.
  unfold Val.sub_overflow.
  destruct a; destruct b; constructor.
Qed.

Lemma negative_inject_neutral:
  forall f a,
    val_inject f (Val.negative a) (Val.negative a).
Proof.
  unfold Val.negative.
  destruct a; constructor.
Qed.

Lemma compare_ints_inject_neutral:
  forall f rs,
    (forall r: preg, val_inject f (rs r) (rs r)) ->
    forall a b m r,
      val_inject f (compare_ints a b rs m r) (compare_ints a b rs m r).
Proof.
  unfold compare_ints.
  intros.
  apply undef_reg_inject.
  eauto using set_reg_inject, cmpu_inject_neutral, undef_reg_inject, negative_inject_neutral, sub_overflow_inject_neutral.
Qed.

Lemma symbol_offset_inject_neutral:
  forall {F V} (ge: _ F V) m,
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    forall i ofs,
    val_inject (Mem.flat_inj (Mem.nextblock m)) (symbol_offset ge i ofs) (symbol_offset ge i ofs).
Proof.
  intros.
  unfold symbol_offset. case_eq (Genv.find_symbol ge i); auto.
  intros.
  destruct (plt b (Mem.nextblock m)) eqn:Heqs.
   econstructor. unfold Mem.flat_inj. rewrite Heqs. reflexivity.
  rewrite Int.add_zero. reflexivity.
  clear Heqs. exfalso. exploit Genv.genv_symb_range; eauto. xomega.
Qed.

Lemma eval_addrmode_inject_neutral:
  forall {F V} (ge: _ F V) m,
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    forall rs,
      (forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)) ->
    forall a,
    val_inject (Mem.flat_inj (Mem.nextblock m)) (eval_addrmode ge a rs) (eval_addrmode ge a rs).
Proof.
  intros.
  unfold eval_addrmode.
  destruct a.
  apply val_add_inject.
   destruct base; auto; constructor.
  apply val_add_inject.
  destruct ofs; try constructor.
  destruct p.
  destruct (Int.eq i0 Int.one); auto.
  destruct (rs i); destruct (Vint i0); constructor.
  destruct const; try constructor.
  destruct p.
  eauto using symbol_offset_inject_neutral.
Qed.

(** Proofs related to CertiKOS *)
Section VAL_INJ_OPS.

Variable f: meminj.

Remark val_and_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.and v1 v2) (Val.and v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_or_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.or v1 v2) (Val.or v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_xor_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.xor v1 v2) (Val.xor v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_ror_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.ror v1 v2) (Val.ror v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
Qed.

Remark val_shl_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.shl v1 v2) (Val.shl v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
Qed.

Remark val_shr_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.shr v1 v2) (Val.shr v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
Qed.

Remark val_shru_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.shru v1 v2) (Val.shru v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
Qed.

Remark val_mul_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.mul v1 v2) (Val.mul v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_mulhs_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.mulhs v1 v2) (Val.mulhs v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_mulhu_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.mulhu v1 v2) (Val.mulhu v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_zero_ext_inject:
  forall v1 v1' n,
    val_inject f v1 v1' ->
    val_inject f (Val.zero_ext n v1) (Val.zero_ext n v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_sign_ext_inject:
  forall v1 v1' n,
    val_inject f v1 v1' ->
    val_inject f (Val.sign_ext n v1) (Val.sign_ext n v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_singleoffloat_inject:
  forall v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.singleoffloat v1) (Val.singleoffloat v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_neg_inject:
  forall v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.neg v1) (Val.neg v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_notint_inject:
  forall v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.notint v1) (Val.notint v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_addf_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.addf v1 v2) (Val.addf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto.
Qed.

Remark val_subf_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.subf v1 v2) (Val.subf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_mulf_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.mulf v1 v2) (Val.mulf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_divf_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.divf v1 v2) (Val.divf v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
Qed.

Remark val_negf_inject:
  forall v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.negf v1) (Val.negf v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_absf_inject:
  forall v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.absf v1) (Val.absf v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_intoffloat_inject:
  forall v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.maketotal (Val.intoffloat v1))  (Val.maketotal (Val.intoffloat v1')).
Proof.
  intros. inv H; simpl; auto.
  destruct (Float.intoffloat); simpl; auto.
Qed.

Remark val_floatofint_inject:
  forall v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.maketotal (Val.floatofint v1))  (Val.maketotal (Val.floatofint v1')).
Proof.
  intros. inv H; simpl; auto.
Qed.

Lemma val_compare_floats_inject_neutral:
  forall rs rs',
    (forall r: preg, val_inject f (Pregmap.get r rs) (Pregmap.get r rs')) ->
    forall v1 v2 v1' v2', 
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    forall r,
      val_inject f (compare_floats v1 v2 rs r) (compare_floats v1' v2' rs' r).
Proof.
  unfold compare_floats. intros.
  inv H0; inv H1; simpl; eauto;
  repeat match goal with
           | [|- context[match ?a with |_ => _ end]] => destruct a
         end;
  repeat apply undef_reg_inject; eauto 1;
  repeat eapply set_reg_inject; eauto;
  auto using of_bool_inject_neutral.
Qed.

Lemma val_compare_ints_inject_neutral:
  forall rs rs' m m',
    (forall r: preg, val_inject f (Pregmap.get r rs) (Pregmap.get r rs')) ->
    Mem.inject f m m' ->
    forall v1 v2 v1' v2', 
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    forall r,
      val_inject f (compare_ints v1 v2 rs m r) (compare_ints v1' v2' rs' m' r).
Proof.
  unfold compare_ints.
  intros; apply undef_reg_inject.
  repeat eapply set_reg_inject; eauto.
  - inv H1; inv H2; simpl; auto.
  - exploit (val_sub_inject f v1 v1' v2); eauto.
    intros Hinv. inv Hinv; simpl; auto.
  - unfold Val.cmpu.
    caseEq (Val.cmpu_bool (Mem.valid_pointer m) Clt v1 v2); intros; try constructor.
    assert (HW: (Val.cmpu_bool (Mem.valid_pointer m') Clt v1' v2' = Some b)).
    {
      eapply val_cmpu_bool_inject; eauto 1; intros.
      - eapply Mem.valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
      - eapply Mem.different_pointers_inject; eauto.
    }
    rewrite HW. simpl.
    destruct b; constructor.
  - unfold Val.cmpu.
    caseEq (Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2); intros; try constructor.
    assert (HW: (Val.cmpu_bool (Mem.valid_pointer m') Ceq v1' v2' = Some b)).
    {
      eapply val_cmpu_bool_inject; eauto 1; intros.
      - eapply Mem.valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_val; eauto.
      - eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
      - eapply Mem.different_pointers_inject; eauto.
    }
    rewrite HW. simpl.
    destruct b; constructor.
Qed.

Remark val_divu_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    forall v,
      Val.divu v1 v2 = Some v ->
      exists v', Val.divu v1' v2' = Some v'
                 /\ val_inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero).
  discriminate.
  inv H1. eauto.
Qed.

Remark val_modu_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    forall v,
      Val.modu v1 v2 = Some v ->
      exists v', Val.modu v1' v2' = Some v'
                 /\ val_inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero).
  discriminate.
  inv H1. eauto.
Qed.

Remark val_divs_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    forall v,
      Val.divs v1 v2 = Some v ->
      exists v', Val.divs v1' v2' = Some v'
                 /\ val_inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero
                   || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone).
  discriminate.
  inv H1; eauto.
Qed.

Remark val_mods_inject:
  forall v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    forall v,
      Val.mods v1 v2 = Some v ->
      exists v', Val.mods v1' v2' = Some v'
                 /\ val_inject f v v'.
Proof.
  intros. inv H; inv H0; simpl in *; try discriminate; eauto.
  destruct (Int.eq i0 Int.zero
                   || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone).
  discriminate.
  inv H1; eauto.
Qed.

Remark val_negl_inject:
  forall f v1 v1',
    val_inject f v1 v1' ->
    val_inject f (Val.negl v1) (Val.negl v1').
Proof.
  intros. inv H; simpl; auto.
Qed.

Remark val_addl_inject:
  forall f v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.addl v1 v2) (Val.addl v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto.
Qed.

Remark val_subl_inject:
  forall f v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.subl v1 v2) (Val.subl v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto.
Qed.

Remark val_mull'_inject:
  forall f v1 v1' v2 v2',
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    val_inject f (Val.mull' v1 v2) (Val.mull' v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto.
Qed.

Remark set_regs_inject': 
  forall f rl vl vl' rs rs',
    (forall r, val_inject f (rs r) (rs' r))
    -> val_list_inject f vl vl' 
    -> forall r, val_inject f ((set_regs rl vl rs) r) ((set_regs rl vl' rs') r).
Proof.
  induction rl; simpl. auto.
  intros. destruct vl; inv H0. auto.
  eapply IHrl; eauto.
  eapply set_reg_inject; eauto.
Qed.

End VAL_INJ_OPS.

(** Proof for [exec_instr] *)

Section WITHMEMACCESSORSINVARIANT.

  Context {exec_load exec_store}
          `{mem_acc_inv: MemAccessorsInvariant exec_load exec_store}.

  Section WITHFINDLABELS.
    Context `{find_labels_prf: FindLabels}.

    Lemma goto_label_wt:
      forall rs,
        wt_regset rs ->
        forall m c lbl rs' m',
          Next rs' m' = goto_label c lbl rs m ->
          wt_regset rs'.
    Proof.
      unfold goto_label. intros until m'. destruct (label_pos lbl 0 (fn_code0 c)); try discriminate.
      case_eq (rs PC); try discriminate.
      injection 2; intros; subst.
      apply set_reg_wt; simpl; auto.
    Qed.

    Lemma goto_label_inject_neutral:
      forall {F V} (ge: _ F V) rs m,
        inject_neutral_invariant ge rs m ->
        forall c lbl rs' m',
          Next rs' m' = goto_label c lbl rs m ->
          inject_neutral_invariant ge rs' m'.
    Proof.
      inversion 1; subst.
      unfold goto_label. intros until m'. destruct (label_pos lbl 0 (fn_code0 c)); try discriminate.
      case_eq (rs PC); try discriminate.
      injection 2; intros; subst.
      split; auto.
      apply set_reg_inject; auto.
      generalize (inv_reg_inject_neutral0 PC).
      rewrite H0.
      inversion 1.
      clear H8. subst. econstructor. eassumption.
      unfold Mem.flat_inj in H6. destruct (plt b (Mem.nextblock m)); try discriminate. inv H6. rewrite Int.add_zero. reflexivity.
    Qed.

    Theorem exec_instr_inject_neutral:
      forall {F V} (ge: _ F V) rs m,
        asm_invariant ge rs m ->
        forall c rs' m' i,
          Next rs' m' = exec_instr ge c i rs m ->
          inject_neutral_invariant ge rs' m'
    .
    Proof.
      inversion 1; subst.
      inversion inv_inject_neutral0; subst.
      intros until i.
      destruct i; simpl;
      repeat match goal with
      | |- Next rs' m' = exec_load _ _ ge ?chunk m ?a rs ?rd ->
        inject_neutral_invariant ge rs' m' =>
        let J := fresh in
        intro J; symmetry in J;
        eapply inv_inject_neutral;
        eapply exec_load_invariant; eauto
      | |- Next rs' m' = exec_store _ _ ge ?chunk m ?a rs ?rd ?l ->
        inject_neutral_invariant ge rs' m' =>
        let J := fresh in
        intro J; symmetry in J;
        eapply inv_inject_neutral;
        eapply exec_store_invariant; eauto
      | |- Next rs' m' = match eval_testcond ?c rs with Some _ => _ | None => _ end -> _ => destruct (eval_testcond c rs) as [[|]|]
      | |- Next rs' m' = goto_label ?c ?lbl rs m -> _ =>
        eapply goto_label_inject_neutral; eauto
      | |- Next rs' m' = (if ?b then _ else _) -> _ => destruct b
      | |- Next rs' m' = Next _ m -> _ =>
        injection 1; intros; subst; constructor; auto;
        repeat match goal with 
          | |- forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (nextinstr ?rs r) (nextinstr ?rs r) => apply nextinstr_inject
          | |- forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (nextinstr_nf ?rs r) (nextinstr_nf ?rs r) => apply nextinstr_inject
          | |- forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (undef_regs ?l ?rs r) (undef_regs ?l ?rs r) => apply undef_regs_inject
          | |- forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (?rs # ?r' <- Vundef r) (?rs # ?r' <- Vundef r) => apply undef_reg_inject
          | |- forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (?rs # ?r' <- ?v r) (?rs # ?r' <- ?v r) => apply set_reg_inject
          | |- val_inject (Mem.flat_inj (Mem.nextblock m)) (rs ?r) (rs ?r) => now auto
          | |- forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r) => now auto
          | |- val_inject (Mem.flat_inj (Mem.nextblock m)) (symbol_offset ge ?sy ?of) (symbol_offset ge ?sy ?of) =>
            eapply symbol_offset_inject_neutral
          | |- val_inject (Mem.flat_inj (Mem.nextblock m)) (eval_addrmode ge ?sy ?of) (eval_addrmode ge ?sy ?of) =>
            eapply eval_addrmode_inject_neutral
          | |- Ple (Genv.genv_next ge) (Mem.nextblock m) => assumption
          | |- val_inject _ (Vint ?i) (Vint ?i) => constructor
          | |- val_inject _ (Vfloat ?i) (Vfloat ?i) => constructor
          | |- forall r, val_inject _ (compare_ints ?a ?b rs m r) (compare_ints ?a ?b rs m r) => apply compare_ints_inject_neutral
          | |- forall r, val_inject _ (compare_floats ?a ?b rs r) (compare_floats ?a ?b rs r) => apply compare_floats_inject_neutral
          | |- val_inject _ (Val.add ?i ?g) (Val.add ?i ?g) => apply val_add_inject
          | |- val_inject _ (Val.sub ?i ?g) (Val.sub ?i ?g) => apply val_sub_inject
          | |- val_inject _ (Val.zero_ext ?n ?v) (Val.zero_ext ?n ?v) => destruct v; simpl; constructor
          | |- val_inject _ (Val.sign_ext ?n ?v) (Val.sign_ext ?n ?v) => destruct v; simpl; constructor
          | |- val_inject _ (Val.singleoffloat ?v) (Val.singleoffloat ?v) => destruct v; simpl; constructor
          | |- val_inject _ (Val.maketotal (Val.floatofint ?v)) (Val.maketotal (Val.floatofint ?v)) => destruct v; simpl; constructor
          | |- val_inject _ (Val.neg ?v) (Val.neg ?v) => destruct v; simpl; constructor
          | |- val_inject _ (Val.notint ?v) (Val.notint ?v) => destruct v; simpl; constructor
          | |- val_inject _ (Val.negf ?v) (Val.negf ?v) => destruct v; simpl; constructor
          | |- val_inject _ (Val.absf ?v) (Val.absf ?v) => destruct v; simpl; constructor
          | |- val_inject _ (Val.mul ?v1 ?v2) (Val.mul ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.mulf ?v1 ?v2) (Val.mulf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.and ?v1 ?v2) (Val.and ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.addf ?v1 ?v2) (Val.addf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.subf ?v1 ?v2) (Val.subf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.mulhs ?v1 ?v2) (Val.mulhs ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.mulhu ?v1 ?v2) (Val.mulhu ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.divf ?v1 ?v2) (Val.divf ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.or ?v1 ?v2) (Val.or ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ (Val.shl ?v1 ?v2) (Val.shl ?v1 ?v2) => apply shl_inject_neutral
          | |- val_inject _ (Val.shr ?v1 ?v2) (Val.shr ?v1 ?v2) => apply shr_inject_neutral
          | |- val_inject _ (Val.shru ?v1 ?v2) (Val.shru ?v1 ?v2) => apply shru_inject_neutral
          | |- val_inject _ (Val.ror ?v1 ?v2) (Val.ror ?v1 ?v2) => apply ror_inject_neutral
          | |- val_inject _ (Val.xor ?v1 ?v2) (Val.xor ?v1 ?v2) => destruct v1; destruct v2; simpl; constructor
          | |- val_inject _ Vzero Vzero => constructor
          | |- val_inject _ Vone Vone => constructor
          | |- val_inject _ (Val.of_optbool ?v) (Val.of_optbool ?v) => destruct v as [[|] |]; simpl; constructor
          | |- val_inject _ Vundef Vundef => constructor
          | |- val_inject _ (Val.maketotal ?v) (Val.maketotal ?v) => case_eq v; simpl; auto
        end
      | |- Next _ _ = Stuck -> _ => discriminate
    end.
    * (* intoffloat *)
      unfold Val.intoffloat. destruct (rs r1); try discriminate. destruct (Float.intoffloat f); try discriminate. simpl. injection 1; intros; subst. constructor.
    * (* unsigned division *)
      case_eq (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
      intros until 1.
      case_eq (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
      intros until 1.
      injection 1; intros; subst.
      destruct (rs EAX); destruct (rs # EDX <- Vundef r1); simpl in *; try discriminate.
      destruct (Int.eq i0 Int.zero); try discriminate.
      inv H0. inv H1.
      constructor; auto.
      apply set_reg_inject.
      apply val_add_inject.
      apply undef_regs_inject.
      apply set_reg_inject.
       constructor.
      apply set_reg_inject.
       constructor.
      assumption.
      constructor.
      apply undef_regs_inject.
      apply set_reg_inject.
       constructor.
      apply set_reg_inject.
       constructor.
      assumption.
    * (* signed division *)
      case_eq (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
      intros until 1.
      case_eq (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
      intros until 1.
      injection 1; intros; subst.
      destruct (rs EAX); destruct (rs # EDX <- Vundef r1); simpl in *; try discriminate.
      destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone);
        try discriminate.
      inv H0. inv H1.
      constructor; auto.
      apply set_reg_inject.
      apply val_add_inject.
      apply undef_regs_inject.
      apply set_reg_inject.
       constructor.
      apply set_reg_inject.
       constructor.
      assumption.
      constructor.
      apply undef_regs_inject.
      apply set_reg_inject.
       constructor.
      apply set_reg_inject.
       constructor.
      assumption.
    * (* switch *)
      destruct (rs r); try discriminate.
      destruct (list_nth_z tbl (Int.unsigned i)); try discriminate.
      eapply goto_label_inject_neutral.
      split; auto.
    * (* Pallocframe *)
      case_eq (Mem.alloc m 0 sz).
      intros until 1.
      exploit @Mem.nextblock_alloc; eauto.
      intro NEXTBLOCK.
      exploit @Mem.alloc_result; eauto.
      intro; subst.
      exploit @Mem.alloc_inject_neutral.
      eassumption.
      eapply Mem.inject_neutral_incr. eassumption. instantiate (1 := Psucc (Mem.nextblock m)). xomega. xomega.
      rewrite <- NEXTBLOCK.
      intro.
      case_eq (Mem.store Mint32 m0 (Mem.nextblock m) (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)); try discriminate.
      intros until 1.
      exploit Mem.store_inject_neutral; eauto.
      unfold block in *; xomega.
      eapply val_inject_neutral_incr; eauto. unfold block in *; xomega.
      intro.
      exploit Mem.nextblock_store; eauto.
      intro.
      case_eq (Mem.store Mint32 m1 (Mem.nextblock m) (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)); try discriminate.
      intros until 1.
      exploit Mem.store_inject_neutral; eauto.
      unfold block in *; xomega.
      eapply val_inject_neutral_incr; eauto. unfold block in *; xomega.
      intro.
      exploit Mem.nextblock_store; eauto.
      intro.
      injection 1; intros; subst.
      split.
       unfold block in *; xomega.
      congruence.
      apply nextinstr_inject.
      apply set_reg_inject.
       econstructor. unfold Mem.flat_inj. destruct (plt (Mem.nextblock m) (Mem.nextblock m2)); try (unfold block in *; exfalso; xomega). reflexivity. reflexivity.
      intro. eapply val_inject_neutral_incr; eauto using set_reg_inject.
      unfold block in *; xomega.
    * (* Pfreeframe *)
      case_eq (rs ESP); try discriminate.
      intros until 1. simpl.
      case_eq (Mem.load Mint32 m b (Int.unsigned (Int.add i ofs_ra))); try discriminate.
      intros until 1.
      case_eq (Mem.load Mint32 m b (Int.unsigned (Int.add i ofs_link))); try discriminate.
      intros until 1.
      case_eq (Mem.free m b 0 sz); try discriminate.
      injection 2; intros; subst.
      assert (Plt b (Mem.nextblock m)).
       eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies. eapply Mem.load_valid_access. eassumption. constructor.
      split;
       erewrite Mem.nextblock_free; eauto.
       eapply Mem.free_inject_neutral; eauto.
      apply nextinstr_inject.
      apply set_reg_inject.
       eapply Mem.load_inject_neutral; eauto. 
      apply set_reg_inject; auto.
      eapply Mem.load_inject_neutral; eauto. 
    Qed.

     (** Well-typed state *)

    Ltac wt_solve := 
      match goal with
        | |- Next _ _ = Stuck -> _ => discriminate
        | |- Next _ _ = Next _ _ -> _ =>
          let H := fresh in (intro H; injection H; clear H; intros; subst)
        | |- wt_regset (nextinstr_nf _) => apply nextinstr_nf_wt
        | |- wt_regset (nextinstr _) => apply nextinstr_wt
        | |- wt_regset (undef_regs _ _) => apply undef_regs_wt
        | |- wt_regset (_ # _ <- Vundef) => apply undef_reg_wt
        | |- wt_regset (_ # _ <- _) => apply set_reg_wt; simpl
        | [ H : wt_regset ?rs |- Val.has_type (?rs _) _ ] => apply H
        | |- True => exact I
        | |- ?x = ?x => reflexivity
        | |- Next ?rs' _ = exec_store _ _ _ _ _ _ _ _ _ -> wt_regset ?rs' =>
          let K := fresh in
          intro K;
            symmetry in K;
            eapply inv_reg_wt;
            eapply exec_store_invariant; eauto
        | |- Next ?rs' _ = exec_load _ _ _ _ _ _ _ _ -> wt_regset ?rs' =>
          let K := fresh in
          intro K;
            symmetry in K;
            eapply inv_reg_wt;
            eapply exec_load_invariant; eauto
        | |- Val.has_type (Val.zero_ext _ ?v) Tint => destruct v; simpl
        | |- Val.has_type (Val.sign_ext _ ?v) Tint => destruct v; simpl
        | |- Val.has_type (Val.singleoffloat ?v) Tfloat => destruct v; simpl
        | |- Val.has_type (Val.maketotal (Val.intoffloat ?v)) Tint => destruct v; simpl
        | |- Val.has_type (Val.maketotal (option_map Vint ?v)) Tint => destruct v; simpl
        | |- Val.has_type (Val.maketotal (Val.floatofint ?v)) Tfloat => destruct v; simpl
        | |- Val.has_type (Val.neg ?v) Tint => destruct v; simpl
        | |- Val.has_type (Val.notint ?v) Tint => destruct v; simpl
        | |- Val.has_type (Val.negative ?v) Tint => destruct v; simpl
        | |- Val.has_type (Val.mul ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.and ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.add ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.sub ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.or ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.xor ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.shl ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.shru ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.shr ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.sub_overflow ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.ror ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.addf ?v1 ?v2) Tfloat => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.mulf ?v1 ?v2) Tfloat => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.divf ?v1 ?v2) Tfloat => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.subf ?v1 ?v2) Tfloat => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.negf ?v) Tfloat => destruct v; simpl
        | |- Val.has_type (Val.absf ?v) Tfloat => destruct v; simpl
        | |- Val.has_type (Val.mulhs ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (Val.mulhu ?v1 ?v2) Tint => destruct v1; destruct v2; simpl
        | |- Val.has_type (if ?cond then _ else _) _ => destruct cond; simpl
        | |- Val.has_type match ?opt with Some _ => _ | None => _ end _ => destruct opt; simpl
        | |- Val.has_type match ?addr with Addrmode _ _ _ => _ end _ => destruct addr; simpl
        | |- Val.has_type (symbol_offset _ _ _) _ => unfold symbol_offset
        | |- Val.has_type (eval_addrmode _ _ _) _ => unfold eval_addrmode
        | |- Val.has_type (Val.cmp _ _ _) _ => unfold Val.cmp
        | |- Val.has_type (Val.cmpu _ _ _ _) _ => unfold Val.cmpu
        | |- Val.has_type (Val.of_optbool ?v) Tint => destruct v; simpl
        | |- Val.has_type (Val.of_bool ?v) Tint => destruct v; simpl
        | |- Next ?rs' _ = goto_label _ _ _ _ -> wt_regset ?rs' => eapply goto_label_wt
        | |- Next ?rs' _ = match eval_testcond ?c ?r with Some _ => _ | None => _ end -> _ => destruct (eval_testcond c r); simpl
        | |- (Next _ _ = if ?b then _ else _) -> _ => destruct b; simpl
        | |- wt_regset (compare_ints _ _ _ _) => unfold compare_ints
        | _ => assumption
      end.

    
    Theorem exec_instr_wt:
      forall {F V} (ge: _ F V) rs m,
        asm_invariant ge rs m ->
        forall c rs' m' i,
          Next rs' m' = exec_instr ge c i rs m ->
          wt_regset rs'
    .
    Proof with (repeat wt_solve).
      inversion 1; subst.
      intros until i.
      
      destruct i; simpl...

      + (* unsigned division *)
        case_eq (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
        intros until 1.
        case_eq (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
        intros until 1.
        injection 1; intros; subst.
        destruct (rs EAX); destruct (rs # EDX <- Vundef r1); simpl in *; try discriminate.
        destruct (Int.eq i0 Int.zero); try discriminate.
        inv H0. inv H1...

      + (* signed division *)
        case_eq (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
        intros until 1.
        case_eq (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); try discriminate.
        intros until 1.
        injection 1; intros; subst.
        destruct (rs EAX); destruct (rs # EDX <- Vundef r1); simpl in *; try discriminate.
        destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); try discriminate.
        inv H0. inv H1...

      + (* compare floats *)
        unfold compare_floats.
        destruct (rs r1)...
        destruct (rs r2)...

      + (* switch *)
        destruct (rs r)...
        destruct (list_nth_z tbl (Int.unsigned i))...

      + (* Pallocframe *)
        destruct (Mem.alloc m 0 sz).
        destruct (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)))...
        destruct (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)))...

      + (* Pfreeframe *)  
        destruct (Val.add (rs ESP) (Vint ofs_ra)); simpl; try discriminate.
        case_eq (Mem.load Mint32 m b (Int.unsigned i)); try discriminate.
        intros until 1.
        exploit Mem.load_type; eauto.
        simpl.
        clear H0.
        intro.
        destruct (Val.add (rs ESP) (Vint ofs_link)); simpl; try discriminate.
        case_eq (Mem.load Mint32 m b0 (Int.unsigned i0)); try discriminate.
        intros until 1.
        exploit Mem.load_type; eauto.
        clear H1.
        simpl.
        intro.
        destruct (rs ESP); try discriminate.
        destruct (Mem.free m b1 0 sz)...

    Qed.

    Theorem exec_instr_invariant:
      forall {F V} (ge: _ F V) rs m,
        asm_invariant ge rs m ->
        forall c rs' m' i,
          exec_instr ge c i rs m = Next rs' m' ->
          asm_invariant ge rs' m'
    .
    Proof.
      intros. symmetry in H0. constructor; eauto using exec_instr_wt, exec_instr_inject_neutral.
    Qed.

End WITHFINDLABELS.  

End WITHMEMACCESSORSINVARIANT.

(** Extensionality properties over [exec_load] and [exec_store] *)

Section WITH2MEMACCESSORS.
  Context `{find_labels_prf: FindLabels}.

  Context {exec_load1 exec_store1}
          `{mem_acc1: !MemAccessors exec_load1 exec_store1}
          {exec_load2 exec_store2}
          `{mem_acc2: !MemAccessors exec_load2 exec_store2}.

  Theorem exec_instr_mem_accessors_ext:
    forall {F V} ge m rs
           (EXEC_LOAD_EXT:
              forall chunk a rd rs' m',
                exec_load1 F V ge chunk m a rs rd = Next rs' m' ->
                exec_load2 F V ge chunk m a rs rd = Next rs' m')
           (EXEC_STORE_EXT:
              forall chunk a rd rl rs' m',
                exec_store1 F V ge chunk m a rs rd rl = Next rs' m' ->
                exec_store2 F V ge chunk m a rs rd rl = Next rs' m')
           f i rs' m'
           (EXEC_INSTR1:
              exec_instr (MemAccessors0 := mem_acc1) ge f i rs m = Next rs' m')
    ,
      exec_instr (MemAccessors0 := mem_acc2) ge f i rs m = Next rs' m'
  .
  Proof.
    destruct i; simpl; intros; eauto.
  Qed.

End WITH2MEMACCESSORS.

(** Extensionality properties over [goto_label] *)

Section WITH2FINDLABEL.

  Context `{find_labels_prf1: FindLabels}
          `{find_labels_prf2: FindLabels}.

  Context {exec_load exec_store}
          `{mem_acc: !MemAccessors exec_load exec_store}.

  Theorem exec_instr_find_labels_ext:
    forall {F V} (ge: _ F V) m rs
           f f'
           (GOTO_LABEL:
              forall l rs' m', goto_label f l rs m = Next rs' m' ->
                               goto_label f' l rs m = Next rs' m')
           i rs' m'
           (EXEC_INSTR1:
              exec_instr (Hfl := find_labels_prf1) ge f i rs m = Next rs' m')
    ,
      exec_instr (Hfl := find_labels_prf2) ge f' i rs m = Next rs' m'
  .
  Proof.
    destruct i; simpl; intros; eauto.
    * destruct (eval_testcond c rs); try discriminate.
      destruct b; eauto.
    * destruct (eval_testcond c1 rs); try discriminate.
      destruct b.
      + destruct (eval_testcond c2 rs); try discriminate.
        destruct b; eauto.
      + destruct (eval_testcond c2 rs); try discriminate; eauto.
    * destruct (rs r); try discriminate.
      destruct (list_nth_z tbl (Int.unsigned i)); try discriminate.
      eauto.
  Qed.

End WITH2FINDLABEL.

(** Extensionality over [ge] *)

Section WITH2GE.
  Context `{find_labels_prf: FindLabels}.

  Context {exec_load exec_store}
          `{mem_acc: !MemAccessors exec_load exec_store}.

  Context  {F1 V1} (ge1: _ F1 V1)
           {F2 V2} (ge2: _ F2 V2)
           (genv_symbols_preserved: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i).

  Lemma symbol_offset_symbols_preserved:
    forall i o,
      symbol_offset ge2 i o = symbol_offset ge1 i o.
  Proof.
    unfold symbol_offset. intros. rewrite genv_symbols_preserved. reflexivity.
  Qed.
    
  Lemma eval_addrmode_symbols_preserved:
    forall a rs,
      eval_addrmode ge2 a rs = eval_addrmode ge1 a rs.
  Proof.
    unfold eval_addrmode. intros. destruct a.
    destruct const; try reflexivity.
    destruct p.
    rewrite symbol_offset_symbols_preserved.
    reflexivity.
  Qed.

  Theorem exec_instr_symbols_preserved:
    forall
      rs m
      (exec_load_symbols_preserved:
         forall chunk a rd,
                exec_load _ _ ge2 chunk m a rs rd =
                exec_load _ _ ge1 chunk m a rs rd)
      (exec_store_symbols_preserved:
         forall chunk a rd rl,
           exec_store _ _ ge2 chunk m a rs rd rl =
           exec_store _ _ ge1 chunk m a rs rd rl)
      f i,
      exec_instr ge2 f i rs m = exec_instr ge1 f i rs m.
  Proof.
  destruct i; try reflexivity; simpl; eauto;
  try rewrite eval_addrmode_symbols_preserved; eauto;
  try rewrite symbol_offset_symbols_preserved; eauto.
  Qed.

End WITH2GE.

End WITHCONFIG.

(** Proof of invariants for default accessors *)

Section WITHMEM.
Context `{Hmem: Mem.MemoryModel}.

Local Instance mem_accessors_default_invariant:
  MemAccessorsInvariant
    _ _
    (mem_acc := Asm.mem_accessors_default).
Proof.
  constructor.
  * unfold exec_load. intros.
    destruct (eval_addrmode ge a rs); try discriminate.
    simpl in H.
    destruct (Mem.load chunk m b (Int.unsigned i)) eqn:?; try discriminate.
    inv H.
    inversion H1.
    inversion inv_inject_neutral0.
    constructor; auto.
    constructor; auto.
    apply nextinstr_nf_inject.
    apply set_reg_inject; auto.
    eapply Mem.load_inject_neutral; eauto.
    apply nextinstr_nf_wt; auto.
    apply set_reg_wt; auto.
    eapply Val.has_subtype; eauto. eapply Mem.load_type; eauto.
  * unfold exec_store. intros.
    destruct (eval_addrmode ge a rs); try discriminate.
    simpl in H.
    destruct (Mem.store chunk m b (Int.unsigned i) (rs rv)) eqn:?; try discriminate.
    inv H.
    inversion H0.
    inversion inv_inject_neutral0.
    constructor.
    constructor.
    + erewrite Mem.nextblock_store; eauto.
    + erewrite Mem.nextblock_store; eauto. eapply Mem.store_inject_neutral; eauto.
      eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies.
      - eapply Mem.store_valid_access_3; eauto.
      - constructor.
    + apply nextinstr_nf_inject; auto.
      apply undef_regs_inject; auto.
      erewrite Mem.nextblock_store; eauto.
    + apply nextinstr_nf_wt.
      apply undef_regs_wt; auto.
Qed.

End WITHMEM.
