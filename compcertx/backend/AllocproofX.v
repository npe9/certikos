Require compcert.backend.Allocproof.
Require LTLX.
Require RTLX.
Require SmallstepX.
Require EventsX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Locations.
Import Conventions.
Import RTLX.
Import RTLtyping.
Import LTLX.
Import Allocation.
Export Allocproof.

Section PRESERVATION.
Context `{i64helpers: SelectLong.I64helpers}.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Variable init_m: mem.
Variable init_ltl_ls: LTL.locset.

Variable sg: signature.
Variable args: list val.
Hypothesis Hargs: args = map init_ltl_ls (loc_arguments sg).

Lemma initial_states_simulation:
  forall i,
  forall st1, 
    initial_state_decode_longs (RTLX.initial_state prog i init_m) sg args st1 ->
    exists st2, LTLX.initial_state init_ltl_ls tprog i sg args init_m st2 /\ match_states tprog (writable_block_ops := writable_block_with_init_mem_writable_block_ops init_m) init_ltl_ls (sig_res sg) st1 st2.
Proof.  
  inversion 1; subst.
  inv INIT.
  exploit function_ptr_translated; eauto.
  destruct 1 as [? [? ?]].
  esplit.
  split.
  econstructor.
  erewrite symbols_preserved; eauto.
  eassumption.
  symmetry. eapply sig_function_translated; eauto.
  reflexivity.
  econstructor.
  constructor.
  f_equal. f_equal. eapply sig_function_translated; eauto.
  assumption.
  erewrite sig_function_translated; eauto.
  apply (val_lessdef_refl (ValLessdefInject := val_lessdef_inject_list)).
  constructor.
  apply Mem.extends_refl.
Qed.

Lemma final_states_simulation:
  forall st1 st2 r
    (MATCH: match_states tprog (writable_block_ops := writable_block_with_init_mem_writable_block_ops init_m) init_ltl_ls (sig_res sg) st1 st2)
    (FINAL: final_state_encode_long (RTLX.final_state) sg st1 r),
    final_state_with_extends (LTLX.final_state init_ltl_ls sg) st2 r.
Proof.
  intros.
  inv FINAL.
  inv FIN.
  inv MATCH.
  inv STACKS.
  econstructor.
  econstructor.
  reflexivity.
  symmetry. apply AG. assumption.
  assumption.
  inv H.
  unfold loc_result in *. rewrite H1 in *.
  assumption.
Qed.

Hypothesis wt_args:
  Val.has_type_list (decode_longs (sig_args sg) args) (normalize_list (sig_args sg)).

Lemma wt_initial_state: 
  forall i,
  forall st, 
    initial_state_decode_longs (RTLX.initial_state prog i init_m) sg args st ->
    wt_state (sig_res sg) st.
Proof.
  inversion 1; subst.
  inv INIT.
  exploit Genv.find_funct_ptr_inversion; eauto.
  destruct 1.
  econstructor.
  constructor.
  reflexivity.
  eapply wt_prog; eauto.
  assumption.
Qed.

Theorem transf_program_correct:
  forall i,
  forward_simulation
    (semantics_as_asm (RTLX.csemantics prog i init_m) sg args)
    (semantics_with_extends (LTLX.semantics init_ltl_ls tprog i sg args init_m)).
Proof.
  intros.
  set (ms := fun s s' => wt_state (sig_res sg) s /\ match_states tprog (writable_block_ops := writable_block_with_init_mem_writable_block_ops init_m) init_ltl_ls (sig_res sg) s s').
  eapply forward_simulation_plus with (match_states := ms). 
- apply symbols_preserved; auto.
- simpl. intros. exploit initial_states_simulation; eauto. intros [st2 [A B]]. 
  exists st2; split; auto. split; auto.
  eapply wt_initial_state; eauto.
- intros. destruct H. eapply final_states_simulation; eauto. 
- intros. destruct H0. 
  simpl in *.
  pose proof (writable_block_with_init_mem_writable_block_ops init_m).
  pose proof (writable_block_with_init_mem_writable_block init_m).
  exploit step_simulation; eauto. intros [s2' [A B]].
  exists s2'; split. exact A. split.
  refine (subject_reduction _ _ _ _ _ _ H H0).
  eapply wt_prog; eauto.
  assumption.
Qed.

End PRESERVATION.
