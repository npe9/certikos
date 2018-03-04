Require compcert.backend.Constpropproof.
Require ConstpropX.
Require ValueAnalysisX.
Require SmallstepX.

Import Coqlib.
Import Errors.
Import AST.
Import Values.
Import Memory.
Import Events.
Import SmallstepX.
Import Globalenvs.
Import ConstpropX.
Import ValueDomainX.
Import ValueAnalysisX.
Export Constpropproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: RTL.program.
Let tprog: RTL.program := transf_program prog.

Let ge : RTL.genv := Genv.globalenv prog.
Let tge: RTL.genv := Genv.globalenv tprog.

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  eapply Constpropproof.genv_next_preserved.
Qed.

Lemma transf_initial_states:
  forall i init_m sg args,
  forall S, RTLX.initial_state prog i init_m sg args S ->
            exists n, exists R, RTLX.initial_state tprog i init_m sg args R /\ match_states rmtop n S R.
Proof.
  unfold transf_program, transf_fundef in tprog.
  intros. inv H.
  exploit function_ptr_translated; eauto. 
  instantiate (1 := rmtop). intros.
  exists O; exists (RTL.Callstate nil (Constprop.transf_fundef rmtop f) args init_m); split.
  econstructor; eauto.
  unfold tprog. erewrite symbols_preserved; eauto.
  symmetry. eapply sig_function_translated; eauto.
  econstructor.
  constructor.
  exact (val_lessdef_refl _).
  apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall sg,
  forall n st1 st2 r, 
  match_states rmtop n st1 st2 -> RTLX.final_state sg st1 r ->
  final_state_with_extends (RTLX.final_state sg) st2 r.
Proof.
  intros. inv H0. inv H.
  inv STACKS.
  econstructor; eauto.
  constructor.
Qed.

(** The following further hypothesis on the memory model is needed by
    value analysis. *)

Context `{mmatch_ops: !ValueDomain.MMatchOps mem}.
Context `{mmatch_constructions_prf: !ValueAnalysis.MMatchConstructions mem}.

(** To prove that the initial per-function state is sound with respect
    to value analysis, we need the following hypotheses, which
    actually hold thanks to the properties on the caller in assembly
    code (see [AsmX.asm_invariant] for the invariant on the assembly
    state, and [Asm.exec_step_external] for the conditions local to
    the function call site.)
*)
 
Variable init_m: mem.
Variable args: list val.

Hypotheses
  (INJECT_NEUTRAL: Mem.inject_neutral (Mem.nextblock init_m) init_m)
  (GENV_NEXT: Ple (Genv.genv_next ge) (Mem.nextblock init_m))
  (ARGS_INJECT_NEUTRAL: val_list_inject (Mem.flat_inj (Mem.nextblock init_m)) args args).

Theorem transf_program_correct:
  forall i sg,
  forward_simulation 
    (semantics_as_c (RTLX.csemantics prog i init_m) sg args)
    (semantics_with_extends (semantics_as_c (RTLX.csemantics tprog i init_m) sg args)).
Proof.
  unfold transf_program, transf_fundef in tprog.
  intros.
  apply Forward_simulation with
     (fsim_order := lt)
     (fsim_match_states := fun n s1 s2 => sound_state prog rmtop s1 /\ match_states rmtop n s1 s2).
- apply lt_wf.
- simpl; intros. exploit transf_initial_states; eauto. intros (n & st2 & A & B).
  exists n, st2; intuition. eapply sound_initial; eauto. 
  typeclasses eauto.
- simpl; intros. destruct H. eapply transf_final_states; eauto. 
- simpl; intros. destruct H0.
  generalize H. intro STEP.
  eapply sound_step in H; eauto.
  eapply transf_step_correct in STEP; eauto.
  destruct STEP as [ [n2 [s2' [A B]]] | [n2 [A [B C]]]].
  exists n2; exists s2'; split; auto. left; apply plus_one; auto.
  exists n2; exists s2; split; auto. right; split; auto. subst t; apply star_refl. 
  typeclasses eauto.
- apply symbols_preserved.
Qed.

End WITHCONFIG.
