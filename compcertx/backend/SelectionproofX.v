Require compcert.backend.Selectionproof.
Require SelectionX.
Require SelectLongproofX.
Require CminorSelX.
Require CminorX.
Require SmallstepX.
Require EventsX.

Import Coqlib.
Import Errors.
Import AST.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import SelectLong.
Import SelectLongproofX.
Import SelectionX.
Export Selectionproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Section TRANSF.

Variable prog: Cminor.program.
Let ge := Genv.globalenv prog.
Variable hf: helper_functions.
Variable find_funct: ident -> option Cminor.fundef.
Let tprog := transform_program (Selection.sel_fundef find_funct hf) prog.
Let tge := Genv.globalenv tprog.

Variable m: mem.

Instance wb: WritableBlockOps (EventsX.writable_block m).
Proof. typeclasses eauto. Defined.

Lemma sel_initial_states:
  forall i sg args,
  forall S, CminorX.initial_state prog i m sg args S ->
  exists R, CminorSelX.initial_state tprog i m sg args R /\ match_states prog hf find_funct S R.
Proof.
  inversion 1; subst.
  exploit function_ptr_translated; eauto.
  instantiate (1 := hf).
  intro.
  esplit. split. econstructor.
   unfold tprog, ge. erewrite symbols_preserved; eauto.
   eassumption.
   symmetry. eapply sig_function_translated; eauto.
  econstructor; eauto.
  constructor.
  refine (val_lessdef_refl _).
  apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall sg,
  forall S R r,
  match_states prog hf find_funct S R -> CminorX.final_state sg S r -> final_state_with_extends (CminorSelX.final_state sg) R r.
Proof.
  intros. inv H0. inv H. inv H3.
  econstructor; eauto.
  econstructor; eauto.
Qed.

End TRANSF.

Lemma genv_next_preserved:
  forall prog,
    let tprog := sel_program prog in
  Genv.genv_next (Genv.globalenv tprog) = Genv.genv_next (Genv.globalenv prog).
Proof.
  intros.
  apply Selectionproof.genv_next_preserved.
Qed.

Context `{genv_valid_prf: GenvValid}. 
Context `{external_calls_i64_helpers: !SelectLongproofX.ExternalCallI64Helpers external_functions_sem I64helpers.hf}
        `{external_calls_i64_builtins: !SelectLongproofX.ExternalCallI64Builtins builtin_functions_sem I64helpers.hf}.

Theorem transf_program_correct:
  forall prog,
    let tprog := sel_program prog in
  forall (ge_contains_helpers:
            SelectLongproofX.genv_contains_helpers I64helpers.hf (Genv.globalenv prog)),
  forall (ge_valid:
            genv_valid (Genv.globalenv prog)),
  forall i sg args m,
  forward_simulation
    (semantics_as_c (CminorX.csemantics prog i m) sg args)
    (semantics_with_extends (semantics_as_c (CminorSelX.csemantics tprog i m) sg args))
.
Proof.
  intros.
  eapply forward_simulation_opt.
  apply symbols_preserved.
  apply sel_initial_states.
  apply sel_final_states.
  apply sel_step_correct. 
  discriminate.
  typeclasses eauto.
  apply helpers_correct_preserved. 
  typeclasses eauto.
  apply SelectLongproofX.get_helpers_correct; eauto.
Qed.

End WITHCONFIG.
