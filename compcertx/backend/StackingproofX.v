Require compcert.backend.Stackingproof.
Require SmallstepX.
Require EventsX.
Require MachX.
Require LinearX.

Import Coqlib.
Import Integers.
Import AST.
Import ValuesX.
Import MemoryX.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Locations.
Import LinearX.
Import Lineartyping.
Import MachX.
Import Stacking.
Export Stackingproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  eapply Genv.genv_next_transf_partial; eauto.
Qed.

Variables
  (init_mach_rs: Mach.regset)
  (init_sp: val)
  (init_m: mem)
.

Definition init_linear_rs: Locations.Locmap.t :=
    fun ros =>
      match ros with
        | R r => init_mach_rs r
        | S Outgoing ofs ty => 
          match load_stack init_m init_sp ty (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) with
            | Some v => v
            | None => Vundef
          end
        | _ => Vundef
      end.

Lemma extcall_args_eq:
  forall ll vl,
    list_forall2 (Mach.extcall_arg init_mach_rs init_m init_sp) ll vl
  -> vl = map init_linear_rs ll.
Proof.
  induction 1; simpl.
   reflexivity.
  f_equal; eauto.
  inv H.
   reflexivity.
  unfold init_linear_rs.
  rewrite H1.
  reflexivity.
Qed.   

Lemma extcall_arg_init_linear_rs:
  forall la,
    list_forall2 (extcall_arg init_mach_rs init_m init_sp) la (map init_linear_rs la) ->
    forall l, In l la ->
    extcall_arg init_mach_rs init_m init_sp l (init_linear_rs l).
Proof.
  induction la; simpl; inversion 1; subst.
   tauto.
  destruct 1; subst; eauto.
Qed.

Variables
  (init_ra: val)
  (sg: signature)
  (args: list val)
  (Hargs: extcall_arguments init_mach_rs init_m init_sp sg args)
  (Hinject_neutral: Mem.inject_neutral (Mem.nextblock init_m) init_m)
  (Hgenv_next: Ple (Genv.genv_next tge) (Mem.nextblock init_m))
.

Hypothesis init_mach_rs_inj:
  forall r, val_inject (Mem.flat_inj (Mem.nextblock init_m)) (init_mach_rs r) (init_mach_rs r).

Lemma transf_initial_states:
  forall i,
  forall s
         (INIT: LinearX.initial_state init_linear_rs prog i sg args init_m s),
    exists s',
      MachX.initial_state init_mach_rs init_sp tprog i sg args init_m s' /\
      match_states prog tprog init_m init_linear_rs init_sp init_ra s s'.
Proof.  
  inversion 1; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as [tf [Htf TRANS]].
  esplit.
  split.
  econstructor.
  erewrite symbols_preserved; eauto.
  assumption.
  econstructor.
  eapply Mem.neutral_inject. assumption.
  econstructor.
  eapply Ple_refl. apply Ple_refl.
  constructor.
  apply Ple_refl.
  unfold Mem.flat_inj. intros. destruct (plt b0 (Mem.nextblock init_m)); eauto. contradiction.
  unfold Mem.flat_inj. intros. destruct (plt b1 (Mem.nextblock init_m)); congruence.
  intros. exploit Genv.genv_symb_range; eauto. erewrite genv_next_preserved in Hgenv_next; eauto. unfold ge in *; xomega.
  intros. exploit Genv.genv_funs_range; eauto. erewrite genv_next_preserved in Hgenv_next; eauto. unfold ge in *; xomega.
  intros. exploit Genv.genv_vars_range; eauto. erewrite genv_next_preserved in Hgenv_next; eauto. unfold ge in *; xomega.
  intros. exploit extcall_arg_init_linear_rs; eauto. intro.
  inv H0.
  esplit. split. econstructor. eassumption.
  destruct init_sp; try discriminate.
  exploit Mem.loadv_inject.
   eapply Mem.neutral_inject. eassumption.
   eassumption.
   unfold Val.add. econstructor.
   unfold Mem.flat_inj. destruct (plt b0 (Mem.nextblock init_m)). reflexivity.
   destruct n.
   eapply Mem.valid_access_valid_block.
   eapply Mem.valid_access_implies.
   eapply Mem.load_valid_access. unfold load_stack, Val.add in H8. eexact H8.
   constructor.
   rewrite Int.add_zero.
   reflexivity.
  destruct 1 as [? [? ?]].
  unfold load_stack, Val.add in H8.
  rewrite H8 in H0. inv H0.
  assumption.
  eassumption.
  assumption.
  assumption.
  constructor.
Qed.

Lemma transf_final_states:
  forall s s' r
         (MATCH: match_states prog tprog init_m init_linear_rs init_sp init_ra s s')
         (FIN: LinearX.final_state init_linear_rs sg s r),
    final_state_with_inject (MachX.final_state init_mach_rs sg) init_m s' r.
Proof.
  intros.
  inv FIN.
  inv MATCH.
  inv STACKS.
  econstructor.
  econstructor.
  reflexivity.
  { (* Callee-save registers. *)
    intros.
    refine (_ (AGLOCS (R r) _)).
    simpl. intro REW.
    eapply Mem.val_inject_flat_inj_lessdef.
    eapply val_inject_incr_recip.
    rewrite <- REW.
    eapply AGREGS.
    eapply init_mach_rs_inj.
    eapply match_globalenvs_inject_incr.
    eassumption.
    assumption.
  }
  eapply match_globalenvs_inject_incr; eauto.
  eapply match_globalenvs_inject_separated; eauto.
  assumption.
  generalize (Conventions1.loc_result sg). induction l; simpl; eauto.
Qed.

Hypothesis wt_init_mach_rs:
  forall r, Val.has_type (init_mach_rs r) (mreg_type r).

Lemma wt_init_linear_rs:
  wt_locset (Some Lineartyping.Locset.empty) init_linear_rs.
Proof.
  constructor.
  destruct l.
   simpl; auto.
  destruct sl; try (constructor; fail).
  unfold init_linear_rs, load_stack.
  case_eq (
      Mem.loadv (chunk_of_type ty) init_m
                (Val.add init_sp
                         (Vint (Int.repr (Stacklayout.fe_ofs_arg + 4 * pos))))
    ); try (constructor; fail).
  destruct init_sp; try discriminate.
  unfold Val.add, Mem.loadv.
  intros.
  exploit Mem.load_type; eauto.
  destruct ty; simpl; tauto.
  inversion 1.
Qed.

Theorem wt_initial_state:
  forall i,
  forall S, LinearX.initial_state init_linear_rs prog i sg args init_m S ->
            Lineartyping.wt_state init_linear_rs S.
Proof.
  induction 1. 
  exploit Genv.find_funct_ptr_inversion; eauto.
  destruct 1.
  econstructor. 
  apply wt_callstack_nil.
  eapply wt_init_linear_rs.
  eapply wt_prog. eassumption. eassumption.
  apply wt_init_linear_rs.
Qed.

Variable return_address_offset: Mach.function -> Mach.code -> int -> Prop.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Hypothesis init_sp_not_global:
  forall (b : block) (o : int),
   init_sp = Vptr b o -> Ple (Genv.genv_next (Genv.globalenv prog)) b.

Hypothesis init_sp_valid:
  forall (b : block) (o : int),
   init_sp = Vptr b o -> Mem.valid_block init_m b.

Hypothesis init_sp_int:
  Val.has_type init_sp Tint.

Hypothesis init_ra_int:
  Val.has_type init_ra Tint.

Local Instance: WritableBlockOps (writable_block init_m).
Proof. typeclasses eauto. Defined.

Theorem transf_program_correct:
  forall i,
  forward_simulation
    (LinearX.semantics init_linear_rs prog i sg args init_m)
    (semantics_with_inject (MachX.semantics return_address_offset init_mach_rs init_sp init_ra tprog i sg args init_m) init_m)
.
Proof.
  set (ms := fun s s' => Lineartyping.wt_state init_linear_rs s /\ match_states prog tprog init_m init_linear_rs init_sp init_ra s s').
  intros.
  eapply forward_simulation_plus with (match_states := ms). 
- apply symbols_preserved; auto.
- intros. simpl in *.
  exploit transf_initial_states; eauto. intros [st2 [A B]]. 
  exists st2; split; auto. split; auto.
  eapply wt_initial_state; eauto.
- intros. destruct H. eapply transf_final_states; eauto. 
- intros. destruct H0. 
  exploit transf_step_correct. 
  eassumption.
  eassumption.
  fold ge. erewrite <- genv_next_preserved; eauto.
  eassumption.
  assumption.
  unfold Events.writable_block_with_init_mem. unfold writable_block. intros. generalize (init_sp_not_global _ _ H2). generalize (init_sp_valid _ _ H2). unfold Mem.valid_block. xomega.
  assumption.
  eexact init_ra_int.
  simpl in H. eassumption.
  assumption.
  eassumption.
  intros [s2' [A B]].
  exists s2'; split. exact A. split.
  eapply step_type_preservation; eauto. 
  eapply wt_prog. eassumption.
  simpl in *. eassumption.
  assumption.
Qed.

End WITHCONFIG.
