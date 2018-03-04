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
Require Import Coqlib.
Require Import Equivalence.
Require Import Decidable.
Require Import Observation.
Require Import Behavior.
Require Import Events.

(* This file defines the SecurityBigstep framework, which converts various lemmas like
   integrity and confidentiality on a semantics sem into a whole-execution security
   property (called low-level security in the paper). *)

Section BIGSTEP.

  Context `{Obs': Observation}.

  Context {ret state : Type}.
  Variable sem : semantics ret state.

  (* observe represents the behavioral (monotonic) observation function used to specify the
     low-level security property (whole-execution behaviors) on the semantics *)
  Variable observe : principal -> state -> obs.

  (* principal_ok defines a subset of principals that the final security theorem will apply to *)
  (* xobserve is the potentially non-behavioral observation function for the semantics *)
  (* state_inv is an invariant the holds across the entire execution *)
  (* active checks whether the observer is the active thread *)
  (* init s means that we can reason about security starting from s
     (in practice, init s will be the point at which the entire
      initialization process is finished and the observer's thread is spawned) *)
  Class SecBigstepOps {ostate : Type} :=
    {
      principal_ok : principal -> Prop;
      xobserve : principal -> state -> ostate;
      active : principal -> state -> Prop;
      state_inv : principal -> state -> Prop;
      init : principal -> state -> Prop
    }.

  Notation obs_eq p s1 s2 := (xobserve p s1 = xobserve p s2).

  Class SecBigstep `{Hsec: SecBigstepOps} :=
    {
      (* note that this property can be viewed as an instance of indistinguishability
         preservation from the paper, where xobserve and observe are different observation
         functions over the same semantics *)
      observe_obs_eq : 
        forall p, principal_ok p ->
          forall s1 s2, obs_eq p s1 s2 -> observe p s1 = observe p s2;

      final_nostep :
        forall s r, final_state sem s r -> Nostep sem s;

      active_obs_eq :
        forall p, principal_ok p ->
          forall s1 s2, obs_eq p s1 s2 -> (active p s1 <-> active p s2);
      active_dec : forall p s, decidable (active p s);

      (* Note: If mCertiKOS were allowed to terminate, this property would need to be 
               altered somewhat. Currently, we always assume the configuration
               will enforce that user processes yield infinitely rather than terminate. *)
      active_forever :
        forall p, principal_ok p ->
          forall s, 
            init p s -> state_inv p s ->
            exists s' t, Plus sem s t s' /\ active p s';

      initial_state_inv :
        forall p, principal_ok p ->
          forall s, initial_state sem s -> state_inv p s;
      state_inv_preserved :
        forall p, principal_ok p ->
          forall s s' t, Step sem s t s' -> state_inv p s -> state_inv p s';

      init_preserved :
        forall p, principal_ok p ->
          forall s s' t, Step sem s t s' -> state_inv p s -> init p s -> init p s';

      conf : 
        forall p,
          principal_ok p ->
          forall s1 s1' s2 s2' t1 t2,
            init p s1 -> state_inv p s1 ->
            init p s2 -> state_inv p s2 ->
            active p s1 -> Step sem s1 t1 s1' -> Step sem s2 t2 s2' ->
            obs_eq p s1 s2 -> obs_eq p s1' s2';

      integ :
        forall p,
          principal_ok p ->
          forall s s' t,
            init p s -> state_inv p s ->
            ~ active p s -> ~ active p s' -> 
            Step sem s t s' -> obs_eq p s s';

       conf_restore :
         forall p,
           principal_ok p ->
           forall s1 s1' s2 s2' t1 t2,
             init p s1 -> state_inv p s1 ->
             init p s2 -> state_inv p s2 ->
             ~ active p s1 -> active p s1' -> active p s2' ->
             Step sem s1 t1 s1' -> Step sem s2 t2 s2' ->
             obs_eq p s1 s2 -> obs_eq p s1' s2';

       (* This property is needed to esablish the bigstep semantics as Behavioral,
          as it prevents a big step from potentially making two observations. Note 
          that it allows the extended observation to change, just not the monotonic 
          observation. Ideally, it would be nice to remove obs_monotonic_measure
          from the Behavioral class, which would make this property unnecessary. *)
       integ_observe :
         forall p,
           principal_ok p ->
           forall s s' t,
             init p s -> state_inv p s ->
             active p s -> ~ active p s' ->
             Step sem s t s' -> observe p s = observe p s'
    }.

  Context `{Hsec: SecBigstepOps}.
  Variable p : principal.

  (* inductive definition of Figure 4 in the paper *)
  Inductive sec_step : Globalenvs.Genv.t (funtype sem) (vartype sem) -> 
                       state -> trace -> state -> Prop :=
  | sec_step_active : 
      forall s s' t,
        init p s -> state_inv p s -> active p s' -> 
        Step sem s t s' -> sec_step (globalenv sem) s t s'
  | sec_step_inactive :
      forall s s' s'' t t',
        init p s -> state_inv p s -> ~ active p s' -> active p s'' ->
        Step sem s t s' -> sec_step (globalenv sem) s' t' s'' -> 
        sec_step (globalenv sem) s (t ** t') s''.

  (* the conversion from a semantics to the local view of principal p *)
  Definition sec_sem : semantics _ state :=
    {|
      funtype:= funtype sem;
      vartype:= vartype sem;
      step:= sec_step;
      initial_state:= initial_state sem;
      final_state:= final_state sem;
      globalenv:= globalenv sem
    |}.

End BIGSTEP.

Section SECURE.

  Context {state : Type} `{Hsec': SecBigstep(state:=state)}.
  Variable p : principal.
  Hypothesis p_ok : principal_ok p.

  Notation obs_eq s1 s2 := (xobserve p s1 = xobserve p s2).
  Notation Sec_step := (sec_step sem p (globalenv sem)).
  Notation ssem := (sec_sem sem p).

  (* the following lemmas are various liftings from sem to ssem (the local view) *)

  Lemma sec_step_final_active :
    forall s s' t, Sec_step s t s' -> active p s'.
  Proof.
    intros s s' t Hstep; inv Hstep; auto.
  Qed.

  Lemma state_inv_preserved_star :
    forall s s' t, Star sem s t s' -> state_inv p s -> state_inv p s'.
  Proof.
    induction 1; auto.
    intros; apply IHstar.
    eapply state_inv_preserved; eauto.
  Qed.

  Lemma init_preserved_star :
    forall s s' t, Star sem s t s' -> state_inv p s -> init p s -> init p s'.
  Proof.
    induction 1; auto.
    intros; apply IHstar.
    eapply state_inv_preserved; eauto.
    eapply init_preserved; eauto.
  Qed.

  Lemma sec_state_inv_preserved :
    forall s s' t, Sec_step s t s' -> state_inv p s -> state_inv p s'.
  Proof.
    intros s s' t Hstep; induction Hstep; destruct Hsec'; eauto.
  Qed.

  Lemma sec_init_preserved :
    forall s s' t, Sec_step s t s' -> state_inv p s -> init p s -> init p s'.
  Proof.
    intros s s' t Hstep; induction Hstep; destruct Hsec'; eauto.
  Qed.

  Lemma sec_state_inv_preserved_star :
    forall s s' t, Star ssem s t s' -> state_inv p s -> state_inv p s'.
  Proof.
    intros s s' t Hstar; induction Hstar; auto.
    intros; apply IHHstar; eapply sec_state_inv_preserved; eauto.
  Qed.

  Lemma sec_init_preserved_star :
    forall s s' t, Star ssem s t s' -> state_inv p s -> init p s -> init p s'.
  Proof.
    intros s s' t Hstar; induction Hstar; auto.
    intros Hinv Hinit.
    apply IHHstar.
    eapply sec_state_inv_preserved; eauto.
    eapply sec_init_preserved; eauto.
  Qed.

  Lemma sec_step_conf_restore :
    forall s1 s1' s2 s2' t1 t2,
      init p s1 -> state_inv p s1 ->
      init p s2 -> state_inv p s2 ->
      ~ active p s1 -> Sec_step s1 t1 s1' -> Sec_step s2 t2 s2' ->
      obs_eq s1 s2 -> obs_eq s1' s2'.
  Proof.
    destruct Hsec'.
    intros s1 s1' s2 s2' t1 t2 Hinit1 Hinv1 Hinit2 Hinv2 Hact Hstep1.
    generalize s2 s2' t2 Hinit2 Hinv2; clear s2 s2' t2 Hinit2 Hinv2.
    induction Hstep1; intros s2 s2' t2 Hinit2 Hinv2 Hstep2 Hobs_eq.
    - induction Hstep2.
      eauto.
      apply IHHstep2; eauto.
      transitivity (xobserve p s0); auto.
      eapply integ; eauto.
      apply active_obs_eq0 in Hobs_eq; intuition.
    - eapply IHHstep1; eauto.
      transitivity (xobserve p s); auto.
      symmetry; eauto.
  Qed.

  Lemma sec_step_conf :
    forall s1 s1' s2 s2' t1 t2,
      init p s1 -> state_inv p s1 ->
      init p s2 -> state_inv p s2 ->
      active p s1 -> Sec_step s1 t1 s1' -> Sec_step s2 t2 s2' ->
      obs_eq s1 s2 -> obs_eq s1' s2'.
  Proof.
    destruct Hsec'.
    intros s1 s1' s2 s2' t1 t2 Hinit1 Hinv1 Hinit2 Hinv2 Hact Hstep1 Hstep2 Hobs_eq.
    inv Hstep1; inv Hstep2.
    - eauto.
    - assert (Hcon: obs_eq s1' s') by eauto.
      apply active_obs_eq0 in Hcon; intuition.
    - assert (Hcon: obs_eq s' s2') by eauto.
      apply active_obs_eq0 in Hcon; intuition.
    - refine (sec_step_conf_restore _ _ _ _ _ _ _ _ _ _ _ H4 H10 _); eauto.
  Qed.

  Definition secure (s1 : state) : Prop :=
    forall s2,
      init p s2 -> state_inv p s2 -> obs_eq s1 s2 -> 
      forall n s1' s2' t1 t2,
        StarN ssem n s1 t1 s1' -> StarN ssem n s2 t2 s2' -> obs_eq s1' s2'.

  Lemma security_after_init_stepn :
    forall n s1 s1' s2 s2' t1 t2,
      init p s1 -> state_inv p s1 ->
      init p s2 -> state_inv p s2 ->
      StarN ssem n s1 t1 s1' -> StarN ssem n s2 t2 s2' ->
      obs_eq s1 s2 -> obs_eq s1' s2'.
  Proof.
    induction n; intros s1 s1' s2 s2' t1 t2 Hinit1 Hinv1 Hinit2 Hinv2 Hstep1 Hstep2 Hobs_eq.
    inv Hstep1; inv Hstep2; assumption.
    inv Hstep1; inv Hstep2.
    refine (IHn _ _ _ _ _ _ _ _ _ _ H1 H3 _); eauto.
    eapply sec_init_preserved; eauto.
    eapply sec_state_inv_preserved; eauto.
    eapply sec_init_preserved; eauto.
    eapply sec_state_inv_preserved; eauto.
    destruct (active_dec _ _ p s1).
    eapply sec_step_conf; [| | | | | eauto..]; auto.
    eapply sec_step_conf_restore; [| | | | | eauto..]; auto.
  Qed.

  Theorem security_after_init :
    forall s,
      init p s -> state_inv p s -> secure s.
  Proof.
    unfold secure; intros; eapply security_after_init_stepn; [| | eauto..]; auto.
  Qed.

  Lemma sec_final_nostep :
    forall s r,
      final_state ssem s r -> Nostep ssem s.
  Proof.
    simpl; intros s r Hfin.
    intros t s' Hstep; inv Hstep.
    contradiction (final_nostep sem _ _ _ Hfin _ _ H2).
    contradiction (final_nostep sem _ _ _ Hfin _ _ H3).
  Qed.

  Lemma sec_step_inv :
    forall s t s',      
      Plus sem s t s' -> 
      init p s -> state_inv p s -> active p s' -> 
      exists s'' t', Step ssem s t' s''.
  Proof.
    apply (Smallstep.plus_ind2 
             (fun s1 t s2 => init p s1 -> state_inv p s1 -> active p s2 ->
                             exists s'' t', Step ssem s1 t' s'')).
    intros s1 t s2 Hstep Hinit Hinv Hact; exists s2, t.
    simpl; econstructor; eauto.
    intros s1 t1 s2 t2 s3 t Hstep Hplus IH Ht Hinit Hinv Hact; subst.
    destruct (IH (init_preserved _ _ _ p_ok _ _ _ Hstep Hinv Hinit) 
                 (state_inv_preserved _ _ _ p_ok _ _ _ Hstep Hinv) Hact) as [s2' [t' Hstep']].
    destruct (active_dec _ _ p s2).
    exists s2, t1; simpl; econstructor; eauto.
    inv Hstep'.
    exists s2', (t1 ** t').
    simpl; eapply sec_step_inactive; eauto.
    econstructor; eauto.
    exists s2', (t1 ** t ** t'0).
    simpl; eapply sec_step_inactive; [| | | |eauto|..]; auto.
    eapply sec_step_inactive; eauto.
  Qed.

  Lemma sec_safe :
    forall s,
      init p s -> state_inv p s ->
      exists s' t, Step ssem s t s'.
  Proof.
    intros s ? ?; destruct (active_forever _ _ _ p_ok s) as [s' [t [Hplus Hact]]]; auto.
    intros; eapply sec_step_inv; eauto.
  Qed.

  Lemma sec_not_final :
    forall s r, 
      init p s -> state_inv p s ->
      ~ final_state ssem s r.
  Proof.
    intros s r Hinit Hinv Hfin.
    destruct (sec_safe _ Hinit Hinv) as [s' [t Hstep]].
    eapply sec_final_nostep; eauto.
  Qed.

End SECURE.

Section BEHAVIORAL.
  
  (* Proof that the local semantics is Behavioral 
     (assuming the original semantics is Behavioral). *)

  Local Open Scope nat_scope.

  Context {state : Type} `{Hsec': SecBigstep(state:=state)}.
  Context `{Obs': @Observation Obs}.
  Variable p : principal.
  Hypothesis p_ok : principal_ok p.
  Context `{Hbeh: !Behavioral sem (observe p)}.

  Notation Sec_step := (sec_step sem p (globalenv sem)).

  Lemma sec_step_obs_leq :
    forall t s s',
      Sec_step s t s' ->
      obs_leq (observe p s) (observe p s').
  Proof.
    induction 1.
    eapply obs_monotonic; eauto.
    eapply obs_leq_trans; eauto.
    eapply obs_monotonic; eauto.
  Qed.

  Lemma sec_step_obs_measure :
    forall t s s',
      Sec_step s t s' ->
      obs_measure (observe p s') <= S (obs_measure (observe p s)).
  Proof.
    induction 1.
    eapply obs_monotonic_measure; eauto.
    destruct (active_dec _ _ p s).
    - erewrite (integ_observe _ _ _ p_ok s s'); eauto.
    - erewrite (observe_obs_eq _ _ _ p_ok s s'); eauto.
      eapply integ; eauto.
  Qed.

  Instance secure_behavioral : Behavioral (sec_sem sem p) (observe p).
  Proof.
    constructor.
    - apply sec_step_obs_leq.
    - apply sec_step_obs_measure.
  Qed.

End BEHAVIORAL.

Section SIM.

  (* Establish a simulation from ssem to sem. We make it transparent
     so that the simulation relation is known to be identity. *)
  
  Context {state : Type} `{Hsec': SecBigstep(state:=state)}.

  Variable p : principal.
  Hypothesis p_ok : principal_ok p.

  Notation ssem := (sec_sem sem p).
  Notation observep := (observe p).

  (* Note: this simulation is slightly easier to prove by applying simulation_no_stutter, 
     but then we cannot establish that the simulation relation is identity. Could solve
     this issue by making simulation_no_stutter transparent. *)
  Definition secure_sim : simulation ssem sem observep observep.
  Proof.
    apply Simulation with (sim_index:= unit) (sim_order:= fun _ _ => False)
                          (sim_match_states:= fun _ s1 s2 => s1 = s2).
    - constructor; intuition.
    - intros; subst; auto.
    - intros; subst; auto.
    - intros s1 t s1' Hstep ? s2 ?; subst; induction Hstep.
      + exists tt, s'; split; auto.
        left; econstructor; eauto.
        constructor.
        rewrite E0_right; auto.
      + destruct IHHstep as [? [s''' [[Hplus | [? Hcon]] ?]]]; try inv Hcon; subst.
        exists tt, s'''; split; auto.
        left; econstructor; eauto.
        eapply Smallstep.plus_star; eauto.
  Defined.

End SIM.

Section BISIM.

  (* Show that behaviors of observably equivalent executions are 
     equal by establishing a bisimulation. *)

  Context {state : Type} `{Hsec': SecBigstep(state:=state)}.
  Context `{Obs': @Observation Obs}.
  Variable p : principal.
  Hypothesis p_ok : principal_ok p.
  Context `{Hbeh: !Behavioral sem (observe p)}.

  Notation obs_eq s1 s2 := (xobserve p s1 = xobserve p s2).
  Notation ssem := (sec_sem sem p).
  Notation observep := (observe p).

  Definition obs_eq_bisim : bisimulation ssem ssem observep observep.
  Proof.
    apply Bisimulation with (bisim_index:= unit)
                            (bisim_order:= fun _ _ => False)
                            (bisim_match_states:= fun _ s1 s2 => init p s1 /\ state_inv p s1 /\ 
                                                                 init p s2 /\ state_inv p s2 /\ 
                                                                 obs_eq s1 s2).
    - constructor; intuition.
    - intros; eapply observe_obs_eq; eauto; intuition.
    - intros; split; intro Hcon; apply sec_not_final in Hcon; intuition.
    - intros s1 t s1' Hstep1 ? s2 [Hinit1 [Hinv1 [Hinit2 [Hinv2 Hobs_eq]]]].
      destruct (sec_safe p p_ok s2) as [s2' [t' Hstep2]]; auto.
      exists tt, t', s2'; split.
      left; eapply Smallstep.plus_one; eauto.
      repeat split.
      eapply sec_init_preserved; [| eapply Hstep1 | eauto..]; auto.
      eapply sec_state_inv_preserved; [| eapply Hstep1 | eauto..]; auto.
      eapply sec_init_preserved; [| eapply Hstep2 | eauto..]; auto.
      eapply sec_state_inv_preserved; [| eapply Hstep2 | eauto..]; auto.
      destruct (active_dec _ _ p s1).
      eapply sec_step_conf; [| | | | | | eapply Hstep1 | eapply Hstep2 |..]; eauto.
      eapply sec_step_conf_restore; [| | | | | | eapply Hstep1 | eapply Hstep2 |..]; eauto.
    - intros s2 t s2' Hstep2 ? s1 [Hinit1 [Hinv1 [Hinit2 [Hinv2 Hobs_eq]]]].
      destruct (sec_safe p p_ok s1) as [s1' [t' Hstep1]]; auto.
      exists tt, t', s1'; split.
      left; eapply Smallstep.plus_one; eauto.
      repeat split.
      eapply sec_init_preserved; [| eapply Hstep1 | eauto..]; auto.
      eapply sec_state_inv_preserved; [| eapply Hstep1 | eauto..]; auto.
      eapply sec_init_preserved; [| eapply Hstep2 | eauto..]; auto.
      eapply sec_state_inv_preserved; [| eapply Hstep2 | eauto..]; auto.
      destruct (active_dec _ _ p s2); symmetry.
      eapply sec_step_conf; [| | | | | | eapply Hstep2 | eapply Hstep1 |..]; eauto.
      eapply sec_step_conf_restore; [| | | | | | eapply Hstep2 | eapply Hstep1 |..]; eauto.
  Defined.

  (* Main theorem of this file: whole-execution behaviors from observably equivalent
     initialized states s1 and s2 are identical. *)

  Theorem obs_eq_beh_eq :
    forall s1 s2,
      init p s1 -> state_inv p s1 ->
      init p s2 -> state_inv p s2 -> obs_eq s1 s2 ->
      state_beh_eq ssem ssem observep observep s1 s2.
  Proof.
    intros s1 s2 Hinit1 Hinv1 Hinit2 Hinv2 Hobs_eq.
    eapply bisim_beh_eq with (i:= tt) (bisim:= obs_eq_bisim); eauto; simpl; intuition.
    apply secure_behavioral; auto.
    apply secure_behavioral; auto.
  Qed.

End BISIM.