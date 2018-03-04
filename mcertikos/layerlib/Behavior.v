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
Require Import CommonTactic.
Require Import Coqlib.
Require Import Smallstep.
Require Import Streams.
Require Import Equivalence.
Require Import Decision.
Require Import Observation.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Conventions.
Require Import Machregs.
Require Import AuxLemma.
Require Import AsmX.
Require Import LAsm.
Require Import Determinism.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import LAsmModuleSemDef.

(* This file defines notions of simulation and whole-execution behavior based on a 
   general observation function. It then proves various theorems showing how 
   certain simulations can imply equality of whole-execution behaviors.
   Paper Reference: Sections 2 and 3 *)

Definition stream_red_help {A} (s : Stream A) : Stream A :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem stream_red : forall {A} (s : Stream A), s = stream_red_help s.
Proof.
  destruct s; reflexivity.
Qed.

Open Scope nat_scope.

Section SEMANTICS.

  (* The following type is the same as defined in CompCert, except that we
     move the state field into a parameter. We need to do this so that we can 
     later require the state type to be a compatdata. *)

  Set Implicit Arguments.

  Record semantics (RETVAL : Type) (state : Type) : Type := 
    Semantics
      { 
        funtype : Type;
        vartype : Type;
        step : Genv.t funtype vartype -> state -> trace -> state -> Prop;
        initial_state : state -> Prop;
        final_state : state -> RETVAL -> Prop;
        globalenv : Genv.t funtype vartype
      }.

  Unset Implicit Arguments.

  (* coercions between this semantics definition and CompCert's *)

  Definition convert_semantics {r s} (sem : semantics r s) : Smallstep.semantics r :=
    {|
      Smallstep.state := s;
      Smallstep.funtype := funtype sem;
      Smallstep.vartype := vartype sem;
      Smallstep.step := step sem;
      Smallstep.initial_state := initial_state sem;
      Smallstep.final_state := final_state sem;
      Smallstep.globalenv := globalenv sem
    |}.

  Definition convert_semantics' {r} (sem : Smallstep.semantics r) : semantics r (Smallstep.state sem) :=
    {|
      funtype := Smallstep.funtype sem;
      vartype := Smallstep.vartype sem;
      step := Smallstep.step sem;
      initial_state := Smallstep.initial_state sem;
      final_state := Smallstep.final_state sem;
      globalenv := Smallstep.globalenv sem
    |}.

  Coercion convert_semantics  : semantics >-> Smallstep.semantics.
  Coercion convert_semantics'  : Smallstep.semantics >-> semantics.

End SEMANTICS.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : behavior_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : behavior_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : behavior_scope.
Notation " 'StarN' L " := (starN (step L) (globalenv L)) (at level 1) : behavior_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : behavior_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : behavior_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : behavior_scope.
Open Scope behavior_scope.

Section BEHAVIOR.

  (* We now define whole-execution behaviors for an arbitrary 
     semantics and observation function. *)

  Context `{Obs': Observation}.

  Context {ret state : Type}.
  Variable sem : semantics ret state.

  Variable observe : state -> obs.

  (* CompCert defines safety for E0 executions only; we need a more general version *)
  Definition safe s :=
    forall s' t,
      Star sem s t s' ->
      (exists r, final_state sem s' r) \/
      (exists s'' t', Step sem s' t' s'').

  Lemma safe_step :
    forall s s' t,
      Step sem s t s' ->
      safe s -> safe s'.
  Proof.
    intros s s' t Hstep Hsafe s'' t' Hstar.
    eapply Hsafe; eapply star_left; eauto.
  Qed.

  Lemma safe_star :
    forall s s' t,
      Star sem s t s' ->
      safe s -> safe s'.
  Proof.
    intros s s' t Hstar Hsafe s'' t' Hstar'.
    eapply Hsafe; eapply star_trans; eauto.
  Qed.

  (* As discussed in Section 2 of the paper, we need to prove a notion of observation
     monotonicity in order to define whole-execution behaviors. 
     For technical reasons, we also require a property on the observation's measure.
     Hopefully a future version can get rid of the measure. *)

  Class Behavioral :=
    {
      obs_monotonic : 
        forall t s1 s2,
          Step sem s1 t s2 -> obs_leq (observe s1) (observe s2);

      obs_monotonic_measure :
        forall t s1 s2,
          Step sem s1 t s2 -> 
          obs_measure (observe s2) <= S (obs_measure (observe s1))

(*
      (* this property is needed if we want to flip forward simulation 
         into backward - currently, we don't need to do this flipping *)
      obs_trace_silent :
        forall ge t s1 s2,
          step ge s1 t s2 -> observe s1 <> observe s2 -> t = E0
*)
    }.

  Section WITHBEH.

  Context `{Beh : Behavioral}.

  (* various helpful lemmas *)

  Lemma obs_monotonic_star : 
    forall t s1 s2, 
      Star sem s1 t s2 -> 
      obs_leq (observe s1) (observe s2).
  Proof.
    intros t s1 s2; induction 1.
    apply obs_leq_refl.
    apply obs_leq_trans with (o2:= observe s2); auto.
    eapply obs_monotonic; eauto.
  Qed.

  Lemma obs_monotonic_plus : 
    forall t s1 s2,
      Plus sem s1 t s2 -> 
      obs_leq (observe s1) (observe s2).
  Proof.
    intros t s1 s2 Hplus; apply plus_star in Hplus.
    eapply obs_monotonic_star; eauto.
  Qed.

  Lemma obs_measure_alt :
    forall t s1 s2,
      Step sem s1 t s2 ->
      obs_measure (observe s2) = obs_measure (observe s1) \/
      obs_measure (observe s2) = S (obs_measure (observe s1)).
  Proof.
    intros t s1 s2 Hstep.
    assert (Hstep':= Hstep); apply obs_monotonic in Hstep.
    apply obs_leq_lt in Hstep; destruct Hstep as [Hstep|Hstep].
    apply obs_lt_measure in Hstep.
    apply obs_monotonic_measure in Hstep'; omega.
    rewrite Hstep; auto.
  Qed.

  Lemma obs_measure_starN :
    forall n t s1 s2,
      StarN sem n s1 t s2 ->
      obs_measure (observe s2) <= n + obs_measure (observe s1).
  Proof.
    induction n; simpl; intros t s1 s2 Hstar.
    inv Hstar; auto.
    inv Hstar.
    apply obs_monotonic_measure in H0.
    apply IHn in H1; omega.
  Qed.

  Lemma obs_measure_star :
    forall t s1 s2,
      Star sem s1 t s2 ->
      obs_measure (observe s1) <= obs_measure (observe s2).
  Proof.
    induction 1; auto.
    destruct (obs_measure_alt _ _ _ H); omega.
  Qed.

  Lemma obs_measure_alt_star' :
    forall t1 t2 s1 s2 s3,
      Star sem s1 t1 s2 ->
      Star sem s2 t2 s3 ->
      obs_measure (observe s3) = S (obs_measure (observe s1)) ->
      obs_measure (observe s2) = obs_measure (observe s1) \/
      obs_measure (observe s2) = obs_measure (observe s3).
  Proof.
    intros t1 t2 s1 s2 s3 Hstar1 Hstar2 Hobs.
    assert (Hleq1: obs_measure (observe s1) <= obs_measure (observe s2)).
    eapply obs_measure_star; eauto.
    assert (Hleq2: obs_measure (observe s2) <= obs_measure (observe s3)).
    eapply obs_measure_star; eauto.
    omega.
  Qed.

  Lemma obs_measure_alt_star :
    forall t1 t2 s1 s2 s3,
      Star sem s1 t1 s2 ->
      Star sem s2 t2 s3 ->
      obs_measure (observe s3) = S (obs_measure (observe s1)) ->
      observe s2 = observe s1 \/ observe s2 = observe s3.
  Proof.
    intros t1 t2 s1 s2 s3 Hstar1 Hstar2 Hobs.
    edestruct obs_measure_alt_star'; [eapply Hstar1 | eapply Hstar2 |..]; auto.
    left; symmetry; apply obs_measure_eq; auto.
    eapply obs_monotonic_star; eauto.
    right; apply obs_measure_eq; auto.
    eapply obs_monotonic_star; eauto.
  Qed.

  Lemma observe_split_one :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      obs_measure (observe s2) = S (obs_measure (observe s1)) ->
      exists s3 s4 t1 t2 t3,
        Star sem s1 t1 s3 /\
        Step sem s3 t2 s4 /\
        Star sem s4 t3 s2 /\
        observe s3 = observe s1 /\ observe s4 = observe s2.
  Proof.
    intros s1 s2 t; induction 1; intros Hmeq; try omega; subst.
    destruct (obs_eq_dec (observe s1) (observe s2)) as [Heq|Hneq].
    - rewrite Heq in Hmeq.
      destruct (IHstar Hmeq) as [s4 [s5 [t3 [t4 [t5 [Hstar2 [Hstar4 [Hstar5 [Hobs4 Hobs5]]]]]]]]].
      exists s4, s5, (Events.Eapp t1 t3), t4, t5; repeat (split; auto); try congruence.
      eapply star_left; eauto.
    - exists s1, s2, Events.E0, t1, t2; repeat (split; auto).
      constructor.
      destruct (obs_measure_alt _ _ _ H) as [Heq'|Hneq'].
      contradiction Hneq; apply obs_measure_eq; auto.
      eapply obs_monotonic; eauto.
      apply obs_measure_eq; try congruence.
      eapply obs_monotonic_star; eauto.
  Qed.

  Lemma observe_split :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      observe s1 <> observe s2 ->
      exists s3 s4 t1 t2 t3,
        Star sem s1 t1 s3 /\
        Step sem s3 t2 s4 /\
        Star sem s4 t3 s2 /\
        observe s1 = observe s3 /\ 
        observe s3 <> observe s4.
  Proof.
    induction 1; try congruence; subst; intro Hobs.
    destruct (obs_eq_dec (observe s1) (observe s2)) as [Hobs'|Hobs'].
    - destruct IHstar as [s4 [s5 [t3 [t4 [t5 A]]]]]; try congruence.
      decompose [and] A.
      exists s4, s5, (Events.Eapp t1 t3), t4, t5; repeat (split; auto; try congruence).
      eapply star_left; eauto.
    - exists s1, s2, Events.E0, t1, t2; repeat (split; auto).
      constructor.
  Qed.

  Lemma observe_split' :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      observe s1 <> observe s2 ->
      exists s3 s4 t1 t2,
        Star sem s1 t1 s3 /\
        Step sem s3 t2 s4 /\
        observe s1 = observe s3 /\ 
        observe s3 <> observe s4.
  Proof.
    intros; edestruct observe_split as [s4 [s5 [t3 [t4 [t5 A]]]]]; eauto.
    decompose [and] A.
    exists s4, s5, t3, t4; auto.
  Qed.

  (* The definition of whole-execution behaviors starts here. We follow
     CompCert's notion of behaviors, where there are four kinds:
     1.) getting stuck
     2.) successful termination
     3.) infinite execution that stops producing observations after a certain point
     4.) infinite execution that produces observations forever *)

  (** Infinitely many non-silent transitions (behavior type 4 above) *)

  CoInductive forever_reactive : state -> Stream obs -> Prop :=
  | forever_reactive_intro: 
      forall s1 s2 s3 t1 t2 os,
        Star sem s1 t1 s2 -> observe s1 = observe s2 -> 
        Step sem s2 t2 s3 -> observe s2 <> observe s3 ->
        forever_reactive s3 os ->
        forever_reactive s1 (Cons (observe s1) os).

  Lemma forever_reactive_star :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      observe s1 = observe s2 ->
      forall os,
        forever_reactive s2 os ->
        forever_reactive s1 os.
  Proof.
    intros s1 s2 t; induction 1; intros Hobs_eq os Hreact; auto; subst.
    assert (Hobs_eq': observe s2 = observe s3).
    apply obs_leq_antisym.
    eapply obs_monotonic_star; eauto.
    rewrite <- Hobs_eq; eapply obs_monotonic; eauto.
    apply IHstar in Hreact; auto; inv Hreact.
    rewrite Hobs_eq', <- Hobs_eq; econstructor; [| | |eauto|..]; eauto.
    eapply star_left; eauto.
    congruence.
  Qed.

  Lemma forever_reactive_star_one :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      obs_measure (observe s2) = S (obs_measure (observe s1)) ->
      forall os,
        forever_reactive s2 os ->
        forever_reactive s1 (Cons (observe s1) os).
  Proof.
    intros s1 s2 t; induction 1; intros Hm os Hreact; try omega; subst.
    destruct (obs_measure_alt _ _ _ H).
    - assert (Hobs_eq: observe s1 = observe s2).
      apply obs_measure_eq; auto.
      eapply obs_monotonic; eauto.
      eapply forever_reactive_star; eauto.
      apply star_one; eauto.
      rewrite Hobs_eq; apply IHstar; auto; congruence.
    - econstructor; eauto.
      constructor.
      intro Hcon; rewrite Hcon in H1; omega.
      eapply forever_reactive_star; eauto.
      apply obs_measure_eq; try congruence.
      eapply obs_monotonic_star; eauto.
  Qed.

  (** Infinitely many silent transitions (behavior type 3 above) *)

  CoInductive forever_silent : state -> Prop :=
  | forever_silent_intro: 
      forall s1 s2 t,
        Step sem s1 t s2 -> observe s1 = observe s2 ->
        forever_silent s2 ->
        forever_silent s1.

  Lemma forever_silent_star : 
    forall s1 s2 t,
      Star sem s1 t s2 -> observe s1 = observe s2 ->
      forever_silent s2 ->
      forever_silent s1.
  Proof.
    cofix COINDHYP; intros s1 s2 t Hstar Hobs_eq Hsil.
    inv Hstar; auto.
    eapply forever_silent_intro; eauto.
    apply obs_leq_antisym.
    eapply obs_monotonic; eauto.
    rewrite Hobs_eq; eapply obs_monotonic_star; eauto.
    eapply COINDHYP; eauto.
    apply obs_leq_antisym.
    eapply obs_monotonic_star; eauto.
    rewrite <- Hobs_eq; eapply obs_monotonic; eauto.
  Qed.

  (** An alternate definition, helpful for some lemmas below. *)

  Variable A: Type.
  Variable order: A -> A -> Prop.
  Hypothesis order_wf: well_founded order.

  CoInductive forever_silent_N : A -> state -> Prop :=
  | forever_silent_N_star: 
      forall s1 s2 a1 a2 t,
        Star sem s1 t s2 ->
        observe s1 = observe s2 ->
        order a2 a1 ->
        forever_silent_N a2 s2 ->
        forever_silent_N a1 s1
  | forever_silent_N_plus: 
      forall s1 s2 a1 a2 t,
        Plus sem s1 t s2 ->
        observe s1 = observe s2 ->
        forever_silent_N a2 s2 ->
        forever_silent_N a1 s1.

  Lemma forever_silent_N_inv:
    forall a s,
      forever_silent_N a s ->
      exists s' a' t,
        Step sem s t s' /\ observe s = observe s' /\
        forever_silent_N a' s'.
  Proof.
    intros a0. pattern a0. apply (well_founded_ind order_wf).
    intros x IH s Hsil. inv Hsil.
    (* star case *)
    - inv H.
      (* no transition *)
      apply (IH a2); auto.
      (* at least one transition *)
      exists s0, x, t1; split; auto; split.
      apply obs_leq_antisym.
      eapply obs_monotonic; eauto.
      rewrite H0; eapply obs_monotonic_star; eauto.
      eapply forever_silent_N_star; eauto.
      apply obs_leq_antisym.
      eapply obs_monotonic_star; eauto.
      rewrite <- H0; eapply obs_monotonic; eauto.
    (* plus case *)
    - inv H.
      exists s0, a2, t1; split; auto; split.
      apply obs_leq_antisym.
      eapply obs_monotonic; eauto.
      rewrite H0; eapply obs_monotonic_star; eauto.
      apply star_inv in H3; destruct H3 as [[? ?]|?]; subst; auto.
      eapply forever_silent_N_plus; eauto.
      apply obs_leq_antisym.
      eapply obs_monotonic_plus; eauto.
      rewrite <- H0; eapply obs_monotonic; eauto.
  Qed.

  Lemma forever_silent_N_forever:
    forall a s, forever_silent_N a s -> forever_silent s.
  Proof.
    cofix COINDHYP; intros.
    destruct (forever_silent_N_inv a s H) as [s' [a' [t [P [Q R]]]]].
    econstructor; eauto.
  Qed.

  (* The type of whole-execution behaviors. *)
  Inductive behavior : Type :=
  | Terminate : obs -> behavior
  | Fault : obs -> behavior
  | SilentDiv : obs -> behavior
  | Reactive : Stream obs -> behavior.

  (* The inductive predicate defining the set of behaviors for a given program state. *)
  Inductive has_behavior s : behavior -> Prop :=
  | has_beh_terminate : 
      forall s' t r,
        Star sem s t s' -> 
        final_state sem s' r -> 
        has_behavior s (Terminate (observe s'))
  | has_beh_fault : 
      forall s' t,
        Star sem s t s' -> 
        (forall r, ~ final_state sem s' r) -> 
        Nostep sem s' ->
        has_behavior s (Fault (observe s'))
  | has_beh_silentdiv :
      forall s' t,
        Star sem s t s' -> 
        forever_silent s' ->
        has_behavior s (SilentDiv (observe s'))
  | has_beh_reactive :
      forall os,
        forever_reactive s os -> has_behavior s (Reactive os).

  (* equality of single behaviors *)
  Definition beh_eq b1 b2 : Prop :=
    match b1, b2 with
      | Terminate o1, Terminate o2 => o1 = o2
      | Fault o1, Fault o2 => o1 = o2
      | SilentDiv o1, SilentDiv o2 => o1 = o2
      | Reactive os1, Reactive os2 => EqSt os1 os2
      | _, _ => False
    end.

  Global Instance beh_eq_equiv : Equivalence beh_eq.
  Proof.
    constructor.
    - intros x; destruct x; simpl; auto.
      apply EqSt_reflex.
    - intros x y Hbeh.
      destruct x, y; inv Hbeh; simpl; auto.
      apply sym_EqSt; constructor; auto.
    - intros x y z Hbeh1 Hbeh2.
      destruct x, y, z; inv Hbeh1; inv Hbeh2; simpl; auto.
      apply trans_EqSt with (s2:= s0); constructor; auto.
  Qed.

  End WITHBEH.

End BEHAVIOR.

Section CDATA_SPEC.

  (* Specialization of observation to an LAsm machine with compatdata D. *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Variable D : compatdata.

  Notation state := (Asm.state (mem:= mwd (cdata D))).

  Context {ret : Type}.
  Variable sem : semantics ret state.

  Definition observe_lasm (p : principal) (s : state) :=
    match s with 
        State _ (_,d) => observe p d 
    end.

End CDATA_SPEC.

Section BEH_IMPLIES.

  (* Behavioral comparison must be allowed between behaviors of two 
     executions on different layers, hence introducing sem1 and sem2 here. 
     Currently we assume that both semantics have the same observation type.
     The technical report version of our paper actually shows that we can 
     support different observation types without difficulty; we will implement
     that theory here in the future. *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context {ret1 ret2 state1 state2 : Type}.
  Variables (sem1 : semantics ret1 state1) (sem2 : semantics ret2 state2).
  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).

  Definition state_beh_implies s1 s2 :=
    forall b, 
      has_behavior sem1 observe1 s1 b -> 
        exists b', has_behavior sem2 observe2 s2 b' /\ beh_eq b b'.

End BEH_IMPLIES.

Section BEH_EQ.

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context {ret1 ret2 state1 state2 : Type}.
  Variables (sem1 : semantics ret1 state1) (sem2 : semantics ret2 state2).
  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).

  Definition state_beh_eq s1 s2 := 
    state_beh_implies sem1 sem2 observe1 observe2 s1 s2 /\ 
    state_beh_implies sem2 sem1 observe2 observe1 s2 s1.

End BEH_EQ.

Section BEH_EQ_EQUIV.

  (* When state_beh_eq takes states of the same type, it is an equivalence relation. *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context {ret state : Type}.
  Variable sem : semantics ret state.
  Variable observe : state -> obs.

  Instance state_beh_eq_equiv : Equivalence (state_beh_eq sem sem observe observe).
  Proof.
    constructor.
    - intros s; split; intros b Hbeh; exists b; split; auto; reflexivity.
    - intros s1 s2 [Himpl1 Himpl2]; split; intros b Hbeh; eauto.
    - intros s1 s2 s3 [Himpl12 Himpl21] [Himpl23 Himpl32]; split; intros b Hbeh.
      + destruct (Himpl12 b) as [b2 [? ?]]; auto.
        destruct (Himpl23 b2) as [b3 [? ?]]; auto.
        exists b3; split; auto.
        transitivity b2; auto.
      + destruct (Himpl32 b) as [b2 [? ?]]; auto.
        destruct (Himpl21 b2) as [b1 [? ?]]; auto.
        exists b1; split; auto.
        transitivity b2; auto.
  Qed.

End BEH_EQ_EQUIV.

Section BEH_EQ_EQUIV2.

  (* Alternatively, we can still define a notion of symmetry and transitivity
     when different state types are used. *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context {ret1 ret2 ret3 state1 state2 state3 : Type}.
  Variables (sem1 : semantics ret1 state1)
            (sem2 : semantics ret2 state2)
            (sem3 : semantics ret3 state3).
  Variables (observe1 : state1 -> obs)
            (observe2 : state2 -> obs)
            (observe3 : state3 -> obs).

  Lemma state_beh_eq_sym : 
    forall s1 s2,
      state_beh_eq sem1 sem2 observe1 observe2 s1 s2 -> 
      state_beh_eq sem2 sem1 observe2 observe1 s2 s1.
  Proof.
    intros s1 s2 [Himpl1 Himpl2]; split; intros b Hbeh; eauto.
  Qed.

  Lemma state_beh_eq_trans : 
    forall s1 s2 s3,
      state_beh_eq sem1 sem2 observe1 observe2 s1 s2 -> 
      state_beh_eq sem2 sem3 observe2 observe3 s2 s3 ->
      state_beh_eq sem1 sem3 observe1 observe3 s1 s3.
  Proof.
    intros s1 s2 s3 [Himpl12 Himpl21] [Himpl23 Himpl32]; split; intros b Hbeh.
    - destruct (Himpl12 b) as [b2 [? ?]]; auto.
      destruct (Himpl23 b2) as [b3 [? ?]]; auto.
      exists b3; split; auto.
      transitivity b2; auto.
    - destruct (Himpl32 b) as [b2 [? ?]]; auto.
      destruct (Himpl21 b2) as [b1 [? ?]]; auto.
      exists b1; split; auto.
      transitivity b2; auto.
  Qed.

End BEH_EQ_EQUIV2.

Section BEH_EXIST.

  (* Proof that at least one behavior always exists from any state. 
     Like in CompCert, this requires assuming excluded middle. *)

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{Obs': Observation}.

  Context {ret state : Type}.
  Variable sem : semantics ret state.
  Variable observe : state -> obs.

  (* excluded middle assumed in this file *)
  Require Import Classical.
  Require Import ClassicalEpsilon.

  Section BUILD_OBS_STREAM.

    Variable s0 : state.

    Hypothesis reacts:
      forall s1 t1, 
        Star sem s0 t1 s1 ->
        exists s2 s3 t2 t3, 
          Star sem s1 t2 s2 /\ Step sem s2 t3 s3 /\ 
          observe s1 = observe s2 /\ observe s2 <> observe s3.

    Lemma reacts':
      forall s1 t1, 
        Star sem s0 t1 s1 ->
        { s2 : state & { s3 : state &
        { t2 : Events.trace & { t3 : Events.trace | 
          Star sem s1 t2 s2 /\ Step sem s2 t3 s3 /\
          observe s1 = observe s2 /\ observe s2 <> observe s3 } } } }.
    Proof.
      intros s1 t1 Hstar. 
      destruct (constructive_indefinite_description _ (reacts s1 t1 Hstar)) as [s2 A].
      destruct (constructive_indefinite_description _ A) as [s3 B].
      destruct (constructive_indefinite_description _ B) as [t2 C].
      destruct (constructive_indefinite_description _ C) as [t3 ?].
      exists s2, s3, t2, t3; auto.
    Qed.

    CoFixpoint build_obs_stream (s1: state) (t1: Events.trace) 
                                (ST: Star sem s0 t1 s1) : Stream obs :=
      match reacts' s1 t1 ST with
        | existT s2 (existT s3 (existT t2 (exist t3 (conj A (conj B _))))) =>
          Cons (observe s1) 
               (build_obs_stream _ _ (star_right _ _ (star_trans ST A (refl_equal _)) 
                                                 B (refl_equal _)))               
      end.

    Lemma reacts_forever_reactive_rec:
      forall s1 t1 (ST: Star sem s0 t1 s1),
        forever_reactive sem observe s1 (build_obs_stream s1 t1 ST).
    Proof.
      cofix COINDHYP; intros s1 t1 ST.
      rewrite (stream_red (build_obs_stream s1 t1 ST)); simpl.
      destruct (reacts' s1 t1 ST) as [s2 [s3 [t2 [t3 [Hstar [Hstep [Hobs1 Hobs2]]]]]]].
      econstructor; eauto.
    Qed.

    Lemma reacts_forever_reactive:
      exists os, forever_reactive sem observe s0 os.
    Proof.
      exists (build_obs_stream s0 Events.E0 (star_refl (step sem) (globalenv sem) s0)).
      apply reacts_forever_reactive_rec.
    Qed.

  End BUILD_OBS_STREAM.

  Lemma diverges_forever_silent:
    forall s0,
      (forall s1 t1, 
         Star sem s0 t1 s1 -> 
         observe s0 = observe s1 /\ exists s2 t2, Step sem s1 t2 s2) ->
      forever_silent sem observe s0.
  Proof.
    cofix COINDHYP; intros s0 Hsafe.
    destruct (Hsafe s0 Events.E0) as [Hobs_eq [s1 [t ST]]].
    constructor.
    econstructor; eauto.
    destruct (Hsafe s1 t) as [Hobs_eq' [s2 [t' ST']]]; auto.
    apply star_one; auto.
    apply COINDHYP. 
    intros s2 t' ST'; split.
    transitivity (observe s0).
    destruct (Hsafe s1 t) as [Hobs_eq' [s2' [t'' ST'']]]; auto.
    apply star_one; auto.
    destruct (Hsafe s2 (Events.Eapp t t')) as [Hobs_eq' [s2' [t'' ST'']]]; auto.
    eapply star_left; eauto.
    eapply Hsafe; eapply star_left; eauto.
  Qed.

  Theorem beh_exists :
    forall s, 
      exists b, has_behavior sem observe s b.
  Proof.
    intros s0.
    destruct (classic (forall s1 t1, Star sem s0 t1 s1 -> 
                         exists s2 t2, Step sem s1 t2 s2)) as [DIV|NODIV].
    - (* 1 Divergence (silent or reactive) *)
      destruct (classic (exists s1 t1, Star sem s0 t1 s1 /\
                           (forall s2 t2, Star sem s1 t2 s2 ->
                                          observe s1 = observe s2 /\
                                          exists s3 t3, Step sem s2 t3 s3))) as [SIL|REACT].
      + (* 1.1 Silent divergence *)
        destruct SIL as [s1 [t1 [A B]]].
        exists (SilentDiv (observe s1)); econstructor; eauto. 
        apply diverges_forever_silent; auto.
      + (* 1.2 Reactive divergence *)
        destruct (reacts_forever_reactive s0) as [os ?].
        intros s1 t1 Hstar.
        generalize (not_ex_all_not _ _ REACT s1); intro A; clear REACT.
        generalize (not_ex_all_not _ _ A t1); intro B; clear A.
        destruct (not_and_or _ _ B) as [C|C]; try contradiction; clear B. 
        destruct (not_all_ex_not _ _ C) as [s2 D']; clear C. 
        destruct (not_all_ex_not _ _ D') as [t2 E]; clear D'.
        destruct (imply_to_and _ _ E) as [F G]; clear E.
        destruct (not_and_or _ _ G) as [I|I]; clear G.
        eapply observe_split'; eauto.
        contradict I; eapply DIV; eapply star_trans; eauto.
        exists (Reactive os); econstructor; eauto.
    - (* 2 Termination (final state or fault) *)
      destruct (not_all_ex_not _ _ NODIV) as [s1 A]; clear NODIV.
      destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
      destruct (imply_to_and _ _ B) as [C D']; clear B.
      destruct (classic (exists r, final_state sem s1 r)) as [[r FINAL] | NOTFINAL].
      + (* 2.1 Normal termination *)
        exists (Terminate (observe s1)); econstructor; eauto.
      + (* 2.2 Going wrong *)
        exists (Fault (observe s1)); econstructor; eauto.
        intros t s Hstep; contradiction D'; eauto.
  Qed.

End BEH_EXIST.

Section BEH_DETERM.

  (* Proof that deterministic executions have at most one behavior. 
     We borrow the definition of determinism directly from CompCert. *)

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{Obs': Observation}.

  Context {ret state : Type}.
  Variable sem : semantics ret state.
  Variable observe : state -> obs.

  Context `{Beh: !Behavioral sem observe}.

  Hypothesis det : sem_deterministic sem.

  Ltac use_step_det :=
    match goal with
      | [ S1: Step _ _ ?t1 _, S2: Step _ _ ?t2 _ |- _ ] =>
        destruct (det_step _ _ det _ _ _ _ _ S1 S2) as [EQ1 EQ2]; subst
    end.

  Ltac use_star_step_diamond :=
    match goal with
      | [ S1: Star _ _ ?t1 _, S2: Star _ _ ?t2 _ |- _ ] =>
        let t := fresh "t" in let P := fresh "P" in let EQ := fresh "EQ" in
        destruct (star_step_diamond _ _ det _ _ _ S1 _ _ S2)
          as [t [ [P EQ] | [P EQ] ]]; subst
    end.

  Ltac use_nostep :=
    match goal with
      | [ S: Step _ ?s _ _, NO: Nostep _ ?s |- _ ] => elim (NO _ _ S)
    end.

  Ltac use_final_nostep :=
    match goal with
      | [ S: Step _ ?s _ _, NO: final_state _ ?s _ |- _ ] => 
        apply (det_final_nostep _ _ det) in NO; elim (NO _ _ S)
    end.

  Lemma starN_det :
    forall n s s1 s2 t1 t2,
      StarN sem n s t1 s1 ->
      StarN sem n s t2 s2 -> s1 = s2.
  Proof.
    induction n; intros s s1 s2 t1 t2 Hstar1 Hstar2.
    - inv Hstar1; inv Hstar2; auto.
    - inv Hstar1; inv Hstar2.
      simpl in *; use_step_det; eapply IHn; eauto.
  Qed.

  Lemma forever_silent_star_det :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      forever_silent sem observe s1 ->
      forever_silent sem observe s2.
  Proof.
    induction 1; auto.
    intros Hsil; inv Hsil.
    simpl in *; use_step_det; auto.
  Qed.

  Lemma forever_silent_star_det_observe :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      forever_silent sem observe s1 ->
      observe s1 = observe s2.
  Proof.
    induction 1; auto.
    intros Hsil; inv Hsil.
    simpl in *; use_step_det.
    transitivity (observe s4); auto.
  Qed.

  Lemma forever_silent_star_not_nostep :
    forall s s1 s2 t1 t2,
      Star sem s t1 s1 ->
      Star sem s t2 s2 ->
      forever_silent sem observe s1 ->
      ~ Nostep sem s2.
  Proof.
    intros s s1 s2 t1 t2 Hstar1 Hstar2 Hsil Hns.
    use_star_step_diamond.
    - assert (Hsil': forever_silent sem observe s2)
        by (eapply forever_silent_star_det; [|eauto..]; eauto).
      inv Hsil'; use_nostep.
    - inv P.
      inv Hsil; use_nostep.
      simpl in *; use_nostep.
  Qed.

  Lemma forever_silent_star_not_final :
    forall s s1 s2 t1 t2,
      Star sem s t1 s1 ->
      Star sem s t2 s2 ->
      forever_silent sem observe s1 ->
      forall r,
        ~ final_state sem s2 r.
  Proof.
    intros s s1 s2 t1 t2 Hstar1 Hstar2 Hsil r Hfin.
    use_star_step_diamond.
    - assert (Hsil': forever_silent sem observe s2)
        by (eapply forever_silent_star_det; [|eauto..]; eauto).
      inv Hsil'; use_final_nostep.
    - inv P.
      inv Hsil; use_final_nostep.
      simpl in *; use_final_nostep.
  Qed.

  Lemma forever_reactive_star_det :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      forall os,
        forever_reactive sem observe s1 os ->
        exists os', 
          forever_reactive sem observe s2 os'.
  Proof.
    induction 1; eauto.
    intros os Hreact; inv Hreact.
    inv H2.
    - simpl in *; use_step_det; eauto.
    - simpl in *; use_step_det.
      eapply IHstar; econstructor; [eapply H7 | eauto..].
      apply obs_leq_antisym.
      eapply obs_monotonic_star; eauto.
      rewrite <- H3; eapply obs_monotonic; eauto.
  Qed.

  Lemma forever_reactive_star_det_eq :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      observe s1 = observe s2 ->
      forall os,
        forever_reactive sem observe s1 os ->
        forever_reactive sem observe s2 os.
  Proof.
    intros s1 s2 t Hstar Hobs_eq os Hreact.
    inv Hreact.
    use_star_step_diamond.
    - rewrite Hobs_eq.
      econstructor; eauto.
      congruence.
    - rewrite Hobs_eq; inv P.
      econstructor; eauto; constructor.
      simpl in *; use_step_det.
      contradiction H2; transitivity (observe s2); try congruence.
      apply obs_leq_antisym.
      rewrite <- Hobs_eq, H0; eapply obs_monotonic; eauto.
      eapply obs_monotonic_star; eauto.
  Qed.

  Lemma forever_reactive_star_not_nostep :
    forall s1 os,
      forever_reactive sem observe s1 os ->
      forall s2 t,
        Star sem s1 t s2 ->
        ~ Nostep sem s2.
  Proof.
    intros s1 os Hreact s2 t Hstar Hns.
    edestruct forever_reactive_star_det as [os' Hreact']; eauto.
    inv Hreact'.
    inv H; use_nostep.
  Qed.

  Lemma forever_reactive_star_not_final :
    forall s1 os,
      forever_reactive sem observe s1 os ->
      forall s2 t,
        Star sem s1 t s2 ->
        forall r,
          ~ final_state sem s2 r.
  Proof.
    intros s1 os Hreact s2 t Hstar r Hfin.
    edestruct forever_reactive_star_det as [os' Hreact']; eauto.
    inv Hreact'.
    inv H; use_final_nostep.
  Qed.

  Lemma forever_silent_star_not_reactive :
    forall s1 s2 t,
      Star sem s1 t s2 ->
      forever_silent sem observe s2 ->
      forall os,
        ~ forever_reactive sem observe s1 os.
  Proof.
    intros s1 s2 t Hstar Hsil os Hreact.
    edestruct forever_reactive_star_det as [os' Hreact']; eauto.
    inv Hreact'.
    contradiction H2; rewrite <- H0.
    eapply forever_silent_star_det_observe; eauto.
    eapply star_right; eauto.
  Qed.

  Lemma forever_reactive_det_eq :
    forall s os1 os2,
      forever_reactive sem observe s os1 ->
      forever_reactive sem observe s os2 -> EqSt os1 os2.
  Proof.
    cofix COINDHYP.
    intros s [o1 os1] [o2 os2] Hreact1 Hreact2.
    inv Hreact1; inv Hreact2.
    assert (s2 = s0).
    {
      use_star_step_diamond.
      - inv P; auto.
        simpl in *; use_step_det.
        contradiction H5.
        apply obs_leq_antisym.
        eapply obs_monotonic; eauto.
        rewrite <- H2; rewrite H7; eapply obs_monotonic_star; eauto.
      - inv P; auto.
        simpl in *; use_step_det.
        contradiction H10.
        apply obs_leq_antisym.
        eapply obs_monotonic; eauto.
        rewrite <- H7; rewrite H2; eapply obs_monotonic_star; eauto.
    }
    subst; use_step_det.
    constructor; simpl; eauto.
  Qed.

  Theorem beh_det :
    forall s b1 b2,
      has_behavior sem observe s b1 -> has_behavior sem observe s b2 -> beh_eq b1 b2.
  Proof.
    intros s b1 b2 Hbeh1 Hbeh2; inv Hbeh1.
    - (* Terminate *)
      inv Hbeh2; simpl.
      + f_equal; eapply proj2; eapply (steps_deterministic _ _ det); eauto.
        eapply det_final_nostep; eauto.
        eapply det_final_nostep; eauto.
      + eapply (terminates_not_goes_wrong _ _ det); [|eauto|..]; eauto.
      + eapply forever_silent_star_not_final; [eapply H1 | eapply H | ..]; eauto.
      + eapply forever_reactive_star_not_final; eauto.
    - (* Fault *)
      inv Hbeh2; simpl.
      + eapply (terminates_not_goes_wrong _ _ det); [..|eauto]; eauto.
      + f_equal; eapply proj2; eapply (steps_deterministic _ _ det); eauto.
      + eapply forever_silent_star_not_nostep; [eapply H2 | eapply H | ..]; eauto.
      + eapply forever_reactive_star_not_nostep; eauto.
    - (* SilentDiv *)
      inv Hbeh2; simpl.
      + eapply forever_silent_star_not_final; [eapply H | eapply H1 | eauto..].
      + eapply forever_silent_star_not_nostep; [eapply H | eapply H1 | eauto..].
      + use_star_step_diamond.
        erewrite forever_silent_star_det_observe; eauto; reflexivity.
        erewrite <- forever_silent_star_det_observe; eauto; reflexivity.
      + eapply forever_silent_star_not_reactive; eauto.
    - (* Reactive *)
      inv Hbeh2; simpl.
      + eapply forever_reactive_star_not_final; eauto.
      + eapply forever_reactive_star_not_nostep; [eapply H | eapply H0 | eauto..].
      + eapply forever_silent_star_not_reactive; eauto.
      + eapply forever_reactive_det_eq; eauto.
  Qed.

End BEH_DETERM.

Section SIMULATION.

  (* And now we define observation-aware simulations. We give a less-general
     version here than is presented in the paper, in two ways:

     1.) As mentioned in Section 3, we assume that all Behavioral machines use 
         the same type for observations. Furthermore, we actually will end up 
         proving that all of the mCertiKOS layers are Behavioral, using the monotonic 
         output buffer observation. Thus we only define simulations here between 
         semantics with observation functions using the same observation type.

     2.) We exploit the fact that output buffers remain the same across all of
         the mCertiKOS layers, and require a strong property on observations that 
         automatically implies the indistinguishability preservation property
         presented in the paper.

     In the future, we plan to extend this to support the whole theory presented
     in the paper (including the extended version of the paper). *)

  Context `{Obs': Observation}.

  Context {ret state1 state2 : Type}.
  Variables (sem1 : semantics ret state1) (sem2 : semantics ret state2).

  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).

  (* Specialization of CompCert's forward simulation that requires
     observations of matched states to be equal. *)
  Record simulation : Type :=
  Simulation {
    sim_index : Type;
    sim_order : sim_index -> sim_index -> Prop;
    sim_order_wf : well_founded sim_order;
    sim_match_states :> sim_index -> state1 -> state2 -> Prop;

    (* The observation property: all matching states must have identical observations.
       Note that this trivially implies the indistinguishability preservation property 
       from the paper. *)
    sim_match_observe :
      forall i s1 s2,
        sim_match_states i s1 s2 -> observe1 s1 = observe2 s2;

    sim_match_final_states :
      forall i s1 s2 r, 
        sim_match_states i s1 s2 -> 
        final_state sem1 s1 r -> final_state sem2 s2 r;
    sim_simulation :
      forall s1 t s1', Step sem1 s1 t s1' -> 
      forall i s2, sim_match_states i s1 s2 -> 
        exists i' s2',
           (Plus sem2 s2 t s2' \/ (Star sem2 s2 t s2' /\ sim_order i' i))
        /\ sim_match_states i' s1' s2'
  }.

  (* Trace-ignorant simulation. Traces are a relic of CompCert that mCertiKOS ignores,
     so we can often work with these instead of the stronger ones. *)
  Record weak_simulation : Type :=
  WeakSimulation {
    wsim_index : Type;
    wsim_order : wsim_index -> wsim_index -> Prop;
    wsim_order_wf : well_founded wsim_order;
    wsim_match_states :> wsim_index -> state1 -> state2 -> Prop;
    wsim_match_observe :
      forall i s1 s2,
        wsim_match_states i s1 s2 -> observe1 s1 = observe2 s2;
    wsim_match_final_states :
      forall i s1 s2 r, 
        wsim_match_states i s1 s2 -> 
        final_state sem1 s1 r -> final_state sem2 s2 r;
    wsim_simulation :
      forall s1 t s1', Step sem1 s1 t s1' -> 
      forall i s2, wsim_match_states i s1 s2 -> 
        exists i' t' s2',
           (Plus sem2 s2 t' s2' \/ (Star sem2 s2 t' s2' /\ wsim_order i' i))
        /\ wsim_match_states i' s1' s2'
  }.

  Definition weak_sim : simulation -> weak_simulation.
  Proof.
    intro sim.
    apply WeakSimulation with (wsim_index:= sim_index sim)
                              (wsim_order:= sim_order sim)
                              (wsim_match_states:= sim_match_states sim); try apply sim.
    intros; edestruct (sim_simulation sim); eauto.
  Defined.

  (* Now we establish various helpful lemmas that relate simulations with behaviors. *)

  Lemma simulation_no_stutter :
    forall (sim_match : state1 -> state2 -> Prop),
      (forall s1 s2,
        sim_match s1 s2 -> observe1 s1 = observe2 s2) ->
      (forall s1 s2 r, 
        sim_match s1 s2 -> 
        final_state sem1 s1 r -> final_state sem2 s2 r) ->
      (forall s1 t s1', Step sem1 s1 t s1' -> 
       forall s2, sim_match s1 s2 -> 
         exists s2', Plus sem2 s2 t s2'
           /\ sim_match s1' s2') -> simulation.
  Proof.
    intros sim_match match_obs match_final match_step.
    apply Simulation with (sim_index:= unit) (sim_order:= fun _ _ => False)
                          (sim_match_states:= fun _ s1 s2 => sim_match s1 s2); eauto.
    constructor; intuition.
    intros s1 t s1' Hstep1 ? s2 Hsim.
    edestruct match_step as [s2' [? ?]]; eauto.
  Qed.

  Lemma weak_simulation_no_stutter :
    forall (sim_match : state1 -> state2 -> Prop),
      (forall s1 s2,
        sim_match s1 s2 -> observe1 s1 = observe2 s2) ->
      (forall s1 s2 r, 
        sim_match s1 s2 -> 
        final_state sem1 s1 r -> final_state sem2 s2 r) ->
      (forall s1 t s1', Step sem1 s1 t s1' -> 
       forall s2, sim_match s1 s2 -> 
         exists t' s2', Plus sem2 s2 t' s2'
           /\ sim_match s1' s2') -> weak_simulation.
  Proof.
    intros sim_match match_obs match_final match_step.
    apply WeakSimulation with (wsim_index:= unit) (wsim_order:= fun _ _ => False)
                              (wsim_match_states:= fun _ s1 s2 => sim_match s1 s2); eauto.
    constructor; intuition.
    intros s1 t s1' Hstep1 ? s2 Hsim.
    edestruct match_step as [t' [s2' [? ?]]]; eauto.
    exists tt, t', s2'; eauto.
  Qed.

  Variable sim : simulation.

  Lemma sim_simulation':
    forall i s1 t s1', 
      Step sem1 s1 t s1' ->
      forall s2, sim i s1 s2 ->
           (exists i' s2', Plus sem2 s2 t s2' /\ sim i' s1' s2')
        \/ (exists i', sim_order sim i' i /\ t = E0 /\ sim i' s1' s2).
  Proof.
    intros. exploit sim_simulation; eauto. 
    intros [i' [s2' [A B]]]. intuition. 
    left; exists i', s2'; auto.
    inv H2. 
    right; exists i'; auto.
    left; exists i', s2'; split; auto. econstructor; eauto. 
  Qed.

  Lemma simulation_star :
    forall s1 t s1', Star sem1 s1 t s1' ->
      forall i s2, sim i s1 s2 ->
        exists i' s2', Star sem2 s2 t s2' /\ sim i' s1' s2'.
  Proof.
    induction 1; intros.
    exists i, s2; split; auto. apply star_refl.
    exploit sim_simulation; eauto. intros [i' [s2' [A B]]].
    exploit IHstar; eauto. intros [i'' [s2'' [C D']]].
    exists i'', s2''; split; auto. eapply star_trans; eauto.
    intuition. apply plus_star; auto. 
  Qed.

  Lemma simulation_plus:
    forall s1 t s1', Plus sem1 s1 t s1' ->
      forall i s2, sim i s1 s2 ->
           (exists i' s2', Plus sem2 s2 t s2' /\ sim i' s1' s2')
        \/ (exists i', clos_trans _ (sim_order sim) i' i /\ t = E0 /\ sim i' s1' s2).
  Proof.
    induction 1 using plus_ind2; intros.
    (* base case *)
    exploit sim_simulation'; eauto. intros [A | [i' A]].
    left; auto.
    right; exists i'; intuition. 
    (* inductive case *)
    exploit sim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A [B C]]]].
    exploit simulation_star. apply plus_star; eauto. eauto. 
    intros [i'' [s2'' [P Q]]].
    left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
    exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P [Q R]]]].
    subst. simpl. left; exists i''; exists s2''; auto.
    subst. simpl. right; exists i''; intuition.
    eapply t_trans; eauto. eapply t_step; eauto.
  Qed.

  Variable wsim : weak_simulation.
  Context `{Beh1: !Behavioral sem1 observe1} `{Beh2: !Behavioral sem2 observe2}.

  Lemma wsim_simulation':
    forall i s1 t s1', 
      Step sem1 s1 t s1' ->
      forall s2, wsim i s1 s2 ->
           (exists i' t' s2', Plus sem2 s2 t' s2' /\ wsim i' s1' s2')
        \/ (exists i', wsim_order wsim i' i /\ wsim i' s1' s2).
  Proof.
    intros. exploit wsim_simulation; eauto. 
    intros [i' [t' [s2' [A B]]]]. intuition. 
    left; exists i', t', s2'; auto.
    inv H2. 
    right; exists i'; auto.
    left; exists i', (t1 ** t2), s2'; split; auto. econstructor; eauto. 
  Qed.

  Lemma wsimulation_star :
    forall s1 t s1', Star sem1 s1 t s1' ->
      forall i s2, wsim i s1 s2 ->
        exists i' t' s2', Star sem2 s2 t' s2' /\ wsim i' s1' s2'.
  Proof.
    induction 1; intros.
    exists i, E0, s2; split; auto. apply star_refl.
    exploit wsim_simulation; eauto. intros [i' [t' [s2' [A B]]]].
    exploit IHstar; eauto. intros [i'' [t'' [s2'' [C D']]]].
    exists i'', (t' ** t''), s2''; split; auto. eapply star_trans; eauto.
    intuition. apply plus_star; auto. 
  Qed.

  Lemma wsimulation_plus:
    forall s1 t s1', Plus sem1 s1 t s1' ->
      forall i s2, wsim i s1 s2 ->
           (exists i' t' s2', Plus sem2 s2 t' s2' /\ wsim i' s1' s2')
        \/ (exists i', clos_trans _ (wsim_order wsim) i' i /\ wsim i' s1' s2).
  Proof.
    induction 1 using plus_ind2; intros.
    (* base case *)
    exploit wsim_simulation'; eauto. intros [A | [i' A]].
    left; auto.
    right; exists i'; intuition. 
    (* inductive case *)
    exploit wsim_simulation'; eauto. intros [[i' [t' [s2' [A B]]]] | [i' [A B]]].
    exploit wsimulation_star. apply plus_star; eauto. eauto. 
    intros [i'' [t'' [s2'' [P Q]]]].
    left; exists i'', (t' ** t''), s2''; split; auto. eapply plus_star_trans; eauto.
    exploit IHplus; eauto. intros [[i'' [t'' [s2'' [P Q]]]] | [i'' [P Q]]].
    subst. simpl. left; exists i'', t'', s2''; auto.
    subst. simpl. right; exists i''; intuition.
    eapply t_trans; eauto. eapply t_step; eauto.
  Qed.

  Lemma simulation_forever_silent :
    forall i s1 s2,
      forever_silent sem1 observe1 s1 -> wsim i s1 s2 -> 
      forever_silent sem2 observe2 s2.
  Proof.
    assert (forall i s1 s2,
              forever_silent sem1 observe1 s1 -> wsim i s1 s2 -> 
              forever_silent_N sem2 observe2 (wsim_index wsim) (wsim_order wsim) i s2).
    cofix COINDHYP; intros i s1 s2 Hsil Hsim; inv Hsil.
    - rename s3 into s1', H into Hstep1.
      edestruct wsim_simulation as [i' [t' [s2' [[Hplus2 | [Hstar2 Hsim']] Hsim'']]]]; eauto.
      + eapply forever_silent_N_plus; eauto.
        erewrite <- wsim_match_observe; [|eauto].
        rewrite H0; eapply wsim_match_observe; eauto.
      + eapply forever_silent_N_star; eauto.
        erewrite <- wsim_match_observe; [|eauto].
        rewrite H0; eapply wsim_match_observe; eauto.
    - intros i s1 s2 Hsil Hsim.
      eapply forever_silent_N_forever; eauto. 
      eapply wsim_order_wf.
  Qed.

  Lemma simulation_forever_reactive_help :
    forall i s1 s2 s2p os t,
      forever_reactive sem1 observe1 s1 os -> wsim i s1 s2 ->
      Star sem2 s2p t s2 -> observe2 s2p = observe2 s2 ->
      forever_reactive sem2 observe2 s2p os.
  Proof.
    cofix COINDHYP; intros i s1 s2 s2p os t Hreact Hsim Hstarp Hobsp; inv Hreact.
    rename s3 into s1', s4 into s1'', os0 into os, H into Hstar1, 
           H1 into Hstar1', H0 into Hobs_eq1, H2 into Hobs_neq1.
    edestruct wsimulation_star as [i' [t' [s2' [Hstar2 Hsim']]]]; eauto.
    edestruct wsim_simulation as [i'' [t'' [s2'' [[Hstar2' | [Hstar2' Hord]] Hsim'']]]]; eauto.
    + assert (Hstar2'': Star sem2 s2 (t' ** t'') s2'').
      apply plus_star; eapply star_plus_trans; eauto.
      destruct (observe_split_one _ _ _ _ _ Hstar2'') 
        as [s3 [s4 [t3 [t4 [t5 [Hstar3 [Hstar4 [Hstar5 [Hobs_eq3 Hobs_neq4]]]]]]]]].
      rewrite <- (wsim_match_observe _ _ _ _ Hsim''), <- (wsim_match_observe _ _ _ _ Hsim).
      rewrite Hobs_eq1.
      destruct (obs_measure_alt _ _ _ _ _ Hstar1'); auto.
      contradiction Hobs_neq1; apply obs_measure_eq; auto.
      apply (obs_monotonic _ _) in Hstar1'; assumption.
      erewrite wsim_match_observe; eauto.
      rewrite <- Hobsp; econstructor.
      eapply star_trans; eauto.
      congruence.
      eapply Hstar4.
      intro Hcon; contradiction Hobs_neq1.
      rewrite (wsim_match_observe _ _ _ _ Hsim''), <- Hobs_eq1.
      rewrite (wsim_match_observe _ _ _ _ Hsim); congruence.
      eauto.
    + assert (Hstar2'': Star sem2 s2 (t' ** t'') s2'').
      eapply star_trans; eauto.
      destruct (observe_split_one _ _ _ _ _ Hstar2'') 
        as [s3 [s4 [t3 [t4 [t5 [Hstar3 [Hstar4 [Hstar5 [Hobs_eq3 Hobs_neq4]]]]]]]]].
      rewrite <- (wsim_match_observe _ _ _ _ Hsim''), <- (wsim_match_observe _ _ _ _ Hsim).
      rewrite Hobs_eq1.
      destruct (obs_measure_alt _ _ _ _ _ Hstar1'); auto.
      contradiction Hobs_neq1; apply obs_measure_eq; auto.
      apply (obs_monotonic _ _) in Hstar1'; assumption.
      erewrite wsim_match_observe; eauto.
      rewrite <- Hobsp; econstructor.
      eapply star_trans; eauto.
      congruence.
      eapply Hstar4.
      intro Hcon; contradiction Hobs_neq1.
      rewrite (wsim_match_observe _ _ _ _ Hsim''), <- Hobs_eq1.
      rewrite (wsim_match_observe _ _ _ _ Hsim); congruence.
      eauto.
  Qed.

  Lemma simulation_forever_reactive :
    forall i s1 s2 os,
      forever_reactive sem1 observe1 s1 os -> wsim i s1 s2 ->
      forever_reactive sem2 observe2 s2 os.
  Proof.
    intros; eapply simulation_forever_reactive_help; eauto.
    constructor.
  Qed.

  (* Now we can prove that behaviors of the higher semantics are a subset of 
     behaviors of the lower semantics, assuming high-level safety. Notice
     that we only need a weak (trace-ignorant) simulation here, since behaviors
     are now defined using the observation function, as opposed to using traces 
     like in CompCert. *)

  Theorem sim_beh_subset :
    forall i s1 s2,
      safe sem1 s1 -> wsim i s1 s2 ->
      forall b,
        has_behavior sem1 observe1 s1 b -> 
        has_behavior sem2 observe2 s2 b.
  Proof.
    intros i s1 s2 Hsafe Hsim b Hbeh; inv Hbeh; simpl.
    - rename s' into s1', H into Hstar1.
      edestruct wsimulation_star as [i' [t' [s2' [Hstar2 Hsim']]]]; eauto.
      erewrite wsim_match_observe; eauto.
      econstructor; eauto.
      eapply wsim_match_final_states; eauto.
    - edestruct Hsafe as [[r Hfin] | [s'' [t' Hstep]]]; eauto.
      contradiction (H0 r).
      contradiction (H1 _ _ Hstep).
    - rename s' into s1', H into Hstar1.
      edestruct wsimulation_star as [i' [t' [s2' [Hstar2 Hsim']]]]; eauto.
      erewrite wsim_match_observe; eauto.
      econstructor; eauto.
      eapply simulation_forever_silent; eauto.
    - constructor.
      eapply simulation_forever_reactive; eauto.
  Qed.

End SIMULATION.

Coercion weak_sim : simulation >-> weak_simulation.

Section BISIM.

  (* Bisimulations are defined in the obvious way. *)

  Context `{Obs': Observation}.

  Context {ret state1 state2 : Type}.
  Variables (sem1 : semantics ret state1) (sem2 : semantics ret state2).

  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).

  (* Note that this is trace-ignorant. We have no need for a stronger,
     trace-dependent version. *)
  Record bisimulation : Type :=
  Bisimulation {
    bisim_index : Type;
    bisim_order : bisim_index -> bisim_index -> Prop;
    bisim_order_wf : well_founded bisim_order;
    bisim_match_states :> bisim_index -> state1 -> state2 -> Prop;
    bisim_match_observe :
      forall i s1 s2,
        bisim_match_states i s1 s2 -> observe1 s1 = observe2 s2;
    bisim_match_final_states :
      forall i s1 s2 r, 
        bisim_match_states i s1 s2 -> (final_state sem1 s1 r <-> final_state sem2 s2 r);
    bisim_simulation1 :
      forall s1 t s1', Step sem1 s1 t s1' ->
      forall i s2, bisim_match_states i s1 s2 ->
        exists i' t' s2',
           (Plus sem2 s2 t' s2' \/ (Star sem2 s2 t' s2' /\ bisim_order i' i))
        /\ bisim_match_states i' s1' s2';
    bisim_simulation2 :
      forall s2 t s2', Step sem2 s2 t s2' ->
      forall i s1, bisim_match_states i s1 s2 ->
        exists i' t' s1',
           (Plus sem1 s1 t' s1' \/ (Star sem1 s1 t' s1' /\ bisim_order i' i))
        /\ bisim_match_states i' s1' s2'
  }.

End BISIM.

Section BISIM_BEH.

  (* various useful facts about bisimulations *)

  Context `{Obs': Observation}.

  Context {ret state1 state2 : Type}.
  Variables (sem1 : semantics ret state1) (sem2 : semantics ret state2).

  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).

  Variable bisim : bisimulation sem1 sem2 observe1 observe2.

  Definition bisim_flip : bisimulation sem2 sem1 observe2 observe1.
  Proof.
    apply Bisimulation with (bisim_index:= bisim_index _ _ _ _ bisim)
                            (bisim_order:= bisim_order _ _ _ _ bisim)
                            (bisim_match_states:= fun i s1 s2 => 
                                                   bisim_match_states _ _ _ _ bisim i s2 s1);
      try apply bisim; try (symmetry; eapply bisim; eauto).
  Defined.

  Lemma bisim_flip_match_states :
    forall i s1 s2, bisim i s1 s2 -> bisim_flip i s2 s1.
  Proof.
    simpl; auto.
  Qed.

  Definition bisim_fsim : weak_simulation sem1 sem2 observe1 observe2.
  Proof.
    econstructor; apply bisim.
  Defined.

  Definition bisim_bsim : weak_simulation sem2 sem1 observe2 observe1.
  Proof.
    apply WeakSimulation with (wsim_index:= bisim_index _ _ _ _ bisim)
                              (wsim_order:= bisim_order _ _ _ _ bisim)
                              (wsim_match_states:= fun i s2 s1 => 
                                 bisim_match_states _ _ _ _ bisim i s1 s2); 
      try apply bisim; try (symmetry; eapply bisim; eauto).
    destruct bisim; intros; eapply bisim_match_final_states0; eauto.
  Defined.

  Context `{Beh1: !Behavioral sem1 observe1} `{Beh2: !Behavioral sem2 observe2}.

  Lemma bisim_beh_subset :
    forall i s1 s2,
      bisim i s1 s2 ->
      forall b,
        has_behavior sem1 observe1 s1 b -> 
        has_behavior sem2 observe2 s2 b.
  Proof.
    intros i s1 s2 Hsim b Hbeh; inv Hbeh; simpl.
    - rename s' into s1', H into Hstar1.
      edestruct (wsimulation_star _ _ _ _ bisim_fsim) as [i' [t' [s2' [Hstar2 Hsim']]]]; eauto.
      erewrite wsim_match_observe; eauto.
      econstructor; eauto.
      eapply wsim_match_final_states; eauto.
    - rename s' into s1', H into Hstar1.
      edestruct (wsimulation_star _ _ _ _ bisim_fsim) as [i' [t' [s2' [Hstar2 Hsim']]]]; eauto.
      erewrite wsim_match_observe; eauto.
      destruct (beh_exists sem2 observe2 s2') as [b Hbeh]; inv Hbeh.
      + apply star_inv in H; destruct H as [[? ?]|?]; subst.
        contradiction (H0 r).
        simpl in *; eapply bisim_match_final_states; eauto.
        edestruct (wsimulation_plus _ _ _ _ bisim_bsim) 
          as [[? [? [s1'' [Hstar1' Hsim'']]]] | [? [? Hsim'']]]; eauto.
        simpl in *; eauto.
        inv Hstar1'.
        contradiction (H1 _ _ H3).
        contradiction (H0 r).
        simpl in *; eapply bisim_match_final_states; eauto.
      + destruct (obs_eq_dec (observe2 s2') (observe2 s')) as [Heq|Hneq].
        rewrite Heq; econstructor; eauto.
        eapply star_trans; eauto.
        contradiction Hneq.
        erewrite <- (bisim_match_observe sem1 sem2); simpl in *; eauto.
        edestruct (wsimulation_star _ _ _ _ bisim_bsim) as [i''' [t''' [s1'' [Hstar1' Hsim'']]]]; eauto.
        simpl; eauto.
        inv Hstar1'.
        erewrite (bisim_match_observe sem1 sem2); simpl in *; eauto.
        contradiction (H1 _ _ H4).
      + assert (Hsil2: forever_silent sem2 observe2 s2').
        {
          eapply forever_silent_star; eauto.
          erewrite <- (bisim_match_observe sem1 sem2); simpl in *; eauto.
          edestruct (wsimulation_star _ _ _ _ bisim_bsim) as [i''' [t''' [s1'' [Hstar1' Hsim'']]]]; eauto.
          simpl; eauto.
          inv Hstar1'.
          erewrite (bisim_match_observe sem1 sem2); simpl in *; eauto.
          contradiction (H1 _ _ H3).
        }
        assert (Hsil1: forever_silent sem1 observe1 s1') by
          (eapply simulation_forever_silent with (wsim:= bisim_bsim); simpl in *; eauto).
        inv Hsil1.
        contradiction (H1 _ _ H3).
      + assert (Hreact: forever_reactive sem1 observe1 s1' os) by
          (eapply simulation_forever_reactive with (wsim:= bisim_bsim); simpl in *; eauto).
        inv Hreact.
        inv H2.
        contradiction (H1 _ _ H4).
        contradiction (H1 _ _ H7).
    - rename s' into s1', H into Hstar1.
      edestruct (wsimulation_star _ _ _ _ bisim_fsim) as [i' [t' [s2' [Hstar2 Hsim']]]]; eauto.
      erewrite wsim_match_observe; eauto.
      econstructor; eauto.
      eapply simulation_forever_silent; eauto.
    - constructor.
      eapply simulation_forever_reactive with (wsim:= bisim_fsim); eauto.
  Qed.

End BISIM_BEH.

Section BISIM_BEH_EQ.

  (* bisimulation => behavior equality (regardless of safety) *)

  Context `{Obs': Observation}.

  Context {ret state1 state2 : Type}.
  Variables (sem1 : semantics ret state1) (sem2 : semantics ret state2).
  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).
  Context `{Beh1: !Behavioral sem1 observe1} `{Beh2: !Behavioral sem2 observe2}.

  Variable bisim : bisimulation sem1 sem2 observe1 observe2.

  Theorem bisim_beh_eq :
    forall i s1 s2,
      bisim i s1 s2 ->
      state_beh_eq sem1 sem2 observe1 observe2 s1 s2.
  Proof.
    intros i s1 s2 Hsim.
    split; intros b Hbeh; exists b; split; try reflexivity.
    eapply (bisim_beh_subset sem1 sem2); eauto.
    eapply (bisim_beh_subset sem2 sem1); eauto.
    apply bisim_flip_match_states; eauto.
  Qed.

End BISIM_BEH_EQ.

Section COMPOSE_SIM.

  (* chaining simulations *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context {ret state1 state2 state3 : Type}.
  Variables (sem1 : semantics ret state1) 
            (sem2 : semantics ret state2) 
            (sem3 : semantics ret state3).
  Variables (observe1 : state1 -> obs)
            (observe2 : state2 -> obs)
            (observe3 : state3 -> obs).

  Theorem compose_simulation :
    simulation sem1 sem2 observe1 observe2 -> 
    simulation sem2 sem3 observe2 observe3 -> 
    simulation sem1 sem3 observe1 observe3.
  Proof.
    intros sim1 sim2.
    apply Simulation with (sim_index:= prod (sim_index _ _ _ _ sim2) (sim_index _ _ _ _ sim1))
                          (sim_order:= lex_ord (clos_trans _ (sim_order _ _ _ _ sim2)) 
                                               (clos_trans _ (sim_order _ _ _ _ sim1)))
                          (sim_match_states:= 
                             fun (i : prod (sim_index _ _ _ _ sim2) (sim_index _ _ _ _ sim1)) 
                                 s1 s3 => 
                               let (i0,i1) := i in
                               exists s2, sim_match_states _ _ _ _ sim1 i1 s1 s2 /\
                                          sim_match_states _ _ _ _ sim2 i0 s2 s3).
    - apply wf_lex_ord; apply Transitive_Closure.wf_clos_trans; destruct sim1, sim2; auto.
    - intros [i1 i0] s1 s3 [s2 [Hmatch0 Hmatch1]].
      apply (sim_match_observe _ _ _ _ _) in Hmatch0.
      apply (sim_match_observe _ _ _ _ _) in Hmatch1; congruence.
    - intros [i1 i0] s1 s3 r [s2 [Hmatch0 Hmatch1]] Hfin.
      eapply sim_match_final_states in Hmatch0; eauto.
      eapply sim_match_final_states in Hmatch1; eauto.
    - intros s1 t s1' Hstep1 [i1 i0] s3 [s2 [Hmatch0 Hmatch1]].
      edestruct (sim_simulation' _ _ _ _ sim1) as 
          [[i0' [s2' [Hplus2 Hmatch0']]] | [i0' [Hord [? Hmatch0']]]]; eauto; subst.
      + (* one or more steps in the middle execution *)
        edestruct (simulation_plus _ _ _ _ sim2) as 
            [[i1' [s3' [Hplus3 Hmatch1']]] | [i1' [Hord' [? Hmatch1']]]]; eauto; subst.
        * (* one or more steps in the bottom execution *)
          exists (i1',i0'), s3'; split; auto.
          exists s2'; auto.
        * (* zero steps in the bottom execution *)
          subst; exists (i1',i0'), s3; split.
          right; split; constructor; auto.
          exists s2'; auto.
      + (* zero steps in the middle execution *)
        subst; exists (i1,i0'), s3; split.
        right; split; [constructor|].
        apply lex_ord_right; constructor; auto.
        exists s2; auto.
  Qed.

  Theorem compose_weak_simulation :
    weak_simulation sem1 sem2 observe1 observe2 -> 
    weak_simulation sem2 sem3 observe2 observe3 -> 
    weak_simulation sem1 sem3 observe1 observe3.
  Proof.
    intros sim1 sim2.
    apply WeakSimulation with 
                          (wsim_index:= prod (wsim_index _ _ _ _ sim2) (wsim_index _ _ _ _ sim1))
                          (wsim_order:= lex_ord (clos_trans _ (wsim_order _ _ _ _ sim2)) 
                                               (clos_trans _ (wsim_order _ _ _ _ sim1)))
                          (wsim_match_states:= 
                             fun (i : prod (wsim_index _ _ _ _ sim2) (wsim_index _ _ _ _ sim1)) 
                                 s1 s3 => 
                               let (i0,i1) := i in
                               exists s2, wsim_match_states _ _ _ _ sim1 i1 s1 s2 /\
                                          wsim_match_states _ _ _ _ sim2 i0 s2 s3).
    - apply wf_lex_ord; apply Transitive_Closure.wf_clos_trans; destruct sim1, sim2; auto.
    - intros [i1 i0] s1 s3 [s2 [Hmatch0 Hmatch1]].
      apply (wsim_match_observe _ _ _ _ _) in Hmatch0.
      apply (wsim_match_observe _ _ _ _ _) in Hmatch1; congruence.
    - intros [i1 i0] s1 s3 r [s2 [Hmatch0 Hmatch1]] Hfin.
      eapply wsim_match_final_states in Hmatch0; eauto.
      eapply wsim_match_final_states in Hmatch1; eauto.
    - intros s1 t s1' Hstep1 [i1 i0] s3 [s2 [Hmatch0 Hmatch1]].
      edestruct (wsim_simulation' _ _ _ _ sim1) as 
          [[i0' [t0' [s2' [Hplus2 Hmatch0']]]] | [i0' [Hord Hmatch0']]]; eauto.
      + (* one or more steps in the middle execution *)
        edestruct (wsimulation_plus _ _ _ _ sim2) as 
            [[i1' [t1' [s3' [Hplus3 Hmatch1']]]] | [i1' [Hord' Hmatch1']]]; eauto.
        * (* one or more steps in the bottom execution *)
          exists (i1',i0'), t1', s3'; split; auto.
          exists s2'; auto.
        * (* zero steps in the bottom execution *)
          subst; exists (i1',i0'), E0, s3; split.
          right; split; constructor; auto.
          exists s2'; auto.
      + (* zero steps in the middle execution *)
        subst; exists (i1,i0'), E0, s3; split.
        right; split; [constructor|].
        apply lex_ord_right; constructor; auto.
        exists s2; auto.
  Qed.

  Corollary compose_simulation_inhabited :
    inhabited (simulation sem1 sem2 observe1 observe2) -> 
    inhabited (simulation sem2 sem3 observe2 observe3) -> 
    inhabited (simulation sem1 sem3 observe1 observe3).
  Proof.
    intros [sim1] [sim2]; constructor; apply compose_simulation; auto.
  Qed.

  Corollary compose_weak_simulation_inhabited :
    inhabited (weak_simulation sem1 sem2 observe1 observe2) -> 
    inhabited (weak_simulation sem2 sem3 observe2 observe3) -> 
    inhabited (weak_simulation sem1 sem3 observe1 observe3).
  Proof.
    intros [sim1] [sim2]; constructor; apply compose_weak_simulation; auto.
  Qed.

End COMPOSE_SIM.

Section SIM_DET.

  (* weak simulation + determinism of lower semantics + safety of higher execution  
        => equal behaviors *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context {ret state1 state2 : Type}.
  Variables (sem1 : semantics ret state1) (sem2 : semantics ret state2).
  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).

  Hypothesis sim : weak_simulation sem1 sem2 observe1 observe2.
  Hypothesis det : sem_deterministic sem2.

  Context `{Beh1: !Behavioral sem1 observe1} `{Beh2: !Behavioral sem2 observe2}.

  Theorem weak_sim_beh_eq :
    forall i s1 s2,
      safe sem1 s1 -> sim i s1 s2 ->
      state_beh_eq sem1 sem2 observe1 observe2 s1 s2.
  Proof.
    intros i s1 s2 Hsafe Hsim; split.
    intros b Hbeh; exists b; split; [|reflexivity].
    eapply (sim_beh_subset _ _ _ _ sim); eauto.
    intros b Hbeh.
    destruct (beh_exists sem1 observe1 s1) as [b' Hbeh']; exists b'; split; auto.
    eapply beh_det; eauto.
    eapply (sim_beh_subset _ _ _ _ sim); eauto.
  Qed.

End SIM_DET.

Section WORLD.

  (* CompCert distinguishes between deterministic semantics and determinate semantics,
     based on traces. Basically, traces represent observable events that may include 
     nondeterministic inputs. A determinate semantics is one that would be deterministic
     if we fixed all inputs from the external world. Thus CompCert also defines a "world"
     to represent an oracle that fixes inputs. "world_sem" converts a world-less semantics
     into one with a given initial world. CompCert proves that whenever you have a 
     determinate semantics, the world_sem conversion of that semantics is deterministic. 
     See Determinism.v for more information.

     In mCertiKOS, we completely ignore traces, so none of this really matters. Nevertheless,
     the worlds show up in our top-level security theorem because we need to interface
     with CompCert's notion of determinism. *)

  Context {ret state : Type}.
  Variable sem : semantics ret state.
  Variable wi : world.
  
  Lemma world_star : 
    forall s t s',
      Star (world_sem ret sem wi) s t s' <-> 
      Star sem (fst s) t (fst s') /\ possible_trace (snd s) t (snd s').
  Proof.
    intros s t s'; split.
    - induction 1.
      split; constructor.
      destruct IHstar, H; split.
      econstructor; eauto.
      subst; eapply possible_trace_app; eauto.
    - intros [Hstar Htrace]; generalize Htrace; clear Htrace.
      destruct s as [s w], s' as [s' w']; unfold fst, snd in *.
      generalize w w'; clear w w'.
      induction Hstar.
      intros w w' Htrace; inv Htrace; constructor.
      subst; intros w w' Htrace; edestruct possible_trace_app_inv as [w'' [Ht1 Ht2]]; eauto.
      eapply star_trans with (s2:= (s2,w'')); eauto.
      eapply star_step with (s2:= (s2,w'')).
      constructor; eauto.
      constructor.
      rewrite E0_right; auto.
  Qed.

  Lemma world_plus : 
    forall s t s',
      Plus (world_sem ret sem wi) s t s' <-> 
      Plus sem (fst s) t (fst s') /\ possible_trace (snd s) t (snd s').
  Proof.
    intros s t s'; split.
    - intro Hplus; inv Hplus.
      inv H; apply world_star in H0; destruct H0; split.
      econstructor; eauto.
      eapply possible_trace_app; eauto.
    - intros [Hplus Htrace]; inv Hplus.
      edestruct possible_trace_app_inv as [w'' [Ht1 Ht2]]; eauto.
      eapply plus_left with (s2:= (s2,w'')); eauto.
      constructor; auto.
      apply world_star; auto.
  Qed.

  Context `{Obs': Observation}.

  Variable observe : state -> obs.

  (* worlds are not observable (mCertiKOS completely ignores them) *)
  Definition world_observe (s : state * world) :=
    match s with (s,_) => observe s end.

  (* simulation from a semantics with worlds to one without worlds *)
  Definition world_sim1 :
    simulation (world_sem ret sem wi) sem world_observe observe.
  Proof.
    apply Simulation with (sim_index:= unit)
                          (sim_order:= fun _ _ => False)
                          (sim_match_states:= fun _ sw s => s = fst sw).
    - constructor; intuition.
    - intros ? [s1 w] s2 ?; subst; auto.
    - intros ? [s1 w] s2 r ?; subst; auto.
    - intros [s1 w] t s1' Hstep ? s2 ?; subst.
      inv Hstep.
      exists tt, (fst s1'); split; auto.
      left; apply plus_one; auto.
  Defined.

  (* We now assume a situation that is true in mCertiKOS: traces are never produced
     once the system is properly initialized (I believe they're also never produced
     prior to initialization, but this hasn't been proved).

     Under this assumption, we establish a simulation from the semantics without
     worlds to the one with worlds. *)

  Variable init : state -> Prop.

  Hypothesis init_preserved :
    forall s t s',
      init s -> Step sem s t s' -> init s'.

  Hypothesis init_no_trace : 
    forall s t s', 
      init s -> Step sem s t s' -> t = E0.

  Hypothesis final_nostep :
    forall s r,
      final_state sem s r -> Nostep sem s.

  Lemma init_preserved_star :
    forall s t s', 
      init s -> Star sem s t s' -> init s'.
  Proof.
    induction 2; eauto.
  Qed.

  Lemma world_safe :
    forall s w,
      init s -> safe sem s -> 
      safe (world_sem ret sem wi) (s,w).
  Proof.
    intros s w Hinit Hsafe [s' w'] t Hstar.
    apply world_star in Hstar; destruct Hstar; simpl in *.
    destruct (Hsafe s' t) as [? | [s'' [t' Hstep]]]; auto.
    right; exists (s'',w'), t'; simpl; split; auto.
    assert (t' = E0).
    eapply init_no_trace; [|eauto].
    eapply init_preserved_star; eauto.
    subst; constructor.
  Qed.

  Definition world_sim2 :
    simulation sem (world_sem ret sem wi) observe world_observe.
  Proof.
    apply Simulation with (sim_index:= unit)
                          (sim_order:= fun _ _ => False)
                          (sim_match_states:= 
                             fun _ s sw => s = fst sw /\ init s /\ 
                                           safe (world_sem ret sem wi) sw).
    - constructor; intuition.
    - intros ? s1 [s2 w] [? ?]; subst; auto.
    - intros ? s1 [s2 w] r [? ?] ?; subst; auto.
    - intros s1 t s1' Hstep ? [s2 w] [? [Hinit Hsafe]]; subst.
      destruct (Hsafe (s2,w) E0) as [[r Hfin] | [s2' [t' Hstep']]].
      constructor.
      simpl in Hfin; edestruct final_nostep; eauto.
      inv Hstep'.
      assert (t = E0) by (eapply init_no_trace; eauto); subst.
      exists tt, (s1',w); split; eauto.     
      left; apply plus_one; constructor; simpl; auto; constructor.
      split; auto; split; eauto.
      eapply safe_step; eauto.
      constructor; simpl; eauto; constructor.
  Defined.

  (* Now we combine the two simulations to prove behavior equality. *)

  Context `{Hbeh : !Behavioral sem observe}.

  Instance world_behavioral : Behavioral (world_sem ret sem wi) world_observe.
  Proof.
    constructor.
    - intros t [s1 w1] [s2 w2]; simpl.
      intros [? ?]; eapply obs_monotonic; eauto.
    - intros t [s1 w1] [s2 w2]; simpl.
      intros [? ?]; eapply obs_monotonic_measure; eauto.
  Qed.

  Theorem world_state_beh_eq :
    forall s w,
      init s -> safe sem s ->
      safe (world_sem ret sem wi) (s,w) ->
      state_beh_eq sem (world_sem ret sem wi) observe world_observe s (s,w).
  Proof.
    intros s w Hinit Hsafe1 Hsafe2; split; intros b Hb; exists b; split; try reflexivity.
    eapply sim_beh_subset with (wsim:= world_sim2) (i:= tt); simpl; eauto.
    apply world_behavioral.
    eapply sim_beh_subset with (wsim:= world_sim1) (i:= tt); simpl; eauto.
    apply world_behavioral.
  Qed.

End WORLD.

Section WORLD_SIM.

  (* strong simulation + determinate lower semantics + fixed input 
        + no traces produced after initialization => behavior equality *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context {ret state1 state2 : Type}.
  Variables (sem1 : semantics ret state1) (sem2 : semantics ret state2).
  Variables (observe1 : state1 -> obs) (observe2 : state2 -> obs).

  Hypothesis sim : simulation sem1 sem2 observe1 observe2.
  Hypothesis det : determinate sem2.
  Variable wi : world.  (* fixed input *)

  Definition world_sim : simulation (world_sem ret sem1 wi) (world_sem ret sem2 wi)
                                 (world_observe observe1) (world_observe observe2).
  Proof.
    apply Simulation with (sim_index:= sim_index _ _ _ _ sim)
                          (sim_order:= sim_order _ _ _ _ sim)
                          (sim_match_states:= fun i (s1 : state1 * world) (s2 : state2 * world) =>
                                                sim_match_states _ _ _ _ sim i (fst s1) (fst s2) /\
                                                snd s1 = snd s2);
      try apply sim.
    - destruct s1, s2; simpl.
      intros [? ?]; eapply sim; eauto.
    - simpl; intros ? ? ? ? [? ?]; eapply sim; eauto.
    - intros [s1 w1] t [s1' w1'] [Hstep Htrace] i [s2 w2] [Hsim ?]; unfold fst, snd in *; subst.
      edestruct (sim_simulation' _ _ _ _ sim) as 
          [[i' [s2' [Hplus2 Hmatch']]] | [i' [Hord [? Hmatch']]]]; eauto.
      exists i', (s2',w1'); split; auto.
      left; apply world_plus; auto.
      exists i', (s2,w1'); split; auto.
      right; split; auto.
      subst; inv Htrace; constructor.
  Defined.

  Context `{Beh1: !Behavioral sem1 observe1} `{Beh2: !Behavioral sem2 observe2}.

  Variable init : state1 -> Prop.

  Hypothesis init_preserved :
    forall s t s',
      init s -> Step sem1 s t s' -> init s'.

  Hypothesis init_safe : 
    forall s, init s -> safe sem1 s.

  Hypothesis init_no_trace : 
    forall s t s', 
      init s -> Step sem1 s t s' -> t = E0.

  Theorem sim_beh_eq : 
    forall i s1 s2 w,
      init s1 -> sim i s1 s2 -> 
      state_beh_eq (world_sem ret sem1 wi) (world_sem ret sem2 wi) 
                   (world_observe observe1) (world_observe observe2) (s1,w) (s2,w).
  Proof.
    intros i s1 s2 w Hinit Hsim.
    eapply (weak_sim_beh_eq _ _ _ _ world_sim).
    apply world_sem_deterministic; auto.
    apply world_behavioral; auto.
    apply world_behavioral; auto.
    eapply world_safe; eauto.
    simpl; eauto.
  Qed.

End WORLD_SIM.

(*
Section F2B.

  (* convert forward simulations to backward, same proof method as in CompCert *)
  (* note that the forward sim must have the strong match_final property, while 
     the constructed backward sim only has the weak one *)

  Context `{Obs': Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context {D1 D2 : compatdata} `{L1: compatlayer D1} `{L2: compatlayer D2}.
  Context `{Hacc1: !AccessorsDefined L1} `{Hacc2: !AccessorsDefined L2}.
  Context `{Beh1: !Behavioral(L:=L1)} `{Beh2: !Behavioral(L:=L2)}.

  Context {p1 p2 : program}.

  Notation sem1 := (LAsm.semantics (lcfg_ops := LC L1) p1).
  Notation sem2 := (LAsm.semantics (lcfg_ops := LC L2) p2).
  Notation state1 := (Smallstep.state sem1).
  Notation state2 := (Smallstep.state sem2).
  Notation step1 := (Smallstep.step sem1).
  Notation step2 := (Smallstep.step sem2).
  Notation ge1 := (globalenv sem1).
  Notation ge2 := (globalenv sem2).

  Variable FS: simulation L1 L2 p1 p2 true.
  Hypothesis L1rec: receptive sem1.
  Hypothesis L2det: determinate sem2.

  (* To flip the simulation, we will need to execute the safe L1 execution
     for enough steps such that the corresponding L2 execution takes at least
     one step. The following inductive type and lemma accomplish this. *)
  Inductive f2b_transitions: state1 -> state2 -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r,
      star step1 ge1 s1 E0 s1' ->
      Asm.final_state s1' r ->
      Asm.final_state s2 r ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall s1 s2 s1' t s1'' s2' i' i'',
      star step1 ge1 s1 E0 s1' ->
      observe s1 = observe s1' ->
      step1 ge1 s1' t s1'' ->
      plus step2 ge2 s2 t s2' ->
      FS i' s1' s2 -> 
      FS i'' s1'' s2' ->
      f2b_transitions s1 s2.

  Lemma f2b_progress:
    forall i s1 s2, FS i s1 s2 -> safe ge1 s1 -> f2b_transitions s1 s2.
  Proof.
    intros i0; pattern i0. apply well_founded_ind with (R := sim_order p1 p2 FS). 
    apply sim_order_wf.
    intros i REC s1 s2 MATCH SAFE.
    destruct (SAFE s1 E0) as [[r FINAL] | [s1' [t STEP1]]]. apply star_refl.
    (* final state reached *)
    eapply f2b_trans_final; eauto. apply star_refl.
    eapply sim_match_final_states_weak with (sim:=FS); eauto.
    (* L1 can make one step *)
    exploit (sim_simulation _ _ FS); eauto. intros [i' [s2' [A MATCH']]].
    assert (B: plus step2 ge2 s2 t s2' \/ (s2' = s2 /\ t = E0 /\ sim_order _ _ FS i' i)).
    destruct A as [? | [A B]]; auto.
    inv A; auto.
    left; econstructor; eauto.
    clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
    eapply f2b_trans_step; eauto. apply star_refl.
    subst. exploit REC; eauto. eapply safe_star; eauto. apply star_one; eauto.
    intros TRANS; inv TRANS.
    eapply f2b_trans_final; eauto.
    eapply star_left; eauto. 
    eapply f2b_trans_step; [| |eauto..].
    eapply star_trans; eauto.
    eapply star_left; eauto.
    constructor.
    auto.
    rewrite (sim_match_observe _ _ _ _ _ _ MATCH).
    rewrite (sim_match_observe _ _ _ _ _ _ H3); auto.
  Qed.

  Lemma fsim_simulation_not_E0:
    forall s1 t s1', step1 ge1 s1 t s1' -> t <> E0 ->
    forall i s2, FS i s1 s2 ->
      exists i' s2', plus step2 ge2 s2 t s2' /\ FS i' s1' s2'.
  Proof.
    intros. exploit (sim_simulation _ _ FS); eauto. intros [i' [s2' [A B]]].
    exists i'; exists s2'; split; auto.
    destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
    congruence.
  Qed.

  Lemma f2b_determinacy_inv:
    forall s2 t' s2' t'' s2'',
      step2 ge2 s2 t' s2' -> step2 ge2 s2 t'' s2'' ->
      (t' = E0 /\ t'' = E0 /\ s2' = s2'')
      \/ (t' <> E0 /\ t'' <> E0 /\ match_traces ge1 t' t'').
  Proof.
    intros. 
    assert (match_traces ge2 t' t'').
    eapply sd_determ_1; eauto. 
    destruct (silent_or_not_silent t').
    subst. inv H1.  
    left; intuition. eapply sd_determ_2; eauto.
    econstructor; eauto.
    destruct (silent_or_not_silent t'').
    subst. inv H1. elim H2; auto. 
    right; intuition.
    eapply match_traces_preserved with (ge1 := ge2); auto.
    intros; apply (sim_symbols_preserved _ _ FS). 
  Qed.

  Lemma f2b_determinacy_star:
    forall s s1, star step2 ge2 s E0 s1 -> 
    forall t s2 s3,
      step2 ge2 s1 t s2 -> t <> E0 ->
      star step2 ge2 s t s3 ->
      star step2 ge2 s1 t s3.
  Proof.
    intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
    intros. inv H3. congruence.
    exploit f2b_determinacy_inv. eexact H. eexact H4.
    intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
    subst. simpl in *. eauto. 
    congruence.
  Qed.

  Lemma f2b_determinacy_star_star:
    forall s s1, star step2 ge2 s E0 s1 -> 
    forall t s2 s3,
      star step2 ge2 s1 t s2 -> t <> E0 ->
      star step2 ge2 s t s3 ->
      star step2 ge2 s1 t s3.
  Proof.
    intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
    intros. inv H3. congruence.
    exploit f2b_determinacy_inv. eexact H. eexact H4.
    intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
    subst. simpl in *. eauto. 
    congruence.
  Qed.

  Inductive f2b_match_states: f2b_index -> state1 -> state2 -> Prop :=
  | f2b_match_at: 
      forall i s1 s2,
        FS i s1 s2 ->
        f2b_match_states (F2BI_after O) s1 s2
  | f2b_match_before_trace: 
      forall s1 t s1' s2b s2 n s2a i,
        step1 ge1 s1 t s1' -> 
        t <> E0 ->
        star step2 ge2 s2b E0 s2 ->
        starN step2 ge2 n s2 t s2a ->
        FS i s1 s2b ->
        f2b_match_states (F2BI_before n) s1 s2
  | f2b_match_before_observe: 
      forall s1 s1' s2b s2 n s2a i,
        step1 ge1 s1 E0 s1' -> 
        observe s2 <> observe s2a ->
        observe s2b = observe s2 ->
        observe s1' = observe s2a ->
        star step2 ge2 s2b E0 s2 ->
        starN step2 ge2 n s2 E0 s2a ->
        FS i s1 s2b ->
        f2b_match_states (F2BI_before n) s1 s2
  | f2b_match_after: 
      forall n s2 s2a s1 i,
        starN step2 ge2 (S n) s2 E0 s2a ->
        observe s2 = observe s2a ->
        FS i s1 s2a ->
        f2b_match_states (F2BI_after (S n)) s1 s2.

  Remark f2b_match_after':
    forall n s2 s2a s1 i,
      starN step2 ge2 n s2 E0 s2a ->
      observe s2 = observe s2a ->
      FS i s1 s2a ->
      f2b_match_states (F2BI_after n) s1 s2.
  Proof.
    intros. inv H. 
    econstructor; eauto.
    econstructor; eauto. econstructor; eauto.
  Qed.

  Lemma f2b_match_before_trace_no_obs :
    forall s1 t s1' s2b s2 n s2a i,
      step1 ge1 s1 t s1' -> 
      t <> E0 ->
      star step2 ge2 s2b E0 s2 ->
      starN step2 ge2 n s2 t s2a ->
      FS i s1 s2b ->
      observe s2b = observe s2.
  Proof.
    intros s1 t s1' s2b s2 n s2a i Hstep1 Ht Hstar2b Hstar2 Hsim.
    edestruct fsim_simulation_not_E0 as [i' [s2' [Hplus2b Hsim']]]; eauto.
    exploit f2b_determinacy_star_star; [eapply Hstar2b|..]; eauto.
    eapply starN_star; eauto.
    eapply plus_star; eauto.
    intro Hstar2'.
    apply obs_leq_antisym.
    eapply obs_monotonic_star; eauto.
    destruct (obs_eq_dec (observe s1) (observe s1')) as [Hobs|Hobs].
    rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim), Hobs.
    rewrite (sim_match_observe _ _ _ _ _ _ Hsim').
    eapply obs_monotonic_star; eauto.
    contradiction Ht; eapply (obs_trace_silent(L:=L1)); eauto.
  Qed.

  Lemma f2b_match_observe :
    forall i s1 s2,
      f2b_match_states i s1 s2 ->
      observe s1 = observe s2.
  Proof.
    intros i s1 s2 Hmatch; inv Hmatch.
    - eapply sim_match_observe; eauto.
    - erewrite <- f2b_match_before_trace_no_obs; eauto.
      eapply sim_match_observe;  eauto.
    - transitivity (observe s2b); auto.
      eapply sim_match_observe; eauto.
    - transitivity (observe s2a); auto.
      eapply sim_match_observe; eauto.
  Qed.

  Lemma f2b_match_final_states :
    forall i s1 s2 r, 
      f2b_match_states i s1 s2 -> 
      Asm.final_state s2 r -> Asm.final_state s1 r.
  Proof.
    intros i s1 s2 r Hmatch; inv Hmatch.
    - destruct FS; eapply sim_match_final_states0; eauto.
    - inv H2; try congruence.
      intros; edestruct final_nostep; eauto.
    - inv H4; try congruence.
      intros; edestruct final_nostep; eauto.
    - inv H; intros; edestruct final_nostep; eauto.
  Qed.

  Lemma f2b_simulation_step:
    forall s2 t s2', step2 ge2 s2 t s2' ->
    forall i s1, f2b_match_states i s1 s2 -> safe ge1 s1 ->
      exists i' s1',
        (plus step1 ge1 s1 t s1' \/ (star step1 ge1 s1 t s1' /\ f2b_order i' i))
        /\ f2b_match_states i' s1' s2'.
  Proof.
    intros s2 t s2' Hstep2 i s1 Hmatch Hsafe.
    inv Hmatch.
    - (* Case 1: f2b_match_at *)
      rename H into Hsimpre; exploit f2b_progress; eauto; intro Htrans; inv Htrans.
      exploit (sd_final_nostep L2det); eauto; contradiction.
      rename s1 into s1pre, s1' into s1, s1'' into s1', s2'0 into s2'', 
             H1 into Hstep1, H2 into Hplus, H3 into Hsim, H4 into Hsim'.
      inv Hplus.
      exploit f2b_determinacy_inv; [eapply H1 | eapply Hstep2 |..].
      intros [Hand|Hand]; decompose [and] Hand; subst; clear Hand.

      (* Case 1a: first step from s2 is silent *)
      destruct (star_starN H2) as [n Hstar3].
      destruct (silent_or_not_silent t2); subst;
      destruct (obs_eq_dec (observe s2') (observe s2'')) as [Hobs|Hobs].
      (* silent, no observation *)
      exists (F2BI_after n), s1'; split.
      left; eapply plus_right; eauto.
      eapply f2b_match_after'; eauto.
      (* silent, observation *)
      exists (F2BI_before n), s1; split.
      right; split; auto; constructor.
      eapply f2b_match_before_observe; [| | |eauto..]; eauto.
      {
        destruct (obs_measure_alt _ _ _ _ Hstep1) as [Hm|Hm].
        - symmetry in Hm; apply obs_measure_eq in Hm; [| eapply obs_monotonic; eauto].
          apply obs_leq_antisym.
          eapply obs_monotonic; eauto.
          rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim).
          rewrite Hm, (sim_match_observe _ _ _ _ _ _ Hsim').
          eapply obs_monotonic_star; eauto.
        - edestruct obs_measure_alt_star as [Hm'|Hm']; [| eapply H2 |..].
          eapply star_left; eauto.
          constructor.
          rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim).
          rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim'); auto.
          auto.
          contradiction.
      }
      rewrite (sim_match_observe _ _ _ _ _ _ Hsim'); auto.
      eapply star_left; eauto.
      constructor.
      auto.
      (* not silent, no observation *)
      exists (F2BI_before n), s1; split.
      right; split; auto; constructor.
      eapply f2b_match_before_trace; [| | | |eauto]; eauto.
      eapply star_left; eauto.
      constructor.
      auto.
      (* not silent, observation (impossible) *)
      contradiction H3.
      destruct (obs_eq_dec (observe s2) (observe s2')) as [Hobs'|Hobs'].
      eapply (obs_trace_silent(L:=L1)); eauto.
      rewrite (sim_match_observe _ _ _ _ _ _ Hsim), Hobs'.
      rewrite (sim_match_observe _ _ _ _ _ _ Hsim'); auto.
      edestruct obs_measure_alt_star; [| eapply H2 |..].
      eapply star_left; eauto.
      constructor.
      assert (obs_measure (observe s1') <> obs_measure (observe s1)).
      {
        rewrite (sim_match_observe _ _ _ _ _ _ Hsim).
        rewrite (sim_match_observe _ _ _ _ _ _ Hsim').
        assert (obs_measure (observe s2) < obs_measure (observe s2')).
        apply obs_lt_measure; split; auto.
        eapply obs_monotonic; eauto.
        assert (obs_measure (observe s2') < obs_measure (observe s2'')).
        apply obs_lt_measure; split; auto.
        eapply obs_monotonic_star; eauto.
        omega.
      }
      edestruct (obs_measure_alt(L:=L1)); eauto; try contradiction.
      rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim).
      rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim'); auto.
      congruence.
      congruence.

      (* Case 1b: first step from s2 is not silent *)
      destruct (silent_or_not_silent t2); subst.
      rewrite E0_right in *.
      edestruct sr_receptive as [s1'' Hstep1']; eauto.
      edestruct fsim_simulation_not_E0 as [i1 [s2''' [Hplus Hsim'']]]; [eapply Hstep1'|..]; eauto.
      inv Hplus.
      destruct (silent_or_not_silent t0); subst.
      contradiction H3.
      exploit f2b_determinacy_inv; [eapply H1 | eapply H4 |..].
      intros [Hand|Hand]; decompose [and] Hand; congruence.
      destruct (silent_or_not_silent t2); subst.
      rewrite E0_right in *.
      exploit sd_determ_2; [eapply L2det | eapply H4 | eapply Hstep2 |..].
      intros; subst.
      destruct (obs_eq_dec (observe s2') (observe s2''')) as [Hobs|Hobs].
      (* no observation *)
      destruct (star_starN H7) as [n Hstar3].
      exists (F2BI_after n), s1''; split.
      left; eapply plus_right; eauto.
      eapply f2b_match_after'; eauto.
      (* observation (impossible) *)
      contradiction H5.
      destruct (obs_eq_dec (observe s2) (observe s2')) as [Hobs'|Hobs'].
      eapply (obs_trace_silent(L:=L1)); eauto.
      rewrite (sim_match_observe _ _ _ _ _ _ Hsim), Hobs'.
      rewrite (sim_match_observe _ _ _ _ _ _ Hsim''); auto.
      eapply (obs_trace_silent(L:=L2)); eauto.
      apply (sr_traces L1rec) in Hstep1'.
      apply not_silent_length in Hstep1'; destruct Hstep1'; congruence.
      apply (sr_traces L1rec) in Hstep1; auto.
      apply not_silent_length in Hstep1; destruct Hstep1; congruence.

    - (* Case 2: f2b_match_before_trace *)
      rename H3 into Hsim, H1 into Hstar2b, H2 into Hstar2.
      inv Hstar2; [congruence|].
      exploit f2b_determinacy_inv; [eapply H1 | eapply Hstep2 |].
      intros [Hand|Hand]; decompose [and] Hand; clear Hand; subst.
      (* Case 2a: first step from s2 is silent *)
      exists (F2BI_before n0), s1; split.
      right; split; constructor; auto.
      econstructor; eauto.
      eapply star_right; eauto.
      (* Case 2b: first step from s2 is not silent *)
      rename s' into s2'', n0 into n, H into Hstep1, H1 into Hstep2'.
      destruct (silent_or_not_silent t3); subst.
      rewrite E0_right in *.
      edestruct sr_receptive as [s1'' Hstep1']; eauto.
      edestruct fsim_simulation_not_E0 as [i [s2''' [Hplus Hsim']]]; [eapply Hstep1'|..]; eauto.
      exploit f2b_determinacy_star; [eapply Hstar2b | eapply Hstep2 |..]; auto.
      eapply plus_star; eauto.
      intro Hstar2; inv Hstar2; try congruence.
      destruct (silent_or_not_silent t0); subst.
      rewrite E0_right in *.
      exploit (sd_determ_2 L2det); [eapply H | eapply Hstep2 |..].
      intros; subst.
      destruct (obs_eq_dec (observe s2') (observe s2''')) as [Hobs|Hobs].
      (* no observation *)
      destruct (star_starN H1) as [n' Hstar].
      exists (F2BI_after n'), s1''; split.
      left; eapply plus_right; eauto; constructor.
      eapply f2b_match_after'; eauto.
      (* observation (impossible) *)
      contradiction Hobs.
      destruct (obs_eq_dec (observe s1) (observe s1'')) as [Hobs'|Hobs'].
      apply obs_leq_antisym.
      eapply obs_monotonic_star; eauto.
      rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim'), <- Hobs'.
      rewrite (sim_match_observe _ _ _ _ _ _ Hsim).
      eapply obs_monotonic_star; eapply star_trans; eauto.
      eapply star_right; eauto; constructor.
      contradiction H5; eapply (obs_trace_silent(L:=L1)); eauto.
      exploit f2b_determinacy_inv; [eapply Hstep2 | eapply H |].
      intros [Hand|Hand]; decompose [and] Hand; clear Hand; subst; try congruence.
      apply (sr_traces L1rec) in Hstep1'.
      apply not_silent_length in Hstep1'; destruct Hstep1'; congruence.
      apply (sr_traces L1rec) in Hstep1; auto.
      apply not_silent_length in Hstep1; destruct Hstep1; congruence.

    - (* Case 3: f2b_match_before_observe *)
      rename H5 into Hsim, H3 into Hstar2b, H4 into Hstar2.
      inv Hstar2; [congruence|].
      rename H3 into Hstep2', H4 into Hstar2, s' into s2'', H5 into Ht, n0 into n.
      symmetry in Ht; apply Eapp_E0_inv in Ht; destruct Ht; subst.
      exploit f2b_determinacy_inv; [eapply Hstep2 | eapply Hstep2' |].
      intros [Hand|Hand]; decompose [and] Hand; clear Hand; subst; try congruence.
      rename s2'' into s2'; destruct (obs_eq_dec (observe s2) (observe s2')) as [Hobs|Hobs].
      (* Case 2a: first step from s2 has no observation *)
      exists (F2BI_before n), s1; split.
      right; split; constructor; auto.
      eapply f2b_match_before_observe; [..|eauto]; eauto.
      congruence.
      congruence.
      eapply star_right; eauto.
      (* Case 2b: first step from s2 has observation *)
      rename H0 into Hobs_neq, H1 into Hobsb, H2 into Hobs'.
      edestruct (sim_simulation _ _ FS) as [i [s2'' [Hstar2' Hsim']]]; eauto.
      assert (Hstar2b': star step2 ge2 s2b E0 s2'').
      destruct Hstar2' as [?|[? ?]]; auto; eapply plus_star; eauto.
      edestruct (Smallstep.star_determinacy L2det) as [Hstar2''|Hstar2'']; 
        [eapply Hstar2b'|eapply Hstar2b|..].
      contradiction Hobs_neq.
      apply obs_leq_antisym.
      eapply obs_monotonic_star.
      eapply star_left; eauto.
      eapply starN_star; eauto.
      rewrite <- Hobs', (sim_match_observe _ _ _ _ _ _ Hsim').
      eapply obs_monotonic_star; eauto.
      inv Hstar2''.
      contradiction Hobs_neq.
      rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim'); auto.
      symmetry in H2; apply Eapp_E0_inv in H2; destruct H2; subst.
      exploit (sd_determ_2 L2det); [eapply Hstep2' | eapply H0 |..].
      intros; subst.
      destruct (star_starN H1) as [n' Hstar].
      exists (F2BI_after n'), s1'; split.
      left; econstructor; eauto; constructor.
      eapply f2b_match_after'; eauto.
      exploit obs_measure_alt_star.
      eapply star_one; eauto.
      eauto.
      edestruct (obs_measure_alt(L:=L1)) as [Heq|Heq]; [eapply H|..].
      symmetry in Heq; apply obs_measure_eq in Heq.
      contradiction Hobs_neq.
      rewrite <- Hobsb, <- (sim_match_observe _ _ _ _ _ _ Hsim); congruence.
      eapply obs_monotonic; eauto.
      rewrite <- Hobsb, <- (sim_match_observe _ _ _ _ _ _ Hsim).
      rewrite <- (sim_match_observe _ _ _ _ _ _ Hsim'); auto.
      intros [Heq|Heq]; congruence.

    - (* Case 4: f2b_match_after *)
      rename s1 into s1pre, H into Hstar2, H0 into Hobs2, H1 into Hsimpre.
      inv Hstar2.
      symmetry in H2; apply Eapp_E0_inv in H2; destruct H2; subst.
      exploit f2b_determinacy_inv; [eapply Hstep2 | eapply H0 |].
      intros [Hand|Hand]; decompose [and] Hand; clear Hand; subst; try congruence.
      clear H0 H3; rename H1 into Hstar2.
      exists (F2BI_after n), s1pre; split.
      right; split; constructor; auto.
      eapply f2b_match_after'; eauto.
      apply obs_leq_antisym.
      eapply obs_monotonic_star; eapply starN_star; eauto.
      rewrite <- Hobs2; eapply obs_monotonic; eauto.
  Qed.

  Lemma flip_simulation: simulation L2 L1 p2 p1 false.
  Proof.
    apply Simulation with (sim_order := f2b_order) 
                          (sim_match_states := fun i s1 s2 => f2b_match_states i s2 s1).
    apply wf_f2b_order.
    (* match observations *)
    symmetry; eapply f2b_match_observe; eauto.
    (* match final states *)
    intros; eapply f2b_match_final_states; eauto.
    (* match step *)
    intros; eapply f2b_simulation_step; eauto.
    intros. symmetry.
    eapply sim_match_observe; eauto.
exploit (sim_match_observe _ _ FS); eauto. intros [i [s2 [A B]]].
    exists s2; auto.
    (* initial states *)
    intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2' [A B]]].
    assert (s2 = s2') by (eapply sd_initial_determ; eauto). subst s2'.
    exists (F2BI_after O); exists s1; split; auto. econstructor; eauto.
    (* final states *)
    intros. inv H.
    exploit f2b_progress; eauto. intros TRANS; inv TRANS.
    assert (r0 = r) by (eapply (sd_final_determ L2_determinate); eauto). subst r0.
    exists s1'; auto.
    inv H4. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
    inv H5. congruence. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
    inv H2. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
    (* progress *)
    intros. inv H. 
    exploit f2b_progress; eauto. intros TRANS; inv TRANS. 
    left; exists r; auto. 
    inv H3. right; econstructor; econstructor; eauto.
    inv H4. congruence. right; econstructor; econstructor; eauto.
    inv H1. right; econstructor; econstructor; eauto.
    (* simulation *)
    exact f2b_simulation_step.
    (* symbols preserved *)
    exact (fsim_symbols_preserved FS).
  Qed.

End F2B.*)

Close Scope nat_scope.