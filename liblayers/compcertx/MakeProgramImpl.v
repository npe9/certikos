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
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.Decision.
Require Import liblayers.lib.Monad.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compcertx.StencilImpl.
Require liblayers.compcertx.InitMem.

(** Missing lemma from Globalenv *)

Module Genv.
Import Maps.
Export Globalenvs.Genv.

Section GENV.

  Context {F V: Type}.

  Lemma find_funct_ptr_find_symbol_aux:
    forall l2 ge l1,
      list_norepet (map fst (l1 ++ l2)) ->
      (forall i b, find_symbol (V := V) ge i = Some b -> In i (map fst l1)) ->
      (forall b f, find_funct_ptr ge b = Some f ->
       exists i, find_symbol ge i = Some b) ->
      forall b (f: F),
      find_funct_ptr (add_globals ge l2) b = Some f ->
      exists i, find_symbol (add_globals ge l2) i = Some b.
  Proof.
    induction l2; simpl; try tauto.
    intros until 3.
    eapply IHl2.
    * instantiate (1 := (l1 ++ a :: nil)).
      rewrite app_ass. assumption.
    * intros. rewrite map_app. simpl.
      apply in_or_app.
      revert H2. unfold find_symbol. simpl.
      rewrite PTree.gsspec.
      destruct (peq i (@fst positive _ a));
      subst; auto.
      left; eauto.
    * assert (P: forall b f, find_funct_ptr ge b = Some f ->
                        exists i, find_symbol (add_global ge a) i = Some b).
      {
        intros. exploit H1; eauto. destruct 1.
        exploit Genv.genv_symb_range; eauto.
        intro.
        unfold find_symbol. simpl.
        exists x.
        rewrite PTree.gso; auto.
        intro; subst.
        exploit H0; eauto.
        intro.        
        rewrite map_app in H.
        rewrite list_norepet_app in H.
        destruct H as (? & ? & K).
        unfold list_disjoint in K.
        eapply K; eauto.
        simpl; auto.
      }
      unfold find_funct_ptr, find_symbol. simpl.
      destruct a; simpl.
      destruct o; simpl; auto.
      destruct g; simpl; auto.
      intros ? ?.
      rewrite PTree.gsspec.
      destruct (peq b (genv_next ge)); eauto.
      inversion 1; subst.
      esplit. eapply PTree.gss.
  Qed.

  Theorem find_funct_ptr_find_symbol:
    forall p b (f: F),
      list_norepet (prog_defs_names (V := V) p) ->
      find_funct_ptr (globalenv p) b = Some f ->
      exists id,
        find_symbol (globalenv p) id = Some b.
  Proof.
    unfold globalenv. unfold prog_defs_names.
    intros.
    eapply find_funct_ptr_find_symbol_aux.
    * instantiate (1 := nil). eassumption.
    * unfold find_symbol. intros ? ?.
      rewrite PTree.gempty. discriminate.
    * unfold find_funct_ptr. intros ? ?.
      rewrite PTree.gempty. discriminate.
    * eassumption.
  Qed.

  Lemma find_var_info_find_symbol_aux:
    forall l2 ge l1,
      list_norepet (map fst (l1 ++ l2)) ->
      (forall i b, find_symbol (F := F) ge i = Some b -> In i (map fst l1)) ->
      (forall b v, find_var_info ge b = Some v ->
       exists i, find_symbol ge i = Some b) ->
      forall b (v: _ V),
      find_var_info (add_globals ge l2) b = Some v ->
      exists i, find_symbol (add_globals ge l2) i = Some b.
  Proof.
    induction l2; simpl; try tauto.
    intros until 3.
    eapply IHl2.
    * instantiate (1 := (l1 ++ a :: nil)).
      rewrite app_ass. assumption.
    * intros. rewrite map_app. simpl.
      apply in_or_app.
      revert H2. unfold find_symbol. simpl.
      rewrite PTree.gsspec.
      destruct (peq i (@fst positive _ a));
      subst; auto.
      left; eauto.
    * assert (P: forall b v, find_var_info ge b = Some v ->
                        exists i, find_symbol (add_global ge a) i = Some b).
      {
        intros. exploit H1; eauto. destruct 1.
        exploit Genv.genv_symb_range; eauto.
        intro.
        unfold find_symbol. simpl.
        exists x.
        rewrite PTree.gso; auto.
        intro; subst.
        exploit H0; eauto.
        intro.        
        rewrite map_app in H.
        rewrite list_norepet_app in H.
        destruct H as (? & ? & K).
        unfold list_disjoint in K.
        eapply K; eauto.
        simpl; auto.
      }
      unfold find_var_info, find_symbol. simpl.
      destruct a; simpl.
      destruct o; simpl; auto.
      destruct g; simpl; auto.
      intros ? ?.
      rewrite PTree.gsspec.
      destruct (peq b (genv_next ge)); eauto.
      inversion 1; subst.
      esplit. eapply PTree.gss.
  Qed.

  Theorem find_var_info_find_symbol:
    forall p b (v: _ V),
      list_norepet (prog_defs_names (F := F) p) ->
      find_var_info (globalenv p) b = Some v ->
      exists id,
        find_symbol (globalenv p) id = Some b.
  Proof.
    unfold globalenv. unfold prog_defs_names.
    intros.
    eapply find_var_info_find_symbol_aux.
    * instantiate (1 := nil). eassumption.
    * unfold find_symbol. intros ? ?.
      rewrite PTree.gempty. discriminate.
    * unfold find_var_info. intros ? ?.
      rewrite PTree.gempty. discriminate.
    * eassumption.
  Qed.

  Theorem find_var_info_symbol_inversion:
    forall p id b v,
      find_symbol (globalenv (F := F) (V := V) p) id = Some b ->
      find_var_info (globalenv p) b = Some v ->
      In (id, Some (Gvar v)) p.(prog_defs).
  Proof.
    intros until v. unfold globalenv, find_symbol, find_var_info. apply add_globals_preserves. 
    (* preserves *)
    intros. simpl in *. rewrite PTree.gsspec in H1. destruct (peq id id0). 
    inv H1. destruct g as [[f1|v1]|]. 
    eelim Plt_strict. eapply genv_vars_range; eauto.
    rewrite PTree.gss in H2. inv H2. auto.
    (** [CompCertX:test-compcert-void-symbols] case none *)
    eelim Plt_strict. eapply genv_vars_range; eauto.  
    destruct g as [[f1|v1]|].
    auto.
    rewrite PTree.gso in H2. auto.
    apply Plt_ne. eapply genv_symb_range; eauto.
    auto.
    (* initial *)
    intros. simpl in *. rewrite PTree.gempty in H. discriminate.
  Qed.

End GENV.

End Genv.

(** Missing lemma from PseudoJoin *)

(*
The following are OK, but useless since they do not apply to (res_le (option_le _)).

Lemma oplus_lb_eq_left `{PJ: PseudoJoin} `{HA: !Antisymmetric A eq (≤)}:
  forall x y, x ⊕ y = lb -> x = lb.
Proof.
  intros.
  apply antisymmetry.
   rewrite <- H. apply oplus_le_left.
  apply oplus_lower_bound.
Qed.

Lemma oplus_lb_eq_right `{PJ: PseudoJoin} `{HA: !Antisymmetric A eq (≤)}:
  forall x y, x ⊕ y = lb -> y = lb.
Proof.
  intros until y. rewrite oplus_comm. apply oplus_lb_eq_left.
Qed.
*)

Lemma oplus_lb_eq' {A: Type}:
  forall x y, x ⊕ y = OK None -> x = OK (None (A := A)) /\ y = OK None.
Proof.
  intros.
  destruct x; destruct y; try discriminate.
  destruct o; destruct o0; try discriminate.
  auto.
Qed.

Lemma oplus_id_left' {A: Type}:
  LeftIdentity eq (⊕) (OK (None (A := A))).
Proof.
  unfold LeftIdentity. intros.
  destruct y; try reflexivity.
  destruct o; reflexivity.
Qed.

Lemma oplus_id_right' {A: Type}:
  RightIdentity eq (⊕) (OK (None (A := A))).
Proof.
  unfold RightIdentity. intros.
  destruct x; try reflexivity.
  destruct o; reflexivity.
Qed.

Lemma oplus_one_left' {A: Type}:
  forall (a: A) x o,
    (OK (Some a)) ⊕ x = OK o ->
    x = OK None /\ o = Some a.
Proof.
  destruct x; try discriminate.
  destruct o; try discriminate.
  inversion 1; auto.
Qed.

(** Missing lemma and tactic from Decision. *)

  Lemma assert_ex P `{P_dec: Decision P}:
    P ->
    {y | forall msg, eassert msg P = OK y}.
  Proof.
    intros.
    unfold eassert.
    destruct (decide P); try contradiction.
    eauto.
  Defined.

  Ltac rewrite_assert H :=
    let y := fresh "y" in
    let Z := fresh "Z" in
    generalize (assert_ex _ H);
      intros [y Z];
      rewrite Z.    

  Ltac rewrite_assert' H HP :=
    let y := fresh "y" in
    let Z := fresh "Z" in
    generalize (assert_ex _ H (P_dec := HP));
      intros [y Z];
      rewrite Z.    

  Ltac autorewrite_assert :=
    match goal with
      | [ H : eassert ?msg ?P = OK ?x |- context [ eassert ?msg ?P ] ] =>
        rewrite H
      | [ H : ?P |- context [ eassert ?msg ?P (HP := ?HP) ] ] =>
        (rewrite_assert' H HP || rewrite_assert H)
    end.

  Ltac spawn_assert :=
    match goal with
      | [ |- context [ eassert ?msg ?P (HP := ?HP) ] ] =>
        cut P; [
            let Z := fresh "Z" in
            intro Z;
              (rewrite_assert' Z HP || rewrite_assert Z);
              clear Z
          | ]
    end.

  Definition globdef_volatile {F V} (g: globdef F V) :=
    match g with
      | Gfun _ => false
      | Gvar g => gvar_volatile g
    end.

  Definition option_globdef_volatile {F V} (g: option (globdef F V)) :=
    match g with
      | None => false
      | Some g => globdef_volatile g
    end.

(** * Implementation of [MakeProgram] *)

(** Below we construct [make_program] from the bottom up, first
  defining functions to produce individual definitions, then using
  them while enumerating the stencil to construct the actual
  program.

  Our proofs of [make_program]'s properties follow the same pattern:
  we first caracterize the components, then use those lemmas as we
  build things up. *)

Section WITHMAKEFUNDEFOPS.
  Context `{progfmt: ProgramFormat}.
  Context `{Hmodule: !Modules ident Fm (globvar Vm) module}.
  Context `{Hlayer: !Layers ident primsem (globvar Vm) layer}.

  (** ** Individual definitions *)

  (** We start with variable definitions. At the moment we reject
    volatile variables: constructing the program will fail if it
    contains any. *)

  Definition get_varinfo_globdef mτ: res (option (AST.globdef Fp Vp)) :=
    match mτ with
      | Some τ =>
          _ <- eassert (MSG "volatile variable"::nil) (gvar_volatile τ = false);
          ret (Some (Gvar (globvar_map make_varinfo τ)))
      | None =>
          OK None
    end.

  Instance get_varinfo_globdef_mon:
    Proper (option_le eq ++> res_le (option_le eq)) get_varinfo_globdef.
  Proof with eauto with liblayers.
    intros τ1 τ2 Hτ.
    destruct Hτ; simpl...
    subst; reflexivity.
  Qed.

  (** Emit internal function definitions from the code in modules. *)

  Definition get_function_globdef mκ: res (option (AST.globdef Fp Vp)) :=
    match mκ with
      | None => OK None
      | Some κ => κdef <- make_internal κ; OK (Some (Gfun κdef))
    end.

  Instance get_function_globdef_mon:
    Proper (option_le eq ++> res_le (option_le eq)) get_function_globdef.
  Proof.
    unfold get_function_globdef.
    intros ? ? [κ2 | κ1 κ2 Hκ].
    * apply lower_bound.
    * subst. reflexivity.
  Qed.

  (** Emit external function definitions from the specifications in layers. *)

  Definition get_primitive_globdef {D} i mσ: res (option (AST.globdef Fp Vp)):=
    match mσ with
      | None => OK None
      | Some σ => σdef <- make_external (D:=D) i σ; OK (Some (Gfun σdef))
    end.

  Instance get_primitive_globdef_mon D:
    Proper (- ==> option_le (≤) ++> res_le (option_le eq)) 
           (get_primitive_globdef (D := D)).
  Proof.
    unfold get_primitive_globdef.
    intros i ? ? [σ2 | σ1 σ2 Hσ].
    * apply lower_bound.
    * solve_monotonicity.
  Qed.

  Instance get_primitive_globdef_sim_mon:
    Proper
      (∀ R, - ==> sim R ++> res_le eq)
      (fun D => make_external (D := D)) ->
    Proper
      (∀ R, - ==> option_le (sim R) ++> res_le (option_le eq))
      (fun D => get_primitive_globdef (D := D)).
  Proof.
    intro make_external_sim_monotonic.
    unfold get_primitive_globdef.
    intros D1 D2 R i ? ? [σ2 | σ1 σ2 Hσ].
    * apply lower_bound.
    * solve_monotonicity.
  Qed.

  (** Now we can put all of those together and produce the [globdef]
    for a given symbol of a module/layer pair. It will fail if the
    symbol is overdefined. *)

  Definition get_globdef {D} (i: ident) (M: module) (L: layer D) :=
    (mf <- get_module_function i M; get_function_globdef mf) ⊕
    (mτ <- get_module_variable i M; get_varinfo_globdef mτ) ⊕
    (mσ <- get_layer_primitive i L; get_primitive_globdef i mσ) ⊕
    (mτ <- get_layer_globalvar i L; get_varinfo_globdef mτ).

  Global Instance get_globdef_monotonic D:
    Proper (- ==> (≤) ++> sim id ++> res_le (option_le eq)) (@get_globdef D).
  Proof.
    unfold get_globdef.
    solve_monotonicity.
  Qed.

  Global Instance get_globdef_sim_monotonic:
    Proper
      (∀ R, - ==> sim R ++> res_le eq)
      (fun D => make_external (D := D)) ->
    Proper (∀ R, - ==> (≤) ++> sim R ++> res_le (option_le eq)) (@get_globdef).
  Proof.
    unfold get_globdef.
    solve_monotonicity.
  Qed.

  Global Instance: Params (@get_globdef) 3%nat.

  (** ** [add_prog_defs] *)

  (** Now we want to build the program by iterating over the list of
    identifiers in the stencil, taking into account that we may fail
    at any point if the given layer and modules do not satisfy the
    required conditions.

    Note that in order to facilitate induction on [ids], we follow the
    same tail-recursive style as [Genv.add_globals]. *)

  Fixpoint add_prog_defs {D} (ids: list ident) (M: module) (L: layer D) defs:
    res (list (ident * option (globdef _ _))) :=
      match ids with
        | nil =>
            ret defs
        | i::ids =>
            def <- get_globdef i M L;
            add_prog_defs ids M L (defs ++ (i, def)::nil)
      end.

  Instance add_prog_defs_monotonic D l:
    Proper
      ((≤) ++> (≤) ++> prog_defs_le ++> res_le prog_defs_le)
      (add_prog_defs (D:=D) l).
  Proof.
    induction l; simpl.
    * solve_monotonicity.
    * solve_monotonicity.
  Qed.

  Instance add_prog_defs_sim_monotonic
           (make_external_sim_monotonic:
              Proper
                (∀ R, - ==> sim R ++> res_le eq)
                (fun D => make_external (D := D)))
           l:
    Proper
      (∀ R, (≤) ++> sim R ++> prog_defs_le ++> res_le prog_defs_le)
      (fun D => add_prog_defs (D:=D) l).
  Proof.
    induction l; simpl.
    * solve_monotonicity.
    * solve_monotonicity.
      eapply IHl; eauto.
      solve_monotonicity.
  Qed.

  Section ADD_PROG_DEFS.
    Context {D} (M: module) (L: layer D).

    Lemma add_prog_defs_append_intro ids1:
      forall ids2 defs defs1 defs2,
        add_prog_defs ids1 M L defs = ret defs1 ->
        add_prog_defs ids2 M L defs1 = ret defs2 ->
        add_prog_defs (ids1 ++ ids2) M L defs = ret defs2.
    Proof.
      induction ids1; simpl; intros ids2 defs defs1 defs2 H1 H2.
      * inv_monad H1.
        congruence.
      * inv_monad H1.
        rewrite H3.
        autorewrite with monad.
        eauto.
    Qed.

    Lemma add_prog_defs_append_elim ids1:
      forall ids2 defs defs2,
        add_prog_defs (ids1 ++ ids2) M L defs = ret defs2 ->
        exists defs1,
          add_prog_defs ids1 M L defs = ret defs1 /\
          add_prog_defs ids2 M L defs1 = ret defs2.
    Proof.
      induction ids1; simpl; intros ids2 defs defs2 H.
      * exists defs; eauto.
      * inv_monad H.
        rewrite H2.
        rewrite H1.
        autorewrite with monad.
        eapply IHids1.
        assumption.
    Qed.

    Lemma add_prog_defs_incl ids:
      forall defs defs',
        add_prog_defs ids M L defs = ret defs' ->
        List.incl defs defs'.
    Proof.
      induction ids as [ | i ids IHids];
        simpl;
        intros defs defs' Hdefs';
        inv_monad Hdefs'.
      * subst.
        now firstorder.
      * intros d Hd.
        eapply IHids; try eassumption.
        apply in_app; now auto.
    Qed.

    Lemma add_prog_defs_prefix_elim ids:
      forall defs0 defs1 defs012,
        add_prog_defs ids M L (defs0 ++ defs1) = ret defs012 ->
        exists defs12,
          defs012 = defs0 ++ defs12 /\
          add_prog_defs ids M L defs1 = ret defs12.
    Proof.
      induction ids; simpl;
      intros ? ? ? Hdefs'; inv_monad Hdefs'.
      * subst; eauto.
      * rewrite app_ass in H1.
        apply IHids in H1. destruct H1 as [defs12 [Hdefs12 Hadd]].
        subst.
        rewrite H0.
        autorewrite with monad.
        eauto.
    Qed.

    Lemma add_prog_defs_prefix_intro ids:
      forall defs0 defs defs',
        add_prog_defs ids M L defs = ret defs' ->
        add_prog_defs ids M L (defs0 ++ defs) = ret (defs0 ++ defs').
    Proof.
      induction ids; simpl; intros ? ? ? Hdefs'; inv_monad Hdefs'.
      * congruence.
      * rewrite H0. autorewrite with monad.
        rewrite app_ass. eauto.
    Qed.

    Lemma add_prog_defs_globdef_exists i ids defs defs':
      add_prog_defs ids M L defs = ret defs' ->
      In i ids ->
      exists d,
        get_globdef i M L = ret d /\
        In (i, d) defs'.
    Proof.
      revert i defs defs'.
      induction ids as [ | j ids IHids]; simpl; intros i defs defs'.
      * tauto.
      * intros Hdefs' Hin.
        inv_monad Hdefs'.
        destruct Hin as [Hij | Hin].
      + subst; clear IHids.
        exists x.
        split; try assumption.
        eapply add_prog_defs_incl.
        eassumption.
        apply in_app.
        simpl.
        tauto.
      + eauto.
    Qed.

    Lemma add_prog_defs_globdef_inversion ids defs defs' i d:
      add_prog_defs (D:=D) ids M L defs = ret defs' ->
      In (i, d) defs' ->
      In i ids \/ In (i, d) defs.
    Proof.
      revert defs defs'.
      induction ids as [ | j ids IHids]; simpl; intros defs defs' H; inv_monad H.
      * intuition congruence.
      * intros Hid.
        eapply IHids in Hid; eauto.
        rewrite in_app in Hid.
        simpl in Hid.
        intuition congruence.
    Qed.

    Lemma add_prog_defs_In_globdef ids i d:
      forall defs,
        add_prog_defs ids M L nil = ret defs ->
        In (i, d) defs ->
        get_globdef i M L = ret d.
    Proof.
      induction ids; simpl; intros defs Hdefs; inv_monad Hdefs.
      * subst. inversion 1.
      * apply (add_prog_defs_prefix_elim _ ((a, x) :: nil) nil) in H1.
        destruct H1 as [? [? ?]].
        subst.
        simpl.
        destruct 1.
        + congruence.
        + eauto.
    Qed.

    Lemma add_prog_defs_globdef_In i d ids:
      forall defs,
        get_globdef i M L = ret d ->
        add_prog_defs ids M L nil = ret defs ->
        In i ids ->
        In (i, d) defs.
    Proof.
      intros.
      exploit add_prog_defs_globdef_exists; eauto.
      destruct 1 as [? [Hget ?]].
      rewrite H in Hget.
      inv_monad Hget.
      congruence.
    Qed.

    Lemma map_add_prog_defs:
      forall l l1,
        map (fun i => (i, get_globdef (D := D) i M L)) l = map (fun is => match is with (i, d) => (i, OK d) end) l1 ->
        forall ld,
          add_prog_defs l M L ld = OK (ld ++ l1).
    Proof.
      induction l; destruct l1; try discriminate.
      intros. rewrite <- app_nil_end. reflexivity.
      intro J. inv J. intro.
      simpl.
      destruct p. inv H0.
      rewrite H3.
      monad_norm.
      erewrite IHl; eauto.
      rewrite app_ass.
      reflexivity.
    Qed.

    Lemma add_prog_defs_map:
      forall l ld l',
        add_prog_defs l M L ld = OK l' ->
        exists l1, l' = ld ++ l1 /\
                   map (fun i => (i, get_globdef (D := D) i M L)) l = map (fun is => match is with (i, d) => (i, OK d) end) l1.
    Proof.
      induction l; simpl; intros.
       inv H. exists nil. split.
        rewrite <- app_nil_end. reflexivity.
        reflexivity.
      inv_monad H.
      exploit IHl; eauto.
      destruct 1 as [? [Hl' Hmap]].
      rewrite app_ass in Hl'.
      simpl in Hl'.
      subst.
      rewrite Hmap.
      rewrite H2.
      eauto.
    Qed.

  End ADD_PROG_DEFS.

  (** ** Definition of [make_program] *)

  (** Once we've built the definitions, building the program is a
    simple matter. *)

  Definition valid_program {D} (s: stencil) (M: module) (L: layer D): Prop :=
    (forall i,
       ~ isOKNone (get_layer_primitive i L) -> In i (stencil_ids s)) /\
    (forall i,
       ~ isOKNone (get_layer_globalvar i L) -> In i (stencil_ids s)) /\
    (forall i,
       ~ isOKNone (get_module_function i M) -> In i (stencil_ids s)) /\
    (forall i,
       ~ isOKNone (get_module_variable i M) -> In i (stencil_ids s)).

  Ltac destruct_valid_program :=
    match goal with H : valid_program ?s ?M ?L |- _ =>
      let Hprim_γ := fresh "Hprim_γ" in
      let Hglob_γ := fresh "Hglob_γ" in
      let Hfun_γ := fresh "Hfun_γ" in
      let Hvar_γ := fresh "Hvar_γ" in
      destruct H as (Hprim_γ & Hglob_γ & Hfun_γ & Hvar_γ)
    end.

  Global Instance valid_program_monotonic D:
    Proper (- ==> (≤) --> (≤) --> impl) (valid_program (D:=D)).
  Proof.
    intros s M1 M2 HM L1 L2 HL.
    red in HM, HL.
    intros (Hs_prim & Hs_glob & Hs_func & Hs_var).
    repeat split; intros i H;
    repeat match goal with H: forall i:ident, _ |- _ => specialize (H i) end;
    rewrite <- HL, <- HM in *; eauto.
  Qed.

  Global Instance valid_program_sim_monotonic:
    Proper (∀ R, - ==> (≤) ++> sim R ++> flip impl) (fun D => valid_program (D:=D)).
  Proof.
    intros D1 D2 R s M1 M2 HM L1 L2 HL.
    red in HM, HL.
    intros (Hs_prim & Hs_glob & Hs_func & Hs_var).
    repeat split; intros i H;
    repeat match goal with H: forall i:ident, _ |- _ => specialize (H i) end;
    rewrite <- HM in *; eauto.
    * eapply Hs_prim. intro ABS. apply H. eapply isOKNone_le; eauto. unfold flip. eapply get_layer_primitive_sim_monotonic; eauto.
    * eapply Hs_glob. intro ABS. apply H. eapply isOKNone_le; eauto. unfold flip. eapply get_layer_globalvar_sim_monotonic; eauto.    
  Qed.

  Global Instance is_OK_None_dec {A} (x: res (option A)):
    Decision (x = OK None).
  Proof.
    destruct x as [[|]|];
    first [ left; abstract congruence | right; abstract congruence ].
  Defined.

  Global Instance valid_program_dec D s M L: Decision (@valid_program D s M L).
  Proof.
    typeclasses eauto.
  Defined.

  Definition make_program {D} s M (L: layer D): res (AST.program Fp Vp) :=
    Hvalid <- eassert nil (valid_program s M L);
    defs <- add_prog_defs (D:=D) (stencil_ids s) M L nil;
    ret {|
      prog_defs := defs;
      prog_main := xH (* dummy *)
    |}.

  Global Instance make_program_monotonic D:
    Proper (- ==> (≤) ++> (≤) ++> res_le program_le) (make_program (D:=D)).
  Proof.
    unfold make_program.
    intros s M1 M2 HM L1 L2 HL.
    solve_monotonic.
  Qed.

  Global Instance make_program_sim_monotonic:
    Proper
      (∀ R, - ==> sim R ++> res_le eq)
      (fun D => make_external (D := D)) ->
    Proper (∀ R, - ==> (≤) ++> sim R ++> res_le program_le) (fun D => make_program (D:=D)).
  Proof.
    unfold make_program.
    intros make_external_sim_monotonic D1 D2 R s M1 M2 HM L1 L2 HL.
    solve_monotonic.
    eapply add_prog_defs_sim_monotonic; eauto.
    constructor.
  Qed.

  Local Instance make_program_ops:
    MakeProgramOps Fm Vm Fp Vp :=
      {
        make_program := @make_program
      }.

  Lemma add_prog_defs_names {D} is M L defs defs':
    add_prog_defs (D:=D) is M L defs = ret defs' ->
    map fst defs' = (map fst defs) ++ is.
  Proof.
    revert defs.
    induction is as [ | i is IHis]; simpl; intros defs.
    * intros H; inv_monad H; subst.
      apply app_nil_end.
    * intros H; inv_monad H; subst.
      erewrite IHis; eauto.
      rewrite map_app.
      rewrite app_ass.
      reflexivity.
  Qed.

  Lemma make_program_names {D} γ M L p:
    make_program (D := D) γ M L = OK p ->
    prog_defs_names p = stencil_ids γ.
  Proof.
    unfold make_program.
    intro H. inv_monad H.
    subst.
    unfold prog_defs_names. simpl.
    erewrite add_prog_defs_names; eauto.
    reflexivity.
  Qed.

  Lemma make_program_names_norepet {D} γ M L p:
    make_program (D := D) γ M L = OK p ->
    list_norepet (prog_defs_names p).
  Proof.
    intros. erewrite make_program_names; eauto using stencil_ids_norepet.
  Qed.

  Lemma make_globalenv_find_symbol
        {D} s L M :
    forall ge,
      make_globalenv (D := D) s L M = OK ge ->
    forall i,
    Genv.find_symbol ge i =
    find_symbol s i.
  Proof.
    unfold make_globalenv.
    simpl. 
    unfold globalenv_of_stencil, program_of_stencil.
    unfold Genv.globalenv.
    simpl.
    intros.
    inv_monad H.
    unfold make_program in H2.
    inv_monad H2.
    subst.
    simpl.
    rewrite <- find_symbol_of_list_correct.
    rewrite <- find_symbol_of_list_correct.
    rewrite list_map_compose.
    simpl.
    unfold Genv.find_symbol; simpl.
    rewrite Maps.PTree.gempty.
    erewrite add_prog_defs_names; eauto.
    simpl.
    rewrite map_id.
    reflexivity.
  Qed.

  Remark advance_next_length_inv:
  forall {F1 V1 F2 V2} (l1: list (ident * option (globdef F1 V1))) (l2: list (ident * option (globdef F2 V2))) b,
    length l1 = length l2 ->
    Genv.advance_next l1 b = Genv.advance_next l2 b.
  Proof.
    induction l1; destruct l2; try discriminate.
     reflexivity.
    simpl. inversion 1; subst.
    exploit IHl1; eauto.
  Qed.

  Lemma make_globalenv_genv_next
        {D} s L M :
    forall ge,
      make_globalenv (D := D) s L M = OK ge ->
      Genv.genv_next ge = genv_next s.
  Proof.
    unfold make_globalenv.
    simpl. 
    unfold globalenv_of_stencil, program_of_stencil.
    unfold Genv.globalenv.
    simpl.
    intros.
    inv_monad H.
    unfold make_program in H2.
    inv_monad H2.
    subst.
    simpl.
    rewrite Genv.genv_next_add_globals.
    rewrite Genv.genv_next_add_globals.
    apply advance_next_length_inv.
    rewrite map_length.
    rewrite <- (map_length fst).
    erewrite add_prog_defs_names; eauto.
    reflexivity.
  Qed.

  Lemma get_globdef_not_volatile {D} M L i g:
    get_globdef (D := D) i M L = OK (Some (Gvar g)) ->
    gvar_volatile g = false.
  Proof.
    unfold get_globdef.
    destruct (get_module_function i M); try discriminate.
    monad_norm.
    unfold get_function_globdef.
    destruct o.
    {
     destruct (make_internal _); try discriminate.
     monad_norm.
     match goal with |- _ ⊕ ?x = _ -> _ => destruct x as [ [ | ] | ]; discriminate end.
    }
    monad_norm.
    destruct (get_module_variable i M); try discriminate.
    monad_norm.
    unfold get_varinfo_globdef at 1.
    destruct o. 
    {
      match goal with [ |- context [ eassert ?x ?y ] ] =>
                      destruct (eassert x y); try discriminate
      end.
      match goal with |- _ ⊕ _ ⊕ ?y ⊕ ?z = _ -> _ => destruct y as [ [ | ] | ]; destruct z as [ [ | ] | ]; try discriminate end.
      monad_norm. simpl. monad_norm. inversion 1; subst. assumption.      
    }
    destruct (get_layer_primitive i L); try discriminate.
    monad_norm.
    unfold get_primitive_globdef.
    destruct o.
    {
      destruct (make_external _ _); try discriminate.
      monad_norm.
      match goal with |- _ ⊕ _ ⊕ _ ⊕ ?x = _ -> _ => destruct x as [ [ | ] | ]; discriminate end.
    }
    destruct (get_layer_globalvar i L); try discriminate.
    simpl. monad_norm.
    destruct o; try discriminate.
    simpl. monad_norm.
    destruct 1. inv H. assumption.
  Qed.

  Lemma make_globalenv_not_volatile {D} s L M:
    forall ge,
      make_globalenv (D := D) s L M = ret ge ->
      forall b,
      Events.block_is_volatile ge b = false.
  Proof.
    unfold make_globalenv.
    simpl.
    unfold make_program.
    intros until 1.
    inv_monad H.
    subst.
    unfold Events.block_is_volatile.
    intro b.
    destruct (Genv.find_var_info (Genv.globalenv _) b) eqn:?; try reflexivity.
    exploit Genv.find_var_info_inversion; eauto.
    destruct 1.
    simpl in H.
    eauto using add_prog_defs_In_globdef, get_globdef_not_volatile.
  Qed.

  Lemma make_globalenv_matches
        {D} s L M:
    forall ge,
      make_globalenv (D := D) s L M = ret ge ->
    stencil_matches s ge.
  Proof.
    constructor.
    eapply make_globalenv_find_symbol; eauto.
    eapply make_globalenv_genv_next; eauto.
    eapply make_globalenv_not_volatile; eauto.
  Qed.

  Lemma make_program_In_globdef_exists {D} i γ M L p:
    make_program (D:=D) γ M L = OK p ->
    (valid_program γ M L -> In i (stencil_ids γ)) ->
    exists def, get_globdef i M L = OK def /\ In (i, def) (prog_defs p).
  Proof.
    unfold make_program.
    intros Hmkp; inv_monad Hmkp; subst.
    intros Hiγ.
    eapply add_prog_defs_globdef_exists; eauto.
  Qed.

  Ltac exploit_make_program_at i :=
    lazymatch goal with
      H: make_program ?γ ?M ?L = ?ret ?p |- _ =>
        destruct (make_program_In_globdef_exists i γ M L p H) as [d [Hgd Hpd]];
        [
          intro; destruct_valid_program;
          match goal with H: forall i:ident, _ -> In i _ |- _ =>
            apply H;
            get_layer_normalize;
            get_module_normalize;
            discriminate
          end
        |
          unfold get_globdef in Hgd;
          get_layer_normalize_in Hgd;
          get_module_normalize_in Hgd;
          unfold
            get_function_globdef,
            get_varinfo_globdef,
            get_primitive_globdef in Hgd;
          monad_norm;
          rewrite ?id_left, ?id_right in Hgd;
          inv_monad Hgd; subst;
          pose proof (make_program_names_norepet γ M L p H)
        ]
    end.

  (** Properties needed for init_mem *)

  Section INITMEM.

    Context {D1 D2} (L1: layer D1) (L2: layer D2)
            (M1 M2: module).

    Hypotheses
      (function_domains:
         forall i,
           (~ isOKNone (get_layer_primitive i L1) \/ ~ isOKNone (get_module_function i M1)) ->
           (~ isOKNone (get_layer_primitive i L2) \/ ~ isOKNone (get_module_function i M2)))
      (variable_domains:
         forall i v,
           (get_layer_globalvar i L1 = OK (Some v) \/ get_module_variable i M1 = OK (Some v)) ->
           (get_layer_globalvar i L2 = OK (Some v) \/ get_module_variable i M2 = OK (Some v)))
    .

    Lemma get_globdef_init_mem_le i d1 d2:
      get_globdef i M1 L1 = OK d1 ->
      get_globdef i M2 L2 = OK d2 ->
      option_le (InitMem.def_le) d1 d2.
    Proof.
      unfold get_globdef.
      destruct (get_module_function i M1) eqn:FUN; try discriminate.
      destruct o.
      {
        monad_norm.
        unfold get_function_globdef at 1.
        destruct (make_internal f); try discriminate.
        monad_norm.
        intro J.
        apply oplus_one_left' in J.
        destruct J; subst.
        exploit (function_domains i).
        {
          rewrite FUN. unfold isOKNone. right; congruence.
        }
        destruct (get_module_function i M2); try discriminate.
        destruct o.
        {
          intros _.
          monad_norm.
          unfold get_function_globdef.
          destruct (make_internal f1); try discriminate.
          monad_norm.
          intro J.
          apply oplus_one_left' in J.
          destruct J; subst.
          constructor. constructor. auto.
        }
        monad_norm. unfold get_function_globdef.
        rewrite oplus_id_left'.
        destruct (
            mτ <- get_module_variable i M2; get_varinfo_globdef mτ
          ); try discriminate.
        destruct o.
        {
          intros J K.
          exfalso.
          apply oplus_one_left' in K.
          destruct K as (K & _).
          apply oplus_lb_eq' in K.
          destruct K as (K & _).
          inv_monad K.
          unfold get_primitive_globdef in H2.
          destruct x.
          { inv_monad H2. discriminate. }
          rewrite H1 in J.
          unfold isOKNone in J.
          unfold ret in J; simpl in J.
          destruct J; simpl; congruence.
        }
        rewrite oplus_id_left'.
        destruct (get_layer_primitive i L2); try discriminate.
        destruct o.
        {
          monad_norm.
          unfold get_primitive_globdef.
          destruct (make_external i p); try discriminate.
          monad_norm.
          intros _ J.
          apply oplus_one_left' in J.
          destruct J; subst.
          constructor. constructor. auto.
        }
        unfold isOKNone. destruct 1; exfalso; congruence.
      }
      monad_norm.
      unfold get_function_globdef at 1.
      rewrite oplus_id_left'.
      destruct (get_module_variable i M1) eqn:VAR; try discriminate.
      destruct o.
      {
        monad_norm.
        generalize (eq_refl (get_varinfo_globdef (Some g))).
        unfold get_varinfo_globdef at 2 3.
        unfold eassert.
        destruct (decide (gvar_volatile g = false)); try discriminate.
        monad_norm.
        intro VARINFO.
        intro J.
        apply oplus_one_left' in J.
        destruct J; subst.
        exploit (variable_domains i).
        {
          rewrite VAR. eauto.
        }
        destruct 1 as [VAR2 | VAR2].
        {
          rewrite VAR2.
          monad_norm.
          rewrite VARINFO.
          destruct ( mf <- get_module_function i M2; get_function_globdef mf
            ) as [ [ | ] | ];
            destruct ( mτ <- get_module_variable i M2; get_varinfo_globdef mτ
              ) as [ [ | ] | ];
            destruct ( mσ <- get_layer_primitive i L2; get_primitive_globdef i mσ
              ) as [ [ | ] | ];
            try discriminate.
          inversion 1; subst.
          repeat constructor.
        }
        rewrite VAR2.
        monad_norm.
        rewrite VARINFO.
          destruct ( mf <- get_module_function i M2; get_function_globdef mf
            ) as [ [ | ] | ];
            destruct ( mσ <- get_layer_primitive i L2; get_primitive_globdef i mσ
              ) as [ [ | ] | ];
            destruct ( mτ <- get_layer_globalvar i L2; get_varinfo_globdef mτ
              ) as [ [ | ] | ];
            try discriminate.
        inversion 1; subst.
        repeat constructor.
      }
      monad_norm. unfold get_varinfo_globdef at 1.
      rewrite oplus_id_left'.
      destruct (get_layer_primitive i L1) eqn:PRIM; try discriminate.
      destruct o.
      {
        monad_norm.
        unfold get_primitive_globdef at 1.
        destruct (make_external i p); try discriminate.
        monad_norm.
        intro J.
        apply oplus_one_left' in J.
        destruct J; subst.
        exploit (function_domains i).
        { rewrite PRIM. unfold isOKNone. left; congruence. }
        destruct (get_module_function i M2); try discriminate.
        destruct o.
        {
          intros _.
          monad_norm.
          unfold get_function_globdef.
          destruct (make_internal f0); try discriminate.
          monad_norm.
          intro J.
          apply oplus_one_left' in J.
          destruct J; subst.
          repeat constructor.
        }
        monad_norm.
        unfold get_function_globdef.
        rewrite oplus_id_left'.
        destruct (get_layer_primitive i L2).
        {
          destruct o.
          {
            intros _.
            monad_norm.
            unfold get_primitive_globdef.
            destruct (make_external i p0);
              destruct (  mτ <- get_module_variable i M2; get_varinfo_globdef mτ
                )  as [ [ | ] | ];
            destruct ( mτ <- get_layer_globalvar i L2; get_varinfo_globdef mτ
              ) as [ [ | ] | ];
            try discriminate.
            inversion 1; subst.
            repeat constructor.
          }
          unfold isOKNone. destruct 1; congruence.
        }
        destruct (  mτ <- get_module_variable i M2; get_varinfo_globdef mτ
                 )  as [ [ | ] | ];
          destruct ( mτ <- get_layer_globalvar i L2; get_varinfo_globdef mτ
                   ) as [ [ | ] | ];
          discriminate.
      }
      monad_norm.
      unfold get_primitive_globdef at 1.
      rewrite oplus_id_left'.
      intro J.
      inv_monad J.
      destruct x.
      {
        generalize H1.
        intro VARINFO.
        inv_monad H1.
        inv_monad H2.
        subst.
        exploit (variable_domains i).
        { rewrite H0. left; reflexivity. }
        destruct 1 as [VAR2 | VAR2].
        {
          rewrite VAR2. monad_norm. rewrite VARINFO.
          destruct ( mf <- get_module_function i M2; get_function_globdef mf
            ) as [ [ | ] | ];
            destruct ( mτ <- get_module_variable i M2; get_varinfo_globdef mτ
              ) as [ [ | ] | ];
            destruct ( mσ <- get_layer_primitive i L2; get_primitive_globdef i mσ
              ) as [ [ | ] | ];
            try discriminate.
          inversion 1; subst.
          repeat constructor.
        }
        rewrite VAR2. monad_norm. rewrite VARINFO.
        destruct ( mf <- get_module_function i M2; get_function_globdef mf
                 ) as [ [ | ] | ];
          destruct ( mτ <- get_layer_globalvar i L2; get_varinfo_globdef mτ
                   ) as [ [ | ] | ];
          destruct ( mσ <- get_layer_primitive i L2; get_primitive_globdef i mσ
                   ) as [ [ | ] | ];
          try discriminate.
        inversion 1; subst.
        repeat constructor.
      }
      inv H1.
      constructor.
    Qed.

    Lemma add_prog_defs_init_mem_le l:
      forall defs1 defs2,
        InitMem.prog_defs_le defs1 defs2 ->
        forall res1,
          add_prog_defs l M1 L1 defs1 = OK res1 ->
          forall res2,
            add_prog_defs l M2 L2 defs2 = OK res2 ->
            InitMem.prog_defs_le res1 res2.
    Proof.
      induction l; simpl.
      * inversion 2; subst. inversion 1; subst. assumption.
      * intros.
        inv_monad H0.
        inv_monad H1.
        eapply IHl; [ | eassumption | eassumption ].
        apply app_rel; auto.
        repeat constructor.
        eauto using get_globdef_init_mem_le.
    Qed.

    Lemma make_program_defs_init_mem_le s p1 p2:
      make_program s M1 L1 = OK p1 ->
      make_program s M2 L2 = OK p2 ->
      InitMem.prog_defs_le (prog_defs p1) (prog_defs p2).
    Proof.
      unfold make_program.
      intros P1 P2.
      inv_monad P1. inv_monad P2.
      subst. simpl.
      eapply add_prog_defs_init_mem_le; eauto.
      constructor.
    Qed.
    
  End INITMEM.

  (** LayerOK and ModuleOK *)

  Lemma make_program_layer_ok {D} s M L:
    isOK (make_program (D := D) s M L) ->
    LayerOK L.
  Proof.
    unfold LayerOK, isOK, make_program.
    destruct 1.
    inv_monad H.
    subst.
    destruct_valid_program.
    intro i.
    assert (HpOK: isOK (get_layer_primitive i L)).
    {
      destruct (get_layer_primitive i L) eqn:PRIM; eauto.
      exfalso.
      generalize (Hprim_γ i).
      rewrite PRIM.
      unfold isOKNone.
      intro K.
      exploit K; [ congruence | ].
      intro IN.
      exploit @add_prog_defs_globdef_exists; eauto.
      unfold get_globdef.
      rewrite PRIM.
      monad_norm.
      destruct 1 as (? & J & _).
      destruct (
          mf <- get_module_function i M; get_function_globdef mf
        );
        destruct (mτ <- get_module_variable i M; get_varinfo_globdef mτ); discriminate.
    }
    assert (HvOK: isOK (get_layer_globalvar i L)).
    {
      destruct (get_layer_globalvar i L) eqn:VAR; eauto.
      exfalso.
      generalize (Hglob_γ i).
      rewrite VAR.
      unfold isOKNone.
      intro K.
      exploit K; [ congruence | ].
      intro IN.
      exploit @add_prog_defs_globdef_exists; eauto.
      unfold get_globdef.
      rewrite VAR.
      monad_norm.
      destruct 1 as (? & J & _).
      destruct (
          mf <- get_module_function i M; get_function_globdef mf
        );
        destruct (mτ <- get_module_variable i M; get_varinfo_globdef mτ);
        destruct (mσ <- get_layer_primitive i L; get_primitive_globdef i mσ);
        discriminate.
    }
    split; eauto.
    {
      destruct HpOK as [[σ|] Hσ]; eauto.
      destruct HvOK as [[τ|] Hτ]; eauto.
      exfalso.
      assert (Hsi: In i (stencil_ids s)) by (apply Hprim_γ; congruence).
      exploit @add_prog_defs_globdef_exists; eauto.
      intros (d & Hd & _).
      revert Hd.
      unfold get_globdef.
      rewrite Hσ, Hτ.
      monad_norm.
      simpl.
      destruct (mf <- get_module_function i M; get_function_globdef mf);
        try discriminate.
      destruct (mτ <- get_module_variable i M; get_varinfo_globdef mτ);
        try discriminate.
      destruct (make_external i σ);
        try discriminate.
      monad_norm.
      intros [_].
      discriminate.
    }
  Qed.

  Lemma make_program_module_ok {D} s M L:
    isOK (make_program (D := D) s M L) ->
    ModuleOK M.
  Proof.
    unfold ModuleOK, isOK, make_program.
    destruct 1.
    inv_monad H.
    subst.
    destruct_valid_program.
    intro i.
    assert (Hf: isOK (get_module_function i M)).
    {
      destruct (get_module_function i M) eqn:FUN; eauto.
      exfalso.
      generalize (Hfun_γ i).
      rewrite FUN.
      unfold isOKNone.
      intro K.
      exploit K; [ congruence | ].
      intro IN.
      exploit @add_prog_defs_globdef_exists; eauto.
      unfold get_globdef.
      rewrite FUN.
      monad_norm.
      destruct 1 as (? & J & _).
      discriminate.
    }
    assert (Hv: isOK (get_module_variable i M)).
    {
      destruct (get_module_variable i M) eqn:VAR; eauto.
      exfalso.
      generalize (Hvar_γ i).
      rewrite VAR.
      unfold isOKNone.
      intro K.
      exploit K; [ congruence | ].
      intro IN.
      exploit @add_prog_defs_globdef_exists; eauto.
      unfold get_globdef.
      rewrite VAR.
      monad_norm.
      destruct 1 as (? & J & _).
      destruct (
          mf <- get_module_function i M; get_function_globdef mf
        );
        discriminate.
    }    
    split; eauto.
    {
      destruct Hf as [[κ|] Hκ]; eauto.
      destruct Hv as [[τ|] Hτ]; eauto.
      exfalso.
      assert (Hsi: In i (stencil_ids s)) by (apply Hfun_γ; congruence).
      exploit @add_prog_defs_globdef_exists; eauto.
      intros (d & Hd & _).
      revert Hd.
      unfold get_globdef.
      rewrite Hκ, Hτ.
      monad_norm.
      simpl.
      destruct (make_internal κ); try discriminate.
      monad_norm.
      intros [_].
      destruct (get_layer_primitive i L); try discriminate; monad_norm.
      destruct (get_primitive_globdef i o); try discriminate; monad_norm.
      destruct (get_layer_globalvar i L); try discriminate; monad_norm.
      destruct (get_varinfo_globdef _); try discriminate; monad_norm.
      destruct (_ o2); try discriminate; monad_norm.
      destruct o3; try discriminate.
    }
  Qed.

  Require Import Semantics.

  Lemma make_program_module_layer_disjoint {D} s M L:
    isOK (make_program (D:=D) s M L) ->
    module_layer_disjoint M L.
  Proof.
    unfold make_program.
    intros [p Hp] i.
    inv_monad Hp.
    subst.
    destruct_valid_program.
    destruct (decide (In i (stencil_ids s))) as [Hi | Hi].
    * eapply add_prog_defs_globdef_exists in Hi; try eassumption.
      destruct Hi as (d & Hd & Hid).
      unfold get_globdef in Hd.
      destruct (_ <- get_module_function _ _; _) as [[|]|] eqn:H; inv_monad H;
      destruct (_ <- get_module_variable _ _; _) as [[|]|] eqn:H; inv_monad H;
      destruct (_ <- get_layer_primitive _ _; _) as [[|]|] eqn:H; inv_monad H;
      destruct (_ <- get_layer_globalvar _ _; _) as [[|]|] eqn:H; inv_monad H;
      try discriminate;
      repeat match goal with
               | H: ?x = ?y |- context [?x] => rewrite H; clear H
             end;
      try (right;
           destruct x2, x3; try discriminate;
           simpl in *; unfold eassert in *;
           try destruct (make_external _ _); try discriminate;
           try destruct (decide (gvar_volatile _ = _)); try discriminate;
           now repeat constructor);
      try (left;
           destruct x, x1; try discriminate;
           simpl in *; unfold eassert in *;
           try destruct (make_internal _); try discriminate;
           try destruct (decide (gvar_volatile _ = _)); try discriminate;
           now repeat constructor).
    * left.
      split.
      + destruct (decide (isOKNone (get_module_function i M))).
        - assumption.
        - elim Hi; eauto.
      + destruct (decide (isOKNone (get_module_variable i M))).
        - assumption.
        - elim Hi; eauto.
  Qed.

  (** "Domains" *)

  Lemma make_program_get_module_function_prop {D} s M L i f:
    isOK (make_program (D := D) s M L) ->
    get_module_function i M = OK (Some f) ->
    isOK (make_internal f) /\
    isOKNone (get_layer_primitive i L) /\
    isOKNone (get_layer_globalvar i L).
  Proof.
    unfold make_program.
    destruct 1 as (? & MKP).
    inv_monad MKP.
    subst.
    intro MOD.
    destruct_valid_program.
    generalize (Hfun_γ i).
    rewrite MOD.
    intro K.
    exploit K; [ discriminate | ].
    intro IN.
    exploit @add_prog_defs_globdef_exists; eauto.
    destruct 1 as (? & GLOBDEF & ?).
    revert GLOBDEF.
    unfold get_globdef. rewrite MOD.
    monad_norm.
    unfold get_function_globdef.
    destruct (make_internal f); try discriminate.
    monad_norm.
    intro GLOBDEF.
    apply oplus_one_left' in GLOBDEF.
    destruct GLOBDEF as (J & _).
    apply oplus_lb_eq' in J.
    destruct J as (_ & J).
    apply oplus_lb_eq' in J.
    destruct J as (PRIM & VAR).
    unfold get_primitive_globdef in PRIM.
    unfold get_varinfo_globdef in VAR.
    inv_monad PRIM.
    destruct x0.
    {
      inv_monad H4. discriminate.
    }
    rewrite H3.
    inv_monad VAR.
    destruct x0.
    {
      inv_monad H6. discriminate.
    }
    unfold get_primitive_globdef in H4.
    rewrite H5.
    unfold isOK, isOKNone. eauto.
  Qed.

  Lemma make_program_get_module_variable_prop {D} s M L i v:
    isOK (make_program (D := D) s M L) ->
    get_module_variable i M = OK (Some v) ->
    gvar_volatile v = false /\
    isOKNone (get_layer_primitive i L) /\
    isOKNone (get_layer_globalvar i L).
  Proof.
    unfold make_program.
    destruct 1 as (? & MKP).
    inv_monad MKP.
    subst.
    intro MOD.
    destruct_valid_program.
    generalize (Hvar_γ i).
    rewrite MOD.
    intro K.
    exploit K; [ discriminate | ].
    intro IN.
    exploit @add_prog_defs_globdef_exists; eauto.
    destruct 1 as (? & GLOBDEF & ?).
    revert GLOBDEF.
    unfold get_globdef. rewrite MOD.
    monad_norm.
    destruct (mf <- get_module_function i M; get_function_globdef mf); try discriminate.
    destruct o.
    {
      intro J.
      apply oplus_one_left' in J.
      destruct J as (J & _).
      apply oplus_lb_eq' in J.
      destruct J as (J & _).
      unfold get_varinfo_globdef in J.
      inv_monad J.
      discriminate.
    }
    rewrite oplus_id_left'.
    unfold get_varinfo_globdef at 1.
    unfold eassert.
    destruct (decide (gvar_volatile v = false)); try discriminate.
    monad_norm.
    intro J.
    apply oplus_one_left' in J.
    destruct J as (J & ?); subst.
    apply oplus_lb_eq' in J.
    unfold get_primitive_globdef, get_varinfo_globdef in J.
    destruct J as (J1 & J2).
    inv_monad J1.
    destruct x.
    {
      inv_monad H4. discriminate.
    }
    inv_monad J2.
    destruct x.
    {
      inv_monad H6.
      discriminate.
    }
    rewrite H3.
    rewrite H5.
    unfold isOK, isOKNone. eauto.
  Qed.

  Lemma make_program_get_layer_primitive_prop {D} s M L i f:
    isOK (make_program (D := D) s M L) ->
    get_layer_primitive i L = OK (Some f) ->
    isOK (make_external i f) /\
    isOKNone (get_module_function i M) /\
    isOKNone (get_module_variable i M).
  Proof.
    unfold make_program.
    destruct 1 as (? & MKP).
    inv_monad MKP.
    subst.
    intro LAY.
    destruct_valid_program.
    generalize (Hprim_γ i).
    rewrite LAY.
    intro K.
    exploit K; [ discriminate | ].
    intro IN.
    exploit @add_prog_defs_globdef_exists; eauto.
    destruct 1 as (? & GLOBDEF & ?).
    revert GLOBDEF.
    unfold get_globdef. rewrite LAY.
    monad_norm.
    destruct (get_module_function i M); try discriminate.
    destruct o.
    {
      monad_norm.
      unfold get_function_globdef.
      destruct (make_internal f0); try discriminate.
      monad_norm.
      intro J.
      apply oplus_one_left' in J.
      destruct J as (J & _).
      apply oplus_lb_eq' in J.
      destruct J as (_ & J).
      apply oplus_lb_eq' in J.
      destruct J as (J & _).
      unfold get_primitive_globdef in J.      
      inv_monad J.
      discriminate.
    }
    monad_norm.
    unfold get_function_globdef.
    rewrite oplus_id_left'.
    destruct (get_module_variable i M); try discriminate.
    destruct o.
    {
      monad_norm.
      unfold get_varinfo_globdef at 1.
      unfold eassert.
      destruct (decide (gvar_volatile g = false)); try discriminate.
      monad_norm.
      intro J.
      apply oplus_one_left' in J.
      destruct J as (J & _).
      apply oplus_lb_eq' in J.
      destruct J as (J & _).
      unfold get_primitive_globdef in J.      
      inv_monad J.
      discriminate.
    }
    monad_norm.
    unfold get_varinfo_globdef at 1.
    rewrite oplus_id_left'.
    unfold get_primitive_globdef at 1.
    destruct (make_external i f); try discriminate.
    monad_norm.
    intro J.
    unfold isOK, isOKNone; eauto.
  Qed.

  Lemma make_program_get_layer_globalvar_prop {D} s M L i v:
    isOK (make_program (D := D) s M L) ->
    get_layer_globalvar i L = OK (Some v) ->
    gvar_volatile v = false /\
    isOKNone (get_module_function i M) /\
    isOKNone (get_module_variable i M).
  Proof.
    unfold make_program.
    destruct 1 as (? & MKP).
    inv_monad MKP.
    subst.
    intro LAY.
    destruct_valid_program.
    generalize (Hglob_γ i).
    rewrite LAY.
    intro K.
    exploit K; [ discriminate | ].
    intro IN.
    exploit @add_prog_defs_globdef_exists; eauto.
    destruct 1 as (? & GLOBDEF & ?).
    revert GLOBDEF.
    unfold get_globdef. rewrite LAY.
    monad_norm.
    destruct (get_module_function i M); try discriminate.
    destruct o.
    {
      monad_norm.
      unfold get_function_globdef.
      destruct (make_internal f); try discriminate.
      monad_norm.
      intro J.
      apply oplus_one_left' in J.
      destruct J as (J & _).
      apply oplus_lb_eq' in J.
      destruct J as (_ & J).
      apply oplus_lb_eq' in J.
      destruct J as (_ & J).
      unfold get_varinfo_globdef in J.      
      inv_monad J.
      discriminate.
    }
    monad_norm.
    unfold get_function_globdef.
    rewrite oplus_id_left'.
    destruct (get_module_variable i M); try discriminate.
    destruct o.
    {
      monad_norm.
      unfold get_varinfo_globdef at 1.
      unfold eassert.
      destruct (decide (gvar_volatile g = false)); try discriminate.
      monad_norm.
      intro J.
      apply oplus_one_left' in J.
      destruct J as (J & _).
      apply oplus_lb_eq' in J.
      destruct J as (_ & J).
      unfold get_varinfo_globdef in J.      
      inv_monad J.
      discriminate.
    }
    monad_norm.
    unfold get_varinfo_globdef at 1.
    rewrite oplus_id_left'.
    destruct (mσ <- get_layer_primitive i L; get_primitive_globdef i mσ); try discriminate.
    destruct o.
    {
      unfold get_varinfo_globdef.
      intro J.
      apply oplus_one_left' in J.
      destruct J as (J & _).
      inv_monad J.
      discriminate.
    }
    rewrite oplus_id_left'.
    unfold get_varinfo_globdef.
    intro J.
    inv_monad J.
    subst.
    unfold isOKNone; eauto.
  Qed.

  Lemma make_program_gfun {D} s M L p i f :
    make_program (D := D) s M L = OK p ->
    In (i, Some (Gfun f)) (prog_defs p) ->
    (exists fi,
       get_module_function i M = OK (Some fi) /\
       make_internal fi = OK f) \/
    (exists fe,
       get_layer_primitive i L = OK (Some fe) /\
       make_external i fe = OK f).
  Proof.
    unfold make_program.
    intro MAKE. intros.
    inv_monad MAKE.
    subst.
    exploit (add_prog_defs_In_globdef (D := D)); eauto.
    unfold get_globdef.
    destruct (get_module_function i M) as [ [ fi | ] | ] eqn:HMOD; try discriminate.
    {
      monad_norm. unfold get_function_globdef.
      destruct (make_internal fi) eqn:?; try discriminate.
      monad_norm.
      intro J. apply oplus_one_left' in J.
      destruct J as (REM & J). inv J.
      apply oplus_lb_eq' in REM.
      destruct REM as (_ & REM).
      apply oplus_lb_eq' in REM.
      destruct REM as (REM & _).
      inv_monad REM.
      unfold get_primitive_globdef in H4.
      destruct x1.
      {
        inv_monad H4. discriminate.
      }
      eauto.
    }
    monad_norm. unfold get_function_globdef.
    rewrite oplus_id_left'.
    destruct (get_module_variable i M) as [ [ | ] | ]; try discriminate.
    {
      monad_norm. unfold get_varinfo_globdef at 1.
      unfold eassert. destruct (decide (gvar_volatile g = false)); try discriminate.
      monad_norm. intro J. apply oplus_one_left' in J.
      destruct J; discriminate.
    }
    monad_norm. unfold get_varinfo_globdef at 1.
    rewrite oplus_id_left'.
    destruct (get_layer_primitive i L) as [ [ fe | ] | ] eqn:HLAY; try discriminate.
    {
      monad_norm. unfold get_primitive_globdef.
      destruct (make_external i fe) eqn:?; try discriminate.
      monad_norm.
      intro J. apply oplus_one_left' in J.
      destruct J as (REM & J). inv J.
      eauto.
    }
    monad_norm. unfold get_primitive_globdef.
    rewrite oplus_id_left'.
    unfold get_varinfo_globdef.
    intro J. inv_monad J.
    destruct x1; try discriminate.
    inv_monad H4. discriminate.
  Qed.

  Lemma make_globalenv_find_funct_ptr {D} s M L ge b f :
    make_globalenv (D := D) s M L = OK ge ->
    Genv.find_funct_ptr ge b = Some f ->
    exists i,
      Genv.find_symbol ge i = Some b /\
      (
        (exists fi,
           get_module_function i M = OK (Some fi) /\
           make_internal fi = OK f) \/
        (exists fe,
           get_layer_primitive i L = OK (Some fe) /\
           make_external i fe = OK f)
      ).
  Proof.
    unfold make_globalenv. simpl. intro MGE.
    inv_monad MGE.
    intros. subst.
    exploit @Genv.find_funct_ptr_find_symbol; eauto using make_program_names_norepet.
    destruct 1.
    exploit Genv.find_funct_ptr_symbol_inversion; eauto.
    intros.
    eauto using make_program_gfun.
  Qed.

  (* The following weak versions are no longer needed.
  Lemma make_globalenv_find_funct_ptr_weak {D} s M L ge i b f :
    make_globalenv (D := D) s M L = OK ge ->
    Genv.find_funct_ptr ge b = Some f ->
    Genv.find_symbol ge i = Some b ->
      (
        (exists fi,
           get_module_function i M = OK (Some fi) /\
           make_internal fi = OK f) \/
        (exists fe,
           get_layer_primitive i L = OK (Some fe) /\
           make_external i fe = OK f)
      ).
  Proof.
    intros.
    exploit @make_globalenv_find_funct_ptr; eauto.
    destruct 1 as (? & ? & ?).
    replace i with x in * by eauto using Genv.genv_vars_inj.
    assumption.
  Qed.

  (** TODO: move this lemma elsewhere *)
  Lemma make_globalenv_find_funct_ptr_very_weak {D} s M L ge b f :
        make_globalenv (D := D) s M L = OK ge ->
        Genv.find_funct_ptr ge b = Some f ->
        (exists i fi,
           get_module_function i M = OK (Some fi) /\
           make_internal fi = OK f) \/
        (exists i fe,
           get_layer_primitive i L = OK (Some fe) /\
           make_external i fe = OK f).
  Proof.
    intros.
    exploit @make_globalenv_find_funct_ptr; eauto.
    destruct 1 as (? & ? & [(? & ? & ?) | (? & ? & ?)] );
      eauto.
  Qed.    
*)

  Lemma make_program_gvar {D} s M L p i v :
    make_program (D := D) s M L = OK p ->
    In (i, Some (Gvar v)) (prog_defs p) ->
    exists vi,
      globvar_map make_varinfo vi = v /\
      (
        get_module_variable i M = OK (Some vi) \/
        get_layer_globalvar i L = OK (Some vi)
      ).
  Proof.
    unfold make_program.
    intro MAKE. intros.
    inv_monad MAKE.
    subst.
    exploit (add_prog_defs_In_globdef (D := D)); eauto.
    unfold get_globdef.
    destruct (get_module_function i M) as [ [ fi | ] | ] eqn:HMOD; try discriminate.
    {
      monad_norm. unfold get_function_globdef.
      destruct (make_internal fi) eqn:?; try discriminate.
      monad_norm.
      intro J. apply oplus_one_left' in J.
      destruct J as (REM & J). inv J.
    }
    monad_norm. unfold get_function_globdef.
    rewrite oplus_id_left'.
    destruct (get_module_variable i M) as [ [ | ] | ]; try discriminate.
    {
      monad_norm. unfold get_varinfo_globdef at 1.
      unfold eassert. destruct (decide (gvar_volatile g = false)); try discriminate.
      monad_norm. intro J. apply oplus_one_left' in J.
      destruct J as (REM & J). inv J.
      apply oplus_lb_eq' in REM.
      destruct REM as (_ & REM).
      inv_monad REM.
      unfold get_varinfo_globdef in H4.
      destruct x1.
      {
        inv_monad H4. discriminate.
      }
      eauto 6.
    }
    monad_norm. unfold get_varinfo_globdef at 1.
    rewrite oplus_id_left'.
    destruct (get_layer_primitive i L) as [ [ fe | ] | ] eqn:HLAY; try discriminate.
    {
      monad_norm. unfold get_primitive_globdef.
      destruct (make_external i fe) eqn:?; try discriminate.
      monad_norm.
      intro J. apply oplus_one_left' in J.
      destruct J as (REM & J). inv J.
    }
    monad_norm. unfold get_primitive_globdef.
    rewrite oplus_id_left'.
    unfold get_varinfo_globdef.
    intro J. inv_monad J.
    destruct x1; try discriminate.
    inv_monad H4.
    inv H4.
    eauto 6.
  Qed.

  Lemma make_globalenv_find_var_info {D} s M L ge b v :
    make_globalenv (D := D) s M L = OK ge ->
    Genv.find_var_info ge b = Some v ->
    exists i,
      Genv.find_symbol ge i = Some b /\
      (
        exists vi,
          globvar_map make_varinfo vi = v /\
          (
            get_module_variable i M = OK (Some vi)
            \/
            get_layer_globalvar i L = OK (Some vi)
          )
      ).
  Proof.
    unfold make_globalenv. simpl. intro MGE.
    inv_monad MGE.
    intros. subst.
    exploit @Genv.find_var_info_find_symbol; eauto using make_program_names_norepet.
    destruct 1.
    exploit @Genv.find_var_info_symbol_inversion; eauto.
    intros.
    exploit @make_program_gvar; eauto.
  Qed.

(* The following weak version is no longer needed.
  Lemma make_globalenv_find_var_info_weak {D} s M L ge i b v :
    make_globalenv (D := D) s M L = OK ge ->
    Genv.find_var_info ge b = Some v ->
    Genv.find_symbol ge i = Some b ->
      (
        exists vi,
          globvar_map make_varinfo vi = v /\
          (
            get_module_variable i M = OK (Some vi)
            \/
            get_layer_globalvar i L = OK (Some vi)
          )
      ).
  Proof.
    intros.
    exploit @make_globalenv_find_var_info; eauto.
    destruct 1 as (? & ? & ? & ?).
    replace i with x in * by eauto using Genv.genv_vars_inj.
    eauto.
  Qed.
*)

  (* Do we need the following?
  Lemma make_program_none {D} s M L p i:
    make_program (D := D) s M L = OK p ->
    In (i, None) (prog_defs p) ->
    get_module_function i M = OK None /\
    get_module_variable i M = OK None /\
    get_layer_primitive i L = OK None /\
    get_layer_globalvar i L = OK None.
   *)    

  Lemma make_program_get_module_function {D} s M L p i fi f:
    make_program (D := D) s M L = OK p ->
    get_module_function i M = OK (Some fi) ->
    make_internal fi = OK f ->
    In (i, Some (Gfun f)) (prog_defs p).
  Proof.
    unfold make_program. intro H.
    inv_monad H.
    subst.
    simpl in *.
    destruct_valid_program.
    intro MOD.
    exploit (Hfun_γ i).
    {
      rewrite MOD.
      unfold isOKNone.
      congruence.
    }
    intros IN MAKEINT.
    exploit @add_prog_defs_globdef_exists; eauto.
    unfold get_globdef.
    rewrite MOD. monad_norm.
    unfold get_function_globdef.
    rewrite MAKEINT. monad_norm.
    destruct 1 as (? & J & IN').
    apply oplus_one_left' in J.
    destruct J; subst; auto.
  Qed.

  Lemma make_globalenv_get_module_function {D} s M L ge i fi f:
    make_globalenv (D := D) s M L = OK ge ->
    get_module_function i M = OK (Some fi) ->
    make_internal fi = OK f ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_funct_ptr ge b = Some f.
  Proof.
    unfold make_globalenv. simpl.
    intro MPROG. inv_monad MPROG.
    intros.
    subst.
    eapply Genv.find_funct_ptr_exists; eauto using make_program_get_module_function, make_program_names_norepet.
  Qed.

  Lemma make_program_get_module_variable {D} s M L p i v:
    make_program (D := D) s M L = OK p ->
    get_module_variable i M = OK (Some v) ->
    In (i, Some (Gvar (globvar_map make_varinfo v))) (prog_defs p).
  Proof.
    unfold make_program. intro H.
    inv_monad H.
    subst.
    simpl in *.
    destruct_valid_program.
    intro MOD.
    exploit (Hvar_γ i).
    {
      rewrite MOD.
      unfold isOKNone.
      congruence.
    }
    intros IN.
    exploit @add_prog_defs_globdef_exists; eauto.
    unfold get_globdef.
    rewrite MOD. monad_norm.
    unfold get_varinfo_globdef at 1.
    unfold eassert.
    destruct 1 as (? & J & IN').
    assert (x = Some (Gvar (globvar_map make_varinfo v))).
    {
      destruct (
          mf <- get_module_function i M; get_function_globdef mf
        ); try discriminate.
      destruct o.
      {
        apply oplus_one_left' in J.
        destruct J as (REM & ?); subst.
        apply oplus_lb_eq' in REM.
        destruct REM as (REM & _).
        destruct (decide (gvar_volatile v = false)); discriminate.
      }
      rewrite oplus_id_left' in J.
      destruct (decide (gvar_volatile v = false)); try discriminate.
      revert J.
      monad_norm.
      intro J.
      apply oplus_one_left' in J.
      tauto.
    }
    subst.
    assumption.
  Qed.

  Lemma make_globalenv_get_module_variable {D} s M L ge i v:
    make_globalenv (D := D) s M L = OK ge ->
    get_module_variable i M = OK (Some v) ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_var_info ge b = Some (globvar_map make_varinfo v).
  Proof.
    unfold make_globalenv. simpl.
    intro MPROG. inv_monad MPROG.
    intros.
    subst.
    eapply Genv.find_var_exists; eauto using make_program_get_module_variable, make_program_names_norepet.
  Qed.

  Lemma make_program_get_layer_primitive {D} s M L p i fe f:
    make_program (D := D) s M L = OK p ->
    get_layer_primitive i L = OK (Some fe) ->
    make_external i fe = OK f ->
    In (i, Some (Gfun f)) (prog_defs p).
  Proof.
    unfold make_program. intro H.
    inv_monad H.
    subst.
    simpl in *.
    destruct_valid_program.
    intro LAY.
    exploit (Hprim_γ i).
    {
      rewrite LAY.
      unfold isOKNone.
      congruence.
    }
    intros IN MAKEEXT.
    exploit @add_prog_defs_globdef_exists; eauto.
    unfold get_globdef.
    rewrite LAY. monad_norm.
    unfold get_primitive_globdef.
    rewrite MAKEEXT. monad_norm.
    destruct 1 as (? & J & IN').
    assert (x = Some (Gfun f)).
    {
      destruct (
          mf <- get_module_function i M; get_function_globdef mf
        ); try discriminate.
      destruct o.
      {
        apply oplus_one_left' in J.
        destruct J as (REM & ?); subst.
        apply oplus_lb_eq' in REM.
        destruct REM as (_ & REM).
        apply oplus_lb_eq' in REM.
        destruct REM.
        discriminate.
      }
      rewrite oplus_id_left' in J.
      destruct (mτ <- get_module_variable i M; get_varinfo_globdef mτ); try discriminate.
      destruct o.
      {
        apply oplus_one_left' in J.
        destruct J as (REM & ?); subst.
        apply oplus_one_left' in REM.
        destruct REM; discriminate.
      }
      rewrite oplus_id_left' in J.
      apply oplus_one_left' in J.
      destruct J; auto.
    }
    subst.
    assumption.
  Qed.

  Lemma make_globalenv_get_layer_primitive {D} s M L ge i fe f:
    make_globalenv (D := D) s M L = OK ge ->
    get_layer_primitive i L = OK (Some fe) ->
    make_external i fe = OK f ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_funct_ptr ge b = Some f.
  Proof.
    unfold make_globalenv. simpl.
    intro MPROG. inv_monad MPROG.
    intros.
    subst.
    eapply Genv.find_funct_ptr_exists; eauto using make_program_get_layer_primitive, make_program_names_norepet.
  Qed.

  Lemma make_program_get_layer_globalvar {D} s M L p i v:
    make_program (D := D) s M L = OK p ->
    get_layer_globalvar i L = OK (Some v) ->
    In (i, Some (Gvar (globvar_map make_varinfo v))) (prog_defs p).
  Proof.
    unfold make_program. intro H.
    inv_monad H.
    subst.
    simpl in *.
    destruct_valid_program.
    intro LAY.
    exploit (Hglob_γ i).
    {
      rewrite LAY.
      unfold isOKNone.
      congruence.
    }
    intros IN.
    exploit @add_prog_defs_globdef_exists; eauto.
    unfold get_globdef.
    rewrite LAY. monad_norm.
    unfold get_varinfo_globdef at 2.
    unfold eassert. destruct (decide (gvar_volatile v = false)).
    {
      monad_norm.
      destruct 1 as (? & J & IN').
      assert (x = Some (Gvar (globvar_map make_varinfo v))).
      {
        destruct (
            mf <- get_module_function i M; get_function_globdef mf
          ); try discriminate.
        destruct o.
        {
          apply oplus_one_left' in J.
          destruct J as (REM & ?); subst.
          apply oplus_lb_eq' in REM.
          destruct REM as (_ & REM).
          apply oplus_lb_eq' in REM.
          destruct REM.
          discriminate.
        }
        rewrite oplus_id_left' in J.
        destruct (mτ <- get_module_variable i M; get_varinfo_globdef mτ); try discriminate.
        destruct o.
        {
          apply oplus_one_left' in J.
          destruct J as (REM & ?); subst.
          apply oplus_lb_eq' in REM.
          destruct REM; discriminate.
        }
        rewrite oplus_id_left' in J.
        destruct (mτ <- get_layer_primitive i L; get_primitive_globdef i mτ); try discriminate.
        destruct o.
        {
          discriminate.
        }
        inv J.
        reflexivity.
      }
      subst.
      assumption.
    }
    monad_norm.
    destruct 1 as (? & ? & ?).
    destruct (mf <- get_module_function i M; get_function_globdef mf); try discriminate.
    destruct (mf <- get_module_variable i M; get_varinfo_globdef mf); try discriminate.
    destruct (mf <- get_layer_primitive i L; get_primitive_globdef i mf); discriminate.
  Qed.

  Lemma make_globalenv_get_layer_globalvar {D} s M L ge i v:
    make_globalenv (D := D) s M L = OK ge ->
    get_layer_globalvar i L = OK (Some v) ->
    exists b,
      Genv.find_symbol ge i = Some b /\
      Genv.find_var_info ge b = Some (globvar_map make_varinfo v).
  Proof.
    unfold make_globalenv. simpl.
    intro MPROG. inv_monad MPROG.
    intros.
    subst.
    eapply Genv.find_var_exists; eauto using make_program_get_layer_globalvar, make_program_names_norepet.
  Qed.

  (** How to prove that make_program actually exists? *)

  Lemma add_prog_defs_exists {D} (L: _ D) M:
    LayerOK L ->
    ModuleOK M ->
    (forall i fe, get_layer_primitive i L = OK (Some fe) -> isOK (make_external i fe) /\ isOKNone (get_module_function i M) /\ isOKNone (get_module_variable i M)) ->
    (forall i fi, get_module_function i M = OK (Some fi) -> isOK (make_internal fi) /\ isOKNone (get_layer_primitive i L) /\ isOKNone (get_layer_globalvar i L)) ->
    (forall i v, get_layer_globalvar i L = OK (Some v) -> gvar_volatile v = false /\ isOKNone (get_module_function i M) /\ isOKNone (get_module_variable i M)) ->
    (forall i v, get_module_variable i M = OK (Some v) -> gvar_volatile v = false /\ isOKNone (get_layer_primitive i L) /\ isOKNone (get_layer_globalvar i L)) ->
    forall l accu,
    isOK (add_prog_defs l M L accu).
  Proof.
    intros LOK MOK Hext Hint Hlayer_non_volat Hmodule_non_volat.
    induction l; simpl.
    { esplit; reflexivity. }
    intro.
    unfold get_globdef.
    destruct (module_ok_function M a (MOK a)) as (of & MODF).
    rewrite MODF.
    destruct of; monad_norm; unfold get_function_globdef.
    {
      destruct (Hint _ _ MODF) as ((? & INT) & HLP & HLV).
      rewrite INT.
      monad_norm.
      destruct (module_ok_disjoint M a (MOK a)) as [|MODV]; try congruence.
      unfold isOKNone in *.
      rewrite MODV.
      rewrite HLP.
      rewrite HLV.
      monad_norm. unfold get_varinfo_globdef, get_primitive_globdef.
      monad_norm. simpl. monad_norm.
      eauto.
    }
    destruct (module_ok_variable M a (MOK a)) as (ov & MODV).
    rewrite oplus_id_left'.
    rewrite MODV.
    destruct ov; monad_norm; unfold get_varinfo_globdef at 1.
    {
      exploit Hmodule_non_volat; eauto.
      unfold isOKNone.
      destruct 1 as (NONVOL & HLP & HLV).
      rewrite NONVOL.
      rewrite HLP.
      rewrite HLV.
      unfold eassert. simpl.
      monad_norm. simpl. monad_norm.
      eauto.
    }
    rewrite oplus_id_left'.
    destruct (layer_ok_primitive L a (LOK a)) as (op & LAYP).
    rewrite LAYP.
    destruct op; monad_norm; unfold get_primitive_globdef.
    {
      exploit Hext; eauto.
      unfold isOKNone.
      destruct 1 as [EXT _].
      destruct EXT as (? & EXT).
      rewrite EXT. monad_norm.
      destruct (layer_ok_disjoint L a (LOK a)) as [|LAYV]; try congruence.
      unfold isOKNone in *.
      rewrite LAYV.
      unfold get_varinfo_globdef.
      monad_norm.
      simpl.
      monad_norm.
      eauto.
    }
    rewrite oplus_id_left'.
    destruct (layer_ok_globalvar L a (LOK a)) as (ov & LAYV).
    rewrite LAYV.
    destruct ov; monad_norm; unfold get_varinfo_globdef.
    {
      exploit Hlayer_non_volat; eauto.
      destruct 1 as [NONVOL _].
      rewrite NONVOL.
      unfold eassert. simpl.
      monad_norm.
      eauto.
    }
    monad_norm.
    eauto.
  Qed.

  (** Missing lemma from StencilImpl *)
  Lemma find_symbol_in_stencil_ids s i:
    isSome (find_symbol s i) ->
    In i (stencil_ids s).
  Proof.
    unfold find_symbol. simpl.
    unfold globalenv_of_stencil, program_of_stencil.
    unfold Genv.globalenv.
    simpl.
    rewrite <- find_symbol_of_list_correct.
    simpl.
    rewrite list_map_compose.
    simpl.
    rewrite list_map_identity.
    destruct (In_dec peq i (stencil_ids s)); auto.
    erewrite find_symbol_of_list_not_in; eauto.
    unfold Genv.find_symbol; simpl.
    rewrite Maps.PTree.gempty.
    destruct 1; discriminate.
  Qed.

  Lemma make_program_exists {D} (L: _ D) M s:
    LayerOK L ->
    ModuleOK M ->
    (forall i fe, get_layer_primitive i L = OK (Some fe) -> isOK (make_external i fe) /\ isOKNone (get_module_function i M) /\ isOKNone (get_module_variable i M)) ->
    (forall i fi, get_module_function i M = OK (Some fi) -> isOK (make_internal fi) /\ isOKNone (get_layer_primitive i L) /\ isOKNone (get_layer_globalvar i L)) ->
    (forall i v, get_layer_globalvar i L = OK (Some v) -> gvar_volatile v = false /\ isOKNone (get_module_function i M) /\ isOKNone (get_module_variable i M)) ->
    (forall i v, get_module_variable i M = OK (Some v) -> gvar_volatile v = false /\ isOKNone (get_layer_primitive i L) /\ isOKNone (get_layer_globalvar i L)) ->
    (forall i p,
       get_layer_primitive i L = OK (Some p) -> isSome (find_symbol s i)) ->
    (forall i v,
       get_layer_globalvar i L = OK (Some v) -> isSome (find_symbol s i)) ->
    (forall i f,
       get_module_function i M = OK (Some f) -> isSome (find_symbol s i)) ->
    (forall i v,
       get_module_variable i M = OK (Some v) -> isSome (find_symbol s i)) ->
    isOK (make_program s M L).
  Proof.
    intros LOK MOK.
    intros until 4.
    intros LPRIM LVAR MFUN MVAR.
    unfold make_program.
    unfold eassert.
    destruct (decide (valid_program s M L)); monad_norm.
    {
      exploit @add_prog_defs_exists; eauto.
      instantiate (1 := nil).
      instantiate (1 := stencil_ids s).
      destruct 1 as (? & PD).
      rewrite PD.
      monad_norm.
      esplit; reflexivity.
    }
    exfalso.
    destruct n.
    repeat split;
      intros;
      eapply find_symbol_in_stencil_ids;
      unfold isOKNone in *.
    * destruct (layer_ok_primitive L i (LOK i)) as (o & ?).
      destruct o; try congruence; eauto.
    * destruct (layer_ok_globalvar L i (LOK i)) as (o & ?).
      destruct o; try congruence; eauto.
    * destruct (module_ok_function M i (MOK i)) as (o & ?).
      destruct o; try congruence; eauto.
    * destruct (module_ok_variable M i (MOK i)) as (o & ?).
      destruct o; try congruence; eauto.
  Qed.

  
  Ltac ret_simpl:=           
    repeat match goal with
             | H0: ret _ = ret _ |- _ => inv H0
           end; try discriminate.

  Lemma get_globaldef_eq {D} (L: _ D) M:    
    forall i v τ p, 
    forall (OKLayer: LayerOK (L ⊕ v ↦ τ)),
      get_globdef i (M ⊕ v ↦ τ) L = ret p 
      -> get_globdef i M (L ⊕ v ↦ τ) = ret p.
  Proof.
    intros.
    unfold get_globdef in *.
    destruct (get_module_function i (M ⊕ v ↦ τ)) eqn: mof1;
      (try (simpl in H; inv_monad H; fail));
      destruct (get_module_variable i (M ⊕ v ↦ τ)) eqn: mov1;
      (try (simpl in H; inv_monad H; fail));
      destruct (get_layer_primitive i L) eqn: laf1;
      (try (simpl in H; inv_monad H; fail));
      destruct (get_layer_globalvar i L) eqn: lav1;
      (try (simpl in H; inv_monad H; fail)).

    monad_norm.
    destruct (OKLayer i) as [PrimOK VarOK _].

    destruct o.
    {
      destruct o0; destruct o1; destruct o2;
      simpl in H; inv_monad H;
      ret_simpl.

      specialize (get_module_function_oplus i M (v ↦ τ)).
      rewrite mof1. get_module_normalize.
      intros Hle.
      destruct (get_module_function i M); try destruct o; simpl in Hle; inv_monad Hle; inv H0.
      apply get_module_variable_cancel in mov1.
      destruct mov1 as [mov1 mov1'].
      rewrite mov1'.

      assert (Hw1: get_layer_primitive i (L ⊕ v ↦ τ) = OK None).
      {
        apply get_layer_primitive_none; try eassumption.
        get_layer_normalize. reflexivity.
      }
      rewrite Hw1. clear Hw1.

      assert (Hw1: get_layer_globalvar i (L ⊕ v ↦ τ) = OK None).
      {
        apply get_layer_globalvar_none; try eassumption.
        destruct (peq i v); subst.
        - get_module_normalize_in mov1.
          inv mov1.
        - get_layer_normalize. reflexivity.
      }
      rewrite Hw1.
      monad_norm. unfold get_function_globdef.
      rewrite H3.
      reflexivity.
    }

    destruct o0.
    {
      destruct o1; destruct o2;
      simpl in H; inv_monad H;
      ret_simpl.

      apply get_module_function_cancel in mof1.
      destruct mof1 as [mof1 mof1'].
      rewrite mof1'.

      assert (Hw1: get_layer_primitive i (L ⊕ v ↦ τ) = OK None).
      {
        apply get_layer_primitive_none; try eassumption.
        get_layer_normalize. reflexivity.
      }
      rewrite Hw1. clear Hw1.      
      
      specialize (get_module_variable_oplus i M (v ↦ τ)).
      rewrite mov1. 
      destruct (peq i v); subst.
      {
        get_module_normalize.
        intros Hle.
        destruct (get_module_variable v M); try destruct o; simpl in Hle; inv_monad Hle; inv H0.

        assert (Hw1: get_layer_globalvar v (L ⊕ v ↦ g) = OK (Some g)).
        {
          apply get_layer_globalvar_right; try eassumption.
          get_layer_normalize. reflexivity.
        }
        rewrite Hw1.
        monad_norm. unfold get_varinfo_globdef.
        rewrite H5.
        reflexivity.
      }
      {
        get_module_normalize.
        intros Hle.
        destruct (get_module_variable i M); try destruct o; simpl in Hle; inv_monad Hle; inv H0.
        assert (Hw1: get_layer_globalvar i (L ⊕ v ↦ τ) = OK None).
        {
          apply get_layer_globalvar_none; try eassumption.
          get_layer_normalize. reflexivity.
        }
        rewrite Hw1.
        monad_norm. unfold get_varinfo_globdef.
        rewrite H5.
        reflexivity.
      }
    }

    destruct o1.
    {
      destruct o2;
      simpl in H; inv_monad H;
      ret_simpl.

      apply get_module_function_cancel in mof1.
      destruct mof1 as [mof1 mof1'].
      rewrite mof1'.

      apply get_module_variable_cancel in mov1.
      destruct mov1 as [mov1 mov1'].
      rewrite mov1'.

      assert (Hw1: get_layer_primitive i (L ⊕ v ↦ τ) = OK (Some p0)).
      {
        apply get_layer_primitive_left; try eassumption.
      }
      rewrite Hw1. clear Hw1.      
      
      assert (Hw1: get_layer_globalvar i (L ⊕ v ↦ τ) = OK None).
      {
        apply get_layer_globalvar_none; try eassumption.
        destruct (peq i v); subst.
        - get_module_normalize_in mov1.
          inv mov1.
        - get_layer_normalize. reflexivity.
      }
      rewrite Hw1.
      monad_norm. unfold get_primitive_globdef.
      rewrite H7.
      reflexivity.
    }

    destruct o2;
      simpl in H; inv_monad H;
      ret_simpl.
    {
      apply get_module_function_cancel in mof1.
      destruct mof1 as [mof1 mof1'].
      rewrite mof1'.

      apply get_module_variable_cancel in mov1.
      destruct mov1 as [mov1 mov1'].
      rewrite mov1'.

      assert (Hw1: get_layer_primitive i (L ⊕ v ↦ τ) = OK None).
      {
        apply get_layer_primitive_none; try eassumption.
        get_layer_normalize. reflexivity.
      }
      rewrite Hw1. clear Hw1.      
      
      assert (Hw1: get_layer_globalvar i (L ⊕ v ↦ τ) = OK (Some g)).
      {
        apply get_layer_globalvar_left; try eassumption.
      }
      rewrite Hw1.
      monad_norm. unfold get_varinfo_globdef.
      rewrite H8.
      reflexivity.
    }      

    {
      apply get_module_function_cancel in mof1.
      destruct mof1 as [mof1 mof1'].
      rewrite mof1'.

      apply get_module_variable_cancel in mov1.
      destruct mov1 as [mov1 mov1'].
      rewrite mov1'.

      assert (Hw1: get_layer_primitive i (L ⊕ v ↦ τ) = OK None).
      {
        apply get_layer_primitive_none; try eassumption.
        get_layer_normalize. reflexivity.
      }
      rewrite Hw1. clear Hw1.
      
      assert (Hw1: get_layer_globalvar i (L ⊕ v ↦ τ) = OK None).
      {
        apply get_layer_globalvar_none; try eassumption.
        destruct (peq i v); subst.
        - get_module_normalize_in mov1.
          inv mov1.
        - get_layer_normalize. reflexivity.
      }
      rewrite Hw1.
      monad_norm. 
      reflexivity.
    }      
  Qed.

  Lemma add_prog_defs_eq {D} (L: _ D) M:    
    forall v τ p, 
    forall (OKLayer: LayerOK (L ⊕ v ↦ τ)) s t,
      add_prog_defs s (M ⊕ v ↦ τ) L t = ret p ->
      add_prog_defs s M (L ⊕ v ↦ τ) t = ret p.
  Proof.
    induction s.
    - inversion 1.
      constructor.
    - Local Opaque oplus mapsto.
      intros. simpl in H.
      simpl.
      destruct (get_globdef a (M ⊕ v ↦ τ) L) eqn: glb.
      + eapply get_globaldef_eq in glb; try eassumption.
        rewrite glb. monad_norm.
        eapply IHs; eassumption.
      + monad_norm. inv H.
  Qed.

  Lemma make_program_var_transfer {D} (L: _ D) M s:
    forall v τ,
    forall (OKLayer: LayerOK (L ⊕ v ↦ τ)) p,
      make_program s (M ⊕ v ↦ τ) L = ret p ->
      make_program s M (L  ⊕ v ↦ τ) = ret p.
  Proof.
    unfold make_program. intros. 
    unfold eassert.
    destruct (decide (valid_program s (M ⊕ v ↦ τ) L)); monad_norm.
    {
      destruct_valid_program.
      destruct (decide (valid_program s M (L ⊕ v ↦ τ))); monad_norm.
      {
        destruct_valid_program.
        destruct H as [v1 HP].
        destruct (add_prog_defs (stencil_ids s) (M ⊕ v ↦ τ) L nil) eqn: glb.
        - eapply add_prog_defs_eq in glb; try eassumption.
          rewrite glb. assumption.
        - monad_norm. inv HP.
      }
      {
        elim n.
        repeat split.
        - intros.
          eapply Hprim_γ.
          red; intros.
          destruct (OKLayer i) as [PrimOK _ _].
          elim H0.
          eapply get_layer_primitive_none; try eassumption.
          get_layer_normalize; reflexivity.
        - intros.
          destruct (OKLayer i) as [_ VarOK _].
          destruct (peq i v); subst.
          + eapply Hvar_γ.
            red; intros.
            eapply get_module_variable_cancel in H1.
            destruct H1 as [HF _].
            get_module_normalize_in HF. inv HF.
          + eapply Hglob_γ.
            red; intros.
            elim H0.
            eapply get_layer_globalvar_none; try eassumption.
            get_layer_normalize. 
            reflexivity.
        - intros.
          eapply Hfun_γ.
          red; intros.
          elim H0.
          eapply get_module_function_cancel in H1.
          destruct H1 as [_ HF].
          assumption.
        - intros.
          eapply Hvar_γ.
          red; intros.
          elim H0.
          eapply get_module_variable_cancel in H1.
          destruct H1 as [_ HF].
          assumption.
      }
    }
    {
      destruct H as [p' HP].
      elim n.
      assumption.
    }
  Qed.

  (** Summary *)

  Local Instance make_program_prf:
    MakeProgram Fm Vm Fp Vp.
  Proof.
    split.
    * intros until ge; apply make_globalenv_matches.
    * intros D γ i σ ge.
      unfold make_globalenv; simpl.
      intros H; inv_monad H.
      exploit_make_program_at i.
      destruct (Genv.find_funct_ptr_exists x i x0); eauto.
    * intros D γ i σ ge.
      unfold make_globalenv; simpl.
      intros H; inv_monad H.
      exploit_make_program_at i.
      destruct (Genv.find_funct_ptr_exists x i x0); eauto.
    * intros D γ i σ ge.
      unfold make_globalenv; simpl.
      intros H; inv_monad H.
      exploit_make_program_at i.
      edestruct (Genv.find_var_exists x i); eauto.
    * intros D γ i σ ge.
      unfold make_globalenv; simpl.
      intros H; inv_monad H.
      exploit_make_program_at i.
      edestruct (Genv.find_var_exists x i); eauto.
    * typeclasses eauto.
    * typeclasses eauto.
    * exact @make_program_get_module_function_prop.
    * exact @make_program_get_module_variable_prop.
    * exact @make_program_get_layer_primitive_prop.
    * exact @make_program_get_layer_globalvar_prop.
    * exact @make_program_gfun.
    * exact @make_globalenv_find_funct_ptr.
    * exact @make_program_gvar.
    * exact @make_globalenv_find_var_info.
    * exact @make_program_get_module_function.
    * exact @make_globalenv_get_module_function.
    * exact @make_program_get_module_variable.
    * exact @make_globalenv_get_module_variable.
    * exact @make_program_get_layer_primitive.
    * exact @make_globalenv_get_layer_primitive.
    * exact @make_program_get_layer_globalvar.
    * exact @make_globalenv_get_layer_globalvar.
    * exact @make_program_layer_ok.
    * exact @make_program_module_ok.
    * exact @make_program_module_layer_disjoint.
    * exact @make_program_exists.
    * intros; eapply make_program_defs_init_mem_le; eauto.
    * intros. unfold MakeProgram.make_program in *.
      unfold make_program_ops in *.
      unfold make_program in *.
      inv_monad prog. subst.
      reflexivity.
    * exact @make_program_var_transfer.
  Qed.

  Lemma make_program_module_function_in_stencil {D} s M L p i :
    make_program (D := D) s M L = OK p ->
    get_module_function i M <> OK None ->
    In i (stencil_ids s).
  Proof.
    unfold make_program. intro H.
    inv_monad H.
    unfold valid_program in x.
    clear H2 x0 H H3.
    firstorder.
  Qed.

  Lemma make_globalenv_module_function {D} s M L p i f :
    make_program (D := D) s M L = OK p ->
    get_module_function i M = OK (Some f) ->
    exists fi, make_internal f = OK fi /\
               exists b,
                 Genv.find_symbol (Genv.globalenv p) i = Some b
                 /\ Genv.find_funct_ptr (Genv.globalenv p) b = Some fi.
  Proof.
    intros.
    exploit (make_program_module_function_in_stencil (D := D)); eauto.
    {
      instantiate (1 := i). rewrite H0. congruence.
    }
    intro.
    exploit (make_program_In_globdef_exists (D := D)); eauto.
    destruct 1 as (? & GLOBDEF & IN).
    unfold get_globdef in GLOBDEF.
    rewrite H0 in GLOBDEF.
    revert GLOBDEF. monad_norm.
    unfold get_function_globdef.
    destruct (make_internal f); try discriminate.
    monad_norm.
    intro.
    apply oplus_one_left' in GLOBDEF.
    destruct GLOBDEF as [GLOBDEF ?]; subst.
    clear GLOBDEF.
    esplit. split; eauto.
    eapply Genv.find_funct_ptr_exists; eauto.
    (** HERE we use stencil_ids_norepet *)
    eapply make_program_names_norepet; eauto.
  Qed.

End WITHMAKEFUNDEFOPS.

(** If we change the function definitions of a module without changing
    either the domain or the variables, then make_program similarly succeeds.
 *)

Section WITH2MAKEFUNDEFOPS1.
  Context `{progfmt: ProgramFormat}.
  Context `{Hmodule: !Modules ident Fm (globvar Vm) module}.
  Context `{Hlayer: !Layers ident primsem (globvar Vm) layer}.

  Context {Fm' module'}
          `{module_ops': !ModuleOps ident Fm' (globvar Vm) module'}.
  Context {Fp' Vp'}
          `{pf_ops': !ProgramFormatOps Fm' Vm Fp' Vp'}
          `{progfmt': !ProgramFormat Fm' Vm Fp' Vp'}.
  Context `{Hmodule': !Modules ident Fm' (globvar Vm) module'}.


  Context {D: layerdata}.

  Variables (L: layer D).

  Hypothesis (transf_layer_primitives:
                forall i s,
                  get_layer_primitive i L = OK (Some s) ->
                  isOK (make_external (ProgramFormatOps := pf_ops) i s) ->
                  isOK (make_external (ProgramFormatOps := pf_ops') i s)).

  Variables (M1: module)
            (M2: module')

    (transf_module_functions:
       forall i f1,
         get_module_function i M1 = OK (Some f1) ->
         isOK (make_internal f1) ->
         exists f2, get_module_function i M2 = OK (Some f2) /\
                    isOK (make_internal f2))
    (transf_module_function_none:
       forall i,
         get_module_function i M1 = OK None ->
         get_module_function i M2 = OK None)
    (transf_module_variables:
       forall i,
         get_module_variable i M2 =
         get_module_variable i M1)
  .

  Lemma get_globdef_ok: forall i,
                          isOK (get_globdef i M1 L) ->
                          isOK (get_globdef i M2 L).
  Proof.
    unfold get_globdef. intro.
    rewrite transf_module_variables.
    unfold isOK.
    destruct 1 as [? HOK].
    revert HOK.
    destruct (get_module_function i M1) eqn:HM1; try discriminate.
    destruct o.
    {
      monad_norm. unfold get_function_globdef at 1.
      destruct (make_internal f) eqn:HMAKE1; try discriminate.
      monad_norm.
      intro.
      apply oplus_one_left' in HOK.
      destruct HOK as [HOK ?]; subst.
      apply oplus_lb_eq' in HOK.
      destruct HOK as [HVAR HOK].
      inv_monad HVAR.
      rewrite H0.
      destruct x.
      {
        unfold get_varinfo_globdef in H1.
        inv_monad H1. discriminate.
      } 
      apply oplus_lb_eq' in HOK.
      destruct HOK as [HPRIM HVAR].
      inv_monad HPRIM.
      rewrite H2.
      destruct x.
      {
        unfold get_primitive_globdef in H3.
        inv_monad H3. discriminate.
      }
      inv_monad HVAR.
      rewrite H4.
      destruct x.
      {
        unfold get_varinfo_globdef in H5.
        inv_monad H5. discriminate.
      }
      exploit transf_module_functions; eauto.
      {
        rewrite HMAKE1. unfold isOK. eauto.
      }
      destruct 1 as (? & HFUN2 & HMAKE2).
      destruct HMAKE2 as (? & HMAKE2).
      rewrite HFUN2. monad_norm. unfold get_function_globdef at 1. rewrite HMAKE2. monad_norm.
      unfold get_varinfo_globdef. unfold get_primitive_globdef. simpl. monad_norm. eauto.
    }
    monad_norm. unfold get_function_globdef at 1.
    rewrite oplus_id_left'.
    erewrite transf_module_function_none; eauto.
    destruct (get_module_variable i M1); try discriminate.
    destruct o.
    {
      monad_norm. unfold get_varinfo_globdef at 1.
      destruct (eassert (MSG "volatile variable" :: nil) (gvar_volatile g = false)) eqn:NONVOLAT;
        try discriminate.
      monad_norm.
      intro REM.
      apply oplus_one_left' in REM.
      destruct REM as [REM ?]; subst.
      apply oplus_lb_eq' in REM.
      destruct REM as [HPRIM HVAR].
      inv_monad HPRIM. rewrite H0.
      destruct x.
      {
        unfold get_primitive_globdef in H1. inv_monad H1. discriminate.
      }
      inv_monad HVAR. rewrite H2.
      destruct x.
      {
        unfold get_varinfo_globdef in H3. inv_monad H3. discriminate.
      }
      unfold get_varinfo_globdef at 1. rewrite NONVOLAT.
      monad_norm. unfold get_function_globdef. unfold get_primitive_globdef. unfold get_varinfo_globdef.
      simpl. monad_norm. eauto.
    }
    monad_norm. unfold get_varinfo_globdef at 1.
    rewrite oplus_id_left'.
    destruct (get_layer_primitive i L) eqn:HPRIM; try discriminate.
    destruct o.
    {
      monad_norm. unfold get_primitive_globdef at 1.
      destruct (make_external i p) eqn:HMAKE1; try discriminate.
      monad_norm.
      intro REM.
      apply oplus_one_left' in REM.
      destruct REM as [REM ?]; subst.
      inv_monad REM. rewrite H0.
      destruct x.
      {
        unfold get_varinfo_globdef in H1. inv_monad H1. discriminate.
      }
      unfold get_primitive_globdef.
      exploit transf_layer_primitives; eauto.
      {
        rewrite HMAKE1. unfold isOK. eauto.
      }
      destruct 1 as (? & HMAKE2).
      rewrite HMAKE2.
      monad_norm. unfold get_function_globdef. unfold get_varinfo_globdef.
      simpl. monad_norm. eauto.
    }
    monad_norm. unfold get_primitive_globdef.
    rewrite oplus_id_left'.
    intro HVAR. inv_monad HVAR.
    unfold get_varinfo_globdef in * |- *.
    destruct (get_layer_globalvar i L); try discriminate.
    monad_norm.
    inv H0.
    destruct x0.
    {
      inv_monad H1; subst.
      rewrite H2.
      monad_norm.
      unfold get_function_globdef. simpl. monad_norm. eauto.
    }
    unfold get_function_globdef. simpl. monad_norm. eauto.
  Qed.

  Lemma add_prog_defs_ok:
    forall l defs1 defs2,
      isOK (add_prog_defs l M1 L defs1) ->
      isOK (add_prog_defs l M2 L defs2).
  Proof.
    unfold isOK. destruct 1.
    revert defs1 defs2 x H.
    induction l; simpl; eauto.
    intros. inv_monad H.
    generalize (get_globdef_ok a). rewrite H2. unfold isOK. intro J.
    exploit J; eauto. clear J. destruct 1 as (? & J).
    rewrite J. monad_norm.
    eauto.
  Qed.

  Lemma valid_program_ok:
    forall s,
      valid_program s M1 L ->
      valid_program s M2 L.
  Proof.
    intros s HVALID.
    inversion HVALID as (? & ? & ? & ?).
    repeat (split; auto).
    * intro i.
      destruct (decide (isOKNone (get_module_function i M1))); eauto.
      unfold isOKNone in *.
      erewrite transf_module_function_none; eauto.
    * intro; rewrite transf_module_variables; eauto.
  Qed.

  Theorem make_program_ok:
    forall s,
      isOK (make_program s M1 L) ->
      isOK (make_program s M2 L).
  Proof.
    unfold isOK. unfold make_program.
    destruct 1.
    inv_monad H.
    unfold eassert.
    destruct (decide (valid_program s M2 L)).
    {
      generalize (add_prog_defs_ok (stencil_ids s) nil nil).
      rewrite H3. unfold isOK. intro K.
      exploit K; eauto.
      destruct 1.
      rewrite H0.
      monad_norm.
      eauto.
    }
    destruct n; eauto using valid_program_ok.
  Qed.

End WITH2MAKEFUNDEFOPS1.

(** Compatibility with CompCert's [transform_partial_program2] *)

Section WITH2MAKEFUNDEFOPS.
  Context `{progfmt: ProgramFormat}.
  Context `{Hmodule: !Modules ident Fm (globvar Vm) module}.
  Context `{Hlayer: !Layers ident primsem (globvar Vm) layer}.

  Context {Fm' module'}
          `{module_ops': !ModuleOps ident Fm' (globvar Vm) module'}.
  Context {Fp' Vp'}
          `{pf_ops': !ProgramFormatOps Fm' Vm Fp' Vp'}
          `{progfmt': !ProgramFormat Fm' Vm Fp' Vp'}.
  Context `{Hmodule': !Modules ident Fm' (globvar Vm) module'}.

  Variables
    (transf_function: Fm -> res Fm')
    (transf_fundef: Fp -> res Fp')

    (* transf_fundef_internal_correct:
       forall f1 fd2, transf_fundef (make_internal f1) = OK fd2 ->
                      exists f2, transf_function f1 = OK f2 /\
                                 fd2 = make_internal f2 *)
    (transf_fundef_internal_complete:
       forall f1 f2, transf_function f1 = OK f2 ->
                     forall fp1, make_internal f1 = OK fp1 ->
                                 exists fp2, make_internal f2 = OK fp2 /\
                                             transf_fundef fp1 = OK fp2).

  Variables
    (transf_varinfo: Vp -> res Vp')
    (transf_make_varinfo:
       forall lv, transf_varinfo (make_varinfo lv) = OK (make_varinfo lv)).

  Context {D: layerdata}.

  Variables (L: layer D)

            (transf_layer_primitives:
               forall i s,
                 get_layer_primitive i L = OK (Some s) ->
                 forall e, make_external (ProgramFormatOps := pf_ops) i s = OK e ->
                           exists e', make_external (ProgramFormatOps := pf_ops') i s = OK e' /\
                                      transf_fundef e = OK e').

  Variables (M1: module)
            (M2: module')

    (transf_module_functions:
       forall i f1,
         get_module_function i M1 = OK (Some f1) ->
         exists f2, transf_function f1 = OK f2 /\
                    get_module_function i M2 = OK (Some f2))
    (transf_module_function_none:
       forall i,
         get_module_function i M1 = OK None ->
         get_module_function i M2 = OK None)
    (transf_module_variables:
       forall i,
         get_module_variable i M2 =
         get_module_variable i M1)
.

(*
  Section WITHNOMAGIC.

    Variables
      (L_no_anything: ptree_forall (fun _ a => a <> anything) L)
      (M1_no_magic: ptree_forall (fun _ a => a <> magic) (let (Mt, _) := M1 in Mt)).
*)

  Lemma get_globdef_transf_globdefs:
    forall l l1,
      map (fun i => (i, get_globdef i M1 L)) l = map (fun is => match is with (i, d) => (i, OK d) end) l1 ->
      exists l2,
        map (fun i => (i, get_globdef i M2 L)) l = map (fun is => match is with (i, d) => (i, OK d) end) l2 /\
        transf_globdefs transf_fundef transf_varinfo l1 = OK l2.
  Proof.
    induction l; destruct l1; try discriminate.
     exists nil. split; reflexivity.
    intro J. inv J.
    destruct p. inv H0.
    exploit IHl; clear IHl; eauto.
    clear H1.
    destruct 1 as [? [? ?]].
    simpl.
    rewrite H; clear H.
    rewrite H0; clear H0.
    simpl.
    unfold get_globdef in *.
    revert H3.
    rewrite transf_module_variables.
    destruct (get_module_function i M1) as [ [ f1 | ] | ] eqn:HM1; try discriminate.
    {
      monad_norm.
      unfold get_function_globdef at 1.
      destruct (make_internal f1) eqn:Hmake1; try discriminate.
      monad_norm.
      intro J.
      apply oplus_one_left' in J.
      destruct J as [REM ?] ; subst.
      exploit transf_module_functions; eauto. clear HM1.
      destruct 1 as [? [TRANSF HM2]].
      rewrite HM2; clear HM2.
      exploit transf_fundef_internal_complete; eauto. clear Hmake1 TRANSF.
      destruct 1 as [? [Hmake2 TRANSFD]].
      rewrite TRANSFD.
      monad_norm. unfold get_function_globdef. rewrite Hmake2; clear Hmake2. monad_norm.
      apply oplus_lb_eq' in REM.
      destruct REM as [HV1 REM].
      destruct (get_module_variable i M1); try discriminate.
      revert HV1. monad_norm.
      destruct o; try discriminate.
      {
        intro. exfalso. destruct g. simpl in HV1.
        inv_monad HV1. discriminate.
      }
      intros _.
      unfold get_varinfo_globdef at 1.
      apply oplus_lb_eq' in REM.
      destruct REM as [HLP HLV].
      destruct (get_layer_primitive i L) eqn:PRIM; try discriminate.
      destruct o.
      {
        exfalso.
        inv_monad HLP.
        unfold get_primitive_globdef in H0. inv_monad H0.
        discriminate.
      }
      clear HLP.
      monad_norm. unfold get_primitive_globdef at 1.
      destruct (get_layer_globalvar i L); try discriminate.
      destruct o.
      {
        inv_monad HLV.
        unfold get_varinfo_globdef in H0. inv_monad H0.
        discriminate.
      }
      clear HLV.
      monad_norm.
      unfold get_varinfo_globdef.
      esplit. split; try reflexivity.
      reflexivity.
    }    
    monad_norm. unfold get_function_globdef at 1.
    rewrite oplus_id_left'.
    exploit transf_module_function_none; eauto. clear HM1.
    intro HM2. rewrite HM2. clear HM2.    
    destruct (get_module_variable i M1); try discriminate.
    destruct o0.
    {
      monad_norm. unfold get_varinfo_globdef at 1.
      destruct (
          eassert (MSG "volatile variable" :: nil) (gvar_volatile g = false)
        ) eqn:NONVOLAT; try discriminate.
      monad_norm.
      intro J. apply oplus_one_left' in J.
      destruct J as [REM ?]; subst.
      unfold get_function_globdef at 1. monad_norm.
      unfold get_varinfo_globdef at 1.
      rewrite NONVOLAT. monad_norm.
      apply oplus_lb_eq' in REM.
      destruct REM as [HLP HLV].
      destruct (get_layer_primitive i L) eqn:PRIM; try discriminate.
      destruct o.
      {
        exfalso.
        inv_monad HLP.
        unfold get_primitive_globdef in H0. inv_monad H0.
        discriminate.
      }
      clear HLP.
      monad_norm. unfold get_primitive_globdef at 1.
      destruct (get_layer_globalvar i L); try discriminate.
      destruct o.
      {
        inv_monad HLV.
        unfold get_varinfo_globdef in H0. inv_monad H0.
        discriminate.
      }
      clear HLV.
      monad_norm.
      unfold get_varinfo_globdef.
      assert (EQVAR: transf_globvar transf_varinfo (globvar_map make_varinfo g) = OK (globvar_map make_varinfo g)).
      {
        unfold transf_globvar. destruct g; simpl.
        rewrite transf_make_varinfo.
        reflexivity.
      }
      rewrite EQVAR.
      esplit. split; try reflexivity.
      reflexivity.
    }
    monad_norm. unfold get_varinfo_globdef at 1.
    rewrite oplus_id_left'.
    destruct (get_layer_primitive i L) eqn:HLP; try discriminate.
    destruct o0.
    {
      monad_norm. unfold get_primitive_globdef at 1.
      destruct (make_external i p) eqn:HEXT; try discriminate.
      monad_norm.
      intro J.
      apply oplus_one_left' in J.
      destruct J as [REM ?] ; subst.
      exploit transf_layer_primitives; eauto. clear HEXT.
      destruct 1 as [? [HEXT2 HTRANS]].
      rewrite HTRANS; clear HTRANS.
      unfold get_primitive_globdef at 1. rewrite HEXT2; clear HEXT2.
      inv_monad REM.
      destruct x1.
      {
        unfold get_varinfo_globdef in H1. inv_monad H1. discriminate.
      }
      rewrite H0. clear H0 H1.
      esplit. split; try reflexivity.
      reflexivity.
    }
    monad_norm. unfold get_primitive_globdef at 1.
    rewrite oplus_id_left'.
    intro J. inv_monad J.
    rewrite H0; clear H0.
    unfold get_varinfo_globdef in H1.
    unfold get_varinfo_globdef. monad_norm.
    destruct x0.
    {
      inv_monad H1.
      subst.
      rewrite H2.
      assert (EQVAR: transf_globvar transf_varinfo (globvar_map make_varinfo g) = OK (globvar_map make_varinfo g)).
      {
        unfold transf_globvar. destruct g; simpl.
        rewrite transf_make_varinfo.
        reflexivity.
      }
      rewrite EQVAR.
      esplit. split; try reflexivity.
      reflexivity.
    }
    inv H1.
    esplit. split; try reflexivity.
    reflexivity.
  Qed.

  Lemma unsafe_make_program_transform_partial2:
    forall s, valid_program s M2 L ->
              forall p1,
                make_program s M1 L = OK p1 ->
                exists p2,
                  transform_partial_program2
                    transf_fundef transf_varinfo
                    p1
                  =
                  OK p2 /\
                  make_program s M2 L = OK p2.
  Proof.
    unfold make_program. intros.
    inv_monad H0.
    subst.
    apply add_prog_defs_map in H4. simpl in H4.
    destruct H4 as [? [? MAP]]; subst.
    apply get_globdef_transf_globdefs in MAP.
    destruct MAP as [? [MAP TRANSF]].
    apply map_add_prog_defs with (ld := nil) in MAP.
    rewrite MAP; clear MAP.
    unfold transform_partial_program2.
    simpl.
    rewrite TRANSF.
    simpl.
    unfold eassert.
    destruct (decide (valid_program s M2 L)); try contradiction.
    monad_norm. eauto.
  Qed.

  Theorem make_program_transf_partial2:
    forall s p1,
      make_program s M1 L = OK p1 ->
      exists p2,
        transform_partial_program2
          transf_fundef transf_varinfo
          p1
        =
        OK p2 /\
        make_program s M2 L = OK p2.
  Proof.
    intros.
    apply unsafe_make_program_transform_partial2; eauto.
    apply valid_program_ok with M1.
    * assumption.
    * assumption.
    * unfold make_program in H. inv_monad H. assumption.
  Qed.

  Hypotheses (transf_layer_primitives_recip:
                forall i s,
                  get_layer_primitive i L = OK (Some s) ->
                  isOK (make_external (ProgramFormatOps := pf_ops') i s) ->
                  isOK (make_external (ProgramFormatOps := pf_ops) i s))
             (transf_module_function_error:
                forall i,
                  isError (get_module_function i M1) ->
                  isError (get_module_function i M2))
             (transf_module_functions_make_internal_error :
                forall (i : ident) (f1 : Fm),
                  get_module_function i M1 = OK (Some f1) ->
                  forall f2,
                    get_module_function i M2 = OK (Some f2) ->
                    isError (make_internal f1) ->
                    isError (make_internal f2)).

  Theorem make_program_transf_partial2_ok_recip:
    forall s,
      isOK (make_program s M2 L) ->
      isOK (make_program s M1 L).
  Proof.
    apply make_program_ok.
    * assumption.
    * unfold isOK. destruct 2.
      destruct (get_module_function i M1) as [ [ | ] | ] eqn:Hfunc.
      {
        exploit transf_module_functions; eauto. destruct 1 as (? & ? & ?).
        destruct (make_internal f) eqn:HMAKE1.
        {
          exploit transf_fundef_internal_complete; eauto. 
        }
        exploit transf_module_functions_make_internal_error; eauto.
        {
          rewrite HMAKE1. esplit; eauto.
        }
        destruct 1. congruence.
      }
      {
        exploit transf_module_function_none; eauto.
        congruence.
      }
      {
        generalize (transf_module_function_error i). rewrite Hfunc.
        unfold isError. intro K. exploit K; eauto.
        destruct 1. congruence.
      }
    * intro.
      destruct (get_module_function i M1) as [ [ | ] | ] eqn:Hfunc; eauto.
      {
        exploit transf_module_functions; eauto. destruct 1 as (? & ? & ?).
        congruence.
      }
      {
        generalize (transf_module_function_error i). rewrite Hfunc.
        unfold isError. intro K. exploit K; eauto.
        destruct 1. congruence.
      }
    * auto.
  Qed.
  
(*
  Lemma transf_module_no_magic:
    ptree_forall (fun _ a => a <> magic) (let (Mt, _) := M2 in Mt).
  Proof.
    intro. intros.
    destruct (ptree_module_get M1 i) eqn:Heq.
    destruct n.
    + (* function *)
      apply transf_module_functions in Heq.
      destruct Heq as [? [? Heq2]].
      unfold ptree_module_get in Heq2.
      destruct M2; congruence.
    + (* variable *)
      apply transf_module_variables in Heq.
      unfold ptree_module_get in Heq.
      destruct M2; congruence.
    + (* magic *)
      destruct (M1_no_magic i magic).
      unfold ptree_module_get in Heq.
      destruct M1; congruence.
      reflexivity.
    + (* none *)
      apply transf_module_none in Heq.
      unfold ptree_module_get in Heq.
      destruct M2; congruence.
  Qed.

  Lemma transf_module_no_volatile
        (M1_no_volatile: ptree_forall (fun _ d => nzdef_volatile d = false) (let (Mt, _) := M1 in Mt)):
    ptree_forall (fun _ d => nzdef_volatile d = false) (let (Mt, _) := M2 in Mt).
  Proof.
    intro. intros a Ha.
    destruct (ptree_module_get M1 i) as [n | ] eqn:?.
    destruct n.
    + (** function *)
      apply transf_module_functions in Heqo.
      destruct Heqo as [f2 [? Hf2]].
      unfold ptree_module_get in Hf2.
      destruct M2.
      rewrite Ha in Hf2. inv Hf2.
      reflexivity.
    + (** variable *)
      exploit transf_module_variables; eauto.
      unfold ptree_module_get.
      destruct M2.
      rewrite Ha.
      intro Heqo'. inv Heqo'.
      apply (M1_no_volatile i (variable v)).
      unfold ptree_module_get in Heqo.
      destruct M1; assumption.
    + (** magic *)
      destruct (M1_no_magic i magic).
      unfold ptree_module_get in Heqo.
      destruct M1; assumption.
      reflexivity.
    + (** none *)
      apply transf_module_none in Heqo.
      unfold ptree_module_get in Heqo.
      destruct M2; congruence.
  Qed.

  End WITHNOMAGIC.

  Lemma transf_module_disjoint
        (L_M1_disjoint: ptree_disjoint L (let (Mt, _) := M1 in Mt)):
    ptree_disjoint L (let (Mt, _) := M2 in Mt).
  Proof.
    intro. intros.
    exploit L_M1_disjoint. eassumption.
    intro.
    exploit (transf_module_none i).
     unfold ptree_module_get. destruct M1; assumption.
    unfold ptree_module_get. destruct M2; tauto.
  Qed.

  Lemma transf_module_in_stencil
        s
        (M1_in_s: ptree_forall (fun i _ => In i (stencil_ids s)) (let (Mt, _) := M1 in Mt)):
    ptree_forall (fun i _ => In i (stencil_ids s)) (let (Mt, _) := M2 in Mt).
  Proof.
    intro.
    intros.
    destruct (ptree_module_get M1 i) as [n | ] eqn:Heqo.
     eapply M1_in_s.
     instantiate (1 := n).
     unfold ptree_module_get in Heqo.
     destruct M1; assumption.
    apply transf_module_none in Heqo.
    unfold ptree_module_get in Heqo.
    destruct M2; congruence.
  Qed.
      
  Theorem make_program_transform_partial2:
    forall s p1
           (MAKE: make_program s M1 L = ret p1),
      exists p2,
        transform_partial_program2
          transf_fundef transf_varinfo
          p1 = OK p2 /\
        make_program s M2 L = ret p2.
  Proof.
    unfold make_program.
    intros.
    inv_monad MAKE.
    repeat autorewrite_assert.
    repeat spawn_assert.
    simpl.
    subst.
    rewrite unsafe_make_program_transform_partial2; now eauto.
    + eapply transf_module_disjoint; eauto.
    + eapply transf_module_in_stencil; eauto.
    + eapply transf_module_no_magic; eauto.
    + eapply transf_module_no_volatile; eauto.
  Qed.
*)

End WITH2MAKEFUNDEFOPS.
