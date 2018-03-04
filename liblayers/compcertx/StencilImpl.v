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
Require Import compcert.lib.Maps.
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.Decision.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.logic.PTrees.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Layers.
Require Import liblayers.compcertx.CompcertStructures.
Require Export liblayers.compcertx.Stencil.
Require Export liblayers.compcertx.ErrorMonad.

Require Import ProofIrrelevance.

(** Missing lemma from Globalenv. *)

Module Genv.
Export Globalenvs.Genv.

Theorem find_var_info_inversion:
  forall F V,
  forall (p: _ F V) b v,
    find_var_info (globalenv p) b = Some v ->
  exists id, In (id, Some (Gvar v)) (prog_defs p).
Proof.
  intros until v. unfold globalenv. apply add_globals_preserves. 
(* preserves *)
  unfold find_var_info; simpl; intros. destruct g; auto. 
  destruct g; auto.
  rewrite PTree.gsspec in H1. destruct (peq b (genv_next ge)).
  inv H1. exists id; auto.
  auto.
(* base *)
  unfold find_var_info; simpl; intros. rewrite PTree.gempty in H. discriminate.
Qed.

End Genv.

(** A stencil is a "program with declarations but without
definitions", i.e. a mere list of identifiers.  We will impose this
list to have no duplicates, which will allow us to use
Genv.find_symbol_exists.

The stencil itself is not implemented in terms of PTree, but in terms
of CompCert program. However, properties on [make_program] will
actually depend on the fact that layers and modules are defined based
on PTree. Hence the name of this library.
 *)

Record stencil: Type :=
  {
    stencil_ids: list ident;
    stencil_ids_norepet: list_norepet stencil_ids
  }.

Definition program_of_stencil (s: stencil): AST.program unit unit :=
  {|
    prog_defs := List.map (fun i => (i, None)) (stencil_ids s);
    prog_main := xH (* we do not really care here *)
  |}.

Definition globalenv_of_stencil (s: stencil): Genv.t unit unit :=
  Genv.globalenv (program_of_stencil s).

Global Instance ptree_stencil_ops: StencilOps stencil :=
  {|
    find_symbol s := Genv.find_symbol (globalenv_of_stencil s);
    genv_next s   := Genv.genv_next (globalenv_of_stencil s)
  |}.

Lemma stencil_ids_prog_names :
  forall s,
    prog_defs_names (program_of_stencil s) = stencil_ids s.
Proof.
  unfold program_of_stencil, prog_defs_names; simpl. intro.
  rewrite list_map_compose.
  simpl.
  apply list_map_identity.
Qed.

Lemma stencil_matches_globalenv_of_stencil:
  forall s, stencil_matches s (globalenv_of_stencil s).
Proof.
  constructor.
  reflexivity.
  reflexivity.
  intros. unfold Events.block_is_volatile.
  case_eq (Genv.find_var_info (globalenv_of_stencil s) b); try reflexivity.
  unfold globalenv_of_stencil; intros. exfalso.
  exploit Genv.find_var_info_inversion; eauto.
  destruct 1.
  simpl in H0.
  apply list_in_map_inv in H0.
  destruct H0 as [? [? ?]].
  discriminate.
Qed.

(** Extensionality properties of stencils (use proof irrelevance). *)

Fixpoint find_symbol_of_list (l: list ident) (i: ident) (res: option Values.block) (b: Values.block) {struct l} : option Values.block :=
  match l with
    | nil => res
    | i' :: l' => find_symbol_of_list l' i (if peq i i' then Some b else res) (Psucc b)
  end.

Lemma find_symbol_of_list_correct:
  forall {F V: Type} l (ge: _ F V) i,
    find_symbol_of_list (List.map fst l) i (Genv.find_symbol ge i) (Genv.genv_next ge) =
    Genv.find_symbol (Genv.add_globals ge l) i.
Proof.
  induction l.
   reflexivity.
  intros.
  change (Genv.add_globals ge (a :: l)) with (Genv.add_globals (Genv.add_global ge a) l).
  rewrite <- IHl. clear IHl.
  simpl.
  destruct (peq i (fst a)).
   subst. unfold Genv.add_global, Genv.find_symbol. simpl. rewrite PTree.gss. reflexivity.
   unfold Genv.add_global, Genv.find_symbol. simpl. rewrite PTree.gso. reflexivity.
  assumption.
Qed.

Lemma find_symbol_of_list_not_in:
  forall l i,
    ~ In i l ->
    forall res b,
    find_symbol_of_list l i res b = res.
Proof.
  induction l; simpl.
   reflexivity.
  intros. destruct (peq i a).
   subst. destruct H. auto.
  apply IHl. tauto.
Qed.

Lemma find_symbol_of_list_cons_not_in:
  forall l i,
    ~ In i l ->
    forall res b,
      find_symbol_of_list (i :: l) i res b = Some b.
Proof.
  simpl.
  intros.
  rewrite peq_true.
  apply find_symbol_of_list_not_in.
  assumption.
Qed.

Lemma find_symbol_of_list_le:
  forall l,
    list_norepet l ->
    forall i b,
    forall b', find_symbol_of_list l i None b = Some b' ->
               Ple b b'.
Proof.
  induction l; simpl.
   discriminate.
  intros. inv H. destruct (peq i a).
   subst. erewrite find_symbol_of_list_not_in in H0; eauto. inv H0. xomega.
  eapply Ple_trans.
  2: eapply IHl; eauto.
  xomega.
Qed.

Lemma find_symbol_of_list_lt:
  forall l i j r',
    j <> i ->
    list_norepet (i :: l) ->
    forall b,
    (find_symbol_of_list (i :: l) j None b) = Some r' ->
    Plt b r'.
Proof.
  simpl.
  intros.
  inv H0.
  destruct (peq j i).
   contradiction.
  generalize (find_symbol_of_list_le _ H5 _ _ _ H1).
  intro. xomega.
Qed.

Lemma find_symbol_of_list_cons:
  forall a1 l1,
    list_norepet (a1 :: l1) ->
    forall a2 l2,
      list_norepet (a2 :: l2) ->
      forall b,
    (forall i, find_symbol_of_list (a1 :: l1) i None b =
               find_symbol_of_list (a2 :: l2) i None b) ->
  a1 = a2.
Proof.
  intros.
  destruct (peq a1 a2).
   assumption.
  exfalso.  
  generalize (find_symbol_of_list_lt _ _ _ b n H0 b).  
  rewrite <- H1.
  inv H.
  rewrite find_symbol_of_list_cons_not_in; auto.
  intros. edestruct Plt_irrefl. apply H. reflexivity.
Qed.    

Lemma find_symbol_of_list_ext:
  forall l1 l2 b,         
    (forall i, find_symbol_of_list l1 i None b = find_symbol_of_list l2 i None b) ->
    list_norepet l1 ->
    list_norepet l2 ->
    length l1 = length l2 ->
    l1 = l2.
Proof.
  induction l1; destruct l2; try discriminate.
  - reflexivity.
  - intros.
    inv H2.
    assert (a = i) by (eapply find_symbol_of_list_cons; eauto).
    subst. f_equal.
    inv H1. inv H0.
    eapply IHl1; eauto.
    instantiate (1 := Pos.succ b).
    intros.
    generalize (H i0).
    simpl.
    destruct (peq i0 i).
     subst. intros. erewrite find_symbol_of_list_not_in; eauto.  erewrite find_symbol_of_list_not_in; eauto.
    eauto.
Qed.

Lemma advance_next_length_le:
  forall {F1 V1 F2 V2} (l1: list (ident * option (globdef F1 V1))) (l2: list (ident * option (globdef F2 V2))) b,
    Genv.advance_next l1 b = Genv.advance_next l2 b ->
    (length l1 <= length l2)%nat.
Proof.
  induction l1; simpl.
   intros; omega.
  destruct l2.
   simpl. intros. exfalso. 
   generalize (Genv.advance_next_le l1 (Pos.succ b)).
   rewrite H.
   intro.
   xomega.
   simpl.
   intros.
   generalize (IHl1 _ _ H).
   intro; omega.
Qed.

Lemma advance_next_length:
  forall {F1 V1 F2 V2} (l1: list (ident * option (globdef F1 V1))) (l2: list (ident * option (globdef F2 V2))) b,
    Genv.advance_next l1 b = Genv.advance_next l2 b ->
    length l1 = length l2.
Proof.
  intros.
  generalize (advance_next_length_le _ _ _ H).
  symmetry in H.
  generalize (advance_next_length_le _ _ _ H).
  omega.
Qed.   

Theorem stencil_ext:
  forall s1 s2,
    (forall i, find_symbol s1 i = find_symbol s2 i) ->
    (genv_next s1 = genv_next s2) ->
    s1 = s2.
Proof.
  destruct s1.
  destruct s2.
  simpl.
  unfold globalenv_of_stencil, program_of_stencil, Genv.globalenv.
  simpl.
  intros.
  cut (stencil_ids0 = stencil_ids1).
   intros. subst. f_equal. apply proof_irrelevance.
  rewrite Genv.genv_next_add_globals in H0.
  rewrite Genv.genv_next_add_globals in H0.
  apply advance_next_length in H0.
  rewrite map_length in H0.
  rewrite map_length in H0.
  eapply find_symbol_of_list_ext; eauto.
  instantiate (1 := Genv.genv_next (Genv.empty_genv unit unit)).
  intros.
  replace (@None Values.block) with (Genv.find_symbol (Genv.empty_genv unit unit) i) by (simpl; apply PTree.gempty).
  replace stencil_ids0 with (map fst (map (fun i => (i, (@None (globdef unit unit)))) stencil_ids0)).
  replace stencil_ids1 with (map fst (map (fun i => (i, (@None (globdef unit unit)))) stencil_ids1)).
  rewrite find_symbol_of_list_correct.
  rewrite find_symbol_of_list_correct.
  auto.
  rewrite list_map_compose. simpl. apply list_map_identity.
  rewrite list_map_compose. simpl. apply list_map_identity.
Qed.  

Corollary stencil_matches_unique :
  forall {F V} (ge: _ F V) s1 s2,
    stencil_matches s1 ge ->
    stencil_matches s2 ge ->
    s1 = s2.
Proof.
  intros.
  inv H. inv H0.
  apply stencil_ext.
   intro. etransitivity. symmetry. eapply stencil_matches_symbols. auto.
  congruence.
Qed.

Global Instance ptree_stencil_prf: Stencil stencil :=
  {|
    genv_symb_range s := Genv.genv_symb_range (globalenv_of_stencil s);
    genv_vars_inj s := Genv.genv_vars_inj (globalenv_of_stencil s);
    stencil_matches_unique := @stencil_matches_unique
  |}.

(** The following will be used for the soundness theorem: given a
    context, how to create a stencil. *)

(** XXX how about the symbols in the low layer? Or is this supposed to
  be the whole concatenated thing already? --jk *)

Definition stencil_of_program
           (F V: Type)
        (p: program F V)
        (Hnorepet: list_norepet (prog_defs_names p))
:
  stencil :=
{|
  stencil_ids := _;
  stencil_ids_norepet := Hnorepet
|}.
Arguments stencil_of_program [_ _] _ _.

Lemma stencil_of_program_symbols:
  forall
    F V (p: _ F V)
    Hnorepet,
    (forall i, find_symbol (stencil_of_program p Hnorepet) i = Genv.find_symbol (Genv.globalenv p) i) /\
    genv_next (stencil_of_program p Hnorepet) = Genv.genv_next (Genv.globalenv p).
Proof.
  intros.
  destruct p; simpl in *. unfold globalenv_of_stencil, stencil_of_program, Genv.globalenv, prog_defs_names in *. simpl in *.
   rewrite list_map_compose. simpl.
   clear Hnorepet.
   assert (H: forall i, Genv.find_symbol (Genv.empty_genv unit unit) i = Genv.find_symbol (Genv.empty_genv F V) i) by reflexivity.
   revert H.   
   assert (H: Genv.genv_next (Genv.empty_genv unit unit) = Genv.genv_next (Genv.empty_genv F V)) by reflexivity.
   revert H.
   generalize (Genv.empty_genv F V). generalize (Genv.empty_genv unit unit).
   induction prog_defs; simpl.
    tauto.
   intros.
   apply IHprog_defs.
   unfold Genv.add_global, Genv.find_symbol in *; simpl.
   congruence.
   unfold Genv.add_global, Genv.find_symbol in *; simpl.
   intro.
   destruct (peq i (fst a)).
    subst. repeat rewrite PTree.gss. congruence.
   repeat rewrite PTree.gso; eauto.
Qed.

Theorem stencil_of_program_matches:
  forall
    F V (p: _ F _)
    (Hno_volatile: forall i (v: V) ini ro, ~ In (i, Some (Gvar (mkglobvar v ini ro true))) (prog_defs p))
    Hnorepet,
      stencil_matches (stencil_of_program p Hnorepet) (Genv.globalenv p).
Proof.
  intros.
  destruct (stencil_of_program_symbols _ _ _ Hnorepet).
  constructor; eauto.
  unfold Events.block_is_volatile.
  intro.
  destruct (Genv.find_var_info (Genv.globalenv p) b) eqn:?; try reflexivity.
  exploit Genv.find_var_info_inversion; eauto.
  destruct 1 as [? ?].
  destruct g; simpl in *.
  destruct gvar_volatile; try reflexivity.
  edestruct Hno_volatile. eassumption.
Qed.
