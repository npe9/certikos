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
Require Import Relations.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcertx.common.MemoryX.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.LogicalRelations.
Require Import liblayers.logic.OptionOrders.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Observation.

(** Properties of initial memory. *)

(** It is true that we need an order on global definitions. 
    We import it from [MakeProgramImpl].
*)

  (** To express the monotonicity of [add_prog_defs], we will need the
    following order on lists of definitions. *)

(** This is not the same relation as for [add_prog_defs], because we
allow functions to be replaced with other functions. *)

(** NOTE: we could make the type of functions change, but here we do
not care because we only consider initial memory in one kind of
machine, namely LAsm. *)

Inductive def_le {F V: Type}:
  relation (globdef F V) :=
  | def_le_fun:
      Proper
        (rel_top ++> def_le)
        (@Gfun F V)
  | def_le_var:
      Proper
        (eq ++> def_le)
        (@Gvar F V)
  .

Global Existing Instance def_le_fun.
Global Existing Instance def_le_var.

Definition prog_defs_le {F V: Type}: relation (list (ident * option (globdef F V))) :=
  list_rel (eq * option_le def_le).

Module Genv.
Export Globalenvs.Genv.

Section WITHMEM.
Context `{Hmem: Mem.MemoryModelX}.

Theorem initmem_inject_neutral:
  forall {F V: Type},
  forall (p: _ F V) m,
    init_mem p = Some m ->
    Mem.inject_neutral (Mem.nextblock m) m.
Proof.
  intros.
  eapply alloc_globals_neutral; eauto. 
  intros. exploit find_symbol_not_fresh; eauto.
  eassumption.
  apply Mem.empty_inject_neutral.
  apply Ple_refl.
Qed.

(** Proving that the initial memory of a program extends to the
initial memory of a more defined program. *)

Lemma store_zeros_right_extends:
  forall m2 b lo hi m2',
    store_zeros m2 b lo hi = Some m2' ->
    forall m1, Mem.extends m1 m2 ->
               (forall o k p, Mem.perm m1 b o k p -> False) ->
               Mem.extends m1 m2'.
Proof.
  intros until hi.
  functional induction (store_zeros m2 b lo hi); try congruence.
  intros. eapply IHo; eauto using Mem.store_outside_extends.
Qed.

Lemma store_init_data_right_extends:
  forall {F V} (ge: _ F V)
         i m2 b o m2',
    store_init_data ge m2 b o i = Some m2' ->
    forall m1, Mem.extends m1 m2 ->
               (forall o k p, Mem.perm m1 b o k p -> False) ->
               Mem.extends m1 m2'.
Proof.
  destruct i; simpl; try congruence; eauto using Mem.store_outside_extends.
  destruct (find_symbol ge i); try discriminate.
  eauto using Mem.store_outside_extends.
Qed.

Lemma store_init_data_list_right_extends:
  forall {F V} (ge: _ F V)
         l m2 b o m2',
    store_init_data_list ge m2 b o l = Some m2' ->
    forall m1, Mem.extends m1 m2 ->
               (forall o k p, Mem.perm m1 b o k p -> False) ->
               Mem.extends m1 m2'.
Proof.
  induction l; simpl; try congruence.
  intros until o.
  destruct (store_init_data ge m2 b o a) eqn:?; try discriminate.
  eauto using store_init_data_right_extends.
Qed.

Lemma init_data_size_nonnegative a:
  0 <= init_data_size a.
Proof.
  destruct a; simpl; try omega.
  apply Z.le_max_r.
Qed.

Lemma init_data_list_size_nonnegative l:
  0 <= init_data_list_size l.
Proof.
  induction l; simpl.
   omega.
  generalize (init_data_size_nonnegative a); omega.
Qed.

Lemma store_zeros_parallel_extends:
  forall m1 b lo hi m1',
    store_zeros m1 b lo hi = Some m1' ->
    forall m2, Mem.extends m1 m2 ->
               exists m2',
                 store_zeros m2 b lo hi = Some m2' /\
                 Mem.extends m1' m2'.
Proof.
  intros until hi.
  functional induction (store_zeros m1 b lo hi); try congruence.
  * intros. inv H. rewrite store_zeros_equation. rewrite e. eauto.
  * intros.
    exploit Mem.store_within_extends; eauto.
    destruct 1 as [? [STORE ?]].
    rewrite store_zeros_equation.
    rewrite e.
    rewrite STORE.
    eauto.
Qed.

Lemma store_init_data_parallel_extends:
  forall {F V} (ge: _ F V)
         i m1 b o m1',
    store_init_data ge m1 b o i = Some m1' ->
    forall m2, Mem.extends m1 m2 ->
               exists m2',
                 store_init_data ge m2 b o i = Some m2' /\
                 Mem.extends m1' m2'.
Proof.
  destruct i; simpl; try congruence; intros; eauto using Mem.store_within_extends.
  * inv H. eauto.
  * destruct (find_symbol ge i); try discriminate.
    eauto using Mem.store_within_extends.
Qed.

Lemma store_init_data_list_parallel_extends:
  forall {F V} (ge: _ F V)
         l m1 b o m1',
    store_init_data_list ge m1 b o l = Some m1' ->
    forall m2, Mem.extends m1 m2 ->
               exists m2',
                 store_init_data_list ge m2 b o l = Some m2' /\
                 Mem.extends m1' m2'.
Proof.
  induction l; simpl.
  * injection 3; intros; subst; eauto.
  * intros until m1'.
    destruct (store_init_data ge m1 b o a) eqn:?; try discriminate.
    intros.
    exploit (store_init_data_parallel_extends (F := F) (V := V)); eauto.
    destruct 1 as [? [STORE ?]].
    rewrite STORE.
    eauto.
Qed.

Lemma store_init_data_symbols_preserved:
  forall {F1 V1 F2 V2} (ge1: _ F1 V1) (ge2: _ F2 V2),
    (forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i) ->
    forall m b o i,
      store_init_data ge2 m b o i = store_init_data ge1 m b o i.
Proof.
  destruct i; try reflexivity.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma store_init_data_list_symbols_preserved:
  forall {F1 V1 F2 V2} (ge1: _ F1 V1) (ge2: _ F2 V2),
    (forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i) ->
    forall l m b o,
      store_init_data_list ge2 m b o l = store_init_data_list ge1 m b o l.
Proof.
  induction l; simpl; try reflexivity.
  intros.
  erewrite store_init_data_symbols_preserved; eauto.
  destruct (store_init_data ge1 m b o a); congruence.
Qed.

  Lemma alloc_global_extends:
  forall {F V: Type},
  forall (ge1 ge2: _ F V),
  forall SYMB: forall i', find_symbol ge2 i' = find_symbol ge1 i',
    forall m1 m2,
      Mem.extends m1 m2 ->
      forall d1 d2,
      option_le def_le d1 d2 ->
      forall i m'1, 
        alloc_global ge1 m1 (i, d1) = Some m'1 ->
        forall m'2, 
        alloc_global ge2 m2 (i, d2) = Some m'2 ->
        Mem.extends m'1 m'2.
  Proof.
    unfold alloc_global.
    inversion 3; subst.
    * (* none *)
      destruct (Mem.alloc m1 0 0) eqn:Halloc1.
      intros until m'1. intro Heq. inv Heq.
      assert (NO_PERM: forall o k p, Mem.perm m'1 b o k p -> False).
      {
       intros until p. intro PERM.
       generalize (Mem.perm_alloc_3 _ _ _ _ _ Halloc1 _ _ _ PERM).
       omega.
      }
      destruct d2 as [ [ | ] | ].
      + (* function *)
        exploit Mem.alloc_extends; eauto.
        apply Z.le_refl. instantiate (1 := 1); omega.
        destruct 1 as [m2' [Halloc2 ?]].
        rewrite Halloc2.
        intros.
        eapply Mem.drop_perm_right_extends; eauto.
      + (* variable *)
        exploit Mem.alloc_extends; eauto.
        apply Z.le_refl. instantiate (1 := init_data_list_size (gvar_init v)); eauto using init_data_list_size_nonnegative.
        destruct 1 as [m'2_1 [Halloc2 ?]].
        rewrite Halloc2. 
        intros m'2.
        destruct (store_zeros m'2_1 b 0 (init_data_list_size (gvar_init v))) as [ m'2_2 | ] eqn:Hstorezeros; try discriminate.
        destruct (store_init_data_list ge2 m'2_2 b 0 (gvar_init v)) as [ m'2_3 | ] eqn:Hstoreinit; try discriminate.
        intro Hdrop.
        eapply Mem.drop_perm_right_extends.
        eapply store_init_data_list_right_extends; eauto.
        eapply store_zeros_right_extends; eauto.
        eassumption.
        eauto.
      + (* none *)
        exploit Mem.alloc_extends; eauto.
        apply Z.le_refl. apply Z.le_refl.
        destruct 1 as [m2' [Halloc2 ?]].
        rewrite Halloc2.
        congruence.
    * (* some *)
      inv H1.
      + (* function *)
        destruct (Mem.alloc m1 0 1) eqn:Halloc1.
        exploit Mem.alloc_extends; eauto.
        apply Z.le_refl. apply Z.le_refl.
        destruct 1 as [m2' [Halloc2 ?]].
        rewrite Halloc2.
        intros.
        exploit Mem.drop_perm_parallel_extends; eauto.
        destruct 1 as [? [? ?]]; congruence.
      + (* variable *)
        destruct (Mem.alloc m1 0 (init_data_list_size (gvar_init y0))) as [m1'_1 b] eqn:Halloc1.
        exploit Mem.alloc_extends; eauto.
        apply Z.le_refl. apply Z.le_refl.
        destruct 1 as [m2'_1 [Halloc2 ?]].
        rewrite Halloc2.
        destruct (store_zeros m1'_1 b 0 (init_data_list_size (gvar_init y0))) as [m1'_2 | ] eqn:Hstorezeros1; try discriminate.
        intros until m'1.
        destruct (store_init_data_list ge1 m1'_2 b 0 (gvar_init y0)) as [m1'_3 | ] eqn:Hstoreinit1; try discriminate.
        intro Hdrop1.
        intros until m'2.
        exploit store_zeros_parallel_extends; eauto.
        destruct 1 as [? [Hstorezeros2 ?]].
        rewrite Hstorezeros2.
        exploit @store_init_data_list_parallel_extends; eauto.
        destruct 1 as [? [Hstoreinit2 ?]].
        erewrite store_init_data_list_symbols_preserved; eauto.
        rewrite Hstoreinit2.
        exploit Mem.drop_perm_parallel_extends; eauto.
        destruct 1 as [? [Hdrop2 ?]].
        rewrite Hdrop2.
        congruence.
  Qed.

  Lemma alloc_globals_extends:
  forall {F V: Type},
  forall (ge1 ge2: _ F V),
  forall SYMB: forall i', find_symbol ge2 i' = find_symbol ge1 i',
  forall l1 l2,
    prog_defs_le l1 l2 ->
    forall m1 m2,
      Mem.extends m1 m2 ->
      forall m'1, 
        alloc_globals ge1 m1 l1 = Some m'1 ->
        forall m'2, 
        alloc_globals ge2 m2 l2 = Some m'2 ->
        Mem.extends m'1 m'2.
  Proof.
    Opaque alloc_global.
    induction 2; simpl; try congruence.
    intros.
    destruct (alloc_global ge1 m1 x) eqn:?; try discriminate.
    destruct (alloc_global ge2 m2 y) eqn:?; try discriminate.
    destruct x.
    destruct y.
    inv H.
    eapply IHlist_rel.
    eapply alloc_global_extends; eauto.
    assumption.
    assumption.
  Qed.

  Lemma add_globals_le_symbols_preserved:
    forall {F V: Type},
    forall l1 l2, prog_defs_le l1 l2 ->
                  forall (ge1 ge2: _ F V),
                  forall SYMB: (forall i', find_symbol ge2 i' = find_symbol ge1 i') /\ genv_next ge2 = genv_next ge1,
                    (forall i, Genv.find_symbol (add_globals ge2 l2) i = Genv.find_symbol (add_globals ge1 l1) i) /\ genv_next (add_globals ge2 l2) = genv_next (add_globals ge1 l1).
  Proof.
    induction 1; simpl; auto.
    intros.
    destruct SYMB as [SYMB NEXT].
    eapply IHlist_rel; eauto.
    unfold find_symbol, add_global; simpl.
    split; try congruence.
    rewrite NEXT.
    intro i'.
    do 2 rewrite PTree.gsspec.
    destruct x; destruct y; inv H.
    inv H1. simpl in *; subst.
    destruct (peq i' i0); try congruence.
    apply SYMB.
  Qed.

  Lemma globalenv_le_symbols_preserved:
    forall {F V: Type},
      forall (p1 p2: _ F V),
        prog_defs_le (prog_defs p1) (prog_defs p2) ->
        (forall i', find_symbol (globalenv p2) i' = find_symbol (globalenv p1) i') /\
        genv_next (globalenv p2) = genv_next (globalenv p1).
  Proof.
    intros.
    apply add_globals_le_symbols_preserved; auto.
  Qed.

  Lemma init_mem_le_extends:
  forall {F V: Type},
  forall (p1 p2: _ F V),
    prog_defs_le (prog_defs p1) (prog_defs p2) ->
    forall m'1, 
      init_mem p1 = Some m'1 ->
      forall m'2,
        init_mem p2 = Some m'2 ->
        Mem.extends m'1 m'2.
  Proof.
    intros.
    eapply alloc_globals_extends.
    eapply globalenv_le_symbols_preserved; eauto.
    eassumption.
    eapply Mem.extends_refl.
    eassumption.
    eassumption.
  Qed.

  Corollary init_mem_le_genv_next:
    forall {F V: Type},
    forall (p1 p2: _ F V),
      prog_defs_le (prog_defs p1) (prog_defs p2) ->
      forall m'1, 
        init_mem p1 = Some m'1 ->
        forall m'2,
          init_mem p2 = Some m'2 ->
          Mem.nextblock m'2 = Mem.nextblock m'1.
  Proof.
    intros.
    symmetry.
    apply Mem.mext_next.
    eauto using init_mem_le_extends.
  Qed.

  Corollary init_mem_le_inject:
    forall {F V: Type},
    forall (p1 p2: _ F V),
      prog_defs_le (prog_defs p1) (prog_defs p2) ->
      forall m'1, 
        init_mem p1 = Some m'1 ->
        forall m'2,
          init_mem p2 = Some m'2 ->
          Mem.inject (Mem.flat_inj (Mem.nextblock m'1)) m'1 m'2.
  Proof.
    intros.
    eapply Mem.inject_extends_compose.
    eapply initmem_inject; eauto.
    eauto using init_mem_le_extends.
  Qed.

(** Proving that there are no permissions for blocks associated to no
function or variable. *)

Definition none_symbols_no_perm {F V} (g: _ F V) (m: mem) :=
  forall i b,
    find_symbol g i = Some b ->
    find_funct_ptr g b = None ->
    find_var_info g b = None ->
    forall o k p,
      Mem.perm m b o k p -> False.
  
Lemma alloc_global_genv_next':
  forall {F V},
  forall (ge0 ge: _ F V) m id g m',
  genv_next ge = Mem.nextblock m ->
  alloc_global ge0 m (id, g) = Some m' ->
  genv_next (add_global ge (id, g)) = Mem.nextblock m'.
Proof.
  intros.
  simpl.
  erewrite alloc_global_nextblock; eauto.
  congruence.
Qed.

Lemma alloc_global_no_perm:
  forall {F V},
  forall (ge0 ge: _ F V) m id g m',
  genv_next ge = Mem.nextblock m ->
  alloc_global ge0 m (id, g) = Some m' ->
  none_symbols_no_perm ge m ->
  none_symbols_no_perm (add_global ge (id, g)) m'.
Proof.
  intros. 
  exploit alloc_global_nextblock; eauto. intros NB.
  destruct g as [[f|v]|].
  * (* function *)
    red; intros.
    Transparent alloc_global.
    unfold alloc_global in H0.
    unfold find_var_info in H4. simpl in H4. 
    unfold find_funct_ptr in H3. simpl in H3.
    unfold find_symbol in H2. simpl in H2.
    rewrite PTree.gsspec in H2.
    destruct (peq i id).
  + subst. inv H2.
    rewrite PTree.gss in H3.
    discriminate.
  + exploit genv_symb_range; eauto.
    intro.
    rewrite PTree.gso in H3; eauto using Plt_ne.
    rewrite H in H6.
    destruct (Mem.alloc m 0 1) eqn:?.
    generalize (Mem.alloc_result _ _ _ _ _ Heqp0).
    intro; subst.
    exploit H1; eauto.
    eapply Mem.perm_alloc_4; eauto using Plt_ne.
    eapply Mem.perm_drop_4; eauto using Plt_ne.
  * (* variable *)
    red; intros.
    Transparent alloc_global.
    unfold alloc_global in H0.
    unfold find_var_info in H4. simpl in H4. 
    unfold find_funct_ptr in H3. simpl in H3.
    unfold find_symbol in H2. simpl in H2.
    rewrite PTree.gsspec in H2.
    destruct (peq i id).
  + subst. inv H2.
    rewrite PTree.gss in H4.
    discriminate.
  + exploit genv_symb_range; eauto.
    intro.
    rewrite PTree.gso in H4; eauto using Plt_ne.
    rewrite H in H6.
    destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))) eqn:?.
    generalize (Mem.alloc_result _ _ _ _ _ Heqp0).
    intro; subst.
    destruct (store_zeros m0 (Mem.nextblock m) 0 (init_data_list_size (gvar_init v))) eqn:?; try discriminate.
    destruct (store_init_data_list ge0 m1 (Mem.nextblock m) 0 (gvar_init v)) eqn:?; try discriminate.
    exploit H1; eauto.
    eapply Mem.perm_alloc_4; eauto using Plt_ne.
    eapply store_zeros_perm; eauto.
    eapply store_init_data_list_perm; eauto.
    eapply Mem.perm_drop_4; eauto using Plt_ne.
  * (* none *)
    red; intros.
    Transparent alloc_global.
    unfold alloc_global in H0.
    unfold find_var_info in H4. simpl in H4. 
    unfold find_funct_ptr in H3. simpl in H3.
    unfold find_symbol in H2. simpl in H2.
    rewrite PTree.gsspec in H2.
    destruct (Mem.alloc m 0 0) eqn:?.
    inv H0.
    generalize (Mem.alloc_result _ _ _ _ _ Heqp0).
    intro; subst.
    destruct (peq i id).
  + subst. inv H2.
    rewrite H in H5.
    exploit Mem.perm_alloc_3; eauto.
    omega.
  + exploit genv_symb_range; eauto.
    intro.
    rewrite H in H0.
    exploit H1; eauto.
    eapply Mem.perm_alloc_4; eauto using Plt_ne.
Qed.

Lemma alloc_globals_no_perm:
  forall {F V} ge0 gl ge m m',
  genv_next ge = Mem.nextblock m ->
  alloc_globals (F := F) (V := V) ge0 m gl = Some m' ->
  none_symbols_no_perm ge m ->
  none_symbols_no_perm (add_globals ge gl) m'.
Proof.
  induction gl; simpl.
  * inversion 2; subst; eauto.
  * intros.
    destruct (alloc_global ge0 m a) eqn:?; try discriminate.
    destruct a.
    eapply IHgl; eauto using alloc_global_genv_next', alloc_global_no_perm.
Qed.

Lemma init_mem_no_perm:
  forall {F V} p m',
  init_mem (F := F) (V := V) p = Some m' ->
  none_symbols_no_perm (Genv.globalenv p) m'.
Proof.
  unfold init_mem.
  intros.
  eapply alloc_globals_no_perm; eauto.
  rewrite Mem.nextblock_empty. reflexivity.
  intro. intros. eapply Mem.perm_empty; eauto.
Qed.
  
(** Proving that the initial state always exists. *)

Lemma store_zeros_exists:
  forall m b o n,
  Mem.range_perm m b o (o + n) Cur Writable ->
  exists m', store_zeros m b o n = Some m'.
Proof.
  intros until n.
  functional induction (store_zeros m b o n); eauto.
  * intros. apply IHo0.
    unfold Mem.range_perm in *. intros.
    eapply Mem.perm_store_1; eauto.
    eapply H. omega.
  * unfold Mem.range_perm. intros.
    exfalso.
    refine (_ (Mem.valid_access_store m Mint8unsigned b p Values.Vzero _)).
    destruct 1; congruence.
    split.
     simpl. unfold Mem.range_perm. intros.  apply H. omega.
     exists p. simpl. ring.
Qed.

End WITHMEM.

Section WITHGE.

Context  {F V: Type} (ge: Genv.t F V).

Function init_data_valid (p: Z) (i: AST.init_data): bool :=
  match i with
    | Init_int8 _ => if Znumtheory.Zdivide_dec (align_chunk Mint8unsigned) p then true else false
    | Init_int16 _ => if Znumtheory.Zdivide_dec (align_chunk Mint16unsigned) p then true else false
    | Init_int32 _ => if Znumtheory.Zdivide_dec (align_chunk Mint32) p then true else false
    | Init_int64 _ => if Znumtheory.Zdivide_dec (align_chunk Mint64) p then true else false
    | Init_float32 _ => if Znumtheory.Zdivide_dec (align_chunk Mfloat32) p then true else false
    | Init_float64 _ => if Znumtheory.Zdivide_dec (align_chunk Mfloat64) p then true else false
    | Init_space _ => true
    | Init_addrof s _ =>
      match find_symbol ge s with
        | None => false
        | Some _ => if Znumtheory.Zdivide_dec (align_chunk Mint32) p then true else false
      end
  end.

Function init_data_list_valid (p: Z) (l: list AST.init_data) {struct l}: bool :=
  match l with
    | nil => true
    | a::l' =>
      if init_data_valid p a
      then init_data_list_valid (p+init_data_size a) l'
      else false
  end.

End WITHGE.

(** [init_data_valid] and [init_data_list_valid] are unchanged if symbols are preserved. *)

Section WITH2GE.

Context  {F1 V1 F2 V2: Type}
         (ge1: Genv.t F1 V1)
         (ge2: Genv.t F2 V2).

Hypothesis symbols_preserved: forall s,
  find_symbol ge1 s = find_symbol ge2 s.

Lemma init_data_valid_symbols_preserved p i:
  init_data_valid ge1 p i =
  init_data_valid ge2 p i.
Proof.
  unfold init_data_valid.
  destruct i; auto.
  rewrite symbols_preserved.
  reflexivity.
Qed.

Lemma init_data_list_valid_symbols_preserved l:
  forall p,
    init_data_list_valid ge1 p l =
    init_data_list_valid ge2 p l.
Proof.
  induction l; simpl; eauto.
  intro.
  rewrite init_data_valid_symbols_preserved.
  rewrite IHl.
  reflexivity.
Qed.

End WITH2GE.

Section WITHMEM2.
Context `{Hmem: Mem.MemoryModelX}.

Lemma store_init_data_exists:
  forall {F V} (ge: _ F V) o i,
    init_data_valid ge o i = true ->
    forall m b,
      Mem.range_perm m b o (o + init_data_size i) Cur Writable ->
      exists m', store_init_data ge m b o i = Some m'.
Proof with try (intros; eapply Mem.valid_access_store; split; auto; fail).
  functional inversion 1; subst; simpl; eauto...
  rewrite H1...
Qed.

Remark store_init_data_perm:
  forall {F V} (ge: _ F V),
  forall k prm b' q idl b m p m',
  store_init_data ge m b p idl = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros until m'.  
  assert (forall chunk v,
          Mem.store chunk m b p v = Some m' ->
          (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
    intros; split; eauto with mem. 
  destruct idl; simpl in H; eauto.
  simpl. clear. split; congruence.
  simpl. destruct (find_symbol ge i). eauto. discriminate.
Qed.

Lemma store_init_data_list_exists:
  forall {F V} (ge: _ F V) l o,
    init_data_list_valid ge o l = true ->
    forall m b,
      Mem.range_perm m b o (o + init_data_list_size l) Cur Writable ->
      exists m', store_init_data_list ge m b o l = Some m'.
Proof.
  intros until o.
  functional induction (init_data_list_valid ge o l); try discriminate; intro; simpl; eauto.
  intros.
  exploit @store_init_data_exists; eauto.
  instantiate (2 := m). instantiate (1 := b).
  unfold Mem.range_perm in *. intros. apply H0.
  generalize (init_data_list_size_nonnegative l'). omega.
  destruct 1 as [? STORE].
  rewrite STORE.
  eapply IHb; eauto.
  unfold Mem.range_perm in *. intros.
  erewrite <- store_init_data_perm; eauto.
  eapply H0.
  generalize (init_data_size_nonnegative a).
  omega.
Qed.

Lemma alloc_global_exists:
  forall {F V} (ge: _ F V),
    forall m i g,
      (match g with
         | Some (Gvar v) => init_data_list_valid ge 0 (gvar_init v) = true
         | _ => True
       end) ->
      exists m', alloc_global ge m (i, g) = Some m'.
Proof.
  destruct g as [ [ | ] | ]; simpl.
  * (* function *)
    intros _.
    destruct (Mem.alloc m 0 1) eqn:?.
    eapply Mem.range_perm_drop_2.
    intro. intros. eapply Mem.perm_alloc_2; eauto.
  * (* variable *)
    intro.
    destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))) as [m1 b] eqn:Halloc.
    generalize (Mem.perm_alloc_2 _ _ _ _ _ Halloc). intro PERM.
    exploit (store_zeros_exists m1 b 0 (init_data_list_size (gvar_init v))).
    {
      intro. intros. eapply Mem.perm_implies. eauto.
      constructor.
    }
    destruct 1 as [m2 STOREZEROS].
    rewrite STOREZEROS.
    refine (_ (store_init_data_list_exists ge (gvar_init v) 0 _ m2 b _)); eauto.
    destruct 1 as [m3 STOREINIT]. rewrite STOREINIT.
    eapply Mem.range_perm_drop_2.
    intro. intros.
    erewrite <- store_init_data_list_perm by eassumption.
    erewrite <- store_zeros_perm; eauto.
    intro. intros.
    erewrite <- store_zeros_perm by eassumption.
    eapply Mem.perm_implies. eauto.
    constructor.
  * (* none *)
    destruct (Mem.alloc m 0 0); eauto.
Qed.

Lemma alloc_globals_exists:
  forall {F V} (ge: _ F V),
    forall l,
      (forall i v, In (i, Some (Gvar v)) l -> init_data_list_valid ge 0 (gvar_init v) = true) ->
      forall m, exists m',
        alloc_globals ge m l = Some m'.
Proof.
  induction l; simpl; eauto.
  intros.
  destruct a as [i o].
  exploit (alloc_global_exists ge m i o).
   destruct o as [ [ | ] | ]; eauto.
  destruct 1 as [? ALLOC].
  rewrite ALLOC.
  eauto.
Qed.

Lemma init_mem_exists:
  forall {F V} (p: _ F V),
    (forall i v, In (i, Some (Gvar v)) (prog_defs p) ->
                 init_data_list_valid (globalenv p) 0 (gvar_init v) = true) ->
    exists m',
      init_mem p = Some m'.
Proof.
  unfold init_mem. intros.
  eapply alloc_globals_exists; eauto.
Qed.

(** Reciprocally, [init_data_list_valid] is necessary for [init_mem] to be well-defined. *)

Lemma store_init_data_valid:
  forall {F V} (ge: _ F V) o i m b m',
    store_init_data ge m b o i = Some m' ->
    init_data_valid ge o i = true.
Proof with
  try (
      match goal with
        | [ |- context [ Znumtheory.Zdivide_dec ?i ?o ] ] =>
          intros;
          destruct (Znumtheory.Zdivide_dec i o);
          try reflexivity;
          intros;
          exploit Mem.store_valid_access_3; eauto;
          destruct 1;
          contradiction
      end
    ).
  unfold store_init_data; intros until m'.
  destruct i; simpl...
  * reflexivity.
  * destruct (find_symbol ge i); try discriminate...
Qed.

Lemma store_init_data_list_valid:
  forall {F V} (ge: _ F V) l o m b m',
    store_init_data_list ge m b o l = Some m'->
    init_data_list_valid ge o l = true.
Proof.
  induction l; simpl; auto.
  intros until m'.
  destruct (store_init_data ge m b o a) eqn:STORE; try discriminate.
  erewrite store_init_data_valid; eauto.
Qed.

Lemma alloc_global_valid:
  forall {F V} (ge: _ F V),
    forall m i g m',
      alloc_global ge m (i, g) = Some m' ->
      (match g with
         | Some (Gvar v) => init_data_list_valid ge 0 (gvar_init v) = true
         | _ => True
       end).
Proof.
  unfold alloc_global.
  intros until m'.
  destruct g; auto.
  destruct g; auto.
  destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))); try discriminate.
  destruct (store_zeros m0 b 0 (init_data_list_size (gvar_init v))); try discriminate.
  destruct (store_init_data_list ge m1 b 0 (gvar_init v)) eqn:STORE; try discriminate.
  eauto using store_init_data_list_valid.
Qed.

Lemma alloc_globals_valid:
  forall {F V} (ge: _ F V),    
    forall l,
    forall m m',
      alloc_globals ge m l = Some m' ->
      (forall i v, In (i, Some (Gvar v)) l -> init_data_list_valid ge 0 (gvar_init v) = true).
Proof.
  induction l; simpl; auto.
  intros.
  destruct (alloc_global ge m a) eqn:ALLOC; try discriminate.
  destruct H0; eauto.
  subst.
  exploit @alloc_global_valid; eauto.
Qed.

Lemma init_mem_valid:
  forall {F V} (p: _ F V),
  forall m',
    init_mem p = Some m' ->
    (forall i v, In (i, Some (Gvar v)) (prog_defs p) ->
                 init_data_list_valid (globalenv p) 0 (gvar_init v) = true).
Proof.
  unfold init_mem; eauto using alloc_globals_valid.
Qed.

End WITHMEM2.

End Genv.

(** Properties of initial memory with data. *)

Section WITHMEMWITHDATA.

Context `{Hobs: ObservationOps}.
Context `{Hmem: Mem.MemoryModelX}.
Context `{Hmwd: UseMemWithData mem}.

Section WITHDATA.

Context {D: layerdata}.

Lemma store_zeros_with_data:
  forall m b o n (d: D),
    store_zeros (m, d) b o n =
    match store_zeros m b o n with
      | Some m' => Some (m', d)
      | None => None
    end.
Proof.
  intros.
  functional induction (store_zeros m b o n); intros.
  * rewrite store_zeros_equation.
    rewrite e.
    reflexivity.
  * rewrite <- IHo0; clear IHo0.
    rewrite store_zeros_equation.
    rewrite e.
    lift_unfold.
    rewrite e0.
    lens_unfold.
    reflexivity.
  * rewrite store_zeros_equation.
    rewrite e.
    lift_unfold.
    rewrite e0.
    reflexivity.
Qed.

Lemma store_init_data_with_data:
  forall {F V: Type} (ge: _ F V) m b p a (d: D),
    Genv.store_init_data ge (m, d) b p a =
    match Genv.store_init_data ge m b p a with
      | Some m' => Some (m', d)
      | None => None
    end.
Proof.
  intros.
  destruct a; simpl; try reflexivity.
  destruct (Genv.find_symbol ge i); reflexivity.
Qed.

Lemma store_init_data_list_with_data:
  forall {F V: Type} (ge: _ F V) l m b p (d: D),
    Genv.store_init_data_list ge (m, d) b p l =
    match Genv.store_init_data_list ge m b p l with
      | Some m' => Some (m', d)
      | None => None
    end.
Proof.
  induction l; simpl; try reflexivity.
  intros.
  rewrite store_init_data_with_data.
  destruct (Genv.store_init_data ge m b p a); try reflexivity.
  eauto.
Qed.

Lemma alloc_global_with_data:
  forall {F V} (ge: _ F V),
    forall m ig (d: D),
      Genv.alloc_global ge (m, d) ig =
      match Genv.alloc_global ge m ig with
        | Some m' => Some (m', d)
        | None => None
      end.
Proof.
  unfold Genv.alloc_global. intros.
  destruct ig as [? [ [ | ] | ]].
  * (* function *)
    lift_unfold.
    destruct (Mem.alloc m 0 1).
    reflexivity.
  * (* variable *)
    lift_unfold.
    destruct (Mem.alloc m 0 (Genv.init_data_list_size (gvar_init v))).
    lens_unfold.
    rewrite store_zeros_with_data.
    destruct (store_zeros m0 b 0 (Genv.init_data_list_size (gvar_init v))); try reflexivity.
    rewrite store_init_data_list_with_data.
    destruct (Genv.store_init_data_list ge m1 b 0 (gvar_init v)); reflexivity.
  * (* none *)
    lift_unfold.
    destruct (Mem.alloc m 0 0); reflexivity.
Qed.

Lemma alloc_globals_with_data:
  forall {F V} (ge: _ F V),
    forall l m (d: D),
      Genv.alloc_globals ge (m, d) l =
      match Genv.alloc_globals ge m l with
        | Some m' => Some (m', d)
        | None => None
      end.
Proof.
  induction l; simpl; try reflexivity.
  intros.
  rewrite alloc_global_with_data.
  destruct (Genv.alloc_global ge m a); try reflexivity.
  eauto.
Qed.

Theorem init_mem_with_data:
  forall {F V} (p: _ F V),
    Genv.init_mem (mem := mwd D) p =
    match Genv.init_mem (mem := mem) p with
      | Some m' => Some (m', init_data)
      | None => None
    end.
Proof.
  intros.
  unfold Genv.init_mem.
  simpl.
  apply alloc_globals_with_data.
Qed.

End WITHDATA.

(** Relation between two initial memories for different data. *)

  Theorem init_mem_le_inject_with_data:
    forall {D1 D2: layerdata},
    forall {F V: Type},
    forall (p1 p2: _ F V),
      prog_defs_le (prog_defs p1) (prog_defs p2) ->
      forall m'1 d1, 
        Genv.init_mem (mem := mwd D1) p1 = Some (m'1, d1) ->
        forall m'2 d2,
          Genv.init_mem (mem := mwd D2) p2 = Some (m'2, d2) ->
          Mem.inject (Mem.flat_inj (Mem.nextblock m'1)) m'1 m'2 /\
          d1 = init_data /\ d2 = init_data.
  Proof.
    intros.
    rewrite init_mem_with_data in H0.
    destruct (Genv.init_mem (mem := mem) p1) eqn:?; try discriminate.
    inv H0.
    rewrite init_mem_with_data in H1.
    destruct (Genv.init_mem (mem := mem) p2) eqn:?; try discriminate.
    inv H1.
    split; auto.
    eapply Genv.init_mem_le_inject; eauto.
  Qed.

End WITHMEMWITHDATA.
