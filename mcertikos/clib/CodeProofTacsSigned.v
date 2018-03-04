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
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import MemoryExtra.
Require Import EventsExtra.
Require Import Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import DataType.
Require Import ZArith.

 Hint Unfold Int.min_signed.
 Hint Unfold Int.max_signed.
 Hint Unfold Int.half_modulus.
 Hint Unfold Int.modulus.

 Lemma min_signed_lt0 : Int.min_signed < 0.
 Proof.
   repeat autounfold; simpl; omega.
 Qed.

 Lemma max_signed_gt0 : Int.max_signed > 0.
 Proof.
   repeat autounfold; simpl; omega.
 Qed.

 Lemma zdiv_range_le_le : forall a b c x: Z, a < 0 -> b > 0 -> c > 0 -> a <= x <= b -> a <= x/ c <= b.
 Proof.
   intros.
   destruct H2.
   split.
   apply Zdiv_le_lower_bound.
   omega.
   assert(a * c <= a).
   assert(- a * c >= - a).
   rewrite <- Zmult_1_r. 
   assert(c >= 1) by omega.
   apply Zmult_ge_compat_l.
   omega.
   omega.
   rewrite Zopp_mult_distr_l_reverse in H4.
   omega.
   omega.
   apply Zdiv_le_upper_bound.
   omega.
   assert(b <= b * c).
   rewrite <- Zmult_1_r at 1.
   assert(1 <= c) by omega.
   apply Zmult_le_compat_l.
   omega.
   omega.
   omega.
 Qed.

 Lemma zdiv_equiv: forall x y : Z, x >= 0 -> y > 0 -> x ÷ y = x / y.
 Proof.
   intros.
   rewrite Int.Zquot_Zdiv.
   destruct (zlt x 0).
   omega.
   trivial.
   assumption.
 Qed.

 Ltac ICS H := inversion H; clear H; subst.
 Ltac diff_ident I1 I2 := unfold I1; unfold I2; congruence.
 Ltac simpleproof := omega || trivial || reflexivity || assumption || eassumption || auto || idtac.
 Ltac solve_signed_range c x:= assert(cge0: c > 0) by omega; generalize(zdiv_range_le_le Int.min_signed Int.max_signed c (Int.signed x) min_signed_lt0 max_signed_gt0 cge0 (Int.signed_range x)); omega; clear cge0.
 Ltac unfold_cmp := simpl; repeat match goal with 
           | [|- context[Int.lt]] => unfold Int.lt
           | [|- context[Int.eq]] => rewrite eq_eq_eq'; unfold eq'
          end.

 Ltac codeproof := match goal with
      | [|- _ /\ _] => split; try(simpleproof)
      | [|- context[Int.signed (Int.repr _)]] => rewrite Int.signed_repr
      | [H: context[Int.signed (Int.repr _)] |- _] => rewrite Int.signed_repr in H
      | [|- context[Int.repr (Int.signed _)]] => rewrite Int.repr_signed
      | [H: context[Int.repr (Int.signed _)] |- _] => rewrite Int.repr_signed in H
      | [|- context [?x ÷ ?y]] => rewrite zdiv_equiv 
      | [|- Int.min_signed <= Int.signed ?x / ?c <= Int.max_signed] => solve_signed_range c x
      | [|- Int.min_signed <= Int.signed ?x / ?c] => solve_signed_range c x
      | [|- Int.signed ?x / ?c <= Int.max_signed] => solve_signed_range c x
      | [|- Int.min_signed <= ?x / ?c] => rewrite <- Int.signed_repr with (z:= x); solve_signed_range c (Int.repr x)
      | [|- ?x / ?c <= Int.max_signed] => rewrite <- Int.signed_repr with (z:= x); solve_signed_range c (Int.repr x)
      | [|- Int.min_signed <= Int.signed ?x + _] => try(generalize(Int.signed_range x); omega)
      | [|- Int.min_signed <= Int.signed ?x - _] => try(generalize(Int.signed_range x); omega)
      | [|- Int.signed ?x + _ <= Int.max_signed] => try(generalize(Int.signed_range x); omega)
      | [|- Int.signed ?x - _ <= Int.max_signed] => try(generalize(Int.signed_range x); omega)
      | [|- Int.min_signed <= ?c] => try(repeat autounfold; simpl; omega)
      | [|- ?c <= Int.max_signed] => try(repeat autounfold; simpl; omega)
      | [|- context[Int.signed Int.zero]] => change (Int.signed Int.zero) with 0
      | [H: context[Int.signed Int.zero] |- _] => change (Int.signed Int.zero) with 0 in H
      | [|- context[Int.signed Int.one]] => change (Int.signed Int.one) with 1
      | [H: context[Int.signed Int.one] |- _] => change (Int.signed Int.one) with 1 in H
      | [|- context[Int.add]] => rewrite Int.add_signed
      | [H: context[Int.add] |- _] => rewrite Int.add_signed in H
      | [|- context[Int.sub]] => rewrite Int.sub_signed
      | [H: context[Int.sub] |- _] => rewrite Int.sub_signed in H
      | [|- context[Int.mul]] => rewrite Int.mul_signed
      | [H: context [Int.mul _ _] |- _] => rewrite Int.mul_signed in H
      | [H: false = true |- _] => inversion H
      | [H: true = false |- _] => inversion H
      | [|- Some _ = Some _] => f_equal
      | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
      | [|- eval_lvalue _ _ _ _ _ _ _] => eapply eval_Evar_global
      | [|- deref_loc _ _ _ _ _] => apply deref_loc_reference
      | [|- context[Int.eq Int.zero Int.zero]] => change (Int.eq Int.zero Int.zero) with true
      | [|- context[Int.eq Int.one Int.zero]] => change (Int.eq Int.one Int.zero) with false
      | [|- context[negb true]] => change (negb true) with false
      | [|- context[negb false]] => change (negb false) with true
      | [|- forall _, _] => intro
      | [|- _ -> _] => intro
      | [|- exec_stmt _ _ _ _ (Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
      | [|- exec_stmt _ _ _ _ (if true then Ssequence _ _ else _) E0 _ _ _] => change E0 with (E0 ** E0)
      | [|- exec_stmt _ _ _ _ (if false then _ else Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
      | [|- exec_stmt _ _ _ _ _ _ _ _ _] => econstructor
      | [|- eval_expr _ _ _ _ _ _] => econstructor
      | [|- eval_exprlist _ _ _ _ _ _ _] => econstructor
      | [|- eval_funcall _ _ _ _ _ _ _] => econstructor
      | [|- external_call _ _ _ _ _ _ _] => econstructor
      | [|- context[set_opttemp]] => unfold set_opttemp
      | [|- (PTree.set ?id _ _) ! ?id = Some _] => eapply PTree.gss
      | [|- (PTree.set ?id1 _ _) ! ?id2 = Some _] => rewrite PTree.gso
      | [|- ?id1 <> ?id2] => diff_ident id1 id2
      | [|- sem_binary_operation _ _ _ _ _ _ = Some _] => unfold_cmp
      | [|- sem_cmp _ _ _ _ _ _ = Some _] => unfold sem_cmp; unfold_cmp
      | [|- sem_div _ _ _ _ = Some _] => unfold sem_div; unfold Int.divs; unfold_cmp
      | [H: context [Int.divs _ _] |- _] => unfold Int.divs in H
      | [H: context [?x ÷ ?y] |- _] => rewrite zdiv_equiv in H
      | [|- context [zlt ?z1 ?z2]] => destruct (zlt z1 z2)
      | [|- context [zeq ?z1 ?z2]] => destruct (zeq z1 z2)
      | _ => simpleproof
  end.