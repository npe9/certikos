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
(* *********************************************************************)
(*                                                                     *)
(*  Tactics for proving Clight code of the Compcert verified compiler  *)
(*                                                                     *)
(*                 Developed by Xiongnan (Newman) Wu                   *)
(*                                                                     *)
(*                         Yale University                             *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the tactics for proving the Clight code using the
    Compcert verified compiler. The main tactic codeproof is the
    verification condition generator for special Clight code. It applies
    the Bigstep operational semantics of the Clight 2 language to generate
    verification condition for a loop-free clight statement where all the
    expression can be evaluated out using the knowledge in the context,
    i.e., if the statement contains conditional statement, appropiate
    case analysis on the conditional expressions need to be applied before
    the application of the codeproof tactic so that the evaluation can go through.
    In presense of loops, the loop has to be proved separately for its
    specification and loop termination. This can be done using a saparate
    frameworks deleloped in LoopProof.v. We recommand to use the version
    of the framework with while loop with no Break, Continue, or Return
    statement in the while body, so that the proof of the loop body can
    still be automated with the codeproof tactic.

Currently we assume:
- We never take address of a local variable in the stack.
- No use of C union.

*)

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
Require Import Ctypes.
Require Import DataType.
Require Import ZArith.

 Hint Unfold Int.max_unsigned.
 Hint Unfold Int.modulus.
 Hint Unfold Int.half_modulus.

 Global Opaque PTree.get PTree.set "!" Z.land Z.lor.

 (** * Frequently used lemmas in tactics. *)

 Lemma zadd_rm_head: forall n p q, p = q -> n + p = n + q.
 Proof.
   intros.
   rewrite H.
   trivial.
 Qed.

 Lemma zadd_rm_tail: forall n p q, p = q -> p + n = q + n.
 Proof.
   intros.
   rewrite H.
   trivial.
 Qed.

 Lemma zdiv_range_le_lt : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x < b -> a <= x/ c < b.
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
   apply Zdiv_lt_upper_bound.
   omega.
   assert(b <= b * c).
   rewrite <- Zmult_1_r at 1.
   assert(1 <= c) by omega.
   apply Zmult_le_compat_l.
   omega.
   omega.
   omega.
 Qed.

 Lemma zdiv_range_le_le : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x <= b -> a <= x/ c <= b.
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

 Lemma max_unsigned_gt0: Int.max_unsigned > 0.
 Proof.
   repeat autounfold.
   simpl.
   omega.
 Qed.

 Lemma max_unsigned_val: Int.max_unsigned  = 4294967295.
 Proof.
   repeat autounfold; reflexivity.
 Qed.

 Lemma unsigned_inj : forall a b, Int.unsigned a = Int.unsigned b -> a = b.
 Proof.
   intros. rewrite <- (Int.repr_unsigned a).
   rewrite <- (Int.repr_unsigned b).
   f_equal.
   trivial.
 Qed.

 Lemma minus1lt: forall i:Z, i - 1 < i.
 Proof.
   intro.
   omega.
 Qed.

 Lemma Z_land_range_lo: forall x y, 0 <= x -> 0 <= Z.land x y.
 Proof.
   intros.
   rewrite Z.land_nonneg.
   left.
   assumption.
 Qed. 

 Lemma Z_land_range_lo_r: forall x y, 0 <= y -> 0 <= Z.land x y.
 Proof.
   intros.
   rewrite Z.land_nonneg.
   right.
   assumption.
 Qed.

 Lemma Z_land_range_hi: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> Z.land x y <= Int.max_unsigned.
 Proof.
   rewrite max_unsigned_val.
   intros.
   assert(Z.land x y < 4294967296).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.land x y) <= Z.min (Z.log2 x) (Z.log2 y)).
       apply Z.log2_land.
       omega.
       omega.
     rewrite Zmin_spec in H1.
     destruct (zlt (Z.log2 x) (Z.log2 y)).
     assert(Z.log2 x <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.   

 Lemma Z_land_range: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> 0 <= Z.land x y <= Int.max_unsigned.
 Proof.
   split.
   apply Z_land_range_lo; omega.
   apply Z_land_range_hi; omega.
 Qed.

 Lemma Z_lor_range_lo: forall x y, 0 <= x -> 0 <= y -> 0 <= Z.lor x y.
 Proof.
   intros.
   apply Z.lor_nonneg; auto.
 Qed.

 Lemma Z_lor_range_hi: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> Z.lor x y <= Int.max_unsigned.
 Proof.
   rewrite max_unsigned_val; simpl.
   intros.
   assert(Z.lor x y < 4294967296).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.lor x y) = Z.max (Z.log2 x) (Z.log2 y)).
       apply Z.log2_lor.
       omega.
       omega.
     rewrite H1.
     rewrite Zmax_spec in *.
     destruct (zlt (Z.log2 y) (Z.log2 x)).
     assert(Z.log2 x <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.

 Lemma Z_lor_range: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> 0 <= Z.lor x y <= Int.max_unsigned.
 Proof.
   intros.
   split.
   apply Z_lor_range_lo; omega.
   apply Z_lor_range_hi; omega.
 Qed.
 
 Lemma Z_lxor_range :
   forall x y,
     0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
     0 <= Z.lxor x y <= Int.max_unsigned.
 Proof.
   rewrite max_unsigned_val; simpl.
   intros.
   split.
   rewrite Z.lxor_nonneg.
   split; omega.
   assert(Z.lxor x y < 4294967296).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.lxor x y) <= Z.max (Z.log2 x) (Z.log2 y)).
       apply Z.log2_lxor.
       omega.
       omega.
     apply Z.le_lt_trans with (m := Z.max (Z.log2 x) (Z.log2 y)); auto.
     rewrite Zmax_spec in *.
     destruct (zlt (Z.log2 y) (Z.log2 x)).
     assert(Z.log2 x <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.

 Lemma Z_shiftl_16_range :
   forall x,
     0 <= x < 65536 -> 0 <= Z.shiftl x 16 <= Int.max_unsigned.
 Proof.
   unfold Int.max_unsigned. simpl (Int.modulus - 1).
   intros.
   split.
   rewrite Z.shiftl_nonneg. omega.

   assert (Z.shiftl x 16 < 4294967296).
     case_eq (zeq x 0); intros; subst.

     (* x = 0 *)
     simpl. omega.

     (* x <> 0 *)
     apply Z.log2_lt_cancel.
     rewrite Z.log2_shiftl; try omega.

     assert (Z.log2 x <= Z.log2 65535).
       apply Z.log2_le_mono. omega.
     simpl in *. omega.

   omega.
 Qed.

 (** * Auxiliary tactics used by other main tactics below. *)

 Ltac ICS H := inversion H; clear H; subst.
 Ltac Caseeq H := generalize H; apply or_ind; clear H.
 Ltac diff_ident I1 I2 := unfold I1; unfold I2; congruence.
 Ltac simpleproof := match goal with
           | [|- _ <= _] => assumption || omega || trivial || eassumption || auto || idtac
           | _ => assumption || omega || trivial || reflexivity || eassumption || auto || idtac
           end.
 Ltac solve_unsigned_range c x := assert(cge0: c > 0) by omega; assert(zlez: 0 <= 0) by omega; generalize(zdiv_range_le_le 0 Int.max_unsigned c (Int.unsigned x) zlez max_unsigned_gt0 cge0 (Int.unsigned_range_2 x)); omega; clear cge0 zlez.
 Ltac solve_unsigned_range_lt c x := assert(cge0: c > 0) by omega; assert(zlez: 0 <= 0) by omega; assert(xpre: 0 <= x < Int.max_unsigned) by omega; generalize(zdiv_range_le_lt 0 Int.max_unsigned c x zlez max_unsigned_gt0 cge0 xpre); omega; clear cge0 zlez xpre.

 Ltac unfold_cmp := simpl; repeat match goal with
           | [|- context[Int.cmpu]] => unfold Int.cmpu
           | [|- context[Int.eq]] => unfold Int.eq
           | [|- context[Int.ltu]] => unfold Int.ltu
           | [|- context[Int.add]] => unfold Int.add
           | [|- context[Int.sub]] => unfold Int.sub
           | [|- context[Int.mul]] => unfold Int.mul
           | [|- context[Int.divu]] => unfold Int.divu
           | [|- context[Int.and]] => unfold Int.and
           | [|- context[Int.or]] => unfold Int.or
           | [|- context[Int.xor]] => unfold Int.xor
           | [|- context[Int.shl]] => unfold Int.shl
           | [|- context[Int.shr]] => unfold Int.shr
           | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; try omega
           | [|- context [zle ?z1 ?z2]] => destruct (zle z1 z2); try omega
           | [|- context [zlt ?z1 ?z2]] => destruct (zlt z1 z2); try omega
           | [|- context [zeq ?z1 ?z2]] => destruct (zeq z1 z2); try omega
           | [|- 0 <= ?af <= Int.max_unsigned] => match af with
                             | Z.shiftl _ _ => simpl; omega
                             | Z.shiftr _ _ => simpl; omega
                             | Z.land ?x ?y => apply Z_land_range; try (simpl; omega)
                             | Z.lor ?x ?y => apply Z_lor_range; try (simpl; omega)
                             | _ => repeat (match goal with
                                               | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                               | _ => fail
                                            end); omega
                              end
           | _ => simpleproof
          end.

 Ltac computedivmul := match goal with
      | [|- context [?x / ?y]] => let val := eval compute in (x / y) in change (x / y) with val
      | [|- context [?x * ?y]] => let val := eval compute in (x * y) in change (x * y) with val
 end.

 (** * The tactic to prove the integers fit in unsigned integers. *)

 Ltac unsigned_range := match goal with
           | [|- _ /\ _] => split
           | [|- 0 <= _] => match goal with
                         | [|- 0 <= Int.unsigned ?i] => generalize (Int.unsigned_range i); omega
                         | [|- 0 <= Int.unsigned ?i + _] => generalize (Int.unsigned_range i); omega
                         | [|- 0 <= Int.unsigned ?i - _] => generalize (Int.unsigned_range i); omega
                         | [|- 0 <= Int.unsigned ?x / ?c] => solve_unsigned_range c x
                         | [|- 0 <= ?x / ?c] => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
                         | [|- 0 <= ?x / ?c + 1] => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
                         | [|- _] => fail 2
                         end
           | [|- _ <= Int.max_unsigned] => match goal with
                         | [|- Int.unsigned ?i <= Int.max_unsigned] => generalize (Int.unsigned_range i); omega
                         | [|- Int.unsigned ?i + _ <= Int.max_unsigned] => generalize (Int.unsigned_range i); omega
                         | [|- Int.unsigned ?i - _ <= Int.max_unsigned] => generalize (Int.unsigned_range i); omega
                         | [|- Int.unsigned ?x / ?c <= Int.max_unsigned] => solve_unsigned_range c x
                         | [|- ?x / ?c <= Int.max_unsigned] => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
                         | [|- ?x / ?c + 1 <= Int.max_unsigned] => solve_unsigned_range_lt c x
                         | [|- _] => fail 2
                         end
 end.

 (** * The tactic to automate the proof for the correctness of the function body using the new bigstep semantics for the language Clight 2. *)

 Ltac codeproof := match goal with
      | [H: Some _ = None |- _] => inversion H
      | [H: None = Some _ |- _] => inversion H
      | [H: false = true |- _] => inversion H
      | [H: true = false |- _] => inversion H
      | [|- context[alignof ?x]] => let val := eval simpl in (alignof x) in change (alignof x) with val
      | [|- context[align ?x ?y]] => let val := eval compute in (align x y) in change (align x y) with val
      | _ => idtac
      end; simpleproof; match goal with
      | [|- _ /\ _] => split
      | [|- ?x / ?y * ?c <= Int.max_unsigned] => try (computedivmul; omega)
      | [|- context[Int.and ?x Int.zero]] => change (Int.and x Int.zero) with Int.zero
      | [|- context[Int.eq Int.zero Int.zero]] => change (Int.eq Int.zero Int.zero) with true
      | [|- context[Int.eq Int.one Int.zero]] => change (Int.eq Int.one Int.zero) with false
      | [|- context[negb true]] => change (negb true) with false
      | [|- context[negb false]] => change (negb false) with true
(*
      | [|- context[Int.add]] => unfold Int.add
      | [|- context[Int.sub]] => unfold Int.sub
      | [|- context[Int.mul]] => unfold Int.mul
      | [|- context[Int.and]] => unfold Int.and
      | [|- context[Int.or]] => unfold Int.or
      | [|- context[Int.xor]] => unfold Int.xor
      | [|- context[Int.shl]] => unfold Int.shl
      | [|- context[Int.shr]] => unfold Int.shr
*)
      | [|- context[Int.unsigned Int.zero]] => change (Int.unsigned Int.zero) with 0
      | [|- context[Int.unsigned Int.one]] => change (Int.unsigned Int.one) with 1
      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; try omega
      | [|- context[Int.unsigned Int.mone]] => rewrite Int.unsigned_mone; simpl
      | [|- 0 <= ?af] => match af with
                             | Z.shiftl _ _ => simpl; omega
                             | Z.shiftr _ _ => simpl; omega
                             | Z.land ?x ?y => apply Z_land_range_lo; try (simpl; omega)
                             | Z.lor ?x ?y => apply Z_lor_range_lo; try (simpl; omega)
                             | _ => repeat (match goal with
                                               | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                               | _ => fail
                                            end); omega
                         end
      | [|- ?af <= Int.max_unsigned] => match af with
                             | Z.shiftl _ _ => simpl; omega
                             | Z.shiftr _ _ => simpl; omega
                             | Z.land ?x ?y => apply Z_land_range_hi; try (simpl; omega)
                             | Z.lor ?x ?y => apply Z_lor_range_hi; try (simpl; omega)
                             | _ => repeat (match goal with
                                               | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                               | _ => fail
                                            end); omega
                         end
      | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
      | [|- context[Int.repr (Int.unsigned _)]] => rewrite Int.repr_unsigned
      | [|- exec_stmt _ _ _ _ _ _ _ _ _] => match goal with
                 | [|- exec_stmt _ _ _ _ (Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- exec_stmt _ _ _ _ (if true then Ssequence _ _ else _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- exec_stmt _ _ _ _ (if false then _ else Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- exec_stmt _ _ _ _ (Swhile _ _) E0 _ _ _] => eassumption || fail 2
                 | [|- exec_stmt _ _ _ _ _ _ _ _ _] => econstructor
                 | _ => fail 2
                 end
      | [|- eval_expr _ _ _ _ _ _] => econstructor
      | [|- eval_exprlist _ _ _ _ _ _ _] => econstructor
      | [|- eval_funcall _ _ _ _ _ _ _] => econstructor
      | [|- external_call _ _ _ _ _ _ _] => econstructor
      | [|- assign_loc _ _ _ _ _ _] => econstructor
      | [|- context[set_opttemp]] => unfold set_opttemp
      | [|- (PTree.set ?id _ _) ! ?id = Some _] => rewrite PTree.gss
      | [|- (PTree.set ?id1 _ _) ! ?id2 = Some _] => rewrite PTree.gso
      | [|- ?id1 <> ?id2] => diff_ident id1 id2
      | [|- sem_binary_operation _ _ _ _ _ _ = Some _] => unfold_cmp
      | [|- sem_cmp _ _ _ _ _ _ = Some _] => unfold sem_cmp; unfold_cmp
      | [|- bool_val _ _ = Some _] => solve [unfold_cmp]
      | [|- sem_div _ _ _ _ = Some _] => unfold sem_div; unfold_cmp
      | [|- sem_and _ _ _ _ = Some _] => unfold sem_and; unfold_cmp
      | [|- context[Int.divu]] => unfold Int.divu
      | [|- forall _, _] => intro
      | [|- _ -> _] => intro
      | [|- Some _ = Some _] => f_equal
      | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
      | [|- eval_lvalue _ _ _ _ ?expr _ _] => match expr with
                                                  | Evar _ _ => eapply eval_Evar_global
                                                  | Ederef _ _ => eapply eval_Ederef
                                                  | Efield _ _ _ => eapply eval_Efield_struct
                                              end
      | [|- deref_loc _ _ _ _ _] => match goal with
                                | [|- deref_loc ?ty _ _ _ _] => match ty with
                                                | typeof (?var ?name ?type) => change (typeof (var name type)) with type
                                                | Tarray _ _ _ => eapply deref_loc_reference
                                                | Tfunction _ _ => eapply deref_loc_reference
                                                | Tstruct _ _ _ => eapply deref_loc_copy
                                                | Tunion _ _ _ => eapply deref_loc_copy
                                                | _ => eapply deref_loc_value
                                                end
                                | [|- _] => idtac
                                end
      | [|- access_mode _ = _] => constructor
      | [|- _] => unfold Int.cmpu, Int.eq, Int.ltu, Int.add, Int.sub, Int.mul, Int.divu, Int.and, Int.or, Int.xor, Int.shl, Int.shr
  end.

 Ltac codeproofsimpl := match goal with
      | [H: Some _ = None |- _] => inversion H
      | [H: None = Some _ |- _] => inversion H
      | [H: false = true |- _] => inversion H
      | [H: true = false |- _] => inversion H
      | _ => idtac
      end; simpleproof; match goal with
      | [|- _ /\ _] => split
      | [|- context[Int.and ?x Int.zero]] => change (Int.and x Int.zero) with Int.zero
      | [|- context[Int.eq Int.zero Int.zero]] => change (Int.eq Int.zero Int.zero) with true
      | [|- context[Int.eq Int.one Int.zero]] => change (Int.eq Int.one Int.zero) with false
      | [|- context[negb true]] => change (negb true) with false
      | [|- context[negb false]] => change (negb false) with true
      | [|- context[Int.add]] => unfold Int.add
      | [|- context[Int.unsigned Int.zero]] => change (Int.unsigned Int.zero) with 0
      | [|- context[Int.unsigned Int.one]] => change (Int.unsigned Int.one) with 1
      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; try omega
      | [|- context[Int.repr (Int.unsigned _)]] => rewrite Int.repr_unsigned
      | [|- exec_stmt _ _ _ _ _ _ _ _ _] => match goal with
                 | [|- exec_stmt _ _ _ _ (Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- exec_stmt _ _ _ _ (if true then Ssequence _ _ else _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- exec_stmt _ _ _ _ (if false then _ else Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- exec_stmt _ _ _ _ _ _ _ _ _] => econstructor
                 | _ => fail 2
                 end
      | [|- eval_expr _ _ _ _ _ _] => econstructor
      | [|- eval_exprlist _ _ _ _ _ _ _] => econstructor
      | [|- eval_funcall _ _ _ _ _ _ _] => econstructor
      | [|- external_call _ _ _ _ _ _ _] => econstructor
      | [|- assign_loc _ _ _ _ _ _] => econstructor
      | [|- context[set_opttemp]] => unfold set_opttemp
      | [|- (PTree.set ?id _ _) ! ?id = Some _] => eapply PTree.gss
      | [|- (PTree.set ?id1 _ _) ! ?id2 = Some _] => rewrite PTree.gso
      | [|- ?id1 <> ?id2] => diff_ident id1 id2
      | [|- sem_binary_operation _ _ _ _ _ _ = Some _] => unfold_cmp
      | [|- sem_cmp _ _ _ _ _ _ = Some _] => unfold sem_cmp; unfold_cmp
      | [|- bool_val _ _ = Some _] => solve [unfold_cmp]
      | [|- forall _, _] => intro
      | [|- _ -> _] => intro
      | [|- Some _ = Some _] => f_equal
      | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
      | [|- eval_lvalue _ _ _ _ ?expr _ _] => match expr with
                                                  | Evar _ _ => eapply eval_Evar_global
                                                  | Ederef _ _ => eapply eval_Ederef
                                                  | Efield _ _ _ => eapply eval_Efield_struct
                                              end
      | [|- deref_loc _ _ _ _ _] => match goal with
                                | [|- deref_loc ?ty _ _ _ _] => match ty with
                                                | typeof (?var ?name ?type) => change (typeof (var name type)) with type
                                                | Tarray _ _ _ => eapply deref_loc_reference
                                                | Tfunction _ _ => eapply deref_loc_reference
                                                | Tstruct _ _ _ => eapply deref_loc_copy
                                                | Tunion _ _ _ => eapply deref_loc_copy
                                                | _ => eapply deref_loc_value
                                                end
                                | [|- _] => idtac
                                end
      | [|- access_mode _ = _] => constructor
      | [|- _] => idtac
  end.

  (** * The tactic to automate the proof for arithmatic destructs. *)

  Ltac zdestruct := match goal with
                     | [|- context [zle ?z1 ?z2]] => destruct (zle z1 z2); try omega
                     | [|- context [zlt ?z1 ?z2]] => destruct (zlt z1 z2); try omega
                     | [|- context [zeq ?z1 ?z2]] => destruct (zeq z1 z2); try omega
                     | [H: context [zle ?z1 ?z2] |- _] => destruct (zle z1 z2); try omega
                     | [H: context [zlt ?z1 ?z2] |- _] => destruct (zlt z1 z2); try omega
                     | [H: context [zeq ?z1 ?z2] |- _] => destruct (zeq z1 z2); try omega
                     | [H: None = Some _ |- _] => inversion H
                     | [H: Some _ = None |- _] => inversion H
                     | [|- Some ?x = Some ?x \/ Some _ = Some _] => left; trivial
                     | [|- Some _ = Some _ \/ Some ?x = Some ?x] => right; trivial
                   end ; trivial.

  Lemma list_disjoint_nil: forall (A: Type) (l1: list A), list_disjoint l1 nil.
  Proof.
    intros.
    unfold list_disjoint.
    simpl.
    intros.
    contradiction.
  Qed.

  (** * The tactic to automate the proof for the function definition using the lemma for the function body. *)

  Ltac fcall := simpleproof; match goal with
      | [|- exec_stmt _ _ _ _ _ _ _ _ _] => match goal with
                | [|- exec_stmt _ _ _ _ (Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                | [|- exec_stmt _ _ _ _ (if true then Ssequence _ _ else _) E0 _ _ _] => change E0 with (E0 ** E0)
                | [|- exec_stmt _ _ _ _ (if false then _ else Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                | [|- exec_stmt _ _ _ _ _ _ _ _ _] => econstructor
                | [|- _] => fail 2
                end
      | [|- eval_expr _ _ _ _ _ _] => econstructor
      | [|- eval_exprlist _ _ _ _ _ _ _] => econstructor
      | [|- eval_funcall _ _ _ _ _ _ _] => econstructor
      | [|- eval_lvalue _ _ _ _ ?expr _ _] => match expr with
                                                  | Evar _ _ => eapply eval_Evar_global
                                                  | Ederef _ _ => eapply eval_Ederef
                                                  | Efield _ _ _ => eapply eval_Efield_struct
                                              end
      | [|- deref_loc _ _ _ _ _] => match goal with
                  | [|- deref_loc ?ty _ _ _ _] => match ty with
                            | typeof (?var ?name ?type) => change (typeof (var name type)) with type
                            | Tarray _ _ _ => eapply deref_loc_reference
                            | Tfunction _ _ => eapply deref_loc_reference
                            | Tstruct _ _ _ => eapply deref_loc_copy
                            | Tunion _ _ _ => eapply deref_loc_copy
                            | _ => eapply deref_loc_value
                            end
                  | [|- _] => idtac
                  end
      | [|- bigstep_terminates _ _ _ _ _ _] => econstructor
      | [|- Val.has_type_list _ _] => repeat econstructor
      | [|- access_mode _ = _] => constructor
      | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
      | [|- alloc_variables _ _ _ _ _] => econstructor
      | [|- outcome_result_value _ _ _] => simpl; split; [try discriminate | try reflexivity]
      | [|- context[In _ _]] => simpl
      | [|- list_norepet _] => econstructor; simpl || idtac; intro || idtac
      | [|- list_disjoint _ nil] => apply list_disjoint_nil
      | [|- list_disjoint _ (_::_)] => apply list_disjoint_cons_r; simpl || idtac; intro || idtac
      | [|- list_disjoint _ _] => simpl
      | [H: ?x = ?y \/ _ |- False] => destruct H; [try unfold x in *; try unfold y in *; try discriminate | idtac]; try subst; try omega
      | [|- forall _, _] => intro
      | [|- _ -> _] => intro
      | [|- _ <> _] => intro
      | [|- _] => idtac
  end.


  (** * The Case notation copied from the Software Foundation book by Benjamin C. Pierce *)

  Require String. Open Scope string_scope.

  Ltac move_to_top x :=
    match reverse goal with
      | H : _ |- _ => try move x after H
    end.

  Tactic Notation "assert_eq" ident(x) constr(v) :=
    let H := fresh in
    assert (x = v) as H by reflexivity;
      clear H.

  Tactic Notation "Case_aux" ident(x) constr(name) :=
    first [
        set (x := name); move_to_top x
      | assert_eq x name; move_to_top x
      | fail 1 "because we are working on a different case" ].

  Tactic Notation "Case" constr(name) := Case_aux Case name.
  Tactic Notation "SCase" constr(name) := Case_aux SCase name.
  Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
  Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
  Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
  Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
  Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
  Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
