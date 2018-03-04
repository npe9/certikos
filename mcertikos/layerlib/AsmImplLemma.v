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
(*           Layers of PM: Assembly Verification for Lemmas            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
Require Import Coqlib.
Require Import Asm.
Require Import Values.
Require Import Integers.
Require Import CommonTactic.
Require Import AST.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Ltac vm_discriminate := vm_compute; intros; discriminate.

Lemma nextinstr_nf_PC:
  forall r',
    nextinstr_nf r' PC = Val.add (r' PC) Vone.
Proof.
  intros.
  unfold nextinstr_nf. unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gss).
  repeat (rewrite Pregmap.gso; try discriminate).
  trivial.
Qed.

Lemma nextinstr_nf_PC':
  forall r' b ofs,
    r' PC = Vptr b ofs ->
    nextinstr_nf r' PC = Vptr b (Int.add ofs Int.one).
Proof.
  intros.
  unfold nextinstr_nf. unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gss).
  repeat (rewrite Pregmap.gso; try discriminate).
  rewrite H.
  simpl.
  trivial.
Qed.

Lemma nextinstr_PC':
  forall r' b ofs,
    r' PC = Vptr b ofs ->
    nextinstr r' PC = Vptr b (Int.add ofs Int.one).
Proof.
  intros.
  unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gss).
  repeat (rewrite Pregmap.gso; try discriminate).
  rewrite H.
  simpl.
  trivial.
Qed.

Lemma nextinstr_nf_RA:
  forall r': regset,
    r' Asm.RA = nextinstr_nf r' Asm.RA.
Proof.
  intros.
  unfold nextinstr_nf. unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gso; try discriminate).
  trivial.
Qed.

Lemma nextinstr_PC:
  forall r',
    nextinstr r' PC = Val.add (r' PC) Vone.
Proof.
  intros.
  unfold nextinstr. unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gss).
  repeat (rewrite Pregmap.gso; try discriminate).
  trivial.
Qed.

Lemma nextinstr_RA:
  forall r': regset,
    r' Asm.RA = nextinstr r' Asm.RA.
Proof.
  intros.
  unfold nextinstr. unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gso; try discriminate).
  trivial.
Qed.

Lemma nextinstr_nf_ireg:
  forall i (r': regset),
    r' (IR i) = nextinstr_nf r' (IR i).
Proof.
  intros.
  unfold nextinstr_nf. unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gso; try discriminate).
  trivial.
Qed.

Lemma nextinstr_ireg:
  forall i (r': regset),
    r' (IR i) = nextinstr r' (IR i).
Proof.
  intros.
  unfold nextinstr. unfold nextinstr. unfold undef_regs; unfold Val.add.
  repeat (rewrite Pregmap.gso; try discriminate).
  trivial.
Qed.

Ltac simpleproof := assumption || omega || trivial || reflexivity || eassumption || auto || idtac.
Ltac pc_add_simpl := 
  (*simpl;*) 
  repeat (unfold Int.eq, Int.add,Int.sub, Int.mul; repeat (autorewrite with arith);
          match goal with
            | [|- context[Int.unsigned Int.zero]] => change (Int.unsigned Int.zero) with 0
            | [|- context[Int.unsigned Int.one]] => change (Int.unsigned Int.one) with 1
            | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; 
            try omega
          end); repeat (autorewrite with arith); (simpleproof).

Ltac simpl_Pregmap :=
match goal with
    | [ |- context[?m # ?i <- ?x ?i]] => rewrite Pregmap.gss
    | [ |- context[?m # ?i <- ?x ?j]] => rewrite Pregmap.gso; [|discriminate]
    | [ |- context[nextinstr_nf _ (_:ireg)]] => rewrite <- nextinstr_nf_ireg
    | [ |- context[nextinstr _ (_:ireg)]] => rewrite <- nextinstr_ireg
    | [ |- context[nextinstr_nf _ RA]] => rewrite <- nextinstr_nf_RA
    | [ |- context[nextinstr _ RA]] => rewrite <- nextinstr_RA
    | [ |- context[nextinstr_nf _ PC]] => apply nextinstr_nf_PC'
    | [ |- context[nextinstr _ PC]] => apply nextinstr_PC'
  end.

Ltac simpl_destruct_reg :=
  repeat match goal with
           | [ |- context[Pregmap.elt_eq ?a ?b]] 
             => destruct (Pregmap.elt_eq a b); [subst; simpl; trivial|]
         end.

 Lemma register_type_load_result:
   forall (rs: regset)  r,
     Val.has_type (rs r) Tint
     -> (Val.load_result Mint32 (rs r)) = rs r.
 Proof.
   intros.
   unfold Val.has_type in *.
   destruct (rs r); inv H; try econstructor; eauto.
 Qed.
