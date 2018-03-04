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
(*           Layers of PM: Assembly Verification for ThreadSched       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import CommonTactic.
Require Import LAsm.
Require Import Conventions.
Require Import FunctionalExtensionality.
Require Import AsmImplLemma.

Section LRegSet.

  Lemma regset_equal:
    forall (rs1 rs2: regset),
      (forall r, Pregmap.get r rs1 = Pregmap.get r rs2) ->
      rs1 = rs2.
  Proof.
    unfold Pregmap.get.
    intros.
    apply functional_extensionality.
    trivial.
  Qed.

  Record Lregset:=
    mkregset_map 
      { LPC: val; LRA: val; LEAX: val; LEBX: val; LECX: val; LEDX: val; LESI: val; LEDI: val;
        LEBP: val; LESP: val; LST0:val; LZF: val; LCF: val; LPF: val; LSF: val; LOF: val;
        LXMM0: val; LXMM1: val; LXMM2: val; LXMM3: val; LXMM4: val; LXMM5: val; LXMM6:val; LXMM7: val}. 

  Definition Lregset_fold (rs: Lregset) : regset :=
    (Pregmap.init Vundef) # ST0 <- (LST0 rs) # XMM0 <- (LXMM0 rs) # XMM1 <- (LXMM1 rs) # XMM2 <- (LXMM2 rs)
                          # XMM3 <- (LXMM3 rs) # XMM4 <- (LXMM4 rs) # XMM5 <- (LXMM5 rs) # XMM6 <- (LXMM6 rs)
                          # XMM7 <- (LXMM7 rs) # ZF <- (LZF rs) # CF <- (LCF rs) # PF <- (LPF rs)
                          # SF <- (LSF rs) # OF <- (LOF rs) # EAX <- (LEAX rs) # EBX <- (LEBX rs)
                          # ECX <- (LECX rs) # EDX <- (LEDX rs) # ESI <- (LESI rs) # EDI <- (LEDI rs)
                          # EBP <- (LEBP rs) # ESP <- (LESP rs) # RA <- (LRA rs) # PC <- (LPC rs).

  Ltac simpl_reg_set :=
    repeat match goal with
             | [ |- context[?m # ?i <- ?x ?i]] => rewrite Pregmap.gss
             | [ |- context[?m # ?i <- ?x ?j]] => rewrite Pregmap.gso; [|discriminate]
           end.

  Lemma Lregset_rewrite:
    forall rs,
      rs = Lregset_fold (mkregset_map (rs PC) (rs RA) (rs EAX) (rs EBX) (rs ECX) (rs EDX) (rs ESI) (rs EDI)
                                      (rs EBP) (rs ESP) (rs ST0) (rs ZF) (rs CF) (rs PF) (rs SF) (rs OF)
                                      (rs XMM0) (rs XMM1) (rs XMM2) (rs XMM3) (rs XMM4) (rs XMM5) (rs XMM6)
                                      (rs XMM7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    simpl_reg_set.
    repeat (rewrite Pregmap.gsspec).
    simpl_destruct_reg; trivial.
    destruct reg; try congruence.
    destruct i; congruence.
    destruct f; congruence.
    destruct c; congruence.
  Qed.
  
  Definition toL i:=
    match i with
      | PC => LPC
      | RA => LRA
      | EAX => LEAX
      | EBX => LEBX
      | ECX => LECX
      | EDX => LEDX
      | ESI => LESI
      | EDI => LEDI
      | EBP => LEBP
      | ESP => LESP
      | ST0 => LST0
      | ZF => LZF
      | CF => LCF
      | PF => LPF
      | SF => LSF
      | OF => LOF
      | XMM0 => LXMM0
      | XMM1 => LXMM1
      | XMM2 => LXMM2
      | XMM3 => LXMM3
      | XMM4 => LXMM4
      | XMM5 => LXMM5
      | XMM6 => LXMM6
      | XMM7 => LXMM7
    end.

  Lemma  Lregset_fold_get:
    forall rs i,
      (Lregset_fold rs) i = toL i rs.
  Proof.
    intros. unfold Lregset_fold.
    destruct i; try reflexivity.
    destruct i; reflexivity.
    destruct f; reflexivity.
    destruct c; reflexivity.
  Qed.

  Lemma Lregset_fold_pc:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # PC <- v = 
      (Lregset_fold 
         (mkregset_map v lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
  Qed.

  Lemma Lregset_fold_ra:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # RA <- v = 
      (Lregset_fold 
         (mkregset_map lpc v leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
  Qed.

  Lemma Lregset_fold_eax:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # EAX <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra v lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_ebx:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # EBX <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax v lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_ecx:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # ECX <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx v ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_edx:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # EDX <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx v lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_esi:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # ESI <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx v ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_edi:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # EDI <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi v lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_ebp:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # EBP <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi v lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_esp:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # ESP <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp v lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal. 
    intros reg.
    destruct reg; try reflexivity.
    destruct i; try reflexivity.
  Qed.

  Lemma Lregset_fold_st0:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # ST0 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp v lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
  Qed.

  Lemma Lregset_fold_zf:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # ZF <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 v lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct c; try reflexivity.
  Qed.

  Lemma Lregset_fold_cf:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # CF <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf v lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct c; try reflexivity.
  Qed.

  Lemma Lregset_fold_pf:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # PF <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf v lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct c; try reflexivity.
  Qed.

  Lemma Lregset_fold_sf:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # SF <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf v lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct c; try reflexivity.
  Qed.

  Lemma Lregset_fold_of:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # OF <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf v lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct c; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm0:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM0 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof v lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm1:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM1 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 v
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm2:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM2 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       v lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm3:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM3 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 v lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm4:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM4 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 v lxmm5 lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm5:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM5 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 v lxmm6 lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm6:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM6 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 v lxmm7)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_xmm7:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7 v,
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) # XMM7 <- v = 
      (Lregset_fold 
         (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 v)).
  Proof.
    intros. unfold Lregset_fold; simpl.
    apply regset_equal.
    intros reg.
    destruct reg; try reflexivity.
    destruct f; try reflexivity.
  Qed.

  Lemma Lregset_fold_nextinstr:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7,
      nextinstr (Lregset_fold 
                   (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                                 lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) = 
      (Lregset_fold 
         (mkregset_map (Val.add lpc Vone) lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                       lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    unfold nextinstr. 
    intros. rewrite Lregset_fold_get; simpl.
    rewrite Lregset_fold_pc. reflexivity.
  Qed.

  Lemma Lregset_fold_nextinstr_nf:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7,
      nextinstr_nf (Lregset_fold 
                   (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                                 lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) = 
      (Lregset_fold 
         (mkregset_map (Val.add lpc Vone) lra leax lebx lecx ledx lesi ledi lebp lesp lst0 Vundef Vundef Vundef Vundef
                       Vundef lxmm0 lxmm1 lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)).
  Proof.
    unfold nextinstr_nf, nextinstr. simpl. intros. 
    repeat rewrite Lregset_fold_zf. 
    repeat rewrite Lregset_fold_cf. 
    repeat rewrite Lregset_fold_pf. 
    repeat rewrite Lregset_fold_sf. 
    repeat rewrite Lregset_fold_of. 
    rewrite Lregset_fold_pc.
    rewrite Lregset_fold_get; simpl.
    reflexivity.
  Qed.

  Lemma Lregset_fold_destroyed:
    forall lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
           lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7,
      undef_regs (map preg_of destroyed_at_call) 
                 (Lregset_fold 
                    (mkregset_map lpc lra leax lebx lecx ledx lesi ledi lebp lesp lst0 lzf lcf lpf lsf lof lxmm0 lxmm1
                                  lxmm2 lxmm3 lxmm4 lxmm5 lxmm6 lxmm7)) = 
      (Lregset_fold 
         (mkregset_map lpc lra Vundef lebx Vundef Vundef lesi ledi lebp lesp Vundef lzf lcf lpf lsf lof
                       Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef)).
  Proof.
    intros. simpl.
    rewrite Lregset_fold_st0. 
    rewrite Lregset_fold_eax. 
    rewrite Lregset_fold_ecx. 
    rewrite Lregset_fold_edx. 
    rewrite Lregset_fold_xmm0. 
    rewrite Lregset_fold_xmm1. 
    rewrite Lregset_fold_xmm2. 
    rewrite Lregset_fold_xmm3. 
    rewrite Lregset_fold_xmm4. 
    rewrite Lregset_fold_xmm5. 
    rewrite Lregset_fold_xmm6. 
    rewrite Lregset_fold_xmm7. 
    reflexivity.
  Qed.

End LRegSet.