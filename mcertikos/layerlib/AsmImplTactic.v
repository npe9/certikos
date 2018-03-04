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
Require Import Smallstep.
Require Import liblayers.compat.CompatLayers.
Require Import LAsm.
(*Require Import LoadStoreSem.*)
Require Import FunctionalExtensionality.
Require Import AsmImplLemma.
Require Import LRegSet.
Require Import Conventions.
Require Import AuxLemma.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(*
 Definition n_instr (n: int) (rs: regset) := rs # PC <- (Val.add (rs PC) (Vint n)).

 Definition n_instr_nf (n: int) (rs: regset) := 
   (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs) # PC <- (Val.add (rs PC) (Vint n)).

 Lemma nextinstr_n_instr:
   forall rs,
     nextinstr rs = n_instr Int.one rs.
 Proof.
   unfold nextinstr, n_instr. 
   reflexivity.
 Qed.

 Lemma nextinstr_nf_n_instr_nf:
   forall rs,
     nextinstr_nf rs = n_instr_nf Int.one rs.
 Proof.
   unfold nextinstr_nf, n_instr_nf. 
   reflexivity.
 Qed.

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

 Lemma n_instr_nf_n_instr:
   forall rs n1 n2,
     n_instr_nf n1 (n_instr n2 rs) = n_instr_nf (Int.add n2 n1) rs.
 Proof.
   unfold n_instr, n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
   destruct (rs PC); simpl; try reflexivity;
   Int_Add_Simpl.
 Qed.

 Lemma n_instr_n_instr_nf:
   forall rs n1 n2,
     n_instr n1 (n_instr_nf n2 rs) = n_instr_nf (Int.add n2 n1) rs.
 Proof.
   unfold n_instr, n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
   destruct (rs PC); simpl; try reflexivity;
   Int_Add_Simpl.
 Qed.

 Lemma n_instr_n_instr:
   forall rs n1 n2,
     n_instr n1 (n_instr n2 rs) = n_instr (Int.add n2 n1) rs.
 Proof.
   unfold n_instr. intros.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
   destruct (rs PC); simpl; try reflexivity;
   Int_Add_Simpl.
 Qed.

 Lemma n_instr_nf_n_instr_nf:
   forall rs n1 n2,
     n_instr_nf n1 (n_instr_nf n2 rs) = n_instr_nf (Int.add n2 n1) rs.
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
   destruct (rs PC); simpl; try reflexivity;
   Int_Add_Simpl.
 Qed.

 Lemma n_instr_ireg_set:
   forall rs n i v,
     (n_instr n rs) # (IR i) <- v = n_instr n (rs # (IR i) <- v).
 Proof.
   unfold n_instr. intros.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_nf_ireg_set:
   forall rs n i v,
     (n_instr_nf n rs) # (IR i) <- v = n_instr_nf n (rs # (IR i) <- v).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_RA_set:
   forall rs n v,
     (n_instr n rs) # RA <- v = n_instr n (rs # RA <- v).
 Proof.
   unfold n_instr. intros.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_nf_RA_set:
   forall rs n v,
     (n_instr_nf n rs) # RA <- v = n_instr_nf n (rs # RA <- v).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_PC_set:
   forall rs n v,
     (n_instr n rs) # PC <- v = rs # PC <- v.
 Proof.
   unfold n_instr. intros.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_nf_PC_set:
   forall rs n b ofs,
     (n_instr_nf n rs) # PC <- (Vptr b ofs) = (n_instr_nf Int.zero rs # PC <- (Vptr b ofs)).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
   rewrite Int.add_zero.
   reflexivity.
 Qed.

 Lemma n_instr_ireg:
   forall rs n i,
     (n_instr n rs) (IR i) = rs # (IR i).
 Proof.
   unfold n_instr. intros.
   repeat simpl_Pregmap. trivial.
 Qed.

 Lemma n_instr_nf_ireg:
   forall rs n i,
     (n_instr_nf n rs) (IR i) = rs # (IR i).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   repeat simpl_Pregmap.
   trivial.
 Qed.

 Lemma n_instr_RA:
   forall rs n,
     (n_instr n rs) RA = rs # RA.
 Proof.
   unfold n_instr. intros.
   repeat simpl_Pregmap. trivial.
 Qed.

 Lemma n_instr_nf_RA:
   forall rs n,
     (n_instr_nf n rs) RA = rs # RA.
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   repeat simpl_Pregmap.
   trivial.
 Qed.

 Lemma n_instr_PC:
   forall rs n b ofs,
     rs PC = Vptr b ofs ->
     (n_instr n rs) PC = Vptr b (Int.add ofs n).
 Proof.
   unfold n_instr. intros.
   rewrite H.
   repeat simpl_Pregmap. trivial.
 Qed.

 Lemma n_instr_nf_PC:
   forall rs n b ofs,
     rs PC = Vptr b ofs ->
     (n_instr_nf n rs) PC = Vptr b (Int.add ofs n).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   repeat simpl_Pregmap.
   rewrite H. trivial.
 Qed.

 Lemma n_instr_freg_set:
   forall rs n i v,
     (n_instr n rs) # (FR i) <- v = n_instr n (rs # (FR i) <- v).
 Proof.
   unfold n_instr. intros.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_nf_freg_set:
   forall rs n i v,
     (n_instr_nf n rs) # (FR i) <- v = n_instr_nf n (rs # (FR i) <- v).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_ST0_set:
   forall rs n v,
     (n_instr n rs) # ST0 <- v = n_instr n (rs # ST0 <- v).
 Proof.
   unfold n_instr. intros.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_nf_ST0_set:
   forall rs n v,
     (n_instr_nf n rs) # ST0 <- v = n_instr_nf n (rs # ST0 <- v).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   apply regset_equal.
   intros reg.
   repeat simpl_Pregmap.
   repeat (rewrite Pregmap.gsspec).
   simpl_destruct_reg; trivial.
 Qed.

 Lemma n_instr_freg:
   forall rs n i,
     (n_instr n rs) (FR i) = rs # (FR i).
 Proof.
   unfold n_instr. intros.
   repeat simpl_Pregmap. trivial.
 Qed.

 Lemma n_instr_nf_freg:
   forall rs n i,
     (n_instr_nf n rs) (FR i) = rs # (FR i).
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   repeat simpl_Pregmap.
   trivial.
 Qed.

 Lemma n_instr_ST0:
   forall rs n,
     (n_instr n rs) ST0 = rs # ST0.
 Proof.
   unfold n_instr. intros.
   repeat simpl_Pregmap. trivial.
 Qed.

 Lemma n_instr_nf_ST0:
   forall rs n,
     (n_instr_nf n rs) ST0 = rs # ST0.
 Proof.
   unfold n_instr_nf. intros.
   unfold undef_regs.
   repeat simpl_Pregmap.
   trivial.
 Qed.

 Ltac regset_simpl_tac :=
   match goal with
     | |- context[(n_instr_nf _ _) # _ <- _] =>
       match goal with
         | |- context[(n_instr_nf _ _) # (_:ireg) <- _] => rewrite n_instr_nf_ireg_set
         | |- context[(n_instr_nf _ _) # RA <- _] => rewrite n_instr_nf_RA_set
         | |- context[(n_instr_nf _ _) # PC <- (Vptr _ _)] => rewrite n_instr_nf_PC_set
         | |- context[(n_instr_nf _ _) # (_:freg) <- _] => rewrite n_instr_nf_freg_set
         | |- context[(n_instr_nf _ _) # ST0 <- _] => rewrite n_instr_nf_ST0_set
       end
     | |- context[(n_instr _ _) # _ <- _] => 
       match goal with
         | |- context[(n_instr _ _) # (_:ireg) <- _] => rewrite n_instr_ireg_set
         | |- context[(n_instr _ _) # RA <- _] => rewrite n_instr_RA_set
         | |- context[(n_instr _ _) # PC <- _] => rewrite n_instr_PC_set
         | |- context[(n_instr _ _) # (_:freg) <- _] => rewrite n_instr_freg_set
         | |- context[(n_instr _ _) # ST0 <- _] => rewrite n_instr_ST0_set
       end
     | |- context[(n_instr_nf _ _) _] => 
       match goal with
         | |- context[(n_instr_nf _ _) (_:ireg)] => rewrite n_instr_nf_ireg
         | |- context[(n_instr_nf _ _) RA] => rewrite n_instr_nf_RA
         | |- context[(n_instr_nf _ _) PC] => erewrite n_instr_nf_PC
         | |- context[(n_instr_nf _ _) (_:freg)] => rewrite n_instr_nf_freg
         | |- context[(n_instr_nf _ _) ST0] => rewrite n_instr_nf_ST0
       end
     | |- context[(n_instr _ _) _] => 
       match goal with
         | |- context[(n_instr _ _) (_:ireg)] => rewrite n_instr_ireg
         | |- context[(n_instr _ _) RA] => rewrite n_instr_RA
         | |- context[(n_instr _ _) PC] => erewrite n_instr_PC
         | |- context[(n_instr _ _) (_:freg)] => rewrite n_instr_freg
         | |- context[(n_instr _ _) ST0] => rewrite n_instr_ST0
       end
     | |- context[n_instr_nf _ (n_instr_nf _ _)] => rewrite n_instr_nf_n_instr_nf
     | |- context[n_instr_nf _ (n_instr _ _)] => rewrite n_instr_nf_n_instr
     | |- context[n_instr _ (n_instr_nf _ _)] => rewrite n_instr_n_instr_nf
     | |- context[n_instr _ (n_instr _ _)] => rewrite n_instr_n_instr

     | |- context[?m # ?i <- ?x ?i] => rewrite Pregmap.gss
     | |- context[?m # ?i <- ?x ?j] => rewrite Pregmap.gso; [|discriminate]
     | |- context[nextinstr] => rewrite nextinstr_n_instr
     | |- context[nextinstr_nf] => rewrite nextinstr_nf_n_instr_nf
   end; simpl.

(* Ltac regset_simpl_tac :=
   match goal with
     | |- context[?m # ?i <- ?x ?i] => rewrite Pregmap.gss
     | |- context[?m # ?i <- ?x ?j] => rewrite Pregmap.gso; [|discriminate]
     | |- context[nextinstr] => rewrite nextinstr_n_instr
     | |- context[nextinstr_nf] => rewrite nextinstr_nf_n_instr_nf
     | |- context[n_instr_nf _ (n_instr _ _)] => rewrite n_instr_nf_n_instr
     | |- context[n_instr _ (n_instr_nf _ _)] => rewrite n_instr_n_instr_nf
     | |- context[n_instr _ (n_instr _ _)] => rewrite n_instr_n_instr
     | |- context[n_instr_nf _ (n_instr_nf _ _)] => rewrite n_instr_nf_n_instr_nf
     | |- context[(n_instr_nf _ _) # (_:ireg) <- _] => rewrite n_instr_nf_ireg_set
     | |- context[(n_instr _ _) # (_:ireg) <- _] => rewrite n_instr_ireg_set
     | |- context[(n_instr_nf _ _) # RA <- _] => rewrite n_instr_nf_RA_set
     | |- context[(n_instr _ _) # RA <- _] => rewrite n_instr_RA_set
     | |- context[(n_instr_nf _ _) # PC <- (Vptr _ _)] => rewrite n_instr_nf_PC_set
     | |- context[(n_instr _ _) # PC <- _] => rewrite n_instr_PC_set
     | |- context[(n_instr_nf _ _) (_:ireg)] => rewrite n_instr_nf_ireg
     | |- context[(n_instr _ _) (_:ireg)] => rewrite n_instr_ireg
     | |- context[(n_instr_nf _ _) RA] => rewrite n_instr_nf_RA
     | |- context[(n_instr _ _) RA] => rewrite n_instr_RA
     | |- context[(n_instr_nf _ _) PC] => erewrite n_instr_nf_PC
     | |- context[(n_instr _ _) PC] => erewrite n_instr_PC
   end; simpl.*)

 Ltac one_step_forward n:=
   match goal with
     | |- star _ _ _ _ _ =>
       eapply star_left; try reflexivity
     | |- plus _ _ _ _ _ =>
       econstructor
   end;
   match goal with
     | |- step _ _ _ _ =>
       econstructor; try eassumption;
       match goal with
         | H: _ PC = Vptr ?b _ |- _ = Vptr ?b _ => 
           repeat regset_simpl_tac; try reflexivity; eassumption
         | |- find_instr ?num _ = _ =>
           replace num with n;
             [pc_add_simpl; simpl| try reflexivity]
         | _ => simpl
       end
     | _ => idtac
   end.*)

(*Ltac lens_norm_ortho_trivial :=
  repeat progress
    match goal with
      | |- context [set ?β ?v (set ?α ?u ?s)] =>
        rewrite (lens_ortho_setr_setl u v s)
      | |- context [?α (set ?β ?v ?s)] =>
        rewrite (lens_ortho_getl_setr α β s v)
      | |- context [?β (set ?α ?u ?s)] =>
        rewrite (lens_ortho_getr_setl α β s u)
    end.

Ltac lens_norm_trivial :=
  repeat progress (simpl; lens_norm_ortho_trivial;
                   autorewrite with lens).

Ltac lens_simpl_trivial :=
  repeat progress (lens_norm_trivial; autorewrite with lens_simpl_trivial).

Ltac lens_unfold_trivial :=
  repeat progress (lens_simpl_trivial; unfold set).

Ltac lift_trivial :=
  unfold lift; lens_unfold_trivial; simpl.*)

(* Ltac regset_simpl_tac_n n:=
   repeat regset_simpl_tac;
   match goal with
     | |- context [n_instr ?a _] =>
       replace a with (Int.repr n); [| try reflexivity]
     | |- context [n_instr_nf ?a _] =>
       replace a with (Int.repr n); [| try reflexivity]
   end.*)

 Ltac store_split:=
   repeat match goal with
            | H: _ /\ _ = _ |- _ => destruct H as [H ?]; subst
          end.

 Ltac one_step_forward':=
   match goal with
     | |- star _ _ _ _ _ =>
       eapply star_left; try reflexivity
     | |- plus _ _ _ _ _ =>
       econstructor
   end;
   match goal with
     | |- step _ _ _ _ =>
       econstructor; try eassumption;
       try reflexivity
     | _ => idtac
   end; simpl; [auto; discriminate|..].

 Ltac one_step_forward n:=
   match goal with
     | |- star _ _ _ _ _ =>
       eapply star_left; try reflexivity
     | |- plus _ _ _ _ _ =>
       econstructor
   end;
   match goal with
     | |- step _ _ _ _ =>
       econstructor; try eassumption;
       match goal with
         | H: _ PC = Vptr ?b _ |- _ = Vptr ?b _ => 
           try reflexivity
         | |- find_instr ?num _ = _ =>
           replace num with n;
             [pc_add_simpl; simpl| try reflexivity]
         | _ => simpl
       end
     | _ => idtac
   end; [auto; discriminate|..].

 Lemma val_add_vptr:
   forall n b ofs,
     Int.repr n = Int.add ofs Int.one ->
     Val.add (Vptr b ofs) Vone = Vptr b (Int.repr n).
 Proof.
   simpl. intros.
   congruence.
 Qed.

 Ltac Lregset_simpl_tac:=
   repeat match goal with
            | |- context [undef_regs (map _ destroyed_at_call) (Lregset_fold _)] =>
              rewrite Lregset_fold_destroyed
            | |- context[(Lregset_fold _) _] => 
              rewrite Lregset_fold_get; simpl
            | |- context [nextinstr (Lregset_fold _)] =>
              rewrite Lregset_fold_nextinstr
            | |- context [nextinstr_nf (Lregset_fold _)] =>
              rewrite Lregset_fold_nextinstr_nf
            | |- context[(Lregset_fold _) # RA <- _ ] =>
              rewrite Lregset_fold_ra
            | |- context[(Lregset_fold _) # PC <- _ ] =>
              rewrite Lregset_fold_pc
            | |- context[(Lregset_fold _) # ST0 <- _ ] =>
              rewrite Lregset_fold_st0
            | |- context[(Lregset_fold _) # (IR ?i) <- _ ] =>
              match i with
                | EAX => rewrite Lregset_fold_eax
                | EDX => rewrite Lregset_fold_edx
                | ESP => rewrite Lregset_fold_esp
                | ECX => rewrite Lregset_fold_ecx
                | EDI => rewrite Lregset_fold_edi
                | ESI => rewrite Lregset_fold_esi
                | EBX => rewrite Lregset_fold_ebx
                | EBP => rewrite Lregset_fold_ebp
              end
            | |- context[(Lregset_fold _) # (CR ?i) <- _ ] =>
              match i with
                | ZF => rewrite Lregset_fold_zf
                | CF => rewrite Lregset_fold_cf
                | PF => rewrite Lregset_fold_pf
                | SF => rewrite Lregset_fold_sf
                | OF => rewrite Lregset_fold_of
              end
            | |- context[(Lregset_fold _) # (FR ?i) <- _ ] =>
              match i with
                | XMM0 => rewrite Lregset_fold_xmm0
                | XMM1 => rewrite Lregset_fold_xmm1
                | XMM2 => rewrite Lregset_fold_xmm2
                | XMM3 => rewrite Lregset_fold_xmm3
                | XMM4 => rewrite Lregset_fold_xmm4
                | XMM5 => rewrite Lregset_fold_xmm5
                | XMM6 => rewrite Lregset_fold_xmm6
                | XMM7 => rewrite Lregset_fold_xmm7
              end
          end.

 Ltac Lregset_simpl_tac' n :=
   Lregset_simpl_tac;
   match goal with
     | |- context [Val.add (Vptr ?b ?ofs) Vone] =>
       rewrite (val_add_vptr n b ofs); [| try reflexivity]
   end. 

 Lemma reg_false:
   forall reg: preg,
     reg <> PC ->
     reg <> EBP ->
     reg <> EBX ->
     reg <> ESI ->
     reg <> EDI ->
     reg <> ESP ->
     reg <> RA ->
     reg <> EAX ->
     reg <> ECX ->
     reg <> EDX ->
     reg <> OF ->
     reg <> SF ->
     reg <> PF ->
     reg <> CF ->
     reg <> ZF ->
     reg <> XMM7 ->
     reg <> XMM6 ->
     reg <> XMM5 ->
     reg <> XMM4 ->
     reg <> XMM3 ->
     reg <> XMM2 ->
     reg <> XMM1 ->
     reg <> XMM0 ->
     reg <> ST0 ->
     False.
 Proof.
   intros.
   destruct reg; try congruence.
   destruct i; try congruence.
   destruct f; try congruence.
   destruct c; try congruence.
 Qed.

 Ltac link_nextblock_asm :=
   repeat match goal with
            | Hstore: Mem.store _ _ _ _ _ = Some ?fm |- context[Mem.nextblock ?fm] =>
              rewrite (Mem.nextblock_store _ _ _ _ _ _ Hstore)
          end; try reflexivity.

 Ltac link_inject_neutral_asm :=
   repeat match goal with
            | Hstore: Mem.store _ _ _ _ _ = Some ?fm |- Mem.inject_neutral _ ?fm =>
              eapply Mem.store_inject_neutral; eauto 1
          end.


 Lemma inv_reg_le:
   forall (rs: regset) a b,        
     (forall r,
        val_inject (Mem.flat_inj a) 
                   (rs r) (rs r)) ->
     (a <= b)%positive ->
     (forall r,
        val_inject (Mem.flat_inj b) 
                   (rs r) (rs r)).
 Proof.
   intros. eapply val_inject_incr; [|eauto].
   eapply flat_inj_inject_incr; assumption.
 Qed.
