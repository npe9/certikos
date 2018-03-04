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
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the tactic for refinement proof between layers*)
Require Import Values.
Require Import AsmX.
Require Import Coqlib.
Require Import Integers.
(*Require Import LAsm.*)
Require Import Maps.
Require Import liblayers.lib.Monad.
Require Import liblayers.compat.CompatGenSem.

Ltac PrimInvariants_simpl H H0:=
  constructor; intros; functional inversion H; inv H0;
  [constructor; trivial|
   subst; constructor; auto; simpl in *; intros; congruence].

  Ltac Equalities :=
    match goal with
      | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
        rewrite H1 in H2; inv H2; Equalities
      | _ => idtac
    end.

  Ltac preserves_invariants_simpl' :=
    constructor; simpl; intros;
    match goal with
      | [H: GenSem.semof _ _ _ _ _ |- _] =>
        inv_generic_sem H
    end.

  Ltac constructor_gso_simpl_tac :=
    try constructor; simpl; eauto;
    try (rewrite ZMap.gso; eauto; fail).

(** * tactics to prove the specification satisfies the invariants *)
  Ltac preserves_invariants_simpl low_level_invariant high_level_invariant:=
    constructor; simpl; intros;
    match goal with
      | [H: GenSem.semof _ _ _ _ _ |- _] =>
        inv_generic_sem H;
        match goal with
          | [H1: _ = ret _ , H0: low_level_invariant _ _ |- _ ] =>
            inv H0; functional inversion H1; subst; constructor; trivial
          | [H1: _ = ret _ , H0: high_level_invariant _ |- _ ] =>
            inv H0; functional inversion H1; subst; constructor; simpl; intros; try congruence
          | [H1: _ = ret _ , H0: _ /\ _ |- _ /\ _ ] =>
            functional inversion H1; subst; simpl; try assumption
          | _ => idtac
        end
    end.

  Ltac preserves_invariants_simpl'' low_level_invariant high_level_invariant:=
    constructor; simpl; intros;
    match goal with
      | [H: GenSem.semof _ _ _ _ _ |- _] =>
        inv_generic_sem H;
        match goal with
          | [H0: low_level_invariant _ _ |- _ ] =>
            inv H0; subst; constructor; trivial
          | [H0: high_level_invariant _ |- _ ] =>
            inv H0; subst; constructor; simpl; intros; try congruence
          | [H0: _ /\ _ |- _ /\ _ ] =>
            subst; simpl; try assumption
          | _ => idtac
        end
    end.

(** * Tactic for arithmetic simplification*)
 Ltac range_simpl :=
   match goal with
     | [ |- 0 <= _ + _] =>  apply Zplus_le_0_compat; try omega
     | [ |- 0 <= _ * _] => apply Zmult_le_0_compat; try omega
     | [ |- ?a * _ <= ?a * _ ]=> apply Zmult_le_compat_l; try omega
     | [ |- _ * ?a <= _ * ?a ]=> apply Zmult_le_compat_r; try omega
     | [ |- _ + ?a <= _ + ?a ] => apply Zplus_le_compat_r; try omega
     | [ |- ?a + _<= ?a + _ ] => apply Zplus_le_compat_l; try omega
     | [ |- _ + _ <= _ + _ ] =>   apply Zplus_le_compat; try omega
   end.

 Ltac contra_inv :=  try discriminate.
 (*
   match goal with
     | [H: None = Some _ |- _ ]  => inv H
     | [H: Stuck = Next _ _ |- _ ] => inv H
     | _ => trivial
   end.*)


(** * Tactic for memory injection*)
Ltac Var_Inject_Simpl H0:=
  match goal with
    | [ |- val_inject ?f (if Pregmap.elt_eq ?reg ?r then _ else _ ) _ ] 
      => destruct (Pregmap.elt_eq reg r); try eapply H0; try constructor
    | _ => trivial
  end.

Ltac IF_Simpl:=
  match goal with
    | [  |- val_inject ?f (if ?R then _ else _ ) _ ] 
      => destruct (R); trivial;  try constructor
    | _ => trivial
  end.

Ltac Val_Calculate H0 :=  
  match goal with
    | [  |- val_inject ?f (?T _ (?rs ?rd) ) _] 
      =>  
      match goal with
        | [ |- val_inject f (T (rs ?rt)  (rs rd) ) _ ] 
          => unfold T; unfold Pregmap.get in H0; generalize H0; intro HT;
             specialize (H0 rt); specialize (HT rd); destruct (rs rt); trivial; destruct (rs rd); inv H0; inv HT; trivial; try constructor
        | _ =>  unfold T; specialize (H0 rd); unfold Pregmap.get in H0; destruct (rs rd); inv H0; trivial; try constructor
      end
    | [  H0: forall reg, val_inject ?f  (Pregmap.get reg ?rs)  _ |- val_inject ?f (?T (?rs ?rd) ) _] 
      => unfold T; specialize (H0 rd); unfold Pregmap.get in H0; destruct (rs rd); inv H0; trivial; try constructor
    | [  H0: forall reg, val_inject ?f  (Pregmap.get reg ?rs)  _ |- val_inject ?f (?T (?T1 (?rs ?rd))) _] 
      => unfold T; unfold T1; specialize (H0 rd); unfold Pregmap.get in H0; destruct (rs rd); inv H0; trivial;try constructor
    | [  H0: forall reg, val_inject ?f  (Pregmap.get reg ?rs)  _ |- val_inject ?f (?T  (?rs ?rd) _) _] 
      => unfold T; specialize (H0 rd); unfold Pregmap.get in H0; 
         destruct (rs rd); inv H0; trivial; try constructor
    | _ => trivial
  end.

(** * Tactic to simplify Int operations*)
Ltac Int_Add_Simpl :=  
  repeat (rewrite Int.add_assoc);
  match goal with
    | [|- (Int.add _ (Int.add ?i1 (Int.add ?i2 ?i3))) = _ ]
      => rewrite (Int.add_commut i1 (Int.add i2 i3));
        rewrite (Int.add_assoc i2 i3 i1);
        trivial
    | [|- (Int.add _ (Int.add ?i1 ?i2)) = _ ]
      => rewrite (Int.add_commut i1 i2);
        trivial
    | _ => trivial
  end.

Ltac Int_Add d:=  
  apply val_inject_ptr with d; trivial; Int_Add_Simpl.

(** * Tactic to deal with small step semantics*)
Ltac Normal_Next H5 H10 MATCH_STATE Pregmap_Simpl :=
  match goal with
    | [  |- exists _ _, Asm.Next (?r) ?m0 = Next _ _ /\ _ ] => 
      exists r; exists m0; split; trivial; inv H5; eapply MATCH_STATE; eauto;
      intros reg; repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
      repeat (Var_Inject_Simpl H10); repeat IF_Simpl
  end.
             
Ltac Goto_Label H5 H10 H2 HPC MATCH_STATE Pregmap_Simpl:=
  match goal with
    | [ |- exists _ _, goto_label ?c ?l  _ _ = _ /\ _] =>
      unfold goto_label in *; rewrite H2 in H5; rewrite HPC; destruct (label_pos l 0 c); 
      match goal with
    | [ |- exists _ _, Stuck = _ /\ _] => inv H5
    | _ =>  Normal_Next H5 H10 MATCH_STATE Pregmap_Simpl;apply val_inject_ptr with 0; auto;  rewrite Int.add_zero; trivial
      end
  end.

Ltac Next_NF_Simpl :=  intros reg; unfold nextinstr_nf; unfold nextinstr; (*unfold undef_regs;*)
                       repeat (rewrite Pregmap.gsspec; simpl).    

Ltac Destruct_Plus H5 H10 MATCH_STATE load_correct store_correct Pregmap_Simpl exec_loadex exec_storeex:=
  match goal with
    | [   |- exists _ _, Next (nextinstr_nf ?r) ?m0 = Next _ _ /\ _] => 
      exists (nextinstr_nf r); exists m0; split; trivial; inv H5; eapply MATCH_STATE; eauto; 
      intros reg; unfold nextinstr_nf; unfold nextinstr; unfold undef_regs;
      repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
      destruct (Pregmap.elt_eq reg PC); trivial; repeat (Var_Inject_Simpl H10); 
      Val_Calculate H10; repeat IF_Simpl
    | [   |- exists _ _, Next (nextinstr ?r) ?m0 = Next _ _ /\ _] => 
      exists (nextinstr r); exists m0; split; trivial; inv H5; eapply MATCH_STATE; eauto;
      intros reg; unfold nextinstr; repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
      destruct (Pregmap.elt_eq reg PC); trivial; repeat (Var_Inject_Simpl H10); 
      Val_Calculate H10; repeat IF_Simpl
    | [ |- exists _ _,  exec_loadex _ _ _ _ _ _ = _ /\ _] =>
      eapply load_correct; eauto
    | [ |- exists _ _, exec_storeex _ _ _ _ _ _ = _ /\ _ ] =>
      eapply store_correct; eauto
    | [ |- exists _ _, Next (?r) ?m0 = Next _ _ /\ _] => 
      exists (r); exists m0; split; trivial; inv H5; eapply MATCH_STATE; eauto;
      intros reg; repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
      repeat (Var_Inject_Simpl H10); repeat IF_Simpl
    | [ |- exists _ _, Stuck = _ /\ _ ] => inv H5 
    | _ => trivial    
  end.
            
    Ltac val_inject_inv :=
       match goal with
         | [ H: val_list_inject _ (_ :: _) _ |- _ ] => inv H
         | [ H: val_list_inject _ nil _ |- _ ] => inv H
         | [ H: val_inject _ (Vint _) _ |- _ ] => inv H
         | _ => reflexivity
       end.

    Ltac arg_inject_inv :=
      match goal with
        | [ HAN: extcall_arguments _ _ _ ?l, HVL: val_list_inject _ ?l_orig ?l |- _] =>
          let HARG := fresh "HARG" in
          assert (HARG: l = l_orig) by repeat val_inject_inv;
            rewrite HARG in HAN;
            clear HARG
      end.

    Ltac subrewrite':=
      repeat (
          match goal with
            | [ H: ?a = ?b |- context[?a] ] => rewrite H
          end); trivial.

    (*Ltac subrewrite':=
        repeat (
            match goal with
              | [ H: ?a = ?b |- context[?a] ] => rewrite H; clear H
            end); trivial.*)

    Ltac subrewrite'':=
      repeat (
          match goal with
            | [ H: ?a = ?b |- _ ] => rewrite H in *; clear H
          end); trivial.

    Ltac subrewrite:= subrewrite'; intros HQ.


    (*Ltac subdestruct:=
      repeat (
          match goal with
            | [ _: context[if ?con then _  else  _] |- _] => destruct con; contra_inv
            | [ _: context[match ?con with |_ => _ end] |- _] => destruct con; contra_inv
          end).*)

    Ltac subdestruct_if term:=
      match term with
        | context [if ?con then _  else  _] => 
          progress subdestruct_if con
        | context[match ?con with |_ => _ end] =>
          progress subdestruct_if con
        | _ => 
          let H := fresh "Hdestruct" in
          destruct term eqn: H; contra_inv
      end.

    Ltac subdestruct:=
      repeat progress (
          match goal with
            | [ HT: context[if ?con then _  else  _] |- _] => subdestruct_if con; simpl in HT
            | [ HT: context[match ?con with |_ => _ end] |- _] =>  subdestruct_if con; simpl in HT
          end; simpl).

    Ltac cases :=
          repeat match goal with
            | [ |- appcontext [if ?a then _ else _] ] => subdestruct_if a
            | [ |- appcontext [match ?a with _ => _ end] ] => subdestruct_if a
          end.

    Ltac inv_uctx := 
      repeat match goal with
               | [ H0: asm_invariant _ _ |- context[ZMap.get ?a (ZMap.set ?b _ _ )]] 
                 => destruct (zeq a b); 
                   [subst; rewrite ZMap.gss; inv H0; 
                    match goal with
                      | [H1: wt_regset _, H2: inject_neutral_invariant _ _ |- _] =>
                        split; [apply H1| inv H2; match goal with
                                                    | [H3: forall _, val_inject _ _ _ |- _ ] => apply H3
                                                  end ]
                    end
                   | rewrite ZMap.gso; auto]
             end.

    Ltac reg_destruct :=
      repeat match goal with
               | [ |- context[Pregmap.elt_eq ?a ?b]] 
                 => destruct (Pregmap.elt_eq a b); try constructor
             end.

    Ltac inv_proc := 
      repeat match goal with
               | [ |- context[ZMap.get ?a (ZMap.set ?b _ _ )]] 
                 => destruct (zeq a b);
                   [subst; repeat rewrite ZMap.gss; eauto
                   | 
                   match goal with
                     | [ H0: a <> b |- _] =>
                       repeat (rewrite (ZMap.gso _ _ H0)); auto
                   end]
             end.

    Ltac reg_destruct_simpl :=
      repeat match goal with
               | [ |- context[Pregmap.elt_eq ?a ?b]] 
                 => destruct (Pregmap.elt_eq a b); trivial; eauto; try econstructor; eauto
             end.

    Ltac load_other_simpl ofs i:= 
      right; simpl;
      destruct (zle (ofs + 1) (Int.unsigned i));
      [left; omega| right; omega].

    Ltac repeat_esplit := 
      repeat progress match goal with
               | [ |- context[exists _, _]] => esplit
             end.

    Ltac repeat_and_split :=
      repeat progress lazymatch goal with
                        | |- _ <= _ < _ => idtac
                        | |- _ < _ <= _ => idtac
                        | |- _ < _ < _ => idtac
                        | |- _ <= _ <= _ => idtac
                        | |- _ /\ _ => split
                      end.


    Ltac constructor_gen_sem_intro := repeat econstructor; autorewrite with monad; eauto.

    Ltac xauto :=
      auto;
      try congruence.

    Ltac inv_one_val_inject :=
      match goal with
        | H:Val.lessdef_list _ _ |- _ => inv H
        | H:Val.lessdef _ _ |- _ => inv H
        | H:val_list_inject _ _ _ |- _ => inv H
        | H:val_inject _ _ _ |- _ => inv H
      end; xauto.

    Ltac inv_one_val_inject_one :=
      inv_one_val_inject; [ idtac ].

    Ltac inv_val_inject' :=
      repeat inv_one_val_inject_one;
      try (now inv_one_val_inject).

    Ltac inv_val_inject :=
      inv_val_inject';
      repeat match goal with
               | [HFB: ?f ?b' = Some (?b', 0), HFB': ?f ?b' = Some (?b2, ?delta) |- _ ] =>
                 rewrite HFB in HFB'; inv HFB'; rewrite Int.add_zero in *
             end.

        Ltac refine_split' :=       
          repeat progress lazymatch goal with
                                 | |- context[exists _, _] => esplit
                                 | |- _ <= _ < _ => idtac
                                 | |- _ < _ <= _ => idtac
                                 | |- _ < _ < _ => idtac
                                 | |- _ <= _ <= _ => idtac
                                 | |- _ /\ _ => split
                               end.

    Ltac refine_split := repeat_esplit; inv_val_inject; repeat_and_split.


Ltac val_inject_simpl :=
  match goal with
    | [match_reg: forall _, val_inject _ _ _ |- context[val_inject _ _ _]] =>
   repeat progress lazymatch goal with
     | [|- context[val_inject _ (Pregmap.get _ (nextinstr_nf _)) _ ]] =>
       eapply nextinstr_nf_inject
     | [|- context[val_inject _ (Pregmap.get _ (nextinstr _)) _ ]] =>
       eapply nextinstr_inject
     | [|- context[val_inject _ (_ # _ <- _ _) _ ]] =>
       eapply set_reg_inject
     | [|- context[val_inject _ (Pregmap.get _ (_ # _ <- _ )) _ ]] =>
       eapply set_reg_inject
     | [|- context[val_inject _ (Val.and _ _) _ ]] =>
       eapply val_and_inject
     | [|- context[val_inject _ (Val.mul _ _) _ ]] =>
       eapply val_mul_inject
     | [|- context[val_inject _ (Val.mulhs _ _) _ ]] =>
       eapply val_mulhs_inject
     | [|- context[val_inject _ (Val.mulhu _ _) _ ]] =>
       eapply val_mulhu_inject
     | [|- context[val_inject _ (Val.sub _ _) _ ]] =>
       eapply val_sub_inject
     | [|- context[val_inject _ (Val.xor _ _) _ ]] =>
       eapply val_xor_inject
     | [|- context[val_inject _ (Val.or _ _) _ ]] =>
       eapply val_or_inject
     | [|- context[val_inject _ (Val.ror _ _) _ ]] =>
       eapply val_ror_inject
     | [|- context[val_inject _ (Val.shl _ _) _ ]] =>
       eapply val_shl_inject
     | [|- context[val_inject _ (Val.shr _ _) _ ]] =>
       eapply val_shr_inject
     | [|- context[val_inject _ (Val.shru _ _) _ ]] =>
       eapply val_shru_inject
     | [|- context[val_inject _ (Val.zero_ext _ _) _ ]] =>
       eapply val_zero_ext_inject
     | [|- context[val_inject _ (Val.sign_ext _ _) _ ]] =>
       eapply val_sign_ext_inject
     | [|- context[val_inject _ (Val.singleoffloat _) _ ]] =>
       eapply val_singleoffloat_inject
     | [|- context[val_inject _ (Val.neg _) _ ]] =>
       eapply val_neg_inject
     | [|- context[val_inject _ (Val.notint _) _ ]] =>
       eapply val_notint_inject
     | [|- context[val_inject _ (Val.addf _ _) _ ]] =>
       eapply val_addf_inject
     | [|- context[val_inject _ (Val.subf _ _) _ ]] =>
       eapply val_subf_inject
     | [|- context[val_inject _ (Val.mulf _ _) _ ]] =>
       eapply val_mulf_inject
     | [|- context[val_inject _ (Val.divf _ _) _ ]] =>
       eapply val_divf_inject
     | [|- context[val_inject _ (Val.absf _) _ ]] =>
       eapply val_absf_inject
     | [|- context[val_inject _ (Val.negf _) _ ]] =>
       eapply val_negf_inject
     | [|- context[val_inject _ (Val.add _ _) _ ]] =>
       eapply val_add_inject
     | [|- context[val_inject _ (Val.maketotal (Val.floatofint _)) _ ]] =>
       eapply val_floatofint_inject
     | [|- context[val_inject _ (Val.maketotal (Val.intoffloat _)) _ ]] =>
       eapply val_intoffloat_inject
     | [|- context[val_inject _ (compare_floats _ _ _ _) _ ]] =>
       eapply val_compare_floats_inject_neutral
     | [|- context[val_inject _ (undef_regs _ _ _) _ ]] =>
            eapply undef_regs_inject
     | [|- context[val_inject _ ((undef_regs _ _)# _) _ ]] =>
            eapply undef_regs_inject
     | _ => (eapply match_reg|| constructor || eauto)
  end
| _ => idtac
       end.



    Require Import liblayers.compat.CompatLayers.

    Ltac lens_norm_ortho_trivial :=
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
      unfold lift; lens_unfold_trivial; simpl.

    Ltac elim_none :=
      match goal with
        | [H : match ?X with | _ => _ end = Some _ |- _ ] => destruct X; try discriminate H
        | [H : if ?X then _ else _ = Some _ |- _ ] => destruct X; try discriminate H
      end.

    Ltac elim_none_eqn Hn :=
      match goal with
        | [H : match ?X with | _ => _ end = Some _ |- _ ] => destruct X eqn:Hn; try discriminate H
        | [H : if ?X then _ else _ = Some _ |- _ ] => destruct X eqn:Hn; try discriminate H
      end.

    Ltac elim_none' Hi :=
      match type of Hi with
        |  match ?X with | _ => _ end = Some _  => destruct X; try discriminate Hi
        |  if ?X then _ else _ = Some _  => destruct X; try discriminate Hi
      end.

    Ltac elim_none_eqn' Hi Hn :=
      match type of Hi with
        | match ?X with | _ => _ end = Some _  => destruct X eqn:Hn; try discriminate Hi
        | if ?X then _ else _ = Some _  => destruct X eqn:Hn; try discriminate Hi
      end.

    Ltac zmap_simpl :=
      repeat match goal with
      | [ H : ?a <> ?b, H' : appcontext [ZMap.get ?a (ZMap.set ?b _ _)] |- _ ] =>
        rewrite (ZMap.gso _ _ H) in H'
      | [ H : ?a <> ?b |- appcontext [ZMap.get ?a (ZMap.set ?b _ _)] ] =>
        rewrite (ZMap.gso _ _ H)
      | [ H : ?a <> ?b, H' : appcontext [ZMap.get ?b (ZMap.set ?a _ _)] |- _ ] =>
        let Hswap := fresh in 
        assert (Hswap: forall A (x y : A), x <> y -> y <> x) by auto;
        apply Hswap in H; rewrite (ZMap.gso _ _ H) in H'; clear Hswap
      | [ H : ?a <> ?b |- appcontext [ZMap.get ?b (ZMap.set ?a _ _)] ] =>
        assert (Hswap: forall A (x y : A), x <> y -> y <> x) by auto;
        apply Hswap in H; rewrite (ZMap.gso _ _ H); clear Hswap
      | [ H : appcontext [ZMap.get ?a (ZMap.set ?a _ _)] |- _ ] =>
        rewrite ZMap.gss in H
      | [ |- appcontext [ZMap.get ?a (ZMap.set ?a _ _)] ] =>
        rewrite ZMap.gss
      | [ H : ?a = ?b, H' : appcontext [ZMap.get ?a (ZMap.set ?b _ _)] |- _ ] =>
        match b with
          | appcontext [a] => rewrite <- H in H'; rewrite ZMap.gss in H'
          | _ => rewrite H in H'; rewrite ZMap.gss in H'
        end
      | [ H : ?a = ?b |- appcontext [ZMap.get ?a (ZMap.set ?b _ _)] ] =>
        match b with
          | appcontext [a] => rewrite <- H; rewrite ZMap.gss
          | _ => rewrite H; rewrite ZMap.gss
        end
      | [ H : ?a = ?b, H' : appcontext [ZMap.get ?b (ZMap.set ?a _ _)] |- _ ] =>
        match b with
          | appcontext [a] => rewrite <- H in H'; rewrite ZMap.gss in H'
          | _ => rewrite H in H'; rewrite ZMap.gss in H'
        end
      | [ H : ?a = ?b |- appcontext [ZMap.get ?b (ZMap.set ?a _ _)] ] =>
        match b with
          | appcontext [a] => rewrite <- H; rewrite ZMap.gss
          | _ => rewrite H; rewrite ZMap.gss
        end
      | [ H : appcontext [ZMap.get _ (ZMap.init _)] |- _ ] =>
        rewrite ZMap.gi in H
      | [ |- appcontext [ZMap.get _ (ZMap.init _)] ] =>
        rewrite ZMap.gi
      end.

    Ltac zmap_solve_goal :=
      repeat match goal with
               | [ |- appcontext [ZMap.get ?a (ZMap.set ?b _ _)] ] =>
                 destruct (zeq a b); zmap_simpl; simpl; auto
             end.

    Ltac zmap_solve :=
      repeat match goal with
               | [ |- appcontext [ZMap.get ?a (ZMap.set ?b _ _)] ] =>
                 destruct (zeq a b); zmap_simpl; simpl; auto
               | [ H : appcontext [ZMap.get ?a (ZMap.set ?b _ _)] |- _ ] =>
                 destruct (zeq a b); zmap_simpl; simpl; auto
             end.

    Ltac rewrites :=
      repeat match goal with
              | Heq1:?a = _, Heq2:?a = _ |- _ => rewrite Heq2 in Heq1; inv Heq1
              | Heq:?a = _ |- appcontext [if ?a then _ else _] => rewrite Heq
              | Heq:_ = ?a |- appcontext [if ?a then _ else _] => rewrite <- Heq
              | Heq:?a = _ |- appcontext [match ?a with _ => _ end] => rewrite Heq
              | Heq:_ = ?a |- appcontext [match ?a with _ => _ end] => rewrite <- Heq
              | Heq:?a = _, H: appcontext [if ?a then _ else _] |- _ => rewrite Heq in H
              | Heq:_ = ?a, H: appcontext [if ?a then _ else _] |- _ => rewrite <- Heq in H
              | Heq:?a = _, H: appcontext [match ?a with _ => _ end] |- _ => rewrite Heq in H
              | Heq:_ = ?a, H: appcontext [match ?a with _ => _ end] |- _ => rewrite <- Heq in H
            end.