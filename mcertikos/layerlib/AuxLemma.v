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
(*          Jérémie Koenig <jk@jk.fr.eu.org>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)
(** This file provide the auxilary lemmas for refinement proof*)
Require Import ClassicalEpsilon.
Require Import Coq.ZArith.BinInt.  
Require Import Coqlib.
(*Require Import compcert.lib.Coqlib.*)
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import AsmX.
Require Import Memory.
Require Import Globalenvs.
Require Import Errors.
Require Import AST.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CommonTactic.
Require Import Memory.
(*Require Import LayerDefinition.*)
Require Import AuxStateDataType.
(*Require Import XOmega.*)
Require Import liblayers.compcertx.Stencil.

(*Require Import DataType.*)

(** * Lemmas about arithmetic*)
Section Aux_Lemma.

  (** ** Properties related to [Z]*)
  Lemma multi_minus: 
    forall a b c :Z, a * c - b * c = (a - b) * c.
  Proof.
    intros.
    assert(HW1: (a - b) = (a + (-b))).
    omega.
    rewrite HW1.
    rewrite Z.mul_add_distr_r.
    rewrite Z.mul_opp_l.
    omega.
  Qed.

  Lemma Z_plus_le_nneg:
    forall a b c, a <= c -> 0<= b -> a <= c + b.
  Proof.
    intros.
    omega.
  Qed.
  
  Lemma Z_minus_le_same:
    forall a b c, a <= c -> a - b <= c - b.
  Proof.
    intros.
    omega.
  Qed.

  Lemma eqmod_mod_eq':
    forall x y, x mod Int.modulus = y mod Int.modulus -> Int.eqmod (Int.modulus) x y.
  Proof.
    intros.
    unfold Int.eqmod.
    assert(HNE: Int.modulus > 0).
    specialize (Int.Z_mod_modulus_range 0).
    intros.
    omega.
    rewrite Zmod_eq in H; trivial.
    rewrite Zmod_eq in H; trivial.
    set (a := x/Int.modulus) in *.
    set (b := y/Int.modulus) in *.
    exists (a - b).
    assert(HW1: x = a * Int.modulus - b * Int.modulus + y).
    omega.
    rewrite multi_minus in HW1.
    trivial.
  Qed.

  (** ** Properties about [Int]*)
  Lemma int_max_unsigned:
    0 <= 0 <= Int.max_unsigned.
  Proof.
    specialize (Int.max_signed_pos).
    specialize (Int.max_signed_unsigned).
    intros.
    omega.
  Qed.

  Lemma max_pos: Int.max_unsigned > 0.
  Proof.
    specialize (Int.max_signed_pos).
    specialize (Int.max_signed_unsigned).
    intros.
    omega.
  Qed.

  Lemma PDX_max: PDX Int.max_unsigned = 1023.
  Proof.
    unfold PDX, Int.max_unsigned.
    simpl. reflexivity.
  Qed.

  Lemma PTX_max: PTX Int.max_unsigned = 1023.
  Proof.
    unfold PTX, Int.max_unsigned.
    simpl. reflexivity.
  Qed.
  
  Lemma int_max: Int.max_unsigned = 4294967295.
  Proof.
    trivial.
  Qed.

  Fixpoint wrap_init_data (n: nat): list init_data :=
    match n with
      | O => nil
      | (Datatypes.S) k => (Init_int32 (Int.repr 0)) :: (wrap_init_data k)
    end.

  Lemma Pregmap_Simpl:
    forall (A : Type) (i j : Pregmap.elt) (x : A) (m : Pregmap.t A),
      m # j <- x i = (if Pregmap.elt_eq i j then x else m i).
  Proof.
    specialize (Pregmap.gsspec).
    intro HG.
    unfold Pregmap.get in HG.
    trivial.
  Qed.

  Lemma kctxt_inj_empty:
    forall f n,
      kctxt_inj f n (ZMap.init (Pregmap.init Vundef)) (ZMap.init (Pregmap.init Vundef)).
  Proof.
    unfold kctxt_inj; intros.
    rewrite ZMap.gi; unfold Pregmap.get.
    rewrite Pregmap.gi; constructor.
  Qed.

  Lemma kctxt_inj_incr:
    forall f f' n kctxt kctxt',
      kctxt_inj f n kctxt kctxt'
      -> inject_incr f f'
      -> kctxt_inj f' n kctxt kctxt'.
  Proof.
    unfold kctxt_inj; intros; eauto.
  Qed.

  Lemma kctxt_inj_set:
    forall f n n' kctxtp kctxtp' kctxt kctxt',
      kctxt_inj f n kctxtp kctxtp'
      -> (forall r i , ZtoPreg i = Some r -> val_inject f (Pregmap.get r kctxt) (Pregmap.get r kctxt'))
      -> kctxt_inj f n (ZMap.set n' kctxt kctxtp) (ZMap.set n' kctxt' kctxtp').
  Proof.
    unfold kctxt_inj; intros.
    destruct (zeq n' n0); subst.
    - repeat rewrite ZMap.gss; eauto.
    - repeat rewrite ZMap.gso; eauto.
  Qed.

  Lemma uctxt_inj_empty:
    forall f,
      uctxt_inj f (ZMap.init (ZMap.init Vundef)) (ZMap.init (ZMap.init Vundef)).
  Proof.
    unfold uctxt_inj; intros.
    repeat rewrite ZMap.gi.
    constructor.
  Qed.

  Lemma uctxt_inj_incr:
    forall f f' uctxt uctxt',
      uctxt_inj f uctxt uctxt'
      -> inject_incr f f'
      -> uctxt_inj f' uctxt uctxt'.
  Proof.
    unfold uctxt_inj; intros; eauto.
  Qed.

  Require Import Constant.

  Lemma uctxt_inj_set:
    forall f uctxtp uctxtp' uctxt uctxt' n',
      uctxt_inj f uctxtp uctxtp'
      -> (forall j,       
            0<= j < UCTXT_SIZE
            -> val_inject f (ZMap.get j uctxt) (ZMap.get j uctxt'))
      -> uctxt_inj f (ZMap.set n' uctxt uctxtp) (ZMap.set n' uctxt' uctxtp').
  Proof.
    unfold uctxt_inj; intros.
    destruct (zeq n' i); subst.
    - repeat rewrite ZMap.gss; eauto.
    - repeat rewrite ZMap.gso; eauto.
  Qed.

  Lemma VMCS_inj_incr:
    forall f f' v1 v2,
      VMCS_inj f v1 v2 ->
      inject_incr f f' ->
      VMCS_inj f' v1 v2.
  Proof.
    intros. inv H.
    econstructor; eauto.
  Qed.

  Lemma VMCS_inj_set:
    forall f r a n v v' value value',
      VMCS_inj f (VMCSValid r a v) (VMCSValid r a v')
      -> val_inject f value value'
      -> VMCS_inj f (VMCSValid r a (ZMap.set n value v))
                    (VMCSValid r a (ZMap.set n value' v')).
  Proof.
    intros. inversion H.
    constructor; intros.
    destruct (zeq i n) as [ -> |];
      [ rewrite 2 ZMap.gss | rewrite 2 ZMap.gso ];
      auto.
  Qed.

  Lemma VMCS_inj_set_int:
    forall f r a n m v v',
      VMCS_inj f (VMCSValid r a v) (VMCSValid r a v')
      -> VMCS_inj f (VMCSValid r a (ZMap.set n (Vint m) v))
                    (VMCSValid r a (ZMap.set n (Vint m) v')).
  Proof.
    intros; apply VMCS_inj_set; auto.
  Qed.

  Lemma VMX_inj_incr:
    forall f f' v1 v2,
      VMX_inj f v1 v2 ->
      inject_incr f f' ->
      VMX_inj f' v1 v2.
  Proof.
    intros. inv H.
    econstructor; eauto.
  Qed.

  Lemma VMX_inj_set:
    forall f n v v' value value',
      VMX_inj f v v'
      -> val_inject f value value'
      -> VMX_inj f (ZMap.set n value v) (ZMap.set n value' v').
  Proof.
    intros; inv H.
    constructor; intros.
    destruct (zeq i n) as [ -> |];
      [ rewrite 2 ZMap.gss | rewrite 2 ZMap.gso ];
      auto.
  Qed.

  Lemma VMX_inj_set_int:
    forall f n m v v',
      VMX_inj f v v'
      -> VMX_inj f (ZMap.set n (Vint m) v) (ZMap.set n (Vint m) v').
  Proof.
    intros; apply VMX_inj_set; auto.
  Qed.

End Aux_Lemma.

Section List_Lemma.

  Lemma Lremove_outside:
    forall (l: list LATOwner) x y, y <> x -> In y l -> In y (Lremove x l).
  Proof.
    induction l; intros.
    - inv H0.
    - simpl. destruct (LATOwner_dec x a); subst.
      + inv H0. congruence. auto.
      + inv H0. left; trivial.
        right; auto.
  Qed.

  Lemma Lremove_incl:
    forall (l: list LATOwner) x, incl (Lremove x l) l.
  Proof.
    induction l; intros.
    - apply incl_refl.
    - simpl. destruct (LATOwner_dec x a); subst.
      + apply incl_tl. simpl.
        destruct (LATOwner_dec a a); subst. eauto.
        congruence.
      + apply incl_cons. simpl; eauto.
        apply incl_tl. auto.
  Qed.

  Lemma removelast_incl:
    forall {A:Type} (l: list A), incl (removelast l) l.
  Proof.
    induction 0.
    simpl.
    apply incl_refl.
    
    simpl.
    destruct l.
    apply incl_tl. 
    apply incl_refl.
    apply incl_cons.
    simpl; eauto.
    apply incl_tl.
    trivial.
  Qed.

  Lemma remove_incl:
    forall (l: list Z) x, incl (remove zeq x l) l.
  Proof.
    intros.
    induction l.
    simpl.
    apply incl_refl.
    
    simpl.
    destruct (zeq x a).
    apply incl_tl. 
    trivial.
    apply incl_cons.
    simpl; eauto.
    apply incl_tl.
    trivial.
  Qed.

  Lemma remove_outside:
    forall (l: list Z) x y, y <> x -> In y l -> In y (remove zeq x l).
  Proof.
    intros.
    induction l.
    inv H0.
    
    simpl.
    destruct (zeq x a).
    inv H0.
    elim H; trivial.
    auto.

    inv H0.
    simpl.
    left; trivial.
    simpl.
    right.
    auto.
  Qed.

  Lemma remove_count_outside:
    forall (l: list Z) x y, y <> x -> count_occ zeq (remove zeq x l) y = count_occ zeq l y.
  Proof.
    intros.
    induction l.
    simpl.
    trivial.
    
    simpl.
    destruct (zeq x a).
    destruct (zeq a y).
    omega.
    trivial.

    destruct (zeq a y).
    subst.
    rewrite count_occ_cons_eq; trivial.
    rewrite IHl.
    trivial.
    rewrite count_occ_cons_neq; auto.

  Qed.

  Lemma last_correct:
    forall (l: list Z) x, x <> (last l x) -> In (last l x) l.
  Proof.
    intros.
    induction l.
    simpl in H.
    elim H.
    trivial.
    
    simpl in *.
    destruct l.
    left; trivial.
    right; auto.
  Qed.

End List_Lemma.

Section Stencil_Lemma.

  Context `{Hstencil: Stencil}.

  Lemma inject_forward_equal:
    forall s id b b' delta ι
           (match_inject_forward : forall (b1 b2 : block) (delta : Z),
                                     ι b1 = Some (b2, delta) ->
                                     delta = 0 /\ (b1 <= b2)%positive)
           (match_inject_flat : inject_incr (Mem.flat_inj (genv_next s)) ι),
      find_symbol s id = Some b ->
      ι b' = Some (b, delta) ->
      (b, delta) = (b', 0).
  Proof.
    intros.
    assert (ι b' = Some (b', 0%Z)).
    {
      apply match_inject_flat.
      unfold Mem.flat_inj.
      destruct (plt b' (genv_next s)) as [Hb' | Hb'].
      reflexivity.
      elim Hb'.
      apply match_inject_forward in H0.
      apply genv_symb_range in H.
      xomega.
    }
    congruence.
  Qed.

  Lemma inject_forward_equal':
    forall s id b b' delta ι
           (match_inject_forward : forall (b1 b2 : block) (delta : Z),
                                     ι b1 = Some (b2, delta) ->
                                     delta = 0 /\ (b1 <= b2)%positive)
           (match_inject_flat : inject_incr (Mem.flat_inj (genv_next s)) ι),
      find_symbol s id = Some b' ->
      ι b' = Some (b, delta) ->
      (b, delta) = (b', 0).
  Proof.
    intros.
    assert (ι b' = Some (b', 0%Z)).
    {
      apply match_inject_flat.
      unfold Mem.flat_inj.
      destruct (plt b' (genv_next s)) as [Hb' | Hb'].
      reflexivity.
      elim Hb'.
      apply match_inject_forward in H0.
      apply genv_symb_range in H.
      xomega.
    }
    congruence.
  Qed.

End Stencil_Lemma.

Section Injection.

(** * Properties related to memory injection*)       
  Lemma val_list_inject_args: 
    forall rs rs' args  f,
      (forall reg : PregEq.t,
         val_inject f (Pregmap.get reg rs) (Pregmap.get reg rs'))
      -> val_list_inject f (map rs args) (map rs' args).
  Proof.
    induction args; intros; constructor; eauto.
  Qed.

  Lemma eval_testcond_inj: 
    forall f rs r' c0 b,
      (forall reg : PregEq.t,
         val_inject f (Pregmap.get reg rs) (Pregmap.get reg r'))
      -> eval_testcond c0 rs = Some b
      -> eval_testcond c0 r' = Some b.
  Proof.
    intros.
    unfold Pregmap.get in H.
    generalize H.
    intro HT.
    generalize HT.
    intro HTT.
    specialize (HT ZF).
    specialize (HTT CF).
    generalize H.
    intro HT1.
    specialize (HT1 SF).
    generalize H.
    intro HT2.
    specialize (HT2 PF).
    generalize H.
    intro HT3.
    specialize (HT3 OF).
    unfold eval_testcond in *.
    destruct c0.
    destruct (rs ZF); inv H0; inv HT; try constructor.
    destruct (rs ZF); inv H0; inv HT; try constructor.
    destruct (rs CF); inv H0; inv HTT; try constructor.
    destruct (rs CF); inv H0; inv HTT; try constructor.
    destruct (rs ZF); inv H2; inv HT; try constructor.
    destruct (rs CF); inv H0; inv HTT; try constructor.
    destruct (rs CF); inv H0; inv HTT; try constructor.
    destruct (rs ZF); inv H2; inv HT; try constructor.
    destruct (rs OF); inv H0; inv HT3; try constructor.
    destruct (rs SF); inv H2; inv HT1; try constructor.
    destruct (rs OF); inv H0; inv HT3; try constructor.
    destruct (rs SF); inv H2; inv HT1; try constructor.
    destruct (rs ZF); inv H1; inv HT; try constructor.
    destruct (rs OF); inv H0; inv HT3; try constructor.
    destruct (rs SF); inv H2; inv HT1; try constructor.
    destruct (rs OF); inv H0; inv HT3; try constructor.
    destruct (rs SF); inv H2; inv HT1; try constructor.
    destruct (rs ZF); inv H1; inv HT; try constructor.
    destruct (rs PF); inv H0; inv HT2; try constructor.
    destruct (rs PF); inv H0; inv HT2; try constructor.
  Qed.

  Lemma flat_inj_inject_incr:
    forall n n',
      (n <= n')%positive
      -> inject_incr (Mem.flat_inj n) (Mem.flat_inj n').
  Proof.
    unfold inject_incr, Mem.flat_inj; intros.
    destruct (plt b n); contra_inv.
    destruct (plt b n'); trivial.
    xomega.
  Qed.

  Section GENV_INJ.
    Context `{F : Type}.
    Context `{V: Type}.
    Context `{ge: (Genv.t F V)}.

    Lemma flat_inj_func:
      forall b c,
        Genv.find_funct_ptr ge b = Some c 
        -> (Mem.flat_inj (Genv.genv_next ge)) b = Some (b, 0).
    Proof.
      intros.
      unfold Mem.flat_inj.
      caseEq(plt b (Genv.genv_next ge)).
      intros.
      trivial.
      intro HB.
      unfold Genv.find_funct_ptr in H.
      specialize (Genv.genv_funs_range _ _ H).
      intro HB'.
      inv HB'.
      intros. elim HB.
      trivial.
    Qed.

    Lemma find_symbol_inject: 
      forall f id b,
        inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
        Genv.find_symbol ge id = Some b ->
        f b = Some (b, 0).
    Proof.
      intros.
      unfold Genv.find_symbol in H0.
      specialize (Genv.genv_symb_range _ _ H0).
      intro HB.
      assert(HF: Mem.flat_inj (Genv.genv_next ge) b = Some (b,0)).
      unfold Mem.flat_inj.
      caseEq(plt b  (Genv.genv_next ge)); intros.
      trivial.
      xomega.
      specialize (H _ _ _ HF).
      trivial.
    Qed.

    Section WITHSTENCIL.

      Context `{Hstencil: Stencil}.

      Lemma stencil_find_symbol_inject: 
        forall s f id b,
          inject_incr (Mem.flat_inj (genv_next s)) f ->
          Genv.find_symbol ge id = Some b ->
          stencil_matches s ge ->
          f b = Some (b, 0).
      Proof.
        intros. inv H1. rewrite <- stencil_matches_genv_next in H.
        eapply find_symbol_inject; eauto.
      Qed.

      Lemma stencil_find_symbol_inject': 
        forall (s: stencil) f id b,
          inject_incr (Mem.flat_inj (genv_next s)) f ->
          find_symbol s id = Some b ->
          f b = Some (b, 0).
      Proof.
        intros. 
        unfold find_symbol in H0.
        specialize (genv_symb_range _ _ _ H0).
        intro HB.
        assert(HF: Mem.flat_inj (genv_next s) b = Some (b,0)).
        unfold Mem.flat_inj.
        caseEq (plt b (genv_next s)); intros.
        trivial.
        xomega.
        specialize (H _ _ _ HF).
        trivial.
    Qed.

      Lemma reg_symbol_inject:
        forall (rs1 rs2: regset) r b n i s f,
          rs1 r = Vptr b n->
          find_symbol s i = Some b ->
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs1) (Pregmap.get reg rs2)) ->
          inject_incr (Mem.flat_inj (genv_next s)) f ->
          rs2 r = Vptr b n.
      Proof.
        intros. specialize (H1 r).
        unfold Pregmap.get in *.
        rewrite H in H1.
        exploit stencil_find_symbol_inject'; eauto.
        intros HFB.
        inv H1. rewrite H6 in HFB.
        inv HFB.
        rewrite Int.add_zero.
        reflexivity.
      Qed.

      Lemma stencil_find_funct_ptr_inject:
        forall f s b ef,
          stencil_matches s ge ->
          Genv.find_funct_ptr ge b = Some ef ->
          inject_incr (Mem.flat_inj (genv_next s)) f ->
          f b = Some (b, 0%Z).
      Proof.
        intros; apply H1. inv H.
        rewrite <-stencil_matches_genv_next.
        eapply flat_inj_func; eauto.
      Qed.

      Lemma stencil_symbol_offset_inject:
        forall s f,
          inject_incr (Mem.flat_inj (genv_next s)) f ->
          stencil_matches s ge ->
          forall id ofs,
            val_inject f (symbol_offset ge id ofs) (symbol_offset ge id ofs).
      Proof.
        intros; unfold symbol_offset. case_eq (Genv.find_symbol ge id); auto.
        intros. eapply stencil_find_symbol_inject in H; eauto.
        econstructor; eauto.
        rewrite Int.add_zero. reflexivity.
      Qed.

      Lemma eval_testcond_inject:
        forall (rs1 rs2: regset) f,
          (forall r, val_inject f (Pregmap.get r rs1) (Pregmap.get r rs2)) ->
          forall c b,
            eval_testcond c rs1 = Some b ->
            eval_testcond c rs2 = Some b.
      Proof.
        intros. unfold Pregmap.get in *.
        destruct c; simpl in *;
        repeat match goal with
                 | [|- context [rs2 ?a]] => 
                   pose proof (H a) as Hv1; destruct (rs1 a); try discriminate; inv Hv1; trivial
               end.
      Qed.

      Lemma meminj_preserves_globals_incr:
        forall s f,
          inject_incr (Mem.flat_inj (genv_next s)) f ->
          stencil_matches s ge ->
          (forall (b1 b2 : block) (delta : Z),
             f b1 = Some (b2, delta) -> delta = 0%Z /\ (b1 <= b2)%positive) ->
          meminj_preserves_globals ge f.
      Proof.
        intros. inv H0. rewrite <- stencil_matches_genv_next in H.
        constructor; eauto.
        intros. eapply find_symbol_inject; eauto.
        split; intros.
        eapply H. unfold Mem.flat_inj.
        eapply Genv.genv_vars_range in H0.
        destruct (plt b (Genv.genv_next ge)); trivial.
        congruence.
        eapply Genv.genv_vars_range in H0.
        assert(f b1 = Some (b1, 0%Z)).
        {
          eapply H. unfold Mem.flat_inj.
          destruct (plt b1 (Genv.genv_next ge)); trivial.
          eapply H1 in H2. destruct H2 as [_ ?].
          xomega.
        }
        rewrite H2 in H3.
        inv H3; trivial.
      Qed.

    End WITHSTENCIL.

    Lemma find_symbol_inject': 
      forall f id b b' delta,
        inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
        Genv.find_symbol ge id = Some b ->
        f b = Some (b', delta) ->
        (b', delta) = (b, 0).
    Proof.
      intros.
      exploit find_symbol_inject; eauto.
      intros HFB.
      rewrite H1 in HFB; inv HFB; trivial.
    Qed.

    Lemma nextinstr_inject':
      forall j rs rs',
        (forall r, val_inject j (Pregmap.get r rs) (Pregmap.get r rs')) ->
        forall r, val_inject j (Pregmap.get r (nextinstr rs)) (Pregmap.get r (nextinstr rs')).
    Proof.
      apply nextinstr_inject.
    Qed.

    Lemma nextinstr_nf_inject':
      forall j rs rs',
        (forall r, val_inject j (Pregmap.get r rs) (Pregmap.get r rs')) ->
        forall r, val_inject j (Pregmap.get r (nextinstr_nf rs)) (Pregmap.get r (nextinstr_nf rs')).
    Proof.
      apply nextinstr_nf_inject.
    Qed.

    Lemma undef_regs_inject':
      forall j rs rs',
        (forall r, val_inject j (Pregmap.get r rs) (Pregmap.get r rs')) ->
        forall l r, val_inject j (Pregmap.get r (undef_regs l rs)) (Pregmap.get r (undef_regs l rs')).
    Proof.
      apply undef_regs_inject.
    Qed.

    Lemma Val_add_simpl:
      forall v1 v2 f n,
        val_inject f v1 v2 ->
        val_inject f (Val.add v1 (Vint n)) (Val.add v2 (Vint n)).
    Proof.
      intros.
      unfold Val.add.
      destruct v1; inv H;
      econstructor; eauto.
      Int_Add_Simpl.
    Qed.

    Lemma PC_add:
      forall rs r' f b ofs n,
        rs PC = Vptr b ofs ->
        r' PC = Vptr b ofs ->
        f b = Some (b,0) ->
        val_inject f (Val.add (rs PC) (Vint n)) (Val.add (r' PC) (Vint n)).
    Proof.
      intros.
      rewrite H.
      rewrite H0.
      econstructor; eauto.
      rewrite Int.add_zero.
      trivial.
    Qed.

    Lemma undef_inj:
      forall rs r' f,
        (forall reg, val_inject f (Pregmap.get reg rs) (Pregmap.get reg r')) ->
        val_inject f (Val.add (rs PC) Vone) (Val.add (r' PC) Vone) ->
        val_inject f (Val.add (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs PC) Vone)
                   (Val.add (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) r' PC) Vone).
    Proof.
      intros.
      unfold undef_regs.
      repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
      trivial.
    Qed.
    
    Lemma undef_inj':
      forall rs r' f,
        (forall reg, val_inject f (Pregmap.get reg rs) (Pregmap.get reg r')) ->
        (forall reg, val_inject f (Pregmap.get reg (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs))
                                (Pregmap.get reg (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) r'))).
    Proof.
      intros.
      unfold undef_regs.
      repeat (rewrite Pregmap.gsspec; simpl); repeat (rewrite Pregmap_Simpl; simpl);
      trivial.
      repeat IF_Simpl.
    Qed.

    Lemma PC_ofs_inj: 
      forall rs r' f b ofs,
        (forall reg, val_inject f (Pregmap.get reg rs) (Pregmap.get reg r')) ->
        inject_incr (Mem.flat_inj (Genv.genv_next ge)) f ->
        Mem.flat_inj (Genv.genv_next ge) b = Some (b, 0) ->
        rs PC = Vptr b ofs ->
        r' PC = Vptr b ofs /\ f b = Some (b,0).
    Proof.
      intros.
      specialize (H PC).
      unfold Pregmap.get in H.
      rewrite H2 in H.
      inv H.
      specialize (H0 _ _ _ H1).
      rewrite H0 in H6.
      inv H6.
      rewrite Int.add_unsigned.
      rewrite Int.unsigned_repr;trivial. 
      rewrite Z.add_0_r. 
      rewrite Int.repr_unsigned.
      split; trivial.
      specialize (Int.unsigned_range_2 Int.zero).
      rewrite Int.unsigned_zero.
      trivial.
    Qed.

    Lemma val_inject_defined:
      forall v1 v2 f, 
        v1 <> Vundef -> val_inject f v1 v2 -> v2 <> Vundef.
    Proof.
      inversion 2; congruence.
    Qed.

    Lemma reg_val_inject_defined:
      forall (rs rs': regset) r f, 
        rs r <> Vundef -> val_inject f (rs r) (rs' r) -> (rs' r) <> Vundef.
    Proof.
      intros; eapply val_inject_defined; eauto 1.
    Qed.

  End GENV_INJ.

End Injection.

Section WITHMEM.

Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compat.CompatData.
Require Import Observation.

  Context `{Hobs: Observation}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Lemma volatile_load_without_d {D: compatdata}:
    forall {F V} (ge: Genv.t F V) m d b ofs t v chunk,
      volatile_load (mem:= mwd D) ge chunk (m, d) b ofs t v
      -> volatile_load ge chunk m b ofs t v.
  Proof.
    intros. inv H; constructor; eauto.
  Qed.

  Lemma volatile_load_with_d {D: compatdata}:
    forall {F V} (ge: Genv.t F V) m d b ofs t v chunk,
      volatile_load ge chunk m b ofs t v ->
      volatile_load (mem:= mwd D) ge chunk (m, d) b ofs t v.
  Proof.
    intros. inv H; constructor; eauto.
  Qed.

  Lemma volatile_store_without_d {D: compatdata}:
    forall {F V} (ge: Genv.t F V) WB m m' d d' b ofs t v chunk,
      volatile_store (mem:= mwd D) WB ge chunk (m, d) b ofs t v (m', d')
      -> volatile_store WB ge chunk m b ofs t v m' /\ d = d'.
  Proof.
    intros. inv H. 
    - split; trivial; try constructor; eauto.
    - lift_unfold. destruct H1 as [? ?]; subst.
      split; trivial. econstructor; eauto.
  Qed.

  Lemma volatile_store_with_d {D: compatdata}:
    forall {F V} (ge: Genv.t F V) WB m m' d b ofs t v chunk,
      volatile_store WB ge chunk m b ofs t v m' ->
      volatile_store (mem:= mwd D) WB ge chunk (m, d) b ofs t v (m', d).
  Proof.
    intros. inv H; constructor; eauto.
    lift_unfold. split; trivial.
  Qed.

  Lemma free_range:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall m1 m1' b lo hi,
      Mem.free m1 b lo hi = Some m1' ->
      (lo < hi)%Z \/ m1' = m1.
  Proof. 
    intro; apply Mem.free_range.
  Qed.

  Lemma storebytes_empty:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall m b ofs m',
      Mem.storebytes m b ofs nil = Some m'
      -> m' = m.
  Proof.
    intro; eapply Mem.storebytes_empty.
  Qed.

End WITHMEM.

Ltac rewrite_omega :=
  repeat (lazymatch goal with
         | [|- context[PDX Int.max_unsigned]] => rewrite PDX_max
         | [ H: context[PDX Int.max_unsigned] |- _] => rewrite PDX_max in *
         | [|- context[PTX Int.max_unsigned]] => rewrite PTX_max
         | [ H: context[PTX Int.max_unsigned] |- _] => rewrite PTX_max in *
         | [|- context[Int.max_unsigned]] => rewrite int_max
         | [H: context[Int.max_unsigned] |- _] => rewrite int_max in *
          end); try xomega.
