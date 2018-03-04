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
Require Import CommonTactic.
Require Import Equivalence.
Require Import Decision.
Require Import FunctionalExtensionality.

Fact f_spec {A B} : forall f g : A -> B, f = g -> forall x, f x = g x.
Proof.
intros; subst; auto.
Qed.

Ltac fspec H x H' := 
  match type of H with
    | ?f = ?g => assert (H':= f_spec _ _ H x); simpl in H'
  end.

Section WITHP.

Section SEC.

  Context {state T U : Type}.
  
  Definition spec := state -> option (prod state (list U)).

  Definition secure (observe : state -> T) (S : spec) : Prop :=
    forall s1 s2 s1' o,
      S s1 = Some (s1',o) -> observe s1 = observe s2 -> 
      exists s2', S s2 = Some (s2',o) /\ observe s1' = observe s2'.

End SEC.

Open Scope nat_scope.
 
(* Parity example *)

Section PARITY.  

  Definition var := nat.
  Inductive par := even | odd.
  Definition p_state := var -> nat.
  Definition p_ostate := var -> par.

  Fixpoint parity (n : nat) : par :=
    match n with
      | O => even
      | S n => match parity n with
                 | even => odd
                 | odd => even
               end
    end.

  Definition p_observe (s : p_state) : p_ostate := fun x => parity (s x).

  (* add() { print (x+y)%2 } *)
  Variables x y : var.
  Definition add_spec : spec := 
    fun s => Some (s, parity (s x + s y) :: nil).

  Lemma add_parity :
    forall a b, parity (a+b) = 
      match parity a, parity b with
        | even, even => even
        | odd, odd => even
        | _, _ => odd
      end.
  Proof.
    induction a; simpl; intros.
    destruct (parity b); auto.
    rewrite IHa; destruct (parity a), (parity b); auto.
  Qed.

  Theorem add_secure : secure p_observe add_spec.
  Proof.
    unfold secure, p_observe, add_spec; intros until o; intros Hexec Hobs.
    inv Hexec; exists s2; split; auto.
    rewrite 2 add_parity.
    fspec Hobs x Hx; fspec Hobs y Hy.
    rewrite Hx, Hy; auto.
  Qed.

End PARITY.

Section AVERAGE.

  Variable N : nat.
  Definition a_state := nat -> nat.
  Definition a_ostate := nat.

  Fixpoint sum (s : a_state) n :=
    s n + match n with 
            | 0 => 0
            | S n => sum s n
          end.

  Definition a_observe (s : a_state) : a_ostate :=
    sum s N.

End AVERAGE.

(* Example for declassifying data in the future *)

Section TIME.

  Definition year := nat.
  Definition t_state := prod year nat.
  Definition t_ostate := option nat.

  Variable Y : year.

  Definition t_observe (s : t_state) : t_ostate :=
    if gt_dec (fst s) Y then Some (snd s) else None.

  (* read() { if (gettime() > Y) then print secret; } *)
  Definition print_spec : spec :=
    fun s : t_state => 
      Some (s, if gt_dec (fst s) Y then snd s :: nil else nil).

  Theorem print_secure : secure t_observe print_spec.
  Proof.
    unfold secure, t_observe, print_spec; intros until o; intros Hexec Hobs.
    inv Hexec; exists s2; split; auto.
    cases; auto.
    inv Hobs; auto.
  Qed.

  Definition t_ostate' := prod bool (option nat).

  Definition t_observe' (s : t_state) : t_ostate' :=
    if gt_dec (fst s) Y then (true, Some (snd s)) else (false, None).

  Lemma t_observe_equiv : 
    forall s1 s2, t_observe s1 = t_observe s2 <-> t_observe' s1 = t_observe' s2.
  Proof.
    unfold t_observe, t_observe'; intros; split; cases; inversion 1; auto.
  Qed.

  Lemma t_secure_equiv {U} : 
    forall S : spec(U:=U), secure t_observe S <-> secure t_observe' S.
  Proof.
    unfold secure; intros; split; intros until o; intros Hexec Hobs.
    - specialize (H s1 s2 s1' o Hexec).
      destruct H as [s2' [Hs2 Ho2]].
      apply t_observe_equiv; auto.
      exists s2'; split; auto.
      apply t_observe_equiv; auto.
    - specialize (H s1 s2 s1' o Hexec).
      destruct H as [s2' [Hs2 Ho2]].
      apply t_observe_equiv; auto.
      exists s2'; split; auto.
      apply t_observe_equiv; auto.
  Qed.

  Definition print_spec_bad : spec :=
    fun s : t_state => 
      Some ((S (fst s), snd s), 
            if gt_dec (fst s) Y then snd s :: nil else nil).

  Theorem print_secure_bad : secure t_observe print_spec_bad.
  Proof.
    unfold secure, t_observe, print_spec_bad; intros until o; intros Hexec Hobs.
    inv Hexec; exists (S (fst s2), snd s2); split; auto.
    cases; auto.
    inv Hobs; auto.
    simpl in *; subdestruct; cases; auto; try omega.
    (* if fst s1 = fst s2 = T, then this subgoal is unprovable! *)
  Abort.

End TIME.

(* Example of label tainting *)

Section LBL.

  Variable lbl : Type.
  Variable bot : lbl.
  Variable leq : lbl -> lbl -> Prop.
  Variable lub : lbl -> lbl -> lbl.
  
  Hypothesis leq_bot : forall l, leq bot l.
  Hypothesis leq_refl : forall l, leq l l.
  Hypothesis leq_antisym : forall l1 l2, leq l1 l2 -> leq l2 l1 -> l1 = l2.
  Hypothesis leq_trans : forall l1 l2 l3, leq l1 l2 -> leq l2 l3 -> leq l1 l3.
  Hypothesis leq_dec : forall l1 l2, {leq l1 l2} + {~ leq l1 l2}.

  Hypothesis lub_l : forall l1 l2, leq l1 (lub l1 l2).
  Hypothesis lub_r : forall l1 l2, leq l2 (lub l1 l2).
  Hypothesis lub_least : forall l l1 l2, leq l1 l -> leq l2 l -> leq (lub l1 l2) l.

  Variable obs : lbl.

  Definition l_state := var -> nat * lbl.
  Definition l_ostate := var -> nat * lbl.
  
  Definition l_observe (s : l_state) : l_ostate :=
    fun x => if leq_dec (snd (s x)) obs then s x else (O, snd (s x)).

  Variables x y z : var.

  (* x = y + z *)
  Definition add_store {U} : spec := 
    fun s => Some (fun w => if eq_nat_dec w x 
                            then (fst (s y) + fst (s z), lub (snd (s y)) (snd (s z)))
                            else s w, nil(A:=U)).

  Lemma leq_lub_convert : forall l1 l2 l, leq (lub l1 l2) l <-> leq l1 l /\ leq l2 l.
  Proof.
    intros; split; intros; [eauto | intuition].
  Qed.

  Ltac llub H := rewrite leq_lub_convert in H; destruct H.

  Theorem add_store_secure {U} : secure l_observe add_store(U:=U).
  Proof.
    unfold secure, l_observe, add_store; intros until o; intros Hexec Hobs.
    inv Hexec; exists (fun w : nat =>
        if eq_nat_dec w x
        then (fst (s2 y) + fst (s2 z), lub (snd (s2 y)) (snd (s2 z)))
        else s2 w); split; auto.
    extensionality w; fspec Hobs w Hw.
    cases; auto; simpl in *; subst.
    clear Hdestruct0; llub l.
    clear Hdestruct1; llub l0.
    fspec Hobs y Hy; fspec Hobs z Hz.
    destruct (leq_dec (snd (s1 y)) obs); try contradiction.
    destruct (leq_dec (snd (s2 y)) obs); try contradiction.
    destruct (leq_dec (snd (s1 z)) obs); try contradiction.
    destruct (leq_dec (snd (s2 z)) obs); try contradiction.
    rewrite Hy, Hz; auto.
    fspec Hobs y Hy; clear Hw.
    assert (snd (s1 y) = snd (s2 y)).
    subdestruct; try congruence; destruct (s1 y); inv Hy; auto.
    fspec Hobs z Hz.
    assert (snd (s1 z) = snd (s2 z)).
    subdestruct; try congruence; destruct (s1 z); inv Hz; auto.
    clear Hdestruct0; rewrite H in l; rewrite H0 in l; contradiction.
    fspec Hobs y Hy; clear Hw.
    assert (snd (s1 y) = snd (s2 y)).
    subdestruct; try congruence; destruct (s1 y); inv Hy; auto.
    fspec Hobs z Hz.
    assert (snd (s1 z) = snd (s2 z)).
    subdestruct; try congruence; destruct (s1 z); inv Hz; auto.
    clear Hdestruct0; rewrite H in n; rewrite H0 in n; contradiction.
    fspec Hobs y Hy; clear Hw.
    assert (snd (s1 y) = snd (s2 y)).
    subdestruct; try congruence; destruct (s1 y); inv Hy; auto.
    fspec Hobs z Hz.
    assert (snd (s1 z) = snd (s2 z)).
    subdestruct; try congruence; destruct (s1 z); inv Hz; auto.
    rewrite H, H0; auto.
  Qed.
                               
End LBL.

(* Modular calendar example *)

Section CAL.

  Variable principal : Type.
  Hypothesis peq_dec : forall p1 p2 : principal, Decision (p1 = p2).
  Variable obs : principal.
  Variable N : nat.

  Definition cal := nat -> option nat.
  Definition c_state := principal -> cal.
  Definition c_ostate := c_state.

  Definition c_observe (cals : c_state) : c_ostate := 
    fun p n => 
      match cals p n with
        | None => None
        | Some v => Some (if peq_dec p obs then v else O)
      end.

  Fixpoint isAllFree (cals : c_state) (ps : list principal) n :=
    match ps with
      | nil => true
      | p :: ps => match cals p n with
                     | None => isAllFree cals ps n
                     | Some _ => false
                   end
    end.

  Fixpoint findAllFree (cals : c_state) (ps : list principal) n :=
    if isAllFree cals ps n then Some n 
    else match n with
           | O => None
           | S n => findAllFree cals ps n
         end.

  Definition upd_cal c n (event : nat) : cal := 
    fun n' => if eq_nat_dec n' n then Some event else c n'.
   
  Fixpoint upd_cals cals ps n (event : nat) :=
    match ps with
      | nil => cals
      | p :: ps => 
          fun p' => if peq_dec p' p then upd_cal (cals p) n event 
                    else upd_cals cals ps n event p'
    end.

  Variable ps : list principal.
  Variable event : nat.
  Definition sched : spec :=
    fun cals => 
      match findAllFree cals ps N with
        | None => Some (cals, nil)
        | Some n => Some (upd_cals cals ps n event, n :: nil)
      end.

   Lemma isAllFree_secure :
    forall ps cals1 cals2 n,
      c_observe cals1 = c_observe cals2 -> 
      isAllFree cals1 ps n = isAllFree cals2 ps n.
  Proof.
    induction ps0; simpl; auto.
    unfold c_observe; intros.
    fspec H a H'; fspec H' n H''; subdestruct; auto.
  Qed.

  Lemma findAllFree_secure :
    forall n cals1 cals2 ps,
      c_observe cals1 = c_observe cals2 -> 
      findAllFree cals1 ps n = findAllFree cals2 ps n.
  Proof.
    induction n; simpl; intros; erewrite isAllFree_secure; eauto.
    erewrite IHn; auto.
  Qed.

  Lemma upd_cal_secure :
    forall cals1 cals2 n event,
      c_observe cals1 = c_observe cals2 -> 
      c_observe (fun p n' => upd_cal (cals1 p) n event n') = 
      c_observe (fun p n' => upd_cal (cals2 p) n event n').
  Proof.
    unfold c_observe; intros.
    extensionality p; extensionality n'.
    unfold upd_cal; fspec H p H'; fspec H' n' H''.
    cases; auto.
  Qed.

  Lemma upd_cals_secure :
    forall ps cals1 cals2 n event,
      c_observe cals1 = c_observe cals2 -> 
      c_observe (upd_cals cals1 ps n event) = c_observe (upd_cals cals2 ps n event).
  Proof.
    induction ps0; unfold c_observe; simpl; intros.
    extensionality p'; extensionality n'.
    fspec H p' H'; fspec H' n' H''; auto.
    extensionality p'; extensionality n'.
    destruct (peq_dec p' a); subst.
    eapply upd_cal_secure in H; unfold c_observe in H.
    fspec H a H1; fspec H1 n' H2; eauto.
    eapply IHps0 in H; unfold c_observe in H.
    fspec H p' H1; fspec H1 n' H2; eauto.
  Qed.

  Theorem find_secure : secure c_observe sched.
  Proof.
    unfold secure, sched; intros until o; intros Hexec Hobs.
    rewrite findAllFree_secure with (cals2:= s2) in Hexec; auto.
    subdestruct; inv Hexec.
    exists (upd_cals s2 ps n event); split; auto.
    apply upd_cals_secure; auto.
    exists s2; auto.
  Qed.

End CAL.

End WITHP.