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
Require Import compcert.lib.Axioms.
Require Export compcert.common.Errors.
Require Import liblayers.lib.ExtensionalityAxioms.
Require Export liblayers.lib.Functor.
Require Export liblayers.lib.Monad.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.Structures.
Require Import liblayers.logic.LayerData.


(** * [res] is a monad *)

Global Instance res_functor_ops: FunctorOps res :=
  {
    fmap A B f x := Errors.bind x (fun x => Errors.OK (f x))
  }.

Global Instance res_functor_prf: Functor res.
Proof.
  split.
  * intros A x.
    destruct x; reflexivity.
  * intros A B C f g x.
    destruct x; reflexivity.
Qed.

Global Instance res_monad_ops: MonadOps res :=
  {
    ret := Errors.OK;
    bind A B f x := Errors.bind x f
  }.

Global Instance res_monad_prf: Monad res.
Proof.
  split; try typeclasses eauto.
  * intros A B f.
    extensionality mx.
    destruct mx; reflexivity.
  * intros A B f x.
    reflexivity.
  * intros A mx.
    destruct mx; reflexivity.
  * intros A B C f g mx.
    destruct mx; reflexivity.
Qed.

Global Instance res_monad_inv_ret:
  MonadInvRet res.
Proof.
  intros A x y Hxy.
  inversion Hxy.
  reflexivity.
Qed.

Global Instance res_monad_inv_bind:
  MonadInvBind res.
Proof.
  intros A B f ma b H.
  unfold ret, bind in H; simpl in *.
  destruct ma; try discriminate.
  eauto.
Qed.

Lemma res_bind_error {A B} (f: A -> res B) msg:
  bind f (Error msg) = Error msg.
Proof.
  reflexivity.
Qed.

Hint Rewrite @res_bind_error : monad.

(** * Lifting orders on [res] *)

(** TODO: define [res_rel] as well? *)

(** We need failure on top: <explain>. *)

Inductive res_le {A B} (R: rel A B): rel (res A) (res B) :=
  | res_le_ok_def:
      (R ++> res_le R) (@OK A) (@OK B)
  | res_le_error (msg: errmsg):
      UpperBound (res_le R) (Error msg).

Global Existing Instance res_le_error.

Global Instance res_le_ok:
  Proper (∀ R, R ++> res_le R) (@OK).
Proof.
  exact @res_le_ok_def.
Qed.

Local Instance res_le_op `(Le): Le (res A) :=
  { le := res_le (≤) }.

Global Instance res_le_monotonic {A B}:
  Proper (subrel ++> subrel) (@res_le A B).
Proof.
  intros R1 R2 HR x y H.
  destruct H; constructor.
  apply HR; assumption.
Qed.

Global Instance res_preorder `(PreOrder):
  PreOrder (res_le R).
Proof.
  split.
  * intros [x | msg].
    constructor; reflexivity.
    constructor.
  * intros x y z Hxy Hyz.
    destruct Hxy as [x y Hxy | x msg].
    + inversion Hyz.
      - constructor.
        transitivity y; trivial.
      - constructor.
    + inversion Hyz.
      constructor.
Qed.

Global Instance res_lower_bound {A B} (R: rel A B) (x: A):
  LowerBound R x ->
  LowerBound (res_le R) (OK x).
Proof.
  intros H [y|m]; constructor.
  apply lower_bound.
Qed.

Global Instance res_le_bind:
  Proper
    (∀ RA, ∀ RB, (RA ++> res_le RB) ++> (res_le RA ++> res_le RB))
    (@bind res _ _).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros f g Hfg.
  intros x1 x2 Hx.
  destruct Hx as [a1 a2 Ha | a1 m2].
  * monad_norm.
    apply Hfg.
    assumption.
  * monad_norm.
    constructor.
Qed.

Global Instance res_le_fmap:
  Proper (∀ RA, ∀ RB, (RA ++> RB) ++> res_le RA ++> res_le RB) (@fmap res _).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros f g Hfg ra1 ra2 Hra.
  destruct Hra; constructor; eauto.
Qed.

Hint Resolve (res_le_ok : forall A B R x y, _ -> res_le _ _ _) : liblayers.
Hint Resolve (res_le_error : forall R msg x, res_le _ _ _) : liblayers.
Hint Resolve (res_le_bind : forall A1 A2 (RA: rel A1 A2) B1 B2 (RB: rel B1 B2) (f: A1 -> res B1) (g: A2 -> res B2) Hfg (x: res A1) (y: res A2) (Hxy: res_le RA x y), res_le RB (bind f x) (bind g y)) : liblayers.
Hint Resolve (res_le_fmap : forall A1 A2 (RA: rel A1 A2) B1 B2 (RB: rel B1 B2) (f: A1 -> B1) (g: A2 -> B2) Hfg (x: res A1) (y: res A2) (Hxy: res_le RA x y), res_le RB (fmap f x) (fmap g y)) : liblayers.
Hint Extern 1 ((_ ==> _) _ _)%signature => intro : liblayers.

(** ** Data-indexed version *)

Local Instance res_sim_op `(Tsim: Sim): Sim _ (fun D => res (T D)) :=
  { simRR D1 D2 R := res_le (sim R) }.

(** I'm not sure if those are still necessary now that we use the
  generalized [rel]. *)

Global Instance OK_sim_monotonic `(Tsim: Sim):
  Proper (∀ R : simrel D1 D2, sim R ++> sim R) (fun D => @OK (T D)).
Proof.
  intros D1 D2 R.
  apply res_le_ok.
Qed.

Global Instance res_sim_bind {V E} {A B: V -> Type}:
  forall (RA: sim_relation E A) (RB: sim_relation E B),
    Proper
      (∀ e: E v1 v2,
         (RA v1 v2 e ++> res_le (RB v1 v2 e)) ++>
         (res_le (RA v1 v2 e) ++> res_le (RB v1 v2 e)))
      (fun (v : V) => bind (A := A v) (B := B v)).
Proof.
  intros RA RB v1 v2 e.
  intros f g Hfg x y Hxy.
  destruct Hxy as [x y Hxy | y msg].
  * monad_norm.
    apply Hfg.
    assumption.
  * monad_norm.
    constructor.
Qed.

Global Instance res_sim_fmap {V E} {A B: V -> Type}:
  forall (RA: sim_relation E A) (RB: sim_relation E B),
    Proper
      (∀ e: E v1 v2,
         (RA v1 v2 e ++> RB v1 v2 e) ++>
         (res_le (RA v1 v2 e) ++> res_le (RB v1 v2 e)))
      (fun (v : V) => fmap (A := A v) (B := B v)).
Proof.
  intros RA RB v1 v2 e.
  intros f g Hfg x y Hxy.
  destruct Hxy as [x y Hxy | y msg].
  * monad_norm.
    constructor.
    apply Hfg.
    assumption.
  * monad_norm.
    constructor.
Qed.


(** * Orders for [res ∘ option] *)

Require Import OptionOrders.

Lemma res_option_le_ok_none {A} (R: relation A) (y: res (option A)):
  res_le (option_le R) (OK None) y.
Proof.
  apply lower_bound.
Qed.

Hint Resolve res_option_le_ok_none: liblayers.


(** * Decision-related definitions *)

(** ** The [res] version of [assert]. *)

Definition eassert (e: errmsg) P `{HP: Decision P}: res P :=
  match decide P with
    | left H => ret H
    | right H => Error e
  end.

Lemma eassert_inv `{Pdec: Decision} {A} m (f: P -> res A) (r: A):
  bind f (eassert m P) = ret r <->
  exists H, f H = ret r.
Proof.
  unfold eassert.
  destruct (decide P) as [HP | HP];
  unfold bind; simpl.
  * split; eauto.
    intros [H Hf].
    assert (H = HP) by apply proof_irr; congruence.
  * split; try discriminate.
    intros [H Hf].
    tauto.
Qed.

Instance eassert_le:
  Proper (⊤ ++> ∀ H: (flip impl) P Q, ⊤ ++> res_le ⊤)%signature eassert.
Proof.
  intros msg1 msg2 _ P Q HPQ Pdec Qdec _.
  unfold eassert, flip, impl in *.
  destruct (decide Q) as [HQ | HQ]; try constructor.
  destruct (decide P) as [HP | HP]; try tauto.
  constructor.
  apply I.
Qed.

Hint Rewrite @eassert_inv using typeclasses eauto : monad.

(** These tactics make it easy to reduce subexpressions of the form
  [H <- eassert msg P; M] in the goal by proving or disproving [P]. *)

Lemma eassert_true msg P `{Pdec: Decision P}:
  P -> exists H, eassert msg P = OK H.
Proof.
  intros.
  unfold eassert.
  destruct (decide P); try contradiction.
  eauto.
Defined.

Ltac eassert_true_aux msg P Pdec :=
  let H := fresh "Hasserted" in
  let HH := fresh "Hassert_eq" in
  destruct (eassert_true msg P (Pdec := Pdec)) as [H HH];
    [ idtac (* The user will prove [P] *)
    | rewrite !HH in *;
      clear HH;
      monad_norm;
      try clear H ].

Ltac eassert_true :=
  lazymatch goal with
    | |- context [@eassert ?msg ?P ?Pdec] =>
      eassert_true_aux msg P Pdec
  end.

Lemma eassert_false msg P `{Pdec: Decision P}:
  ~P -> eassert msg P = Error msg.
Proof.
  intros.
  unfold eassert.
  destruct (decide P); try contradiction.
  eauto.
Defined.

Ltac eassert_false_aux msg P Pdec :=
  let H := fresh in
  assert (H: ~P);
    [ idtac (* The user will prove [~P] *)
    | rewrite !(eassert_false msg P (Pdec:=Pdec) H);
      monad_norm;
      clear H ].

Ltac eassert_false :=
  lazymatch goal with
    | |- context [@eassert ?msg ?P ?Pdec] =>
      eassert_false_aux msg P Pdec
  end.

(** ** Whether a [res A] is [OK] or [Error] *)

Definition isOK {A} (x: res A): Prop :=
  exists (a: A), x = OK a.

Definition isError {A} (x: res A): Prop :=
  exists (m: errmsg), x = Error m.

Definition isOKNone {A} (x: res (option A)) :=
  x = OK None.

Global Instance isOK_dec {A} (x: res A): Decision (isOK x) :=
  match x with
    | OK _ => left _
    | Error _ => right _
  end.
Proof.
  abstract (red; eauto).
  abstract (intros [a Ha]; discriminate).
Defined.

Global Instance isError_dec {A} (x: res A): Decision (isError x) :=
  match x with
    | OK _ => right _
    | Error _ => left _
  end.
Proof.
  abstract (intros [msg Hmsg]; discriminate).
  abstract (red; eauto).
Defined.

Global Instance isOKNone_dec {A} (x: res (option A)):
  Decision (isOKNone x) :=
  match x with
    | OK None => left _
    | _ => right _
  end.
Proof.  
  abstract (unfold isOKNone; simpl; congruence).
  abstract reflexivity.
  abstract (unfold isOKNone; simpl; congruence).
Defined.

Global Instance isOK_le:
  Proper (∀ R, res_le R --> impl) (@isOK).
Proof.
  intros B A R x y Hxy [x' Hx].
  subst.
  inversion Hxy.
  exists x.
  reflexivity.
Qed.

Global Instance isError_le:
  Proper (∀ R, res_le R ++> impl) (@isError).
Proof.
  intros A B R x y Hxy Hx.
  destruct Hx as [err Hx]; subst.
  inversion Hxy as [| err' x]; subst.
  eexists.
  reflexivity.
Qed.

Instance isOKNone_le:
  Proper (∀ R, res_le (option_le R) --> impl) (@isOKNone).
Proof.
  unfold isOKNone.
  intros A1 A2 RA x y Hxy Hx.
  destruct Hxy as [x y Hxy | ]; try discriminate.
  destruct Hxy as [x y Hxy | ]; try discriminate.
  reflexivity.
Qed.

(** *** Some lemmas and [eauto] hints. *)

Lemma isOK_OK {A} (a: A):
  isOK (OK a).
Proof.
  eexists.
  reflexivity.
Qed.

Lemma isOK_Error {A} msg:
  ~ isOK (@Error A msg).
Proof.
  intros [a Ha].
  discriminate.
Qed.

Hint Resolve isOK_OK.

Lemma isOKNone_OKNone {A}:
  isOKNone (OK (@None A)).
Proof.
  reflexivity.
Qed.

Hint Resolve isOKNone_OKNone.

Lemma isError_Error {A} msg:
  isError (@Error A msg).
Proof.
  eexists.
  reflexivity.
Qed.

Hint Resolve isError_Error.


(** * Miscellaneous helpers *)

Definition fallback {A} (x: A) (y: res A): A :=
  match y with
    | OK a => a
    | Error _ => x
  end.

(** ** Flip [option (res -)] <-> [res (option -)] *)

(** Overall, [res ∘ option] is more convenient to manipulate and
  that's what we have in most places. However, it is more
  straightforward to store into [PTree]s as [option ∘ res].
  Fortunately these wrappers can be used to flip between the two
  representations. *)

Definition res_option_flip {A} (roa: res (option A)): option (res A) :=
  match roa with
    | OK None => None
    | OK (Some a) => Some (OK a)
    | Error msg => Some (Error msg)
  end.

Global Instance res_option_flip_le:
  Proper
    (∀ R, res_le (option_le R) ++> option_le (res_le R))
    (@res_option_flip).
Proof.
  intros A1 A2 RA _ _ [_ _ [y | x y Hxy] | msg [[|]|]];
  simpl;
  eauto with liblayers.
Qed.

Definition option_res_flip {A} (ora: option (res A)): res (option A) :=
  match ora with
    | None => OK None
    | Some (OK a) => OK (Some a)
    | Some (Error msg) => Error msg
  end.

Global Instance option_res_flip_le:
  Proper
    (∀ R, option_le (res_le R) ++> res_le (option_le R))
    (@option_res_flip).
Proof.
  intros A1 A2 RA x y Hxy.
  destruct Hxy as [[[y|msg]|] | _ _ [x y Hxy | msg x]];
  simpl;
  eauto with liblayers.
Qed.

Lemma res_option_flip_inv {A} (x: res (option A)):
  option_res_flip (res_option_flip x) = x.
Proof.
  destruct x as [[x|] | msg]; reflexivity.
Qed.

Lemma option_res_flip_inv {A} (x: option (res A)):
  res_option_flip (option_res_flip x) = x.
Proof.
  destruct x as [[x|msg] | ]; reflexivity.
Qed.


(** * [PseudoJoin] structure for [res (option -)] *)

Require Import PseudoJoin.

Section RES_OPTION_PSEUDO_JOIN.
  Global Instance res_option_oplus_op (A: Type): Oplus (res (option A)) | 10 :=
    { oplus rox roy :=
    ox <- rox;
    oy <- roy;
    match ox, oy with
      | None, None => ret None
      | Some x, None => ret (Some x)
      | None, Some y => ret (Some y)
      | Some x, Some y => Error nil
    end }.

  Global Instance res_option_oplus_monotonic {A} (R: relation A):
    Proper
      (res_le (option_le R) ==> res_le (option_le R) ==> res_le (option_le R))
      (⊕).
  Proof.
    simpl.
    solve_monotonic.
    destruct H1 as [[y1|] | x1 y1 H1];
    destruct H2 as [[y2|] | x2 y2 H2];
    solve_monotonic.
  Qed.

  Existing Instance res_le_op.
  Existing Instance option_le_op.

  Local Hint Extern 4 => reflexivity.

  Global Instance res_option_oplus_prf (A: Type) `{Ale: Le A}:
    @PreOrder A (≤) ->
    PseudoJoin (res (option A)) (OK None).
  Proof with simpl; monad_norm; repeat constructor; reflexivity.
    intros Hpre.
    split; try typeclasses eauto.
    * intros [[y|]|err]...
    * intros [[x|]|xerr] [[y|]|yerr] [[z|]|zerr]...
    * intros [[x|]|xerr] [[y|]|yerr]...
    * intros [[x|]|xerr] [[y|]|yerr]...
  Qed.

  (** In addition, we have stronger versions of those. *)

  Global Instance res_option_oplus_id_left A:
    @LeftIdentity (res (option A)) eq (⊕) (OK None).
  Proof.
    intros [[|]|]; reflexivity.
  Qed.

  Global Instance res_option_oplus_comm A:
    @RightIdentity (res (option A)) eq (⊕) (OK None).
  Proof.
    intros [[|]|]; reflexivity.
  Qed.
End RES_OPTION_PSEUDO_JOIN.

Section OPTION_RES_PSEUDO_JOIN.
  Global Instance option_res_oplus_op (A: Type): Oplus (option (res A)) | 10 :=
    {
      oplus orx ory :=
        match orx, ory with
          | None, None => None
          | Some x, None => Some x
          | None, Some y => Some y
          | Some (Error e), Some y => Some (Error e)
          | Some (OK x), Some (Error e) => Some (Error e)
          | Some (OK x), Some (OK y) => Some (Error nil)
        end
    }.

  Existing Instance option_le_op.
  Existing Instance res_le_op.

  Global Instance option_res_oplus_prf (A: Type) `{Ale: Le A} `{Hle: PreOrder A (≤)}:
    PseudoJoin (option (res A)) None.
  Proof with simpl; eauto with liblayers; try solve_monotonic.
    split; try typeclasses eauto.
    * intros x1 x2 Hx y1 y2 Hy; simpl.
      destruct Hx as [ [[x2|xerr]|] | _ _ [x1 x2 Hx | xerr [x|xe]]];
      destruct Hy as [ [[y2|yerr]|] | _ _ [y1 y2 Hy | yerr [y|ye]]]...
    * intros [[|]|]...
    * intros [[|]|] [[|]|] [[|]|]...
    * intros [[|]|] [[|]|]...
    * intros [[|]|] [[|]|]...
  Qed.

  (** In addition, we have a top element. *)
  Global Instance option_res_top {A B} (R: rel A B) errmsg:
    UpperBound (option_le (res_le R)) (Some (Error errmsg)).
  Proof.
    intro x.
    destruct x as [|]; repeat constructor.
  Qed.
End OPTION_RES_PSEUDO_JOIN.
