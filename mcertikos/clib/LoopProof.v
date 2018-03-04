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
(* Frameworks for proving Clight loops: specification and termination  *)
(*                                                                     *)
(*                 Developed by Xiongnan (Newman) Wu                   *)
(*                                                                     *)
(*                         Yale University                             *)
(*                                                                     *)
(* *********************************************************************)


Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Locations.
Require Import Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Ctypes.
Require Import Cop.
Require Import ZArith.Zwf.
Require Import Integers.
Require Import CDataTypes.

Module LoopProof.

Section S.

  Context `{Hcc: Events.CompilerConfiguration}
          `{Hwb: Events.WritableBlock}.

  Variables (body: statement) (genv: genv) (env: env)
            (P Q: temp_env -> mem -> Prop)
            (R: temp_env-> mem -> option (val * type)-> Prop).

  Record t  : Type := make {
         W: Type;
         lt: W-> W-> Prop;
         lt_wf: well_founded lt;
         I: temp_env-> mem-> W-> Prop;
         P_implies_I: forall le m, P le m-> exists n0, I le m n0;
         I_invariant:
         forall le m n, I le m n ->
           exists out le' m', exec_stmt genv env le m body E0 le' m' out /\
             ((out = Out_normal \/ out = Out_continue)-> exists n', lt n' n /\ I le' m' n') /\
              (out = Out_break-> Q le' m') /\
              (forall v, out = Out_return v-> R le' m' v)
  }.

  Theorem termination: t -> forall le m, P le m ->
    (exists out le' m', exec_stmt genv env le m (Sloop body Sskip) E0 le' m' out /\
      ((exists v, out = Out_return v /\ R le' m' v) \/ (out = Out_normal /\ Q le' m'))).
  Proof.
    destruct 1; simpl.
    intros.
    generalize (P_implies_I0 le m H).
    intro.
    destruct H0 as [n0].
    clear H.
    revert le m H0.
    induction n0 using (well_founded_ind lt_wf0).

    intros.
    
    generalize (I_invariant0 le m n0 H0).
    intro I_invariant.
    destruct I_invariant as [out tinv].
    destruct tinv as [le' tinv].
    destruct tinv as [m' tinv].
    destruct tinv as [Inv1 tinv].
    destruct tinv as [Inv2 tinv].
    destruct tinv as [Inv3 Inv4].
    
    destruct out.

    (* out = Out_break *)
    exists Out_normal.
    exists le'.
    exists m'.
    split.
    econstructor.
    eassumption.
    econstructor.
    right.
    split.
    trivial.
    apply Inv3.
    trivial.

    (* out = Out_continue *)
    destruct Inv2 as [n'].
    auto.
    destruct H1.
    generalize (H n' H1 le' m' H2).
    intro.
    destruct H3 as [out].
    destruct H3 as [le'0'].
    destruct H3 as [m'0].
    destruct H3.
    destruct H4.
      (* finalout = Out_return *)
      destruct H4 as [v].
      destruct H4.
      esplit. esplit. esplit.
      split.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      eassumption.
      econstructor.
      econstructor.
      eassumption.
      subst.
      left.
      exists v.
      auto.
      (* finalout = Out_normal *)
      destruct H4.
      esplit. esplit. esplit.
      split.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      eassumption.
      econstructor.
      econstructor.
      eassumption.
      subst.
      right.
      auto.

    (* out = Out_normal *)
    destruct Inv2 as [n'].
    auto.
    destruct H1.
    generalize (H n' H1 le' m' H2).
    intro.
    destruct H3 as [out].
    destruct H3 as [le'0'].
    destruct H3 as [m'0].
    destruct H3.
    destruct H4.
      (* finalout = Out_return *)
      destruct H4 as [v].
      destruct H4.
      esplit. esplit. esplit.
      split.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      eassumption.
      econstructor.
      econstructor.
      eassumption.
      subst.
      left.
      exists v.
      auto.
      (* finalout = Out_normal *)
      destruct H4.
      esplit. esplit. esplit.
      split.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      eassumption.
      econstructor.
      econstructor.
      eassumption.
      subst.
      right.
      auto.

    (* out = Out_return *)
    exists (Out_return o).
    exists le'.
    exists m'.
    split.
    econstructor.
    eassumption.
    econstructor.
    left.
    exists o.
    auto.
  Qed.

End S.
End LoopProof.




Module LoopProofWhileWithContinue.

Section S.

  Context `{Hcc: Events.CompilerConfiguration}
          `{Hwb: Events.WritableBlock}.

  Variables (condition: expr) (body: statement) 
            (genv: genv) (env: env)
            (P Q: temp_env -> mem -> Prop).

  Record t  : Type := make {
         W: Type;
         lt: W-> W-> Prop;
         lt_wf: well_founded lt;
         I: temp_env-> mem-> W-> Prop;
         P_implies_I: forall le m, P le m-> exists n0, I le m n0;
         I_invariant:
         forall le m n, I le m n-> exists v b, (eval_expr genv env le m condition v /\
            (bool_val v (typeof condition) = Some b) /\
            (b = false -> Q le m) /\
            (b = true -> 
             exists out le' m', exec_stmt genv env le m body E0 le' m' out /\
             (out = Out_normal \/ out = Out_continue) /\
             exists n', lt n' n /\ I le' m' n'
           ))
  }.

  Theorem termination: t -> forall le m, P le m ->
    (exists le' m', exec_stmt genv env le m (Swhile condition body) E0 le' m' Out_normal /\ Q le' m').
  Proof.
    unfold Swhile.
    destruct 1; simpl.
    intros.
    generalize (P_implies_I0 le m H).
    intro.
    destruct H0 as [n0].
    clear H.
    revert le m H0.
    induction n0 using (well_founded_ind lt_wf0).

    intros.
    
    generalize (I_invariant0 le m n0 H0).
    intro I_invariant.
    destruct I_invariant as [v tinv].
    destruct tinv as [b tinv].
    destruct tinv as [evalexpr tinv].
    destruct tinv as [boolval tinv].
    destruct tinv as [condfalse tinv].

    destruct b.

    (* b = true *)
    
    destruct tinv as [out tinv]; trivial.
    destruct tinv as [le' tinv].
    destruct tinv as [m' tinv].
    destruct tinv as [Inv1 tinv].
    destruct tinv as [Inv2 tinv].
    destruct tinv as [n' tinv].
    destruct tinv as [Inv3 Inv4].
    destruct Inv2.

    (* out = Out_normal *)
    subst.
    generalize (H n' Inv3 le' m' Inv4).
    intro.
    destruct H1 as [le'0'].
    destruct H1 as [m'0].
    destruct H1.
    esplit. esplit.
    split.
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop.
    change E0 with (E0 ** E0).
    econstructor.
    econstructor.
    eassumption.
    eassumption.
    simpl.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
    eassumption.

    (* out = Out_continue *)
    subst.
    generalize (H n' Inv3 le' m' Inv4).
    intro.
    destruct H1 as [le'0'].
    destruct H1 as [m'0].
    destruct H1.
    esplit. esplit.
    split.
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop.
    change E0 with (E0 ** E0).
    econstructor.
    econstructor.
    eassumption.
    eassumption.
    simpl.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
    eassumption.

    (* b = false *)
    exists le.
    exists m.
    split.
    eapply exec_Sloop_stop1.
    econstructor.
    econstructor.
    eassumption.
    eassumption.
    simpl.
    econstructor.
    congruence.
    econstructor.
    auto.
  Qed.

End S.
End LoopProofWhileWithContinue.



Module LoopProofSimpleWhile.

Section S.

  Context `{Hcc: Events.CompilerConfiguration}
          `{Hwb: Events.WritableBlock}.

  Variables (condition: expr) (body: statement) 
            (genv: genv) (env: env)
            (P Q: temp_env -> mem -> Prop).

  Record t  : Type := make {
         W: Type;
         lt: W-> W-> Prop;
         lt_wf: well_founded lt;
         I: temp_env-> mem-> W-> Prop;
         P_implies_I: forall le m, P le m-> exists n0, I le m n0;
         I_invariant:
         forall le m n, I le m n-> exists v b, (eval_expr genv env le m condition v /\
            (bool_val v (typeof condition) = Some b) /\
            (b = false -> Q le m) /\
            (b = true -> 
             exists le' m', exec_stmt genv env le m body E0 le' m' Out_normal /\
             exists n', lt n' n /\ I le' m' n'
           ))
  }.

  Theorem termination: t -> forall le m, P le m ->
    (exists le' m', exec_stmt genv env le m (Swhile condition body) E0 le' m' Out_normal /\ Q le' m').
  Proof.
    unfold Swhile.
    destruct 1; simpl.
    intros.
    generalize (P_implies_I0 le m H).
    intro.
    destruct H0 as [n0].
    clear H.
    revert le m H0.
    induction n0 using (well_founded_ind lt_wf0).

    intros.
    
    generalize (I_invariant0 le m n0 H0).
    intro I_invariant.
    destruct I_invariant as [v tinv].
    destruct tinv as [b tinv].
    destruct tinv as [evalexpr tinv].
    destruct tinv as [boolval tinv].
    destruct tinv as [condfalse tinv].

    destruct b.

    (* b = true *)
    
    destruct tinv as [le' tinv]; trivial.
    destruct tinv as [m' tinv].
    destruct tinv as [Inv1 tinv].
    destruct tinv as [n' tinv].
    destruct tinv as [Inv2 Inv3].

    generalize (H n' Inv2 le' m' Inv3).
    intro.
    destruct H1 as [le'0'].
    destruct H1 as [m'0].
    destruct H1.
    esplit. esplit.
    split.
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop.
    change E0 with (E0 ** E0).
    econstructor.
    econstructor.
    eassumption.
    eassumption.
    simpl.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
    eassumption.

    (* b = false *)
    exists le.
    exists m.
    split.
    eapply exec_Sloop_stop1.
    econstructor.
    econstructor.
    eassumption.
    eassumption.
    simpl.
    econstructor.
    congruence.
    econstructor.
    auto.
  Qed.

End S.
End LoopProofSimpleWhile.