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
Require Import Decision.

(* This file defines a typeclass for observations (the return type of the 
   observation functions discussed in the paper). We require all observations
   to come with a partial order here, in anticipation of proving monotonicity 
   with respect to a semantics (see Section 2 of the paper for discussion of 
   monotonicity). *)

Section OBSERVATION.

  (* To talk about observations, we need a carrier type for both the observations
     themselves and the principals that can do the observing. 

     The obs_leq predicate defines the partial order.

     The obs_measure function maps each observation to a natural number, which
     is meant to represent the "number of observations" made (e.g., if the 
     observation type is an output buffer, then the measure would be the size
     of the buffer). We need it for technical reasons that come up in simulations 
     and whole-execution behaviors; we hope that a future version will be able to 
     get rid of this measure. *)
  Class ObservationOps :=
    {
      principal : Type;
      obs : Type;
      obs_leq : obs -> obs -> Prop;
      obs_lt o1 o2 := obs_leq o1 o2 /\ o1 <> o2;
      obs_measure : obs -> nat
    }.

  Class Observation `{Obs: ObservationOps} :=
    {
      (* decidability is useful for technical reasons *)
      principal_eq_dec : forall p1 p2 : principal, Decision (p1 = p2);
      obs_eq_dec : forall o1 o2 : obs, Decision (o1 = o2);

      (* obs_leq must be a partial order *)
      obs_leq_refl : forall o, obs_leq o o;
      obs_leq_antisym : 
        forall o1 o2, obs_leq o1 o2 -> obs_leq o2 o1 -> o1 = o2;
      obs_leq_trans : 
        forall o1 o2 o3, obs_leq o1 o2 -> obs_leq o2 o3 -> obs_leq o1 o3;
      
      (* obs_measure must be consistent with obs_leq *)
      obs_lt_measure :
        forall o1 o2, obs_lt o1 o2 -> obs_measure o1 < obs_measure o2
    }.

  Context `{Obs : Observation}.

  Lemma obs_leq_lt :
    forall o1 o2,
      obs_leq o1 o2 <-> obs_lt o1 o2 \/ o1 = o2.
  Proof.
    unfold obs_lt; intros o1 o2; split; intro H.
    destruct (obs_eq_dec o1 o2); auto.
    destruct H as [[? ?]|?]; auto.
    subst; apply obs_leq_refl.
  Qed.

  Lemma obs_measure_eq :
    forall o1 o2,
      obs_leq o1 o2 ->
      obs_measure o1 = obs_measure o2 -> 
      o1 = o2.
  Proof.
    intros o1 o2 Hleq Hm.
    rewrite obs_leq_lt in Hleq; destruct Hleq; auto.
    apply obs_lt_measure in H; omega.
  Qed.

End OBSERVATION.

