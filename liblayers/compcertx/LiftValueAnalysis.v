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
Require Import Coq.Program.Basics.
Require Import Coq.Classes.Morphisms.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcertx.common.MemoryX.
Require Import liblayers.lib.Functor.
Require Import liblayers.lib.Monad.
Require Import liblayers.lib.Lens.
Require Export liblayers.compcertx.LiftMem.
Require Import compcert.backend.ValueDomain.
Require Import compcert.backend.ValueAnalysis.
Require Import liblayers.compcertx.LiftValueDomain.

(** CompCert passes based on value analysis now require the definition
    of a [mmatch] "memory abstraction" predicate.

    A memory has to inject into itself if the abstract memory state
    satisfies some well-formedness properties. This requirement is
    formalized by the [compcert.backend.ValueDomain.mmatch_inj]
    property.

    Unfortunately, it is not possible to prove [mmatch_inj] directly
    using the axioms of the CompCert memory model, so in practice, a
    proof is directly made in [compcert.backend.ValueDomainImpl] on
    the concrete memory implementation [compcert.common.Memimpl]. It
    should be possible to generalize this property over all lenses to
    [Memimpl.mem].

    In this file, we are lifting the [mmatch_inj] property along a
    lens to a [bmem] memory model, assuming that [mmatch_inj] is
    already specified on [bmem].

    In fact, we have to lift the whole specification of [mmatch], not
    just [mmatch_inj] (that property alone fails).
*)

Section LIFTDERIVED.

  Context `{HW: LiftMemoryModel}.

  Context `{mmatch_ops: !MMatchOps bmem}.
  Context `{mmatch_prf: !MMatchConstructions bmem}.

  Global Instance lift_mmatch_constructions: MMatchConstructions mem.
  Proof.
    constructor.   
    typeclasses eauto.
    lift π allocate_stack.
    lift π anonymize_stack.
    lift π hide_stack.
    lift π return_from_public_call.
    lift π return_from_private_call.
    (** HELP: need to improve [lift] tactic *)
    lift_partial π external_call_match'. 
     intro K. intros. apply Hf; eauto. intros. exploit K; eauto.
     split; auto. reflexivity.
     destruct 1 as [? [? [? [? [[? ?] [? [? ?]]]]]]]; eauto 8.
Qed.

End LIFTDERIVED.
