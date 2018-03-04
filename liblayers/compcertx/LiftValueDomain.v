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

  Global Instance lift_mmatch_ops: MMatchOps mem :=
    {|
      mmatch bc m am := lift π (fun bm => mmatch bc bm am) m
    |}.

  Context `{mmatch_prf: !MMatch bmem}.

  Global Instance lift_mmatch_prf: MMatch mem.
  Proof.
    constructor.
    lift π mmatch_stack.
    lift π mmatch_glob.
    lift π mmatch_nonstack.
    lift π mmatch_top.
    lift π mmatch_below.
    lift π load_sound.
    lift π store_sound.
    lift π loadbytes_sound.
    lift π storebytes_sound.
    lift π mmatch_ext.
    lift π mmatch_free.
    lift π mmatch_top'.
    lift π mbeq_sound.
    lift π mmatch_lub_l.
    lift π mmatch_lub_r.
    lift π mmatch_inj.
    lift π mmatch_inj_top.
Qed.

End LIFTDERIVED.
