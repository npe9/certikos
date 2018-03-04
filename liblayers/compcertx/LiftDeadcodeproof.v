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
Require Import compcert.backend.Deadcodeproof.

(** Dead code elimination requires the definition of a [magree]
    relation on memories, which is a stronger version of memory
    extension parameterized on a predicate on memory locations over
    which contents must be equal between the two memories.

    Unfortunately, it is not possible to define this predicate only
    using operations and axioms of the CompCert memory model. Thus,
    CompCert provides in [compcert.backend.DeadcodeproofImpl] an
    implementation of [magree] on the concrete implementation
    [compcert.common.Memimpl] of the memory model. It becomes then
    desirable to be able to lift this implementation along any lens to
    [Memimpl.mem].

    In this file, assuming any memory model [mem] with [magree], we
    provide a uniform way to lift [magree] along a lens to [mem].
*)

Section LIFTDERIVED.
  Context `{HW: LiftMemoryModel}.

  Context `{magree_ops: !MAgreeOps bmem}
          `{magree_prf: !MAgree bmem}.

  Global Instance lift_magree_ops:
    MAgreeOps mem
    :=
      {|
        magree m1 m2 ls := lift π (fun (bm1 bm2: bmem) => magree bm1 bm2 ls) m1 m2
      |}.

  Global Instance lift_magree:
    MAgree mem.
  Proof.
    constructor.
    lift π ma_perm.
    lift π magree_monotone.
    lift π mextends_agree.
    lift π magree_extends.
    lift π magree_loadbytes.
    lift π magree_load.
    lift π magree_storebytes_parallel.
    lift π magree_store_parallel.
    lift π magree_storebytes_left.
    lift π magree_store_left.
    lift π magree_free.
  Qed.

End LIFTDERIVED.
