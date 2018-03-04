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
Require Import compcert.lib.Coqlib.
Require Import liblayers.lib.Decision.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import compcertx.common.MemimplX.
Require Import liblayers.compcertx.MakeProgramImpl.
Require Import liblayers.compat.CompatLayers.
Require Import mcertikos.layerlib.LAsmModuleSemDef.
Require Import mcertikos.layerlib.ObservationImpl.

Require Import mcertikos.driver.Symbols.

(** Helpers for extraction *)

Section WITHDEC.

  Local Instance list_norepet_dec {A}
        (A_eq_dec: forall x y: A, Decision (x = y))
        (l: _ A):
    Decision (list_norepet l) :=
    Coqlib.list_norepet_dec A_eq_dec l.

  Program Definition certikos_stencil: StencilImpl.stencil :=
    {|
      StencilImpl.stencil_ids := List.map fst symbols
    |}.
  Next Obligation.
    eapply isTrue_correct.
    vm_compute.
    reflexivity.
  Qed.

  Existing Instance list_observation_ops.

  Program Definition nodata: compatdata :=
    {|
      cdata_type := unit
    |}.
  Next Obligation.
    constructor.
    * exact tt.
    * exact (fun _ => True).
    * exact (fun _ _ => True).
    * exact (fun _ => True).
    * exact (fun _ _ => nil).
  Defined.
  Next Obligation.
    constructor; simpl; tauto.
  Qed.

  Local Instance mwd_ops: MemWithData.UseMemWithData Memimpl.mem.

  Definition extract_module (OM: res LAsm.module): res (AST.program LAsm.fundef unit) :=
    M <- OM;
    make_program (Fm := LAsm.function) (Vm := Ctypes.type) (module_ops := LAsm.module_ops) (D := nodata) certikos_stencil M ∅.

End WITHDEC.
