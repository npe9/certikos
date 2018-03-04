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
Require Import liblayers.logic.Structures.
Require Export compcert.common.Values.
Require Export compcert.common.Memtype.
Require Import liblayers.compcertx.Observation.

(** * Types of abstract data *)

(** To use [data] as a layer's abstract data, we need the associated
  initial abstract [init_data], and an invariant [data_inv] that hold
  on the initial data and is to be preserved by all primitives.

  Additionally, since the data may contain pointers, we need a
  relation [data_inject] that tells us what it means for one abstract
  state to inject to another, by analogy to Compcert's [val_inject]
  and friends. It is not yet entierly clear what properties will be
  required of [data_inject] besides [data_inject_compose], but I list
  a few things that make sense.

  WILL NEED: [data_inject] is preserved by a modification of the
  injection above the current [Mem.nextblock]. *)

Class AbstractDataOps `{mem_ops: Mem.MemoryModelOps} data :=
  {
    init_data : data;
    inv: mem -> data -> Prop;
    data_inject (ι: meminj): relation data
  }.

Class AbstractData {mem} data `{data_ops: AbstractDataOps mem data}: Prop :=
  {
    init_data_inv:
      inv Mem.empty init_data;
    data_inject_id d:
      data_inject inject_id d d;
    data_inject_compose ι ι' d1 d2 d3:
      data_inject ι d1 d2 ->
      data_inject ι' d2 d3 ->
      data_inject (compose_meminj ι ι') d1 d3;
    data_inject_incr :>
      Proper (inject_incr ++> eq ==> eq ==> impl) data_inject
  }.

(** We can bundle all of those as a first-class object. *)

Record layerdata `{obs_ops: ObservationOps} `{mem_ops: Mem.MemoryModelOps} :=
  ldata {
    ldata_type :> Type;
    ldata_ops : AbstractDataOps ldata_type;
    ldata_prf : AbstractData ldata_type
  }.

Global Arguments ldata {_ _ _} _ {_ _}.
Existing Instance ldata_ops.
Existing Instance ldata_prf.

(** NB: We could define [+], [×] and the like. *)
