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
Require Import compcert.common.Memtype.
Require Import compcert.common.Globalenvs.
Require Import liblayers.logic.LayerData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compcertx.Observation.

Section WITH_MEMORY_MODEL.
Context `{Hobs: Observation}.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hstencil: Stencil}.

(** * Abstract data and simulation relation blueprints *)

Class CompatDataOps data :=
  {
    empty_data : data;
    high_level_invariant: data -> Prop;
    low_level_invariant: block -> data -> Prop;
    kernel_mode: data -> Prop;
    observe: principal -> data -> obs
  }.

Class CompatData data `{data_ops: CompatDataOps data} :=
  {
    low_level_invariant_incr n n' d:
      (n <= n')%positive ->
      low_level_invariant n d ->
      low_level_invariant n' d;
    empty_data_low_level_invariant:
      forall n, low_level_invariant n empty_data;
    empty_data_high_level_invariant:
      high_level_invariant empty_data
  }.

(** Although we do not need a memory model to define our [CompatData],
  it is needed for [LayerData], and so we include it here as well so
  that the coercion [compatdata_layerdata] can work properly. *) 
Record compatdata {mem} `{mem_ops: !Mem.MemoryModelOps mem} :=
  {
    cdata_type : Type;
    cdata_ops : CompatDataOps cdata_type;
    cdata_prf : CompatData cdata_type
  }.

Global Existing Instance cdata_ops.
Global Existing Instance cdata_prf.

Definition cdata := Build_compatdata.
Global Arguments cdata {_ _} _ {_ _}.

Class CompatRelOps `{stencil_ops: StencilOps} (D1 D2: compatdata) :=
  {
    relate_AbData: stencil -> meminj -> cdata_type D1 -> cdata_type D2 -> Prop;
    match_AbData: stencil -> cdata_type D1 -> mem -> meminj -> Prop;
    new_glbl: list AST.ident
  }.

Class CompatRel D1 D2 `{ops: !CompatRelOps D1 D2} :=
  {
    match_compose:
      forall s d1 m2 f m2' j,
        match_AbData s d1 m2 f ->
        Mem.inject j m2 m2' ->
        inject_incr (Mem.flat_inj (genv_next s)) j ->
        match_AbData s d1 m2' (compose_meminj f j);

    store_match_correct:
      forall s abd m0 m0' f b2 v v' chunk,
        match_AbData s abd m0 f ->
        (forall i b,
           In i new_glbl ->
           find_symbol s i = Some b -> b <> b2) ->
        Mem.store chunk m0 b2 v v' = Some m0' ->
        match_AbData s abd m0' f;

    alloc_match_correct:
      forall s abd m'0  m'1 f f' ofs sz b0 b'1,
        match_AbData s abd m'0 f->
        Mem.alloc m'0 ofs sz = (m'1, b'1) ->
        f' b0 = Some (b'1, 0%Z) ->
        (forall b : block, b <> b0 -> f' b = f b) ->
        inject_incr f f' ->
        (forall i b,
           In i new_glbl ->
           find_symbol s i = Some b -> b <> b0) ->
        match_AbData s abd m'1 f';

    free_match_correct:
      forall s abd m0 m0' f ofs sz b2,
        match_AbData s abd m0 f->
        (forall i b,
           In i new_glbl ->
           find_symbol s i = Some b -> b <> b2) ->
        Mem.free m0 b2 ofs sz = Some m0' ->
        match_AbData s abd m0' f;

    storebytes_match_correct:
      forall s abd m0 m0' f b2 v v',
        match_AbData s abd m0 f ->
        (forall i b,
           In i new_glbl ->
           find_symbol s i = Some b -> b <> b2) ->
        Mem.storebytes m0 b2 v v' = Some m0' ->
        match_AbData s abd m0' f;

    relate_incr:
      forall s abd abd' f f',
        relate_AbData s f abd abd' ->
        inject_incr f f' ->
        relate_AbData s f' abd abd';

    relate_kernel_mode:
      forall s f abd abd',
        relate_AbData s f abd abd' ->
        (kernel_mode abd <-> kernel_mode abd');

    relate_observe:
      forall s f abd abd' p,
        relate_AbData s f abd abd' ->
        observe p abd = observe p abd'
  }.

Class compatrel D1 D2 :=
  {
    crel_ops :> CompatRelOps D1 D2;
    crel_prf :> CompatRel D1 D2
  }.

Instance one_crel data1 data2
  `{CompatData data1}
  `{CompatData data2}
  `{!CompatRelOps (cdata data1) (cdata data2)}
  `{!CompatRel (cdata data1) (cdata data2)}:
  compatrel (cdata data1) (cdata data2) := {}.

Definition crel data1 data2
  `{CompatData data1}
  `{CompatData data2}
  `{!CompatRelOps (cdata data1) (cdata data2)}
  `{!CompatRel (cdata data1) (cdata data2)}:
  freerg compatrel (cdata data1) (cdata data2) :=
  freerg_inj _ _ _ (one_crel data1 data2).

(*
Global Existing Instance crel_ops.
Global Existing Instance crel_prf.
*)

Global Instance compat_rg: ReflexiveGraph compatdata (freerg compatrel).


(** * Compatibility with the new framework *)

Instance compatdata_layerdata_ops data `{CompatDataOps data}:
  AbstractDataOps data :=
  {
    init_data := empty_data;
    data_inject ι d1 d2 := True;
    inv m d := high_level_invariant d /\ low_level_invariant (Mem.nextblock m) d
  }.

Instance compatdata_layerdata_prf:
  forall data `{CompatDataOps data}, CompatData data -> AbstractData data.
Proof.
  intros data data_ops Hdata; split.
  * split.
    apply empty_data_high_level_invariant.
    apply empty_data_low_level_invariant.
  * intros d.
    apply I.
  * intros ι ι' d1 d2 d3 H12 H23.
    apply I.
  * intros ι1 ι2 Hι d1 d2 Hd d1' d2' Hd' H.
    apply I.
Qed.

Definition compatdata_layerdata (D: compatdata): layerdata :=
  {|
    ldata_type := cdata_type D
  |}.

End WITH_MEMORY_MODEL.

Coercion compatdata_layerdata : compatdata >-> layerdata.