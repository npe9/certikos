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
Require Export liblayers.compcertx.AbstractData.
Require Export liblayers.lib.Lens.
Require Export liblayers.lib.Lift.
Require Export compcertx.common.MemoryX.
Require Import liblayers.compcertx.LiftMemX.
Require Import liblayers.compcertx.Observation.

(** * Memory with data *)

Definition mwd `{Mem.MemoryModelOps} `{ObservationOps} (D: layerdata) := (mem * ldata_type D)%type.

Section WITH_MEMORY_MODEL.
Context `{Hmem: Mem.MemoryModelX}.
Context `{Hobs: Observation}.

Definition π_mem {D}: mwd D -> mem := fst.
Definition π_data {D}: mwd D -> ldata_type D := snd.

Global Instance π_mem_lens D: Lens (@π_mem D).
Proof.
  typeclasses eauto.
Qed.

(** * Injections with data *)

Definition mwd_inject {D} ι (m1 m2: mwd D) :=
  Mem.inject ι (π_mem m1) (π_mem m2) /\
  data_inject ι (π_data m1) (π_data m2).

Lemma mwd_inject_compose {D} ι12 ι23 (m1 m2 m3: mwd D):
  mwd_inject ι12 m1 m2 ->
  mwd_inject ι23 m2 m3 ->
  mwd_inject (compose_meminj ι12 ι23) m1 m3.
Proof.
  intros [Hm12 Hd12] [Hm23 Hd23].
  split.
  * eapply Mem.inject_compose;
    eassumption.
  * eapply data_inject_compose;
    eassumption.
Qed.

Definition mwd_inject_neutral {D} (m: mwd D) :=
  Mem.inject_neutral (Mem.nextblock (π_mem m)) (π_mem m) /\
  data_inject (Mem.flat_inj (Mem.nextblock (π_mem m))) (π_data m) (π_data m).

Lemma mwd_neutral_inject {D} (m: mwd D) :
  mwd_inject_neutral m ->
  mwd_inject (Mem.flat_inj (Mem.nextblock (π_mem m))) m m.
Proof.
  unfold mwd_inject_neutral, mwd_inject.
  destruct m as [m d]; simpl.
  intros [Hm Hd].
  eauto using Mem.neutral_inject.
Qed.

(** * Lifting the memory model *)

End WITH_MEMORY_MODEL.

(** Given a type of memory states with data, we can lift the memory
  model on [bmem] to the whole thing. To avoid loops in typeclass
  resolution, we only attempt it if an instance of the following
  marker class is declared. *)
Class UseMemWithData (mem : Type).

Local Instance mwd_liftmem_ops `{Mem.MemoryModelOps} `{ObservationOps} D:
  LiftMemoryModelOps (π_mem (D:=D)) :=
  {
    liftmem_empty := (Mem.empty, init_data)
  }.

Local Instance mwd_liftmem_prf `{Mem.MemoryModel} `{ObservationOps} D:
  LiftMemoryModel (π_mem (D:=D)).
Proof.
  split.
  typeclasses eauto.
  reflexivity.
Qed.

Global Instance mwd_memory_model_ops `{Mem.MemoryModelOps} `{ObservationOps} `{UseMemWithData mem}:
  forall D, Mem.MemoryModelOps (mwd D) | 5 := _.

Global Instance mwd_memory_model `{Mem.MemoryModel} `{ObservationOps} `{UseMemWithData mem}:
  forall D, Mem.MemoryModel (mwd D) | 5 := _.

Global Instance mwd_memory_model_x `{Mem.MemoryModelX} `{ObservationOps} `{UseMemWithData mem}:
  forall D, Mem.MemoryModelX (mwd D) | 5 := _.

Section WITH_MEM_WITH_DATA.
  Context `{Hmem: Mem.MemoryModel} `{ObservationOps} `{Hmwd: UseMemWithData mem}.

  Lemma mwd_same_context_mem_eq_data {D} (m1 m2: mwd D):
    same_context π_mem m1 m2 <->
    π_data m1 = π_data m2.
  Proof.
    apply fst_same_context_eq_snd.
  Qed.
End WITH_MEM_WITH_DATA.

Hint Rewrite @mwd_same_context_mem_eq_data using typeclasses eauto : lens_simpl.
