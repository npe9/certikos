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
Require Import LayerData.
Require Import Structures.
Require Import OptionMonad.
Require Import ErrorMonad.
Require Import liblayers.logic.PseudoJoin.

Section PRIMITIVES.
  Context `{HVE: ReflexiveGraph}.

  Class PrimitiveOps (primsem: V -> Type) :=
    {
    }.

  Class Primitives (primsem: V -> Type)
      `{primsem_ops: PrimitiveOps primsem}
      `{primsem_sim_op: Sim V E primsem} :=
    {
      prim_quiv_sim_prf :> ReflexiveGraphSim V E primsem
    }.
End PRIMITIVES.
