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
Require Import compcert.common.Values.
Require compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.


(** * Interface of stencils *)

Class StencilOps (stencil: Type) :=
  {
    find_symbol: stencil -> AST.ident -> option block;
    genv_next: stencil -> block
  }.


(** * Related definitions *)

(** FIXME: possibly not strong enough, or needed. *)
Definition meminj_preserves_stencil `{StencilOps} (s: stencil) (ι: meminj) :=
  forall i b, find_symbol s i = Some b -> ι b = Some (b, 0).

Record stencil_matches `{StencilOps} {F V} (s: stencil) (ge: Genv.t F V) :=
  {
    stencil_matches_symbols i:
      Genv.find_symbol ge i = find_symbol s i;
    stencil_matches_genv_next:
      Genv.genv_next ge = genv_next s;
    stencil_matches_volatile b:
      block_is_volatile ge b = false
  }.


(** * Properties *)

Class Stencil stencil `{stencil_ops: StencilOps stencil}: Prop :=
  {  
    genv_symb_range s i b:
      find_symbol s i = Some b -> Plt b (genv_next s);
    genv_vars_inj s i i' b:
      find_symbol s i = Some b ->
      find_symbol s i' = Some b ->
      i = i';
    stencil_matches_unique :
      forall {F V} (ge: _ F V) s1 s2,
        stencil_matches s1 ge ->
        stencil_matches s2 ge ->
        s1 = s2
  }.


Theorem stencil_matches_preserves_symbols
        `{StencilOps}
        F1 V1 F2 V2
        (ge1: Genv.t F1 V1)
        (ge2: Genv.t F2 V2)        
        (s: stencil)
        (Hsymbols_preserved: forall i, Genv.find_symbol ge1 i = Genv.find_symbol ge2 i)
        (Hgenv_next_preserved: Genv.genv_next ge1 = Genv.genv_next ge2)
        (Hblock_is_volatile: forall b, block_is_volatile ge1 b = block_is_volatile ge2 b)
        (Hmatch: stencil_matches s ge1)
:
  stencil_matches s ge2.
Proof.
  inv Hmatch. constructor; congruence.
Qed.        

Lemma stencil_matches_preserves_symbols_trans
        `{StencilOps}
        F1 V1 F2 V2
        (ge1: Genv.t F1 V1)
        (ge2: Genv.t F2 V2)        
        (s: stencil)
        (Hmatch1: stencil_matches s ge1)
        (Hmatch2: stencil_matches s ge2)
:
  forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i.
Proof.
  inv Hmatch1. inv Hmatch2. 
  intros; congruence.
Qed.        

Lemma stencil_matches_preserves_next_trans
        `{StencilOps}
        F1 V1 F2 V2
        (ge1: Genv.t F1 V1)
        (ge2: Genv.t F2 V2)        
        (s: stencil)
        (Hmatch1: stencil_matches s ge1)
        (Hmatch2: stencil_matches s ge2)
:
  Genv.genv_next ge2 = Genv.genv_next ge1.
Proof.
  inv Hmatch1. inv Hmatch2. 
  intros; congruence.
Qed.        

Lemma stencil_matches_preserves_volatile_trans
        `{StencilOps}
        F1 V1 F2 V2
        (ge1: Genv.t F1 V1)
        (ge2: Genv.t F2 V2)        
        (s: stencil)
        (Hmatch1: stencil_matches s ge1)
        (Hmatch2: stencil_matches s ge2)
:
  forall b, block_is_volatile ge2 b = block_is_volatile ge1 b.
Proof.
  inv Hmatch1. inv Hmatch2. 
  intros; congruence.
Qed.        

Lemma stencil_matches_preserves_trans
        `{StencilOps}
        F1 V1 F2 V2
        (ge1: Genv.t F1 V1)
        (ge2: Genv.t F2 V2)        
        (s: stencil)
        (Hmatch1: stencil_matches s ge1)
        (Hmatch2: stencil_matches s ge2)
:
  (forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i)
  /\ Genv.genv_next ge2 = Genv.genv_next ge1
  /\ (forall b, block_is_volatile ge2 b = block_is_volatile ge1 b).
Proof.
  repeat split.
  eapply stencil_matches_preserves_symbols_trans; eauto.
  eapply stencil_matches_preserves_next_trans; eauto.
  eapply stencil_matches_preserves_volatile_trans; eauto.
Qed.

Global Arguments stencil_matches_preserves_symbols {_ _} [_ _ _ _] _ _ _ _ _ _ _.
