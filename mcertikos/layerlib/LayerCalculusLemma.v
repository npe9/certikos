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
Require Import Coqlib.
Require Import MemoryX.
Require Import MemWithData.
Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compcertx.Stencil.
Require Import Observation.

Section LayerCalculus.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Lemma sim_commutativity {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L L1 L2,
      sim R L (L1 ⊕ L2) ->
      sim R L (L2 ⊕ L1).
  Proof.
    intros. 
    rewrite commutativity.
    assumption.
  Qed.

  Lemma sim_associativity {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L L1 L2 L3,
      sim R L (L1 ⊕ (L2 ⊕ L3)) ->
      sim R L ((L1 ⊕ L2) ⊕ L3).
  Proof.
    intros.
    rewrite associativity.
    assumption.
  Qed.

  Lemma sim_assoc_comm {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L L1 L2 L3,
      sim R L (L2 ⊕ (L1 ⊕ L3)) ->
      sim R L ((L1 ⊕ L2) ⊕ L3).
  Proof.
    intros.
    rewrite oplus_assoc_comm_equiv.
    assumption.
  Qed.

  Lemma sim_left {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L L1 L2,
      sim R L L1 ->
      sim R L (L1 ⊕ L2).
  Proof.
    intros.
    rewrite <- left_upper_bound.
    assumption.
  Qed.

  Lemma sim_eq {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L1',
      L1 = L1' ->
      forall L,
        sim R L L1' ->
        sim R L L1.
  Proof.
    intros. rewrite H. assumption.
  Qed.

  Lemma sim_eq_left {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L1' L1'',
      L1 = (L1' ⊕ L1'') ->
      forall L,
        sim R L L1' ->
        sim R L L1.
  Proof.
    intros. eapply sim_eq; try eassumption.
    apply sim_left. assumption.
  Qed.

  Lemma le_commutativity {D: compatdata}:
    forall (L L1 L2: compatlayer D),
      L ≤ (L1 ⊕ L2) ->
      L ≤ (L2 ⊕ L1).
  Proof.
    intros. 
    rewrite commutativity.
    assumption.
  Qed.

  Lemma le_associativity {D: compatdata}:
    forall (L L1 L2 L3: compatlayer D),
      L ≤ (L1 ⊕ (L2 ⊕ L3)) ->
      L ≤ ((L1 ⊕ L2) ⊕ L3).
  Proof.
    intros.
    rewrite associativity.
    assumption.
  Qed.

  Lemma le_assoc_comm  {D: compatdata}:
    forall (L L1 L2 L3: compatlayer D),
      L ≤ (L2 ⊕ (L1 ⊕ L3)) ->
      L ≤ ((L1 ⊕ L2) ⊕ L3).
  Proof.
    intros.
    rewrite oplus_assoc_comm_equiv.
    assumption.
  Qed.

  Lemma le_left {D: compatdata}:
    forall (L L1 L2: compatlayer D),
      L ≤ L1 ->
      L ≤ (L1 ⊕ L2).
  Proof.
    intros.
    rewrite <- left_upper_bound.
    assumption.
  Qed.

  Lemma le_right {D: compatdata}:
    forall (L L1 L2: compatlayer D),
      L ≤ L2 ->
      L ≤ (L1 ⊕ L2).
  Proof.
    intros.
    rewrite <- right_upper_bound.
    assumption.
  Qed.

  Lemma layer_le_trans `{D: compatdata}:
    forall (LT LL LH: compatlayer D),
      LL ⊕ LT = LH ->
      LL ≤ LH.
  Proof.
    intros.
    rewrite <- H.
    apply left_upper_bound.
  Qed.
  
  Lemma sim_monotonic8 {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L2 L3 L4 L5 L6 L7 L8 L1' L2' L3' L4' L5' L6' L7' L8',
      sim R L1 L1' ->
      sim R L2 L2' ->
      sim R L3 L3' ->
      sim R L4 L4' ->
      sim R L5 L5' ->
      sim R L6 L6' ->
      sim R L7 L7' ->
      sim R L8 L8' ->
      sim R (L1 ⊕ L2 ⊕ L3 ⊕ L4 ⊕ L5 ⊕ L6 ⊕ L7 ⊕ L8) 
          (L1' ⊕ L2' ⊕ L3' ⊕ L4' ⊕ L5' ⊕ L6' ⊕ L7' ⊕ L8').
  Proof.
    intros. repeat apply oplus_sim_monotonic; assumption.
  Qed.

  Lemma sim_monotonic7 {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L2 L3 L4 L5 L6 L7 L1' L2' L3' L4' L5' L6' L7',
      sim R L1 L1' ->
      sim R L2 L2' ->
      sim R L3 L3' ->
      sim R L4 L4' ->
      sim R L5 L5' ->
      sim R L6 L6' ->
      sim R L7 L7' ->
      sim R (L1 ⊕ L2 ⊕ L3 ⊕ L4 ⊕ L5 ⊕ L6 ⊕ L7) 
          (L1' ⊕ L2' ⊕ L3' ⊕ L4' ⊕ L5' ⊕ L6' ⊕ L7').
  Proof.
    intros. repeat apply oplus_sim_monotonic; assumption.
  Qed.

  Lemma sim_monotonic6 {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L2 L3 L4 L5 L6 L1' L2' L3' L4' L5' L6' ,
      sim R L1 L1' ->
      sim R L2 L2' ->
      sim R L3 L3' ->
      sim R L4 L4' ->
      sim R L5 L5' ->
      sim R L6 L6' ->
      sim R (L1 ⊕ L2 ⊕ L3 ⊕ L4 ⊕ L5 ⊕ L6) 
          (L1' ⊕ L2' ⊕ L3' ⊕ L4' ⊕ L5' ⊕ L6').
  Proof.
    intros. repeat apply oplus_sim_monotonic; assumption.
  Qed.

  Lemma sim_monotonic5 {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L2 L3 L4 L5 L1' L2' L3' L4' L5' ,
      sim R L1 L1' ->
      sim R L2 L2' ->
      sim R L3 L3' ->
      sim R L4 L4' ->
      sim R L5 L5' ->
      sim R (L1 ⊕ L2 ⊕ L3 ⊕ L4 ⊕ L5) 
          (L1' ⊕ L2' ⊕ L3' ⊕ L4' ⊕ L5').
  Proof.
    intros. repeat apply oplus_sim_monotonic; assumption.
  Qed.

  Lemma sim_monotonic4 {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L2 L3 L4 L1' L2' L3' L4',
      sim R L1 L1' ->
      sim R L2 L2' ->
      sim R L3 L3' ->
      sim R L4 L4' ->
      sim R (L1 ⊕ L2 ⊕ L3 ⊕ L4) (L1' ⊕ L2' ⊕ L3' ⊕ L4').
  Proof.
    intros. repeat apply oplus_sim_monotonic; assumption.
  Qed.

  Lemma sim_monotonic3 {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L2 L3 L1' L2' L3',
      sim R L1 L1' ->
      sim R L2 L2' ->
      sim R L3 L3' ->
      sim R (L1 ⊕ L2 ⊕ L3 ) 
          (L1' ⊕ L2' ⊕ L3').
  Proof.
    intros. repeat apply oplus_sim_monotonic; assumption.
  Qed.

  Lemma sim_monotonic2 {D1: compatdata} {D2: compatdata} {R: _ D1 D2}:
    forall L1 L2 L1' L2',
      sim R L1 L1' ->
      sim R L2 L2' ->
      sim R (L1 ⊕ L2) (L1' ⊕ L2').
  Proof.
    intros. apply oplus_sim_monotonic; assumption.
  Qed.

End LayerCalculus.


    Ltac sim_oplus_split_straight:=
      lazymatch goal with
        | |- sim _ (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _ ⊕ _ ⊕ _ ⊕ _) _ =>
          apply sim_monotonic8; [| | | | | | | sim_oplus_split_straight]
        | |- sim _ (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _ ⊕ _ ⊕ _) _ =>
          apply sim_monotonic7; [| | | | | |sim_oplus_split_straight]
        | |- sim _ (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _ ⊕ _) _ =>
          apply sim_monotonic6; [| | | | |sim_oplus_split_straight]
        | |- sim _ (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _) _ =>
          apply sim_monotonic5; [| | | | sim_oplus_split_straight]
        | |- sim _ (_ ⊕ _ ⊕ _ ⊕ _) _ =>
          apply sim_monotonic4; [| | |sim_oplus_split_straight]
        | |- sim _ (_ ⊕ _ ⊕ _) _ =>
          apply sim_monotonic3; [| | sim_oplus_split_straight]
        | |- sim _ (_ ⊕ _) _ =>
          apply sim_monotonic2; [|sim_oplus_split_straight]
        | _ => idtac
      end.


  Ltac sim_move_to_head a := 
    match goal with
      | |- sim _ _ ?T =>
        match T with
          | a ↦ _ => idtac
          | ?A ⊕ ?B => 
            match A with
              | context [ a ] => 
                match A with
                  | ?C ⊕ ?D => 
                    match C with
                      | context [a] => apply sim_associativity;
                                      sim_move_to_head a
                      | _ => apply sim_assoc_comm; sim_move_to_head a
                    end
                  | _ => idtac
                end
              | _ => apply sim_commutativity; sim_move_to_head a
            end
        end
    end.

   Ltac sim_oplus_split:=
    match goal with
      | |- sim _ ?A ?B =>
        match A with
          | (?a ↦ _) => sim_move_to_head a; 
                       match B with
                         | (_ ↦ _) => idtac
                         | _ => apply sim_left
                       end
          | (?a ↦ _ ⊕ _ ) => 
            sim_move_to_head a; apply oplus_sim_monotonic; [| sim_oplus_split]
        end
      | _ => idtac
    end.

  Ltac le_move_to_head a := 
    match goal with
      | |- _ ≤ ?T =>
        match T with
          | a ↦ _ => idtac
          | ?A ⊕ ?B => 
            match A with
              | context [ a ] => 
                match A with
                  | ?C ⊕ ?D => 
                    match C with
                      | context [a] => apply le_associativity;
                                      le_move_to_head a
                      | _ => apply le_assoc_comm; le_move_to_head a
                    end
                  | _ => idtac
                end
              | _ => apply le_commutativity; le_move_to_head a
            end
        end
    end.

  Ltac le_oplus_split:=
    match goal with
      | |- ?A ≤ ?B =>
        match A with
          | (?a ↦ _) => le_move_to_head a; 
                       match B with
                         | (_ ↦ _) => idtac
                         | _ => apply le_left
                       end
          | (?a ↦ _ ⊕ _ ) => 
            le_move_to_head a; apply oplus_monotonic; [ reflexivity | le_oplus_split]
        end
      | _ => idtac
    end. 

  Ltac le_move_to_head_quick a := 
    match goal with
      | |- _ ≤ ?T =>
        match T with
          | a ↦ _ => idtac
          | ?A ⊕ ?B => 
            match A with
              | context [ a ] => apply le_left; le_move_to_head_quick a
              | _ => apply le_right; le_move_to_head_quick a
            end
        end
    end.

  Ltac le_oplus_split_quick:=
    match goal with
      | |- (?a ↦ _) ≤ ?B =>
        le_move_to_head_quick a; reflexivity
    end.


  (** Recursively unfold layer definitions. *)

  Ltac unfold_layer t :=
    lazymatch t with
      | _ ↦ _ =>
        idtac
      | ?L1 ⊕ ?L2 =>
        unfold_layer L1;
        unfold_layer L2
      | _ =>
        let def := eval red in t in
        change t with def;
        unfold_layer def
      | _ =>
        idtac
    end.

  Ltac unfold_layers :=
    match goal with
      | |- ?L1 ≤ ?L2 =>
        unfold_layer L1;
        unfold_layer L2
      | |- sim _ ?L1 ?L2 =>
        unfold_layer L1;
        unfold_layer L2
    end.

  (** For [(≤)], we can use the pseudojoin reflection-based tactic.
    TODO: extend to sim and see if that's faster, for [sim_oplus]. *)

  Require Import PseudoJoinReflection.

  Ltac le_oplus :=
    match goal with
      | |- le (A := compatlayer ?D) _ _ =>
        pose proof (sim_pseudojoin _ D);
        unfold_layers;
        unfold AST.ident;
        pjr
      | |- le _ _ =>
        unfold_layers;
        unfold AST.ident;
        pjr
      | |- ?goal =>
        fail 1 "le_oplus could not prove:" goal
    end.

  (** Final tactic: break down the inequality into components and try
    to solve the parts that are the same. *)

  Ltac construct_passthrough_layer T1 T2:= 
    match T1 with
      | (?a ↦ _) ⊕ ?B =>
        match T2 with
          | context [a ↦ ?X] => 
            let T2' := (construct_passthrough_layer B T2) in
            constr : ((a ↦ X) ⊕ T2')
        end
      | (?a ↦ _)=>
        match T2 with
          | context [a ↦ ?X] => 
            constr : (a ↦ X)
        end
    end.

  Ltac construct_left_layer T1 T2 D:= 
    match T2 with
      | ?A ⊕ ?B =>
        let T21 := (construct_left_layer T1 A D) in
        let T22 := (construct_left_layer T1 B D) in
        match T21 with
          | ∅  => T22
          | _ => match T22 with
                   | ∅ => T21
                   | _ => constr : (T21 ⊕ T22)
                 end
        end
      | (?a ↦ ?X) =>
        match T1 with
          | context [a] => constr : (@emptyset _ (layer_empty D))
          | _ => constr : (a ↦ X)
        end
    end.

  Ltac sim_oplus := 
    unfold_layers;
    match goal with
      | |- le (A := _ ?D) ?T1 ?T2 =>
        change (sim id T1 T2);
        sim_oplus
      | |- simRR _ ?D _ ?T1 ?T2 =>
        let L1 := construct_passthrough_layer T1 T2 in
        let L2 := construct_left_layer T1 T2 D in
        change T2 with (L1 ⊕ L2);
          apply sim_left;
          try reflexivity;
          sim_oplus_split_straight
    end.

  (** For backward compatibility. Calls can be replaced by
    [sim_oplus_final], which infers [D] automatically and unfolds layers if needed. *)
  Ltac sim_oplus_split_final D := 
    sim_oplus.
