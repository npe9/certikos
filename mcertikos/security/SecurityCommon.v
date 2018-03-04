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
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import AbstractDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.
Require Import CommonTactic.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import Soundness.
Require Import liblayers.lib.Monad.
Require Import TSysCall.
Require Import I64Layer.

(* This file defines various useful tactics and lemmas for the security proof. *)

(* We will assume that all processes with ID high_id or less are trusted. That is,
   we will only prove that processes with ID greater than high_id cannot learn
   information about other processes. This allows us to support shared memory IPC
   between trusted processes, which is a nice feature to have. *)
Notation high_id := 2%Z.

Ltac inv_layer Hl :=
          match type of Hl with
          | get_layer_primitive ?name _ = OK (Some ?σ) => let Hl' := fresh in
            repeat (apply Soundness.get_layer_primitive_oplus_either in Hl; destruct Hl as [Hl|Hl]);
              try (match goal with
                   | [ H : get_layer_primitive _ (?id ↦ _) = _ |- _ ] => destruct (Pos.eq_dec name id); subst
                   end; 
                   [rewrite get_layer_primitive_mapsto in Hl; inv Hl | 
                    rewrite get_layer_primitive_mapsto_other_primitive in Hl; auto; inv Hl]); simpl in *;        
              try solve [assert (Hl':= Soundness.get_layer_primitive_oplus_either name ∅ ∅ σ Hl);
                         destruct Hl' as [Hl'|Hl']; rewrite get_layer_primitive_empty in Hl'; inv Hl']
          end.

Ltac unfold_lift := simpl in *; unfold lift in *; simpl in *.

Ltac gensem_simpl := 
    repeat (        
        match goal with
        | [ H: GenSem.semof _ _ _ _ _ |- _ ] => inv H
        end).

Section WITHMEM.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (* The tsyscall layer includes both the primitives of tsyscall, as well as the
     semantics for user-land assembly instructions, L64. *)
  Definition tsyscall_layer := tsyscall ⊕ L64.

  Context {D : compatdata} {L : compatlayer D}.
  Context `{Hacc: !AccessorsDefined L}.

  Local Instance : ExternalCallsOps (mwd D) := 
    CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance : LayerConfigurationOps := 
    compatlayer_configuration_ops L.

  Section OWNER.

    Local Open Scope Z_scope.

    (* The concept of an owner defines which data belong to which principals.
       This allows us to state security properties with respect to this ownership. *)

    Inductive isOwner (lat : ZMap.t LATInfo) (id : Z) (p : Z) : Prop :=
    | isOwner_intro : forall b t l pdi pti,
                        ZMap.get p lat = LATValid b t l -> In (LATO id pdi pti) l ->
                        isOwner lat id p.

    Inductive noOwner (lat : ZMap.t LATInfo) (p : Z) : Prop :=
    | noOwner_intro : forall b t, 
                        ZMap.get p lat = LATValid b t nil -> noOwner lat p.

    Inductive noValidOwner (lat : ZMap.t LATInfo) (p : Z) : Prop :=
    | noValidOwner_intro : 
        forall b t l, 
          ZMap.get p lat = LATValid b t l -> 
          (forall id pdi pti, In (LATO id pdi pti) l -> id <= high_id) ->
          noValidOwner lat p.

    Lemma pmap_owners_consistent : 
      forall d id p va pt pte perm,
        high_level_invariant d -> 0 <= id < num_id -> 0 <= va < adr_max ->
        ZMap.get (PDX va) (ZMap.get id (ptpool d)) = PDEValid pt pte ->
        ZMap.get (PTX va) pte = PTEValid p perm ->
        isOwner (LAT d) id p.
    Proof.
      intros m id p va pt pte perm Hinv Hid Hva Hpd Hpt.
      apply valid_pmap_domain in Hinv.
      destruct (Hinv _ Hid _ Hva _ _ Hpd _ _ Hpt) as [Hnps [Hperm Howner]].
      destruct Howner as [l [Hlat Hin]]; econstructor; eauto.
      rewrite (count_occ_In LATOwner_dec _ (LATO id (PDX va) (PTX va))).
      rewrite Hin; auto.
    Qed.

    Lemma PDEValid_usr :
      forall id i d pti pte,
        high_level_invariant d -> ikern d = false -> 0 <= id < num_id ->
        ZMap.get (PDX (Int.unsigned i)) (ZMap.get id (ptpool d)) = PDEValid pti pte ->
        adr_low <= Int.unsigned i < adr_high.
    Proof.
      intros id i d pti pte Hinv Hkern Hid Hpdx.
      assert (Hrange:= Int.unsigned_range_2 i).
      assert (Hmax:= max_unsigned_val).
      destruct Hinv.
      destruct (valid_PMap (valid_kern Hkern) id Hid) as [Hpmap _].
      assert (Hcases: adr_low <= Int.unsigned i < adr_high \/
                      (0 <= Int.unsigned i < 262144*PgSize \/ 
                       983040*PgSize <= Int.unsigned i < 1048576*PgSize)) by omega.
      destruct Hcases as [|Hcases]; auto.
      assert (Hk: 0 <= Int.unsigned i / PgSize < 262144 \/
                  983040 <= Int.unsigned i / PgSize < 1048576) 
        by  (destruct Hcases; [left|right]; split;
             try (apply Zdiv_le_lower_bound; omega); 
             try (apply Zdiv_lt_upper_bound; omega)).
      specialize (Hpmap _ Hk); unfold PDE_kern in Hpmap.
      replace (PDX (Int.unsigned i / 4096 * 4096)) with (PDX (Int.unsigned i)) in Hpmap.
      rewrites.
      unfold PDX.
      rewrite (Z_div_mod_eq (Int.unsigned i) PgSize); try omega.
      repeat rewrite <- Zdiv.Zdiv_Zdiv; try omega.
      rewrite Z.mul_comm.
      rewrite Z_div_plus_full_l; try omega.
      rewrite (Zdiv_small (Int.unsigned i mod PgSize) PgSize).
      rewrite Zplus_0_r.
      rewrite Z_div_mult_full; try omega.
      apply Z_mod_lt; omega.
    Qed.

  End OWNER.

  Section EXTERNAL_CALL.

    Ltac unfold_lift := simpl in *; unfold lift in *; simpl in *.

    Lemma external_call'_eq_aux : 
      forall WB ef (ge : genv) vargs (m m' : mem) (d d' : D) t v,
        match ef with EF_external _ _ => False | _ => True end ->
        external_call' WB ef ge vargs (m,d) t v (m',d') -> d = d'.
    Proof.
      intros WB ef ge vargs m m' d d' t v Hef Hexec.
      inv Hexec.
      destruct ef; inv Hef; inv H; auto.
      - inv H1; auto.
        unfold_lift; elim_none; inv H2; auto.
      - inv H2; auto.
        unfold_lift; elim_none; inv H3; auto.
      - unfold_lift; subdestruct; inv H1; inv H2; auto.
      - unfold_lift; subdestruct; inv H1; inv H3; auto.
      - unfold_lift; subdestruct; inv H8; auto.
    Qed.

    (*Lemma external_call'_eq : 
      forall WB ef (ge : genv) vargs (m m' : mem) (d d' : cdata RData) t v,        
        external_call' WB ef ge vargs (m,d) t v (m',d') -> pg d = true -> d = d'.
    Proof.
      intros WB ef ge vargs m m' d d' t v Hexec Hpg.
      destruct ef; try solve [apply external_call'_eq_aux in Hexec; auto].
      inv Hexec.
      destruct H as [σ [Hl Hsem]].
      destruct Hsem as [s [σ' [Hmatch [Hexec [Heq1 [Heq2 Heq3]]]]]]; subst.
      inv_layer Hl; try solve [inv Hexec; reflexivity].
      - inv Hexec; gensem_simpl.
        unfold proc_init_spec in *; subdestruct.
    Qed.*)

  End EXTERNAL_CALL.

  Section LASM_STEP.
    
    Variable P: D -> D -> Prop.

    Lemma step_P :
      forall ge rs rs' (m m' : mem) (d d' : D) t,
        LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
        forall (refl_P: forall d, P d d)
               (exec_loadex_P:
                  forall chunk a rd,
                    LAsm.exec_loadex ge chunk (m,d) a rs rd = Next rs' (m',d') ->
                    P d d')
               (exec_storeex_P :
                  forall chunk a rd rds,
                    LAsm.exec_storeex ge chunk (m,d) a rs rd rds = Next rs' (m',d') ->
                    P d d')
               (external_call_P: 
                  forall name sg args res,
                    external_call' (fun _ : block => True) (EF_external name sg) 
                                   ge args (m, d) t res (m', d') ->
                    P d d')
               (primitive_call_P:     
                  forall ef,      
                    primitive_call ef ge rs (m, d) t rs' (m', d') ->
                    P d d'),
          P d d'.
    Proof.
      Opaque primitive_call.
      intros ge' rs rs' m m' d d' t Hstep. intros.
      inv Hstep.
      {
        (* Case 1: internal step (assembly command) *)
        rename H7 into Hexec.
        destruct i; simpl in *; inv Hexec; eauto.
        destruct i; simpl in *;
        try solve [inv H0; eauto |
                   unfold goto_label in *; subdestruct; inv H0; auto |
                   unfold lift in *; simpl in *; subdestruct; inv H0; auto].
      }
      {
        erewrite <- external_call'_eq_aux; eauto.
      }
      {
        erewrite <- external_call'_eq_aux; eauto.
      }
      {
        destruct ef; try solve [apply external_call'_eq_aux in H7; subst; auto].
        eapply external_call_P; eauto.
      }
      {
        eapply primitive_call_P; eauto.
      }
    Qed.

  End LASM_STEP.

End WITHMEM.

  (*Ltac solve_extcall :=
    repeat match goal with
    | [ H : appcontext [external_call'] |- _ ] => 
      apply external_call'_eq in H; try assumption
    end; subst; try assumption; try congruence.*)

  Ltac solve_extcall_aux :=
    match goal with
    | [ H : appcontext [external_call' _ ?ef] |- _ ] => 
      destruct ef; try solve [apply external_call'_eq_aux in H; subst; auto]
    end.

  (* removed a simpl from subdestruct that had a tendency to cause unbounded execution *)
  Ltac subdestruct':=
    repeat progress (
             match goal with
               | [ HT: context[if ?con then _  else  _] |- _] => subdestruct_if con
               | [ HT: context[match ?con with |_ => _ end] |- _] => subdestruct_if con
             end; simpl).

  Ltac inv_spec :=
    repeat (
        match goal with
          | [ H: ?f _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
        end); subdestruct'.

  (* inv_spec sometimes takes forever if there's too many layers of unfolding 
     use inv_spec' in this situation (although more work will be needed to complete the proof) *)
  Ltac inv_spec' :=
    repeat (
        match goal with
          | [ H: ?f _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ = Some _ |- _ ] => unfold f in H
        end); subdestruct'.

  Ltac inv_extcall_spec :=
    repeat (
        match goal with
          | [ H: ?f _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ _ = ret _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ _ _ = ret _ |- _ ] => unfold f in H
        end); subdestruct'.

  Remark inv_some {A} : forall (x y : A), Some x = Some y -> x = y.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Remark inv_some2 {A B} : 
    forall (x1 x2 : A) (y1 y2 : B), Some (x1,y1) = Some (x2,y2) -> x1 = x2 /\ y1 = y2.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Ltac inv_rewrite := 
    match goal with
      | [ H : Some (_,_) = Some (_,_) |- _ ] => apply inv_some2 in H; destruct H
      | [ H : Some _ = Some _ |- _ ] => apply inv_some in H
    end; subst; simpl; auto.

  Ltac inv_rewrite' := 
    match goal with
      | [ H : Some (_,_) = Some (?X,_) |- _ _ = _ ?X ] => apply inv_some2 in H
      | [ H : Some _ = Some ?X |- _ _ = _ ?X ] => apply inv_some in H
    end; subst; simpl; auto.

  Ltac elim_stuck :=
    match goal with
      | [H : match ?X with | _ => _ end = Next _ _ |- _ ] => destruct X; try discriminate H
      | [H : if ?X then _ else _ = Next _ _ |- _ ] => destruct X; try discriminate H
    end.

  Ltac elim_stuck_eqn H' :=
    match goal with
      | [H : match ?X with | _ => _ end = Next _ _ |- _ ] => destruct X eqn:H'; try discriminate H
      | [H : if ?X then _ else _ = Next _ _ |- _ ] => destruct X eqn:H'; try discriminate H
    end.

  Ltac determ_simpl := 
    repeat (match goal with 
            | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H' in H; inv H
            end).

  Ltac unfold_specs :=
    repeat (
        match goal with
          | [ H: ?f _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
          | [ H: ?f _ _ _ _ _ _ _ _ _ _ = Some _ |- _ ] => unfold f in H
        end).

  Ltac inv_layer_no_simpl Hl :=
          match type of Hl with
          | get_layer_primitive ?name _ = OK (Some ?σ) => let Hl' := fresh in
            repeat (apply Soundness.get_layer_primitive_oplus_either in Hl; destruct Hl as [Hl|Hl]);
              try (match goal with
                   | [ H : get_layer_primitive _ (?id ↦ _) = _ |- _ ] => destruct (Pos.eq_dec name id); subst
                   end; 
                   [rewrite get_layer_primitive_mapsto in Hl; inv Hl | 
                    rewrite get_layer_primitive_mapsto_other_primitive in Hl; auto; inv Hl]);  
              try solve [assert (Hl':= Soundness.get_layer_primitive_oplus_either name ∅ ∅ σ Hl);
                         destruct Hl' as [Hl'|Hl']; rewrite get_layer_primitive_empty in Hl'; inv Hl']
          end.

  Ltac inv_somes := 
    repeat match goal with
      | [ H : Some (_,_) = Some (_,_) |- _ ] => apply inv_some2 in H; destruct H
      | [ H : Some _ = Some _ |- _ ] => apply inv_some in H
    end; try subst.

  Ltac eqdestruct :=
      repeat match goal with
      | [ |- if ?a then _ else _ = if ?a then _ else _ ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      | [ |- match ?a with _ => _ end = match ?a with _ => _ end ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      end.

  Ltac destructgoal :=
      repeat match goal with
      | [ |- appcontext [if ?a then _ else _] ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      | [ |- appcontext [match ?a with _ => _ end] ] => 
        let H := fresh "Hdestruct" in destruct a eqn:H; auto
      end.

  Ltac elim_stuck' H :=
    match type of H with
    | match ?X with | _ => _ end = Next _ _ => destruct X; try discriminate H
    | if ?X then _ else _ = Next _ _  => destruct X; try discriminate H
    end.

  Ltac elim_stuck_eqn' H H' :=
    match type of H with
    | match ?X with | _ => _ end = Next _ _ => destruct X eqn:H'; try discriminate H
    | if ?X then _ else _ = Next _ _ => destruct X eqn:H'; try discriminate H
    end.

  Ltac subst' :=
  repeat match goal with
  | [ H : ?a = _ |- _ ] => rewrite H in *; clear a H
  | [ H : _ = ?a |- _ ] => rewrite <- H in *; clear a H
  end.

  Ltac inv' H := inversion H; clear H; subst'.

  Ltac rewrites' :=
   repeat match goal with
   | Heq1:?a = _, Heq2:?a = _ |- _ => rewrite Heq2 in Heq1; inv' Heq1
   | Heq:?a = _ |- appcontext [if ?a then _ else _] => rewrite Heq
   | Heq:_ = ?a |- appcontext [if ?a then _ else _] => rewrite <- Heq
   | Heq:?a = _ |- appcontext [match ?a with
                               | _ => _
                               end] => rewrite Heq
   | Heq:_ = ?a |- appcontext [match ?a with
                               | _ => _
                               end] => rewrite <- Heq
   | Heq:?a = _, H:appcontext [if ?a then _ else _] |- _ => rewrite Heq in H
   | Heq:_ = ?a, H:appcontext [if ?a then _ else _]
     |- _ => rewrite <- Heq in H
   | Heq:?a = _, H:appcontext [match ?a with
                               | _ => _
                               end] |- _ => rewrite Heq in H
   | Heq:_ = ?a, H:appcontext [match ?a with
                               | _ => _
                               end] |- _ => rewrite <- Heq in H
   end.

  Ltac inv_somes' :=
   repeat match goal with
   | H:Some (_, _) = Some (_, _) |- _ => apply inv_some2 in H; destruct H
   | H:Some _ = Some _ |- _ => apply inv_some in H
   end; subst'.

