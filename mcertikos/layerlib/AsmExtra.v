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
Require Import Integers.
Require Import Values.
Require Import AST.
Require Export Asm.
Require Import EventsExtra.
Require Import AbstractData.
Require Import BuiltinFunctionsExtra.
Require Import MemoryExtra.
Require Import Locations.
Require Export LayerConfiguration.


    Ltac specDecIn NAME EQDEC ITEM LIST :=
      let HTEMP := fresh "HTEMP" in
      destruct (In_dec EQDEC ITEM LIST) as [NAME | NAME] eqn:HTEMP; compute in HTEMP; try discriminate; clear HTEMP.

    Ltac specDecInApply EQDEC ITEM LIST :=
      let NAME := fresh "NAME" in
      specDecIn NAME EQDEC ITEM LIST; apply NAME.

    Ltac decIn EQDEC :=
      match goal with
        | |- In ?ITEM ?LIST => specDecInApply EQDEC ITEM LIST
        | |- ~ In ?ITEM ?LIST => specDecInApply EQDEC ITEM LIST
      end.

    Lemma reg_inv:
      forall reg
             (n0: reg <> PC)
             (n2 : reg <> SOF)
             (n3 : reg <> PF)
             (n4 : reg <> CF)
             (n5 : reg <> ZF)
             (n6 : reg <> RA)
             (n7 : reg <> ST0)
             (n8 : reg <> XMM7)
             (n9 : reg <> XMM6)
             (n10 : reg <> ECX)
             (n11 : reg <> EDX)
             (n12 : reg <> XMM5)
             (n13 : reg <> XMM4)
             (n14 : reg <> XMM3)
             (n15 : reg <> XMM2)
             (n16 : reg <> XMM1)
             (n17 : reg <> XMM0)
             (n18 : reg <> EAX)
             (n19 : reg <> ESP) (* particular case *)
      ,
        exists l, reg = preg_of l
                                /\ ~ In (R l) Conventions1.temporaries
                                /\ ~ In (R l) Conventions1.destroyed_at_call.
    Proof with (split; try reflexivity; split; decIn Loc.eq).
      Transparent Loc.eq mreg_eq.
      intros. destruct reg; try congruence.
      destruct i; try congruence.
       exists BX...
       exists SI...
       exists DI...
       exists BP...
      destruct f; congruence.
      destruct c; congruence.
      Opaque Loc.eq mreg_eq.
    Qed.


Section EXTRA_WITHOUT_EF.
  Context `{Hlayer: LayerConfiguration}.

  Lemma asm_invariant_put_abstract_data:
    forall (ge: genv) rs m,
      asm_invariant ge (State rs m) ->
      forall d: data,
        asm_invariant ge (State rs (Mem.put_abstract_data m d)).
  Proof.
    inversion 1; subst.
    inversion INJECT_NEUTRAL; subst.
    split; auto.
    split; rewrite Mem.nextblock_put_abstract_data; auto.
    apply Mem.inject_neutral_put_abstract_data; auto.
  Qed.

Lemma exec_load_abstract_data:
  forall m ge chunk a rd r rs' m',
      exec_load ge chunk m a r rd = Next rs' m' ->
      Mem.get_abstract_data m' = Mem.get_abstract_data m.
Proof.
  intros until m'.
  unfold exec_load.
  destruct (eval_addrmode ge a r); try discriminate.
  simpl.
  destruct (Mem.load chunk m b (Int.unsigned i)) as [] eqn:LOAD; simpl in *; try discriminate.
  injection 1; intros; subst; eauto.
Qed.

Lemma exec_store_abstract_data:
  forall m ge chunk a rd r rs' m',
      exec_store ge chunk m a r rd = Asm.Next rs' m' ->
      Mem.get_abstract_data m' = Mem.get_abstract_data m.
Proof.
  intros until m'.
  unfold exec_store.
  destruct (eval_addrmode ge a r); try discriminate.
  simpl.
  destruct (Mem.store chunk m b (Int.unsigned i) (r rd)) as [] eqn:STORE; simpl in *; try discriminate.
  injection 1; intros; subst; erewrite <- Mem.store_get_abstract_data by eassumption; eauto.
Qed.

Ltac injauto := injection 1; intros; subst; eauto.

Lemma exec_instr_abstract_data:
  forall m ge c i r rs' m',
      Asm.exec_instr ge c i r m = Asm.Next rs' m' ->
      Mem.get_abstract_data m' = Mem.get_abstract_data m.
Proof.
  Opaque preg_eq.
  destruct i; simpl; try discriminate; try injauto;
  try (intros; eapply exec_load_abstract_data; now eauto);
  try (intros; eapply exec_store_abstract_data; now eauto).

  + (* Pdivision *)
    intros until m'.
    destruct (exec_division div r1 r); try discriminate.
    injauto.

  + (* Pwrap division *)
    intros until m'.
    destruct (preg_eq rd EAX); try discriminate.
    destruct (exec_division div ECX (r # EAX <- (r rd)) # ECX <- (r r1)); try discriminate.
    injauto.

  + (* Pwrap division *)
    intros until m'.
    destruct (preg_eq rd EAX); try discriminate.
    destruct (exec_division div ECX (r # EAX <- (r rd)) # ECX <- (r r1)); try discriminate.
    injauto.

  + (* eval testcond 1 *)
    intros until m'.
    destruct (eval_testcond c0 r) as [ [ | ] | ]; injauto.

  + (* goto label *)
    intros until m'; goto_label_mem_unch.

  + (* eval testcond 2 *)
    intros until m'.
    destruct (eval_testcond c0 r) as [ [ | ] | ]; try discriminate; try goto_label_mem_unch; injauto.

  + (* eval testcond cascading *)
    intros until m'.
    destruct (eval_testcond c1 r) as [ [ | ] | ]; try discriminate; destruct (eval_testcond c2 r) as [ [ | ] | ]; try discriminate; try goto_label_mem_unch; injauto.

  + (* switch table *)
    intros until m'.
    destruct (r0 r); try discriminate.
    destruct (list_nth_z tbl (Int.unsigned i)); try discriminate.
    goto_label_mem_unch.

  + (* Pallocframe *)
    intros until m'.
    destruct (Mem.alloc Tag_stack m 0 sz) as [] eqn:ALLOC. simpl in *.
    destruct (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)) (r ESP)) as [ | ] eqn: STORE_LINK; try discriminate.
    destruct (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)) (r RA)) as [ | ] eqn:STORE_RA; try discriminate.
    injection 1; intros; subst.
    erewrite <- Mem.store_get_abstract_data by eassumption.
    erewrite <- Mem.store_get_abstract_data by eassumption.
    erewrite <- Mem.alloc_get_abstract_data by eassumption.
    eauto.

  + (* Pfreeframe *)
    intros until m'.
    destruct (Mem.loadv Mint32 m (Val.add (r ESP) (Vint ofs_ra))) as [ | ] eqn:LOAD_RA; simpl in *; try discriminate.
    destruct (Mem.loadv Mint32 m (Val.add (r ESP) (Vint ofs_link))) as [ | ] eqn:LOAD_LINK; simpl in *; try discriminate.
    destruct (r ESP); try discriminate.
    destruct (Mem.free m b 0 sz) as [ | ] eqn:FREE; try discriminate.
    injection 1; intros; subst.
    erewrite <- Mem.free_get_abstract_data by eassumption.
    eauto.
 Qed.

   Variable kernel_mode: data -> Prop.

   Hypothesis prim_kernel_mode:
     forall p (ge: genv) args m t res m',
         external_call p ge args m t res m' ->
         kernel_mode (Mem.get_abstract_data m) ->
         kernel_mode (Mem.get_abstract_data m').

   Lemma asm_kernel_invariant:
     forall m,
       kernel_mode (Mem.get_abstract_data m) ->
       forall ge r t r' m',
      Asm.step ge (State r m) t (State r' m') ->
      kernel_mode (Mem.get_abstract_data m').
   Proof.
     inversion 2; subst. 
     + (* exec_instr *)
       erewrite exec_instr_abstract_data. eassumption. eassumption.
     + (* builtin *)
       erewrite builtin_abstract_data; simpl in *; eauto.
     + (* annot *)
       erewrite builtin_abstract_data; simpl in *; eauto.
     + (* external *)
       eapply prim_kernel_mode. 
       eassumption.
       assumption.
   Qed.

End EXTRA_WITHOUT_EF.

(*
Section COMPAT.
  Context `{layer: LAYERSPEC}.

  Definition genv := Asm.genv (external_function := _ + _).
  Definition fundef := Asm.fundef (external_function := _ + _).
  Definition program := Asm.program (external_function := _ + _).
  Definition outcome := Asm.outcome (mem := bmem × abstract_data layer).
  Definition Next := Asm.Next (mem := bmem × abstract_data layer).
  Definition state := Asm.state (mem := bmem × abstract_data layer).
  Definition State := Asm.State (mem := bmem × abstract_data layer).
  Definition extcall_arguments := Asm.extcall_arguments (mem := bmem × _).
End COMPAT.

Notation "'Asm.genv' ( 'layer' := x )" := (genv (layer := x)).
Notation "'Asm.genv'" := genv.
*)
