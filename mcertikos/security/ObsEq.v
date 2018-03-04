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
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.

Require Import compcert.cfrontend.Ctypes.
Require Import Conventions.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.

Require Import AbstractDataType.
Require Import Soundness.

Require Import SecurityCommon.
Require Import FunctionalExtensionality.

Open Scope Z_scope.

(* This file defines the observation function for mCertiKOS.
   Paper Reference: Section 4 *)

Section WITHMEM.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{Hcomp: CompatData RData}.

  (* A typeclass for defining observation functions over mCertiKOS abstract state 
     (type cdata RData). As in the paper, the function takes both a principal
     and a state as parameters, and produces a value of an arbitrary observation type.
     Observable equivalence is defined to be equality of observations.
     We add a property over principals to allow for distinguishing trusted processes
     from untrusted processes (the final security proof will only apply to principals
     for which the property holds). *)
  Class Observer (obs : Type) :=
    {
      obs_id : Z;
      obs_id_prop: obs_id > high_id;

      observe : cdata RData -> obs;
      obs_eq s1 s2 := observe s1 = observe s2
    }.

  Lemma obs_eq_equiv {obs} {o : Observer obs} : Equivalence (obs_eq(Observer:=o)).
  Proof.
    constructor; unfold obs_eq; congruence.
  Qed.

  Section OBS_EQ.

    (* This is the virtual address space observation function, which produces
       an option value for each virtual address location, based on whether
       that location is mapped in the process's page tables. As explained in
       the paper, it is *crucial* that this observation hides physical
       address locations like the pi variable below (pi is the physical
       page index; "PTADRR pi vadr" is defined as pi*PGSIZE + (vadr % PGSIZE)). *)

    Function vread i vadr (ptp: PMapPool) (hp : FlatMem.flatmem) :=
      (* User space addresses are between constants adr_low and adr_high *)
      if zle_lt adr_low vadr adr_high then
        (* first level of page tables *)
        match ZMap.get (PDX vadr) (ZMap.get i ptp) with
          | PDEValid _ pte =>
            (* second level of page tables *)
            match ZMap.get (PTX vadr) pte with
              | PTEValid pi _ => Some (ZMap.get (PTADDR pi vadr) hp)
              | _ => None
            end
          | _ => None
        end
      else None.

    (* Various permission bits in the page tables must be observable. This
       is mostly only needed for the SafeSecure lemma. *)

    Inductive ObsPerm :=
    | ObsValid : PTPerm -> PPgInfo -> ObsPerm
    | ObsPDEID : ObsPerm
    | ObsPDEUnPresent : ObsPerm
    | ObsPDEUndef : ObsPerm
    | ObsPTEUnPresent : ObsPerm
    | ObsPTEUndef : ObsPerm.

    Function vread_perm i vadr (ptp: PMapPool) (pp : PPermT) :=
      if zle_lt adr_low vadr adr_high then
        match ZMap.get (PDX vadr) (ZMap.get i ptp) with
          | PDEValid _ pte =>
            match ZMap.get (PTX vadr) pte with
              | PTEValid v p => Some (ObsValid p (ZMap.get v pp))
              | PTEUnPresent => Some ObsPTEUnPresent
              | PTEUndef => Some ObsPTEUndef
            end
          | PDEUnPresent => Some ObsPDEUnPresent
          | PDEID => Some ObsPDEID
          | PDEUndef => Some ObsPDEUndef
        end
      else None.

    (* The type of observations over abstract data *)
    Record my_obs :=
      {
        observe_HP: Z -> option FlatMem.flatmem_val;
        observe_perm: Z -> option ObsPerm;
        observe_AC_quota: Z;
        observe_AC_nchildren: nat;
        observe_AC_used: bool;
        observe_cid: bool;
        observe_kctxt: regset;          
        observe_uctxt: UContext;
        observe_ti: option int;
        observe_OUT: list DeviceAction;
        observe_ikern: option bool;
        observe_ihost: option bool;
        observe_pg: option bool;
        observe_ipt: option bool;
        observe_init: option bool
      }.

    (* For some reason, the f_equal tactic takes an extremely long time for this definition 
       of my_obs (too many fields maybe?). Following is a specialization of the tactic
       that terminates immediately. *)
    Fact f_equal_my_obs :
      forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
             b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15,
        a1 = b1 -> a2 = b2 -> a3 = b3 -> a4 = b4 -> a5 = b5 -> 
        a6 = b6 -> a7 = b7 -> a8 = b8 -> a9 = b9 -> a10 = b10 -> 
        a11 = b11 -> a12 = b12 -> a13 = b13 -> a14 = b14 -> a15 = b15 ->
        Build_my_obs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =
        Build_my_obs b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15.
    Proof.
      intros; subst; reflexivity.
    Qed.

    (* The observation function for abstract data.
       Paper Reference: Section 4 *)
    Definition my_observe (i: Z) (d: cdata RData) : my_obs :=
      {|
        observe_HP vadr:= vread i vadr (ptpool d) (HP d);
        observe_perm vadr:= vread_perm i vadr (ptpool d) (pperm d);
        observe_AC_quota:= 
          cquota (ZMap.get i (AC d)) - cusage (ZMap.get i (AC d));
        observe_AC_nchildren:= length (cchildren (ZMap.get i (AC d)));
        observe_AC_used:= cused (ZMap.get i (AC d));
        observe_cid:= zeq i (cid d);
        observe_kctxt:= ZMap.get i (kctxt d);          
        observe_uctxt:= ZMap.get i (uctxt d);
        observe_ti:= if zeq i (cid d) then Some (fst (ti d)) else None;
        observe_OUT:= ZMap.get i (devout d);

        (* the following global flags only need to be observable for the SafeSecure proof *)
        observe_ikern:= if zeq i (cid d) then Some (ikern d) else None;
        observe_ihost:= if zeq i (cid d) then Some (ihost d) else None;
        observe_pg:= if zeq i (cid d) then Some (pg d) else None;
        observe_ipt:= if zeq i (cid d) then Some (ipt d) else None;
        observe_init:= if zeq i (cid d) then Some (init d) else None
      |}.

    (* An observable equivalence relation defined for convenience *)
    Record my_obs_eq (i: Z) (d1 d2: cdata RData) :=
      {
        obs_eq_HP: 
          forall vadr, 
            vread i vadr (ptpool d1) (HP d1) = vread i vadr (ptpool d2) (HP d2);
        obs_eq_perm: 
          forall vadr, 
            vread_perm i vadr (ptpool d1) (pperm d1) = vread_perm i vadr (ptpool d2) (pperm d2);
        obs_eq_AC_quota: 
          cquota (ZMap.get i (AC d1)) - cusage (ZMap.get i (AC d1)) = 
          cquota (ZMap.get i (AC d2)) - cusage (ZMap.get i (AC d2));
        obs_eq_AC_nchildren: length (cchildren (ZMap.get i (AC d1))) = 
                             length (cchildren (ZMap.get i (AC d2)));
        obs_eq_AC_used: cused (ZMap.get i (AC d1)) = cused (ZMap.get i (AC d2));
        obs_eq_cid: i = cid d1 <-> i = cid d2;
        obs_eq_kctxt: ZMap.get i (kctxt d1) = ZMap.get i (kctxt d2);          
        obs_eq_uctxt: ZMap.get i (uctxt d1) = ZMap.get i (uctxt d2);
        obs_eq_ti: i = cid d1 -> fst (ti d1) = fst (ti d2);
        obs_eq_OUT: ZMap.get i (devout d1) = ZMap.get i (devout d2);
        obs_eq_ikern: i = cid d1 -> ikern d1 = ikern d2;
        obs_eq_ihost: i = cid d1 -> ihost d1 = ihost d2;
        obs_eq_pg: i = cid d1 -> pg d1 = pg d2;
        obs_eq_ipt: i = cid d1 -> ipt d1 = ipt d2;
        obs_eq_init: i = cid d1 -> init d1 = init d2
      }.

    (* Proof that the observable equivalence relation is 
       consistent with the observation function *)
    Lemma my_obs_eq_convert : 
      forall i d1 d2, my_obs_eq i d1 d2 <-> my_observe i d1 = my_observe i d2.
    Proof.
      intros i d1 d2; split; intro.
      - unfold my_observe.
        apply f_equal_my_obs.
        + extensionality vadr; apply obs_eq_HP; auto.
        + extensionality vadr; apply obs_eq_perm; auto.
        + apply obs_eq_AC_quota; auto.
        + apply obs_eq_AC_nchildren; auto.
        + apply obs_eq_AC_used; auto.
        + destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); simpl; auto.
          erewrite obs_eq_cid in e; eauto; contradiction.
          erewrite <- obs_eq_cid in e; eauto; contradiction.
        + apply obs_eq_kctxt; auto.
        + apply obs_eq_uctxt; auto.
        + destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); simpl; auto.
          f_equal; eapply obs_eq_ti; eauto.
          erewrite obs_eq_cid in e; eauto; contradiction.
          erewrite <- obs_eq_cid in e; eauto; contradiction.
        + apply obs_eq_OUT; auto.
        + destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); simpl; auto.
          f_equal; eapply obs_eq_ikern; eauto.
          erewrite obs_eq_cid in e; eauto; contradiction.
          erewrite <- obs_eq_cid in e; eauto; contradiction.
        + destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); simpl; auto.
          f_equal; eapply obs_eq_ihost; eauto.
          erewrite obs_eq_cid in e; eauto; contradiction.
          erewrite <- obs_eq_cid in e; eauto; contradiction.
        + destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); simpl; auto.
          f_equal; eapply obs_eq_pg; eauto.
          erewrite obs_eq_cid in e; eauto; contradiction.
          erewrite <- obs_eq_cid in e; eauto; contradiction.
        + destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); simpl; auto.
          f_equal; eapply obs_eq_ipt; eauto.
          erewrite obs_eq_cid in e; eauto; contradiction.
          erewrite <- obs_eq_cid in e; eauto; contradiction.
        + destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); simpl; auto.
          f_equal; eapply obs_eq_init; eauto.
          erewrite obs_eq_cid in e; eauto; contradiction.
          erewrite <- obs_eq_cid in e; eauto; contradiction.
      - inv H; constructor; auto; 
          try solve [destruct (zeq i (cid d1)); destruct (zeq i (cid d2)); inv H6; intuition].
        + apply equal_f; auto.
        + apply equal_f; auto.
    Qed.

  End OBS_EQ.

  Section WITHOBS.

    Variable id : Z.
    
    Hypothesis id_prop: id > high_id.

    Instance user_observer : Observer my_obs.
    Proof.
      apply (Build_Observer _ id id_prop (my_observe id)).
    Defined.

  End WITHOBS.

End WITHMEM.

  Lemma quota_convert :
    forall x y, (x <? y) = (0 <? y - x).
  Proof.
    intros.
    destruct (x <? y) eqn:H1; destruct (0 <? y - x) eqn:H2; auto.
    rewrite Z.ltb_lt in H1; rewrite Z.ltb_nlt in H2; omega.
    rewrite Z.ltb_nlt in H1; rewrite Z.ltb_lt in H2; omega.
  Qed.

  Lemma quota_convert' :
    forall x y, (cusage x <? cquota y) = (0 <? cquota y - cusage x).
  Proof.
    intros; apply quota_convert.
  Qed.

  Close Scope Z_scope.

  Ltac obs_eq_rewrite Hobs_eq :=
      try rewrite <- (obs_eq_HP _ _ _ Hobs_eq) in *;
      try rewrite quota_convert' in *;
      try rewrite <- (obs_eq_AC_quota _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_AC_nchildren _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_AC_used _ _ _ Hobs_eq) in *;
      try match goal with
            | [ H : id = cid ?d |- _ ] =>
              rewrite <- H in *;
              rewrite <- (proj1 (obs_eq_cid _ _ _ Hobs_eq)) in *; auto
          end;
      auto; try rewrite <- (obs_eq_kctxt _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_uctxt _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_OUT _ _ _ Hobs_eq) in *;
      try rewrite <- (obs_eq_ti _ _ _ Hobs_eq) in *; auto.

  Ltac obs_eq_rewrites Hobs_eq := repeat obs_eq_rewrite Hobs_eq.

  Ltac solve_obs_eq Hobs_eq := 
    destruct Hobs_eq; constructor; simpl; auto; zmap_solve; try congruence.