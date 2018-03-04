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
(* *********************************************************************)
(*                                                                     *)
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*          Jérémie Koenig <jk@jk.fr.eu.org>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide to the extension to the [Compcert] memory model*)
Require Import Coqlib.
(*Require Import Maps.*)
(*Require Import Values.*)
Require Export MemWithData.

Module MemEx.

  Section INJECT.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

    (** ** [free] operation will not violate the memory injection with different abstract data*)
    Theorem free_parallel_inject:
      forall f m1 m2 b b' lo hi m1' delta,
        Mem.inject f m1 m2 ->
        f b = Some (b', delta) ->
        Mem.free m1 b lo hi = Some m1' ->
        exists m2',
          Mem.free m2 b' (lo + delta) (hi + delta)  = Some m2'
          /\ Mem.inject f m1' m2'.
    Proof.
      intros until delta.
      intros MEM_INJ BLOCK_INJ FREE_SRC.
      generalize (Mem.free_range_perm _ _ _ _ _ FREE_SRC). intro PERM_SRC.
      generalize (Mem.range_perm_inject _ _ _ _ _ _ _ _ _ _ BLOCK_INJ MEM_INJ PERM_SRC). intro PERM_TGT.
      destruct (Mem.range_perm_free _ _ _ _ PERM_TGT) as [? FREE_TGT].      
      rewrite FREE_TGT.
      esplit. split.
       reflexivity.
       eapply Mem.free_right_inject.
       eapply Mem.free_left_inject.
       eassumption.
       eassumption.
       eassumption.
       intros b1 delta1 ofs1 k1 p1 BLOCK_INJ1 PERM1 RANGE1.
       destruct (peq b1 b).
        subst.
        replace delta1 with delta in * by congruence.
        eapply (Mem.perm_free_2 (mem := mem)). eexact FREE_SRC. 2: eassumption. omega.
       eapply Mem.perm_free_3 in PERM1; eauto.
       exploit Mem.inject_no_overlap.
        eexact MEM_INJ.
        eassumption.
        eassumption.
        eassumption.
        eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
        eapply Mem.perm_max. eapply Mem.perm_implies. eapply PERM_SRC. instantiate (1 := ofs1 + delta1 - delta). 
        omega. constructor.
        intros; elim H; intros; apply H0; trivial.
        xomega.
    Qed.

  End INJECT.
  
End MemEx.
