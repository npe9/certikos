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
(*              Object Primitives                                      *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import FlatMemory.
Require Import AbstractDataType.
Require Import Integers.
Require Import Values.
Require Import Constant.
Require Import RealParams.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import CalRealSMSPool.
Require Import CalRealProcModule.
(*Require Import CalRealIntelModule.*)
Require Import liblayers.compat.CompatGenSem.
(*
Require Import ObjLMM.
Require Import ObjVMM.*)

Section OBJ_Arg.

  Function uctx_arg1_spec (adt : RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match (ZMap.get U_EAX (ZMap.get (cid adt) (uctxt adt))) with
          | Vint n => Some (Int.unsigned n)
          | _ => None
        end
      | _ => None
    end.

  Function uctx_arg2_spec (adt : RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match (ZMap.get U_EBX (ZMap.get (cid adt) (uctxt adt))) with
          | Vint n => Some (Int.unsigned n)
          | _ => None
        end
      | _ => None
    end.

  Function uctx_arg3_spec (adt : RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match (ZMap.get U_ECX (ZMap.get (cid adt) (uctxt adt))) with
          | Vint n => Some (Int.unsigned n)
          | _ => None
        end
      | _ => None
    end.

  Function uctx_arg4_spec (adt : RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match (ZMap.get U_EDX (ZMap.get (cid adt) (uctxt adt))) with
          | Vint n => Some (Int.unsigned n)
          | _ => None
        end
      | _ => None
    end.

  Function uctx_arg5_spec (adt : RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match (ZMap.get U_ESI (ZMap.get (cid adt) (uctxt adt))) with
          | Vint n => Some (Int.unsigned n)
          | _ => None
        end
      | _ => None
    end.

  Function uctx_arg6_spec (adt : RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match (ZMap.get U_EDI (ZMap.get (cid adt) (uctxt adt))) with
          | Vint n => Some (Int.unsigned n)
          | _ => None
        end
      | _ => None
    end.

  Function uctx_set_errno_spec (n: Z) (adt : RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        let uctx := ZMap.get (cid adt) (uctxt adt) in
        let uctx':= ZMap.set U_EAX (Vint (Int.repr n)) uctx in
        Some (adt {uctxt: ZMap.set (cid adt) uctx' (uctxt adt)})
      | _ => None
    end.

  Function uctx_set_retval1_spec (n: Z) (adt : RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        let uctx := ZMap.get (cid adt) (uctxt adt) in
        let uctx':= ZMap.set U_EBX (Vint (Int.repr n)) uctx in
        Some (adt {uctxt: ZMap.set (cid adt) uctx' (uctxt adt)})
      | _ => None
    end.

  Function uctx_set_retval2_spec (n: Z) (adt : RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        let uctx := ZMap.get (cid adt) (uctxt adt) in
        let uctx':= ZMap.set U_ECX (Vint (Int.repr n)) uctx in
        Some (adt {uctxt: ZMap.set (cid adt) uctx' (uctxt adt)})
      | _ => None
    end.

  Function uctx_set_retval3_spec (n: Z) (adt : RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        let uctx := ZMap.get (cid adt) (uctxt adt) in
        let uctx':= ZMap.set U_EDX (Vint (Int.repr n)) uctx in
        Some (adt {uctxt: ZMap.set (cid adt) uctx' (uctxt adt)})
      | _ => None
    end.

  Function uctx_set_retval4_spec (n: Z) (adt : RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        let uctx := ZMap.get (cid adt) (uctxt adt) in
        let uctx':= ZMap.set U_ESI (Vint (Int.repr n)) uctx in
        Some (adt {uctxt: ZMap.set (cid adt) uctx' (uctxt adt)})
      | _ => None
    end.

  Function uctx_set_retval5_spec (n: Z) (adt : RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        let uctx := ZMap.get (cid adt) (uctxt adt) in
        let uctx':= ZMap.set U_EDI (Vint (Int.repr n)) uctx in
        Some (adt {uctxt: ZMap.set (cid adt) uctx' (uctxt adt)})
      | _ => None
    end.

  (*Function la2pa_resv_spec (vadr : Z) (adt: RData) : option (RData * Z):=
    match (pg adt, ptRead_spec (cid adt) vadr adt) with
      | (true, Some padr) =>
        if zeq padr 0 then
          match ptResv_spec (cid adt) vadr PT_PERM_PTU adt with
            | Some (adt', _) =>
              match ptRead_spec (cid adt) vadr adt' with
                | Some padr' => 
                  if zlt_lt 0 padr' maxpage then
                    Some (adt', padr' * PgSize + (vadr mod PgSize))
                  else None
                | _ => None
              end
            | _ => None
          end
        else
          if zlt_lt 0 padr maxpage then
            Some (adt, padr * PgSize + (vadr mod PgSize))
          else None
      | _ => None
    end.*)

End OBJ_Arg.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import AuxLemma.
Require Import Observation.

Section OBJ_SIM.

  Context `{Hobs: Observation}.

  Context `{data : CompatData(Obs:=Obs) RData}.
  Context `{data0 : CompatData(Obs:=Obs) RData}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_prf := data) RData).
  Notation LDATAOps := (cdata (cdata_prf := data0) RData).

  Context `{rel_prf: CompatRel _ (Obs:=Obs) (memory_model_ops:= memory_model_ops) _
                               (stencil_ops:= stencil_ops) HDATAOps LDATAOps}.

  Local Open Scope Z.

  Context {re1: relate_impl_iflags}.
  Context {re2: relate_impl_cid}.
  Context {re3: relate_impl_uctxt}.

  Definition uctx_argn_spec n (adt : RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        match (ZMap.get n (ZMap.get (cid adt) (uctxt adt))) with
          | Vint n => Some (Int.unsigned n)
          | _ => None
        end
      | _ => None
    end.

  Lemma uctx_argn_exist:
    forall n, 0 <= n < UCTXT_SIZE ->
    forall s habd z labd f,
      uctx_argn_spec n habd = Some z ->
      0 <= cid habd < num_proc ->
      relate_AbData s f habd labd ->
      uctx_argn_spec n labd = Some z.
  Proof.
    unfold uctx_argn_spec in *. intros.
    exploit relate_impl_iflags_eq; eauto. inversion 1.
    exploit relate_impl_cid_eq; eauto. intros.
    exploit relate_impl_uctxt_eq; eauto.
    revert H0; subrewrite. inversion 1; subdestruct.
    inv HQ. inv H6. reflexivity.
  Qed.

  Lemma uctx_argn_sim:
    forall n, 0 <= n < UCTXT_SIZE ->
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem (uctx_argn_spec n))
          (id ↦ gensem (uctx_argn_spec n)).
  Proof.
    intros ? valid_n ? valid_cid.
    layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    erewrite uctx_argn_exist; eauto.
    reflexivity.
  Qed.

  Lemma uctx_arg1_sim:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_arg1_spec)
          (id ↦ gensem uctx_arg1_spec).
  Proof.
    apply uctx_argn_sim.
    split; [ discriminate | reflexivity ].
  Qed.

  Lemma uctx_arg2_sim:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_arg2_spec)
          (id ↦ gensem uctx_arg2_spec).
  Proof.
    apply uctx_argn_sim.
    split; [ discriminate | reflexivity ].
  Qed.

  Lemma uctx_arg3_sim:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_arg3_spec)
          (id ↦ gensem uctx_arg3_spec).
  Proof.
    apply uctx_argn_sim.
    split; [ discriminate | reflexivity ].
  Qed.

  Lemma uctx_arg4_sim:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_arg4_spec)
          (id ↦ gensem uctx_arg4_spec).
  Proof.
    apply uctx_argn_sim.
    split; [ discriminate | reflexivity ].
  Qed.

  Lemma uctx_arg5_sim:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_arg5_spec)
          (id ↦ gensem uctx_arg5_spec).
  Proof.
    apply uctx_argn_sim.
    split; [ discriminate | reflexivity ].
  Qed.

  Lemma uctx_arg6_sim:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_arg6_spec)
          (id ↦ gensem uctx_arg6_spec).
  Proof.
    apply uctx_argn_sim.
    split; [ discriminate | reflexivity ].
  Qed.

  Section UCTX_SET_REGK_SIM.
    Variable k : Z.
    (* Hypothesis k_range : 0 <= k < UCTXT_SIZE. *)

    Definition uctx_set_regk_spec (n: Z) (adt : RData) : option RData :=
      match (ikern adt, pg adt, ihost adt) with
        | (true, true, true) =>
          let uctx := ZMap.get (cid adt) (uctxt adt) in
          let uctx':= ZMap.set k (Vint (Int.repr n)) uctx in
          Some (adt {uctxt: ZMap.set (cid adt) uctx' (uctxt adt)})
        | _ => None
      end.

    Lemma uctx_set_regk_exist:
      forall s habd habd' labd n f,
        uctx_set_regk_spec n habd = Some habd'
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd', uctx_set_regk_spec n labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold uctx_set_regk_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_cid_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_uctxt_update; try assumption.
      unfold uctxt_inj; intros.
      destruct (zeq i (cid labd)) as [ -> | ? ];
        [ rewrite 2 ZMap.gss
        | rewrite 2 ZMap.gso; try eapply relate_impl_uctxt_eq; eassumption ].
      destruct (zeq j k) as [ -> | ? ];
        [ rewrite 2 ZMap.gss; constructor
        | rewrite 2 ZMap.gso; try eapply relate_impl_uctxt_eq; eassumption ].
    Qed.

    Context {mt1: match_impl_uctxt}.

    Lemma uctx_set_regk_match:
      forall s d d' m n f,
        uctx_set_regk_spec n d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold uctx_set_regk_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_uctxt_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) uctx_set_regk_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) uctx_set_regk_spec}.

    Lemma uctx_set_regk_sim:
      forall id,
        (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                    0 <= cid d1 < num_proc) ->
        sim (crel RData RData) (id ↦ gensem uctx_set_regk_spec)
            (id ↦ gensem uctx_set_regk_spec).
    Proof.
      intros ? valid_cid. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit uctx_set_regk_exist; eauto; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply uctx_set_regk_match; eauto.
    Qed.

  End UCTX_SET_REGK_SIM.

  Lemma uctx_set_errno_sim
      {mt1: match_impl_uctxt}
      {inv: PreservesInvariants (HD:= data) uctx_set_errno_spec}
      {inv0: PreservesInvariants (HD:= data0) uctx_set_errno_spec}:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_set_errno_spec)
          (id ↦ gensem uctx_set_errno_spec).
  Proof uctx_set_regk_sim U_EAX.

  Lemma uctx_set_retval1_sim
      {mt1: match_impl_uctxt}
      {inv: PreservesInvariants (HD:= data) uctx_set_retval1_spec}
      {inv0: PreservesInvariants (HD:= data0) uctx_set_retval1_spec}:
    forall id,
      (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 ->
                  0 <= cid d1 < num_proc) ->
      sim (crel RData RData) (id ↦ gensem uctx_set_retval1_spec)
          (id ↦ gensem uctx_set_retval1_spec).
  Proof uctx_set_regk_sim U_EBX.

End OBJ_SIM.
