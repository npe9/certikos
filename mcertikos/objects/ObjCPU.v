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

Section CPU.

  (** primitve: trap into the kernel mode from user mode*)
  Function trapin_spec (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (false, true) => Some adt {ikern: true}
      | _ => None
    end.

  (** primitve: return to the user mode from kernel mode*)
  Function trapout'_spec (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => Some adt {ikern: false}
      | _ => None
    end.

  (** primitve: return to the user mode from kernel mode*)
  Function trapout0_spec (adt: RData): option RData :=
    match (ikern adt, init adt, pg adt, ihost adt) with
      | (true, true, true, true) => Some adt {ikern: false}
      | _ => None
    end.

  Function trapout_spec (adt: RData): option RData :=
    match (ikern adt, init adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true, false) => 
        Some adt {ikern: false}
      | _ => None
    end.

  (** primitve: return to the host/kernel mode from guest/kernel mode*)
  Function hostin_spec (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, false) => Some adt {ihost: true}
      | _ => None
    end.

  (** primitve: return to the guest/kernel mode from host/kernel mode*)
  Function hostout'_spec (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) => Some adt {ihost: false}
      | _ => None
    end.

  (** primitve: return to the guest/kernel mode from host/kernel mode*)
  Function hostout_spec (adt: RData): option RData :=
    match (ikern adt, init adt, pg adt, ihost adt) with
      | (true, true, true, true) => Some adt {ihost: false}
      | _ => None
    end.

  Definition trap_info_get_spec (adt: RData): int := fst (ti adt).
  Definition trap_info_ret_spec (adt: RData): val := snd (ti adt).

  Function trapinfo_set (adt: RData) (addr: int) (ra: val) : RData := adt {ti: (addr, ra)}.

  Function clearCR2_spec (adt: RData) : option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) => Some adt {ti: (Int.zero, snd (ti adt))}
      | _ => None
    end.

  (** primitve: set the pointer to the page table*)
  Function setCR3_spec (adt: RData) (cr3: globalpointer): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) => Some adt {CR3: cr3}
      | _ => None
    end.

  (** primitve: set the pointer to the page table*)
  Function setCR30_spec (adt: RData) (cr3: globalpointer): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) => 
        if CR3_valid_dec cr3 then Some adt {CR3: cr3}
        else None
      | _ => None
    end.

  (** primitve: enable the paging mechanism*)
  Function setPG_spec (adt: RData): option RData :=
    match (pg adt, ikern adt, ihost adt) with
      | (false, true, true) => Some adt {pg: true}
      | _ => None
    end.

  Function setPG0_spec (adt: RData) : option RData :=
    match (pg adt, ikern adt, init adt, ihost adt) with
      | (false, true, true, true) => 
        if CR3_valid_dec (CR3 adt) then Some adt {pg: true}
        else None
      | _ => None
    end.

  Function setPG1_spec (adt: RData) : option RData :=
    match (pg adt, ikern adt, init adt, ihost adt, ipt adt) with
      | (false, true, true, true, true) =>
        if zle_lt 0 (PT adt) num_proc then
          if PMap_valid_dec (ZMap.get (PT adt) (ptpool adt)) then
            if PMap_kern_dec (ZMap.get (PT adt) (ptpool adt)) then
              Some adt {pg: true}
            else None
          else None
        else None
      | _ => None
    end.

  Function vmxinfo_get_spec (i: Z) (adt: RData) :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        Some (ZMap.get i (vmxinfo adt))
      | _ => None
    end.

  Function device_output_spec (from to content: Z) (adt: RData) :=
    Some adt {devout: DeviceOutput_update (devout adt) from to (OUT content)}.

End CPU.

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

  Section DEVOUT_SIM.

    Context {re1: relate_impl_devout}.

    Lemma device_output_exist:
      forall from to content s habd habd' labd f,
        device_output_spec from to content habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', device_output_spec from to content labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold device_output_spec; intros.
      exploit relate_impl_devout_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_devout_update. assumption.
    Qed.

    Context {mt2: match_impl_devout}.

    Lemma device_output_match:
      forall from to content s d  d' m f,
        device_output_spec from to content d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold device_output_spec; intros. subdestruct.
      inv H. eapply match_impl_devout_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) device_output_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) device_output_spec}.

    Lemma device_output_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem device_output_spec)
            (id ↦ gensem device_output_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit (device_output_exist (Int.unsigned i) (Int.unsigned i0) (Int.unsigned i1)); eauto 1.
      reflexivity.
      intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply (device_output_match (Int.unsigned i) (Int.unsigned i0) (Int.unsigned i1)); eauto.
      reflexivity.
    Qed.

  End DEVOUT_SIM.

  Section CPU_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2': relate_impl_vmxinfo}.

    Section vmxinfo_get_SIM.

      Lemma vmxinfo_get_exist:
        forall s i habd  labd v f,
          vmxinfo_get_spec i habd = Some v
          -> relate_AbData s f habd labd
          -> vmxinfo_get_spec i labd = Some v.
      Proof.
        unfold vmxinfo_get_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_vmxinfo_eq; eauto. intros.
        revert H; subrewrite. 
      Qed.

      Lemma vmxinfo_get_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem vmxinfo_get_spec)
              (id ↦ gensem vmxinfo_get_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        match_external_states_simpl.
        erewrite vmxinfo_get_exist; eauto 1. trivial. 
      Qed.

    End vmxinfo_get_SIM.

    Context {mt1: match_impl_iflags}.

    Section SETPG_SIM.

      Lemma setPG_exist:
        forall s habd habd' labd f,
          setPG_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', setPG_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold setPG_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_pg_update. assumption.
      Qed.

      Lemma setPG_match:
        forall s d d' m f,
          setPG_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold setPG_spec; intros. subdestruct.
        inv H. eapply match_impl_pg_update. assumption.
      Qed.

      Context {inv: PreservesInvariants (HD:= data) setPG_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) setPG_spec}.

      Lemma setPG_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem setPG_spec)
              (id ↦ gensem setPG_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit setPG_exist; eauto 1. intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply setPG_match; eauto.
      Qed.

    End SETPG_SIM.

    Section SETPG0_SIM.

      Context {re2: relate_impl_init}.
      Context {re3: relate_impl_CR3}.

      Lemma setPG0_exist:
        forall s habd habd' labd f,
          setPG0_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', setPG0_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold setPG0_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_init_eq; eauto.
        exploit relate_impl_CR3_eq; eauto. intros.
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_pg_update. assumption.
      Qed.

      Lemma setPG0_match:
        forall s d d' m f,
          setPG0_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold setPG0_spec; intros. subdestruct.
        inv H. eapply match_impl_pg_update. assumption.
      Qed.

      Context {inv: PreservesInvariants (HD:= data) setPG0_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) setPG0_spec}.

      Lemma setPG0_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem setPG0_spec)
              (id ↦ gensem setPG0_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit setPG0_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply setPG0_match; eauto.
      Qed.

    End SETPG0_SIM.

    Section SETPG1_SIM.

      Context {re2: relate_impl_init}.
      Context {re3: relate_impl_PT}.
      Context {re4: relate_impl_ipt}.
      Context {re5: relate_impl_ptpool}.

      Lemma setPG1_exist:
        forall s habd habd' labd f,
          setPG1_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', setPG1_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold setPG1_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_init_eq; eauto.
        exploit relate_impl_ipt_eq; eauto.
        exploit relate_impl_ptpool_eq; eauto.
        exploit relate_impl_PT_eq; eauto. intros.
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_pg_update. assumption.
      Qed.

      Lemma setPG1_match:
        forall s d d' m f,
          setPG1_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold setPG1_spec; intros. subdestruct.
        inv H. eapply match_impl_pg_update. assumption.
      Qed.

      Context {inv: PreservesInvariants (HD:= data) setPG1_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) setPG1_spec}.

      Lemma setPG1_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem setPG1_spec)
              (id ↦ gensem setPG1_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit setPG1_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply setPG1_match; eauto.
      Qed.

    End SETPG1_SIM.

    Section CLEARCR2_SIM.

      Context {re2: relate_impl_trapinfo}.
      Context {mt2: match_impl_trapinfo}.

      Lemma clearCR2_exist:
        forall s habd habd' labd f,
          clearCR2_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', clearCR2_spec labd = Some labd' 
                           /\ relate_AbData s f habd' labd'.
      Proof.
        unfold clearCR2_spec; intros.        
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_trapinfo_eq; eauto; intro Hti; inv Hti.
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        inv H1; eapply relate_impl_trapinfo_update; assumption.
      Qed.

      Lemma clearCR2_match:
        forall s d d' m f,
          clearCR2_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold clearCR2_spec; intros. subdestruct.
        inv H. eapply match_impl_trapinfo_update. assumption.
      Qed.

      Context {inv: PreservesInvariants (HD:= data) clearCR2_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) clearCR2_spec}.

      Lemma clearCR2_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem clearCR2_spec)
              (id ↦ gensem clearCR2_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
        exploit clearCR2_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply clearCR2_match; eauto.
      Qed.

    End CLEARCR2_SIM.

    Section SETCR3_SIM.

      Context {re2: relate_impl_CR3}.
      Context {mt2: match_impl_CR3}.

      Lemma setCR3_exist:
        forall s habd habd' labd id ofs f,
          setCR3_spec habd (GLOBP id ofs) = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', setCR3_spec labd (GLOBP id ofs) = Some labd' 
                           /\ relate_AbData s f habd' labd'.
      Proof.
        unfold setCR3_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_CR3_update. assumption.
      Qed.    

      Lemma setCR3_match:
        forall s d d' m id ofs f,
          setCR3_spec d (GLOBP id ofs) = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold setCR3_spec; intros. subdestruct.
        inv H. eapply match_impl_CR3_update. assumption.
      Qed.

      Context {inv: SetCR3Invariants (data_ops:= data_ops) setCR3_spec}.
      Context {inv0: SetCR3Invariants (data_ops:= data_ops0) setCR3_spec}.

      Lemma setCR3_sim :
        forall id,
          sim (crel RData RData) (id ↦ setCR3_compatsem setCR3_spec)
              (id ↦ setCR3_compatsem setCR3_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv_val_inject.
        eapply inject_forward_equal' in H2; eauto 1. inv H2.
        exploit setCR3_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        rewrite Int.add_zero. eauto.
        eapply setCR3_match; eauto.
      Qed.

    End SETCR3_SIM.

    Section SETCR30_SIM.

      Context {re2: relate_impl_CR3}.
      Context {mt2: match_impl_CR3}.

      Lemma setCR30_exist:
        forall s habd habd' labd id ofs f,
          setCR30_spec habd (GLOBP id ofs) = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', setCR30_spec labd (GLOBP id ofs) = Some labd' 
                           /\ relate_AbData s f habd' labd'.
      Proof.
        unfold setCR30_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_CR3_eq; eauto. intros.
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_CR3_update. assumption.
      Qed.    

      Lemma setCR30_match:
        forall s d d' m id ofs f,
          setCR30_spec d (GLOBP id ofs) = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold setCR30_spec; intros. subdestruct.
        inv H. eapply match_impl_CR3_update. assumption.
      Qed.

      Context {inv: SetCR3Invariants (data_ops:= data_ops) setCR30_spec}.
      Context {inv0: SetCR3Invariants (data_ops:= data_ops0) setCR30_spec}.

      Lemma setCR30_sim :
        forall id,
          sim (crel RData RData) (id ↦ setCR3_compatsem setCR30_spec)
              (id ↦ setCR3_compatsem setCR30_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv_val_inject.
        eapply inject_forward_equal' in H2; eauto 1. inv H2.
        exploit setCR30_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        rewrite Int.add_zero. eauto.
        eapply setCR30_match; eauto.
      Qed.

    End SETCR30_SIM.

    Section TRAPIN_SIM.

      Lemma trapin_exist:
        forall s habd habd' labd f,
          trapin_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', trapin_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold trapin_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_ikern_update. assumption.
      Qed.

      Lemma trapin_match:
        forall s d d' m f,
          trapin_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold trapin_spec; intros. subdestruct.
        inv H. eapply match_impl_ikern_update. assumption.
      Qed.

      Context `{inv: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops) trapin_spec}.
      Context `{inv0: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops0) trapin_spec}.

      Lemma trapin_sim :
        forall id,
          sim (crel RData RData) (id ↦ primcall_general_compatsem trapin_spec)
              (id ↦ primcall_general_compatsem trapin_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv H4. inv match_extcall_states.

        exploit trapin_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply trapin_match; eauto.
      Qed.

    End TRAPIN_SIM.

    Section TRAPOUT'_SIM.

      Lemma trapout'_exist:
        forall s habd habd' labd f,
          trapout'_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', trapout'_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold trapout'_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        revert H. subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_ikern_update. assumption.
      Qed.

      Lemma trapout'_match:
        forall s d d' m f,
          trapout'_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold trapout'_spec; intros. subdestruct.
        inv H. eapply match_impl_ikern_update. assumption.
      Qed.

      Context `{inv: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops) trapout'_spec}.
      Context `{inv0: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops0) trapout'_spec}.

      Lemma trapout'_sim :
        forall id,
          sim (crel RData RData) (id ↦ primcall_general_compatsem trapout'_spec)
              (id ↦ primcall_general_compatsem trapout'_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv H4. inv match_extcall_states.
        exploit trapout'_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply trapout'_match; eauto.
      Qed.

    End TRAPOUT'_SIM.

    Section TRAPOUT0_SIM.

      Context {re2: relate_impl_init}.

      Lemma trapout0_exist:
        forall s habd habd' labd f,
          trapout0_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', trapout0_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold trapout0_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_init_eq; eauto. intros. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_ikern_update. assumption.
      Qed.

      Lemma trapout0_match:
        forall s d d' m f,
          trapout0_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold trapout0_spec; intros. subdestruct.
        inv H. eapply match_impl_ikern_update. assumption.
      Qed.

      Context `{inv: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops) trapout0_spec}.
      Context `{inv0: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops0) trapout0_spec}.

      Lemma trapout0_sim :
        forall id,
          sim (crel RData RData) (id ↦ primcall_general_compatsem trapout0_spec)
              (id ↦ primcall_general_compatsem trapout0_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv H4. inv match_extcall_states.
        exploit trapout0_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply trapout0_match; eauto.
      Qed.

    End TRAPOUT0_SIM.

    Section TRAPOUT_SIM.

      Context {re2: relate_impl_init}.
      Context {re3: relate_impl_ipt}.

      Lemma trapout_exist:
        forall s habd habd' labd f,
          trapout_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', trapout_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold trapout_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_init_eq; eauto.
        exploit relate_impl_ipt_eq; eauto. intros. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_ikern_update. assumption.
      Qed.

      Lemma trapout_match:
        forall s d d' m f,
          trapout_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold trapout_spec; intros. subdestruct.
        inv H. eapply match_impl_ikern_update. assumption.
      Qed.

      Context `{inv: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops) trapout_spec}.
      Context `{inv1: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops0) trapout_spec}.

      Lemma trapout_sim :
        forall id,
          sim (crel RData RData) (id ↦ primcall_general_compatsem trapout_spec)
              (id ↦ primcall_general_compatsem trapout_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv H4. inv match_extcall_states.
        exploit trapout_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply trapout_match; eauto.
      Qed.

    End TRAPOUT_SIM.

    Section HOSTIN_SIM.

      Lemma hostin_exist:
        forall s habd habd' labd f,
          hostin_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', hostin_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold hostin_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_ihost_update. assumption.
      Qed.

      Lemma hostin_match:
        forall s d d' m f,
          hostin_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold hostin_spec; intros. subdestruct.
        inv H. eapply match_impl_ihost_update. assumption.
      Qed.

      Context `{inv: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops) hostin_spec}.
      Context `{inv0: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops0) hostin_spec}.

      Lemma hostin_sim :
        forall id,
          sim (crel RData RData) (id ↦ primcall_general_compatsem hostin_spec)
              (id ↦ primcall_general_compatsem hostin_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv H4. inv match_extcall_states.
        exploit hostin_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply hostin_match; eauto.
      Qed.

    End HOSTIN_SIM.

    Section HOSTOUT'_SIM.

      Lemma hostout'_exist:
        forall s habd habd' labd f,
          hostout'_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', hostout'_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold hostout'_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_ihost_update. assumption.
      Qed.

      Lemma hostout'_match:
        forall s d d' m f,
          hostout'_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold hostout'_spec; intros. subdestruct.
        inv H. eapply match_impl_ihost_update. assumption.
      Qed.

      Context `{inv: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops) hostout'_spec}.
      Context `{inv0: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops0) hostout'_spec}.

      Lemma hostout'_sim :
        forall id,
          sim (crel RData RData) (id ↦ primcall_general_compatsem hostout'_spec)
              (id ↦ primcall_general_compatsem hostout'_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv H4. inv match_extcall_states.
        exploit hostout'_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply hostout'_match; eauto.
      Qed.

    End HOSTOUT'_SIM.

    Section HOSTOUT_SIM.

      Context {re2: relate_impl_init}.

      Lemma hostout_exist:
        forall s habd habd' labd f,
          hostout_spec habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', hostout_spec labd = Some labd' /\ 
                           relate_AbData s f habd' labd'.
      Proof.
        unfold hostout_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_init_eq; eauto. intros. 
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_ihost_update. assumption.
      Qed.

      Lemma hostout_match:
        forall s d d' m f,
          hostout_spec d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold hostout_spec; intros. subdestruct.
        inv H. eapply match_impl_ihost_update. assumption.
      Qed.

      Context `{inv: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops) hostout_spec}.
      Context `{inv0: PrimInvariants (Obs:=Obs) RData (data_ops:= data_ops0) hostout_spec}.

      Lemma hostout_sim :
        forall id,
          sim (crel RData RData) (id ↦ primcall_general_compatsem hostout_spec)
              (id ↦ primcall_general_compatsem hostout_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        inv H4. inv match_extcall_states.
        exploit hostout_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply hostout_match; eauto.
      Qed.

    End HOSTOUT_SIM.

  End CPU_SIM.

  Section TRAP_INFO_SIM.

    Context {re1: relate_impl_trapinfo}.

    Lemma trap_info_get_exist:
      forall habd labd s z f,
        trap_info_get_spec habd = z
        -> relate_AbData s f habd labd
        -> trap_info_get_spec labd = z.
    Proof.
      unfold trap_info_get_spec; unfold trap_info_get_spec.
      intros. exploit relate_impl_trapinfo_eq; eauto.
      inversion 1. congruence.
    Qed.

    Lemma trap_info_ret_exist:
      forall habd labd s f,
        relate_AbData s f habd labd
        -> val_inject f (trap_info_ret_spec habd) (trap_info_ret_spec labd).
    Proof.
      intros. exploit relate_impl_trapinfo_eq; eauto.
      inversion 1. assumption.
    Qed.

    Lemma trap_info_get_sim :
      forall id,
        sim (crel RData RData)
            (id ↦ primcall_trap_info_get_compatsem trap_info_get_spec)
            (id ↦ primcall_trap_info_get_compatsem trap_info_get_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      inv match_extcall_states.
      match_external_states_simpl.
      erewrite (trap_info_get_exist d1' d2); eauto.
    Qed.

    Context {low1: low_level_invariant_impl}.

    Lemma trap_info_ret_sim :
      forall id,
      sim (crel RData RData)
          (id ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec)
          (id ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      inv match_extcall_states.
      exploit low_level_invariant_impl_eq; eauto. inversion 1.
      match_external_states_simpl.
      eapply trap_info_ret_exist; eauto.
    Qed.      

  End TRAP_INFO_SIM.

End OBJ_SIM.
