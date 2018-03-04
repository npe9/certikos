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
Require Import ObjVMMDef.

Section OBJ_VMM.

  (** primitve: in the kernel mode, after switching to kernel's page table, set ipt to true*)
  Function ptin'_spec (adt: RData): option RData :=
    match (ipt adt, ikern adt, ihost adt) with
      | (false, true, true) => 
        if PMap_kern_dec (ZMap.get (PT adt) (ptpool adt))
        then Some adt {ipt: true}
        else None
      | _ => None
    end.
  
  (** primitve: in the kernel mode, after switching to user's page table, set ipt to false*)
  Function ptout_spec (adt: RData): option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true, true) => Some adt {ipt: false}
      | _ => None
    end.
  
  (** primitve: set the page table index to n*)
  Function setPT'_spec (n: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 n num_proc then
          if PMap_valid_dec (ZMap.get n (ptpool adt)) then 
            match ipt adt with
              | true =>
                if PMap_kern_dec (ZMap.get n (ptpool adt)) then
                  Some adt {PT: n}
                else None
              | _ => Some adt {PT: n}
            end
          else None
        else None
      | _ => None
    end.

  Function getPDE_spec (n i: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt, init adt, ipt adt, PDE_Arg n i) with
      | (true, true, true, true, true) =>
        let pt:= ZMap.get n (ptpool adt) in
        match ZMap.get i pt with
          | PDEValid pi pdt => Some pi
          | PDEUnPresent => Some 0
          | _ => None
        end
      | _ => None
    end.
  
  Function setPDE_spec (n i: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, init adt, ipt adt, PDE_Arg n i) with
      | (true, false, true, true, true, true) =>
        let pt':= ZMap.set i PDEID (ZMap.get n (ptpool adt)) in
        Some adt {ptpool: (ZMap.set n pt' (ptpool adt))}
      |_ => None
    end.

  Function ptReadPDE_spec (n vadr :Z) (adt: RData) : option Z :=
    let pdi := PDX vadr in
    getPDE_spec n pdi adt.

  Function rmvPTE_spec (n i vadr: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, init adt, ipt adt, PTE_Arg n i vadr) with
      | (true, true, true, true, true) => 
        if zeq n (PT adt) then None
        else
          let pt:= ZMap.get n (ptpool adt) in
          match ZMap.get i pt with
            | PDEValid pi pdt =>
              let pdt':= ZMap.set vadr PTEUnPresent pdt in
              let pt' := ZMap.set i (PDEValid pi pdt') pt in
              Some adt {ptpool: ZMap.set n pt' (ptpool adt)}
            | _ => None
          end
      | _ => None
    end.

  (** primitve: set the n-th page table with virtual address vadr to unpresent: only used in the refinement proof*)    
  Function ptRmvAux_spec (n vadr: Z) (adt: RData): option RData :=
    let pdi:= PDX vadr in
    let pti := PTX vadr in
    rmvPTE_spec n pdi pti adt.

  Definition IDPTE_Arg (i vadr: Z) : bool :=
    if zle_le 0 i (PDX Int.max_unsigned) then
      if zle_le 0 vadr (PTX Int.max_unsigned) then
        true
      else false
    else false.      

  Function setIDPTE_spec (i vadr perm: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, init adt, ipt adt, IDPTE_Arg i vadr) with
      | (true, false, true, true, true, true) =>
        match ZtoPerm perm with
          | Some p =>
            let pde:= (ZMap.get i (idpde adt)) in
            let pde':= ZMap.set vadr (IDPTEValid p) pde in
            Some adt {idpde: ZMap.set i pde' (idpde adt)}
          | _ => None
        end
      | _ => None
    end.

End OBJ_VMM.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
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

  Section SETPT_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.

    Lemma setPT'_exist:
      forall s habd habd' labd i f,
        setPT'_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', setPT'_spec i labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold setPT'_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. 
      subdestruct; inv HQ; refine_split'; trivial.
      eapply relate_impl_PT_update; assumption.
      eapply relate_impl_PT_update; assumption.
    Qed.

    Context {mt1: match_impl_PT}.

    Lemma setPT'_match:
      forall s d d' m i f,
        setPT'_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold setPT'_spec; intros. subdestruct; trivial.
      inv H. eapply match_impl_PT_update. assumption.
      inv H. eapply match_impl_PT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) setPT'_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) setPT'_spec}.

    Lemma setPT'_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem setPT'_spec)
            (id ↦ gensem setPT'_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit setPT'_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply setPT'_match; eauto.
    Qed.

  End SETPT_SIM.

  Section SETPDE_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.

    Lemma setPDE_exist:
      forall s habd habd' labd n i f,
        setPDE_spec n i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', setPDE_spec n i labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold setPDE_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. 
      subdestruct; inv HQ; refine_split'; trivial.
      eapply relate_impl_ptpool_update; assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.

    Lemma setPDE_match:
      forall s d d' m n i f,
        setPDE_spec n i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold setPDE_spec; intros. subdestruct; trivial.
      inv H. eapply match_impl_ptpool_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) setPDE_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) setPDE_spec}.

    Lemma setPDE_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem setPDE_spec)
            (id ↦ gensem setPDE_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit setPDE_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply setPDE_match; eauto.
    Qed.

  End SETPDE_SIM.

  Section PTIN'_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.

    Lemma ptin'_exist:
      forall s habd habd' labd f,
        ptin'_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptin'_spec labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold ptin'_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_PT_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_ipt_update. assumption.
    Qed.

    Context {mt1: match_impl_ipt}.

    Lemma ptin'_match:
      forall s d d' m f,
        ptin'_spec d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptin'_spec; intros. subdestruct.
      inv H. eapply match_impl_ipt_update. assumption.
    Qed.

    Context {inv: PrimInvariants (data_ops:= data_ops) ptin'_spec}.
    Context {inv0: PrimInvariants (data_ops:= data_ops0) ptin'_spec}.

    Lemma ptin'_sim :
      forall id id',
        sim (crel RData RData) (id ↦ primcall_general_compatsem' ptin'_spec (prim_ident:= id'))
            (id ↦ primcall_general_compatsem' ptin'_spec (prim_ident:= id')).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      inv match_extcall_states.
      exploit ptin'_exist; eauto 1. intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ptin'_match; eauto.
    Qed.

  End PTIN'_SIM.

  Section PTOUT_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_ipt}.

    Lemma ptout_exist:
      forall s habd habd' labd f,
        ptout_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptout_spec labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold ptout_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_ipt_update. assumption.
    Qed.

    Context {mt1: match_impl_ipt}.

    Lemma ptout_match:
      forall s d d' m f,
        ptout_spec d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptout_spec; intros. subdestruct.
      inv H. eapply match_impl_ipt_update. assumption.
    Qed.

    Context {inv: PrimInvariants (data_ops:= data_ops) ptout_spec}.
    Context {inv0: PrimInvariants (data_ops:= data_ops0) ptout_spec}.

    Lemma ptout_sim :
      forall id id',
        sim (crel RData RData) (id ↦ primcall_general_compatsem' ptout_spec (prim_ident:= id'))
            (id ↦ primcall_general_compatsem' ptout_spec (prim_ident:= id')).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      inv match_extcall_states.
      exploit ptout_exist; eauto 1. intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ptout_match; eauto.
    Qed.

  End PTOUT_SIM.


  Section PT_READ_PDE_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.

    Lemma ptReadPDE_exist:
      forall s habd labd n vadr z f,
        ptReadPDE_spec n vadr habd = Some z
        -> relate_AbData s f habd labd
        -> ptReadPDE_spec n vadr labd = Some z.
    Proof.
      unfold ptReadPDE_spec, getPDE_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. 
    Qed.

    Lemma ptReadPDE_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptReadPDE_spec)
            (id ↦ gensem ptReadPDE_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'.
      match_external_states_simpl.
      erewrite ptReadPDE_exist; eauto. reflexivity.
    Qed.

  End PT_READ_PDE_SIM.


  Section RMVPTE_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.

    Lemma rmvPTE_exist:
      forall s habd habd' labd n i v f,
        rmvPTE_spec n i v habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', rmvPTE_spec n i v labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold rmvPTE_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. 
      subdestruct; inv HQ; refine_split'; trivial.
      eapply relate_impl_ptpool_update; assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.

    Lemma rmvPTE_match:
      forall s d d' m n i v f,
        rmvPTE_spec n i v d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold rmvPTE_spec; intros. subdestruct; trivial.
      inv H. eapply match_impl_ptpool_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) rmvPTE_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) rmvPTE_spec}.

    Lemma rmvPTE_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem rmvPTE_spec)
            (id ↦ gensem rmvPTE_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit rmvPTE_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply rmvPTE_match; eauto.
    Qed.

  End RMVPTE_SIM.

  Section RMVPDE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.
    Context {re6: relate_impl_pperm}.

    Lemma rmvPDE_exist:
      forall s habd habd' labd n i f,
        rmvPDE_spec n i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', rmvPDE_spec n i labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold rmvPDE_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_pperm_eq; eauto.
      intros.
      revert H; subrewrite.
      subdestruct; inv HQ; refine_split'; trivial;
      eapply relate_impl_ptpool_update; try assumption;
      eapply relate_impl_pperm_update; try assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_pperm}.

    Lemma rmvPDE_match:
      forall s d d' m n i f,
        rmvPDE_spec n i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold rmvPDE_spec; intros. subdestruct;
      inv H;
      try eapply match_impl_ptpool_update;
      try eapply match_impl_pperm_update;
      assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) rmvPDE_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) rmvPDE_spec}.

    Lemma rmvPDE_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem rmvPDE_spec)
            (id ↦ gensem rmvPDE_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit rmvPDE_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply rmvPDE_match; eauto.
    Qed.

  End RMVPDE_SIM.

  Section PT_RMV_AUX_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.
        
    Lemma ptRmvAux_exist:
      forall s habd habd' labd n vadr f,
        ptRmvAux_spec n vadr habd  = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptRmvAux_spec n vadr labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      intros. eapply rmvPTE_exist; eauto.
    Qed.

    Context {mt1: match_impl_ptpool}.

    Lemma ptRmvAux_match:
      forall s d d' n vadr m f,
        ptRmvAux_spec n vadr d  = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      intros. eapply rmvPTE_match; eauto.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ptRmvAux_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptRmvAux_spec}.

    Lemma ptRmvAux_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptRmvAux_spec)
            (id ↦ gensem ptRmvAux_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. intros.
      exploit ptRmvAux_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ptRmvAux_match; eauto.
    Qed.

  End PT_RMV_AUX_SIM.

End OBJ_SIM.
