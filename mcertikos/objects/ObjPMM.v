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

Section OBJ_PMM.

  Context `{real_params: RealParams}.

  (** primitve: returns whether i-th page has type "normal"*)    
  Function is_at_norm_spec (i: Z) (adt: RData) : option Z := 
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 i maxpage then
          match ZMap.get i (AT adt) with 
            | ATValid _ st _ => 
              if ATType_dec st ATNorm then Some 1
              else Some 0
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: returns whether i-th page is allocated or not*)
  Function get_at_u_spec (i: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 i maxpage then
          match ZMap.get i (AT adt) with 
            | ATValid true _ _ => Some 1
            | ATValid _ _ _ => Some 0
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: returns whether i-th page is allocated or not*)
  Function get_at_c_spec (i: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 i maxpage then
          match ZMap.get i (AT adt) with 
            | ATValid _ _ n => Some n
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: get the number of pages*)
  Function get_nps_spec (adt: RData) : option Z :=
    match (ikern adt, ihost adt) with
      | (true, true) => Some (nps adt)
      | _ => None
    end.

  (** primitve: set the allocated-bit of the i-th page*)
  Function set_at_u_spec (i: Z) (b: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 i maxpage then
          match ZtoBool b with
            | Some b' =>
              match ZMap.get i (AT adt) with
                | ATValid b1 ATNorm n => Some adt {AT: ZMap.set i (ATValid b' ATNorm n) (AT adt)}
                | _ => None
              end
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: set the type of the i-th page*)
  Function set_at_norm_spec (i: Z) (n: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 i maxpage then
          match ZtoATType n with
            | Some t => Some adt {AT: ZMap.set i (ATValid false t 0) (AT adt)}
            | _ => None
          end
        else None
      | _ => None
    end. 

  Function set_at_c_spec (i: Z) (n: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 i maxpage then
          match ZMap.get i (AT adt) with
            | ATValid b ATNorm _ => Some adt {AT: ZMap.set i (ATValid b ATNorm n) (AT adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  Function set_at_c0_spec (i: Z) (n: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) =>
        if zle_lt 0 i maxpage then
          match ZMap.get i (AT adt) with
            | ATValid true ATNorm _ => 
              Some adt {AT: ZMap.set i (ATValid true ATNorm n) (AT adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: set number of pages*)        
  Function set_nps_spec (n: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) => Some adt {nps: n}
      | _ => None
    end.

  (** primitive: initialize the allocation table*)   
  Function mem_init_spec (mbi_adr: Z) (adt: RData) : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt) with
      | (false, false, true, true) => 
        Some adt {MM: real_mm} {MMSize: real_size} {vmxinfo: real_vmxinfo} {AT: real_AT (AT adt)} 
             {nps: real_nps} {init: true}
      | _ => None
    end.

  (** primitve: free the i-th page, only used in the refienment proof*)    
  Function pfree'_spec (i: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt, init adt) with
      | (true, true, true) =>
        if zle_lt 0 i maxpage then
          match (ZMap.get i (AT adt), ZMap.get i (pperm adt))  with
            | (ATValid true ATNorm 0, PGAlloc) =>
              Some adt {AT: ZMap.set i (ATValid false ATNorm 0) (AT adt)}
                   {pperm: ZMap.set i PGUndef (pperm adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: alloc a page and returns the page index*)
  Function palloc'_spec (adt: RData): option (RData * Z) := 
    match (ikern adt, init adt, ihost adt) with
      | (true, true, true) =>
          match first_free (AT adt) (nps adt) with
            | inleft (exist i _) => 
              Some (adt {AT: ZMap.set i (ATValid true ATNorm 0) (AT adt)}
                        {pperm: ZMap.set i PGAlloc (pperm adt)}, i)
            | _ => Some (adt, 0)
          end
      | _ => None
    end.

End OBJ_PMM.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
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


  (** ** The low level specifications exist*)
  Section MEMINIT_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_AT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_MM}.
    Context {re6: relate_impl_vmxinfo}.

    Lemma mem_init_exist:
      forall s habd habd' labd i f,
        mem_init_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', mem_init_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold mem_init_spec; intros. 
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_init_eq; eauto; intros.
      exploit relate_impl_AT_eq; eauto; intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_init_update.
      apply relate_impl_nps_update.
      apply relate_impl_AT_update.
      apply relate_impl_vmxinfo_update.
      apply relate_impl_MMSize_update.
      apply relate_impl_MM_update. assumption.
    Qed.

    Context {mt1: match_impl_init}.
    Context {mt2: match_impl_nps}.
    Context {mt3: match_impl_AT}.
    Context {mt4: match_impl_MM}.
    Context {mt5: match_impl_vmxinfo}.

    Lemma mem_init_match:
      forall s d d' m i f,
        mem_init_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold mem_init_spec; intros. subdestruct. inv H. 
      eapply match_impl_init_update.
      eapply match_impl_nps_update. 
      eapply match_impl_AT_update.
      eapply match_impl_vmxinfo_update.
      eapply match_impl_MMSize_update.
      eapply match_impl_MM_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) mem_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) mem_init_spec}.

    Lemma mem_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem mem_init_spec)
            (id ↦ gensem mem_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit mem_init_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply mem_init_match; eauto.
    Qed.

  End MEMINIT_SIM.

  Section AT_SETTER_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_AT}.
    Context {mt1: match_impl_AT}.

    Section SET_AT_U_SIM.

      Lemma set_at_u_exist:
        forall s habd habd' labd i z f,
          set_at_u_spec i z habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', set_at_u_spec i z labd = Some labd' 
                           /\ relate_AbData s f habd' labd'.
      Proof.
        unfold set_at_u_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_AT_eq; eauto; intros.
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_AT_update. assumption.
      Qed.

      Lemma set_at_u_match:
        forall s d d' m i z f,
          set_at_u_spec i z d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold set_at_u_spec; intros. subdestruct.
        inv H. eapply match_impl_AT_update. assumption.
      Qed.

      Context {inv: PreservesInvariants (HD:= data) set_at_u_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) set_at_u_spec}.

      Lemma set_at_u_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem set_at_u_spec)
              (id ↦ gensem set_at_u_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit set_at_u_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply set_at_u_match; eauto.
      Qed.

    End SET_AT_U_SIM.

    Section SET_AT_C_SIM.

      Lemma set_at_c_exist:
        forall s habd habd' labd i z f,
          set_at_c_spec i z habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', set_at_c_spec i z labd = Some labd' 
                           /\ relate_AbData s f habd' labd'.
      Proof.
        unfold set_at_c_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_AT_eq; eauto; intros.
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_AT_update. assumption.
      Qed.

      Lemma set_at_c_match:
        forall s d d' m i z f,
          set_at_c_spec i z d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold set_at_c_spec; intros. subdestruct.
        inv H. eapply match_impl_AT_update. assumption.
      Qed.

      Context {inv: PreservesInvariants (HD:= data) set_at_c_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) set_at_c_spec}.

      Lemma set_at_c_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem set_at_c_spec)
              (id ↦ gensem set_at_c_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit set_at_c_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply set_at_c_match; eauto.
      Qed.

    End SET_AT_C_SIM.

    Section SET_AT_C0_SIM.

      Lemma set_at_c0_exist:
        forall s habd habd' labd i z f,
          set_at_c0_spec i z habd = Some habd'
          -> relate_AbData s f habd labd
          -> exists labd', set_at_c0_spec i z labd = Some labd' 
                           /\ relate_AbData s f habd' labd'.
      Proof.
        unfold set_at_c0_spec; intros.
        exploit relate_impl_iflags_eq; eauto. inversion 1. 
        exploit relate_impl_AT_eq; eauto; intros.
        revert H; subrewrite. subdestruct.
        inv HQ. refine_split'; trivial.
        eapply relate_impl_AT_update. assumption.
      Qed.

      Lemma set_at_c0_match:
        forall s d d' m i z f,
          set_at_c0_spec i z d = Some d'
          -> match_AbData s d m f
          -> match_AbData s d' m f.
      Proof.
        unfold set_at_c0_spec; intros. subdestruct.
        inv H. eapply match_impl_AT_update. assumption.
      Qed.

      Context {inv: PreservesInvariants (HD:= data) set_at_c0_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) set_at_c0_spec}.

      Lemma set_at_c0_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem set_at_c0_spec)
              (id ↦ gensem set_at_c0_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit set_at_c0_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply set_at_c0_match; eauto.
      Qed.

    End SET_AT_C0_SIM.

  End AT_SETTER_SIM.

  Section AT_GETTER_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_AT}.

    Lemma is_at_norm_exist:
      forall s habd labd i z f,
        is_at_norm_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> is_at_norm_spec i labd = Some z.
    Proof.
      unfold is_at_norm_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_AT_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_at_u_exist:
      forall s habd labd i z f,
        get_at_u_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> get_at_u_spec i labd = Some z.
    Proof.
      unfold get_at_u_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_AT_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_at_c_exist:
      forall s habd labd i z f,
        get_at_c_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> get_at_c_spec i labd = Some z.
    Proof.
      unfold get_at_c_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_AT_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_at_c_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_at_c_spec)
            (id ↦ gensem get_at_c_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_at_c_exist; eauto. reflexivity.
    Qed.      

    Lemma is_at_norm_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem is_at_norm_spec)
            (id ↦ gensem is_at_norm_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite is_at_norm_exist; eauto. reflexivity.
    Qed.      

    Lemma get_at_u_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_at_u_spec)
            (id ↦ gensem get_at_u_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_at_u_exist; eauto. reflexivity.
    Qed.      

  End AT_GETTER_SIM.

  Section GET_NPS_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_nps}.

    Lemma get_nps_exist:
      forall s habd labd z f,
        get_nps_spec habd = Some z
        -> relate_AbData s f habd labd
        -> get_nps_spec labd = Some z.
    Proof.
      unfold get_nps_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_nps_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_nps_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_nps_spec)
            (id ↦ gensem get_nps_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_nps_exist; eauto. reflexivity.
    Qed.

  End GET_NPS_SIM.

  Section PALLOC'_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_AT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.

    Lemma palloc'_exist:
      forall s habd habd' labd i f,
        palloc'_spec habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', palloc'_spec labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold palloc'_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_init_eq; eauto; intros.
      exploit relate_impl_AT_eq; eauto; intros.
      exploit relate_impl_nps_eq; eauto; intros.
      exploit relate_impl_pperm_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      
      apply relate_impl_pperm_update.
      apply relate_impl_AT_update. assumption.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_AT}.

    Lemma palloc'_match:
      forall s d d' m i f,
        palloc'_spec d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold palloc'_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_pperm_update.
      eapply match_impl_AT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) palloc'_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) palloc'_spec}.

    Lemma palloc'_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem palloc'_spec)
            (id ↦ gensem palloc'_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit palloc'_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply palloc'_match; eauto.
    Qed.

  End PALLOC'_SIM.

  Section PFREE'_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_AT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.

    Lemma pfree'_exist:
      forall s habd habd' labd i f,
        pfree'_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', pfree'_spec i labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold pfree'_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_init_eq; eauto; intros.
      exploit relate_impl_AT_eq; eauto; intros.
      exploit relate_impl_pperm_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      
      apply relate_impl_pperm_update.
      apply relate_impl_AT_update. assumption.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_AT}.

    Lemma pfree'_match:
      forall s d d' m i f,
        pfree'_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold pfree'_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_pperm_update.
      eapply match_impl_AT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) pfree'_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) pfree'_spec}.

    Lemma pfree'_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem pfree'_spec)
            (id ↦ gensem pfree'_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit pfree'_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply pfree'_match; eauto.
    Qed.

  End PFREE'_SIM.

End OBJ_SIM.
