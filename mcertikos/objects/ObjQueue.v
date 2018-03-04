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

Section OBJ_QUEUE.

  Context `{real_params: RealParams}.

  (** primitve: test whether the nth thread's state is s*)
  Function get_state_spec (n:Z) (adt: RData) : option Z := 
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          match ZMap.get n (tcb adt) with
            | TCBValid s _ _ => 
              Some (ThreadStatetoZ s)
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: get the nth thread's prev*)
  Function get_prev_spec (n:Z) (adt: RData) : option Z := 
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          match ZMap.get n (tcb adt) with
            | TCBValid _ prev _ => Some prev
            | _ => None
          end
        else None
      | _ => None
    end.                                                 

  (** primitve: get the nth thread's next*)
  Function get_next_spec (n:Z) (adt: RData) : option Z := 
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          match ZMap.get n (tcb adt) with
            | TCBValid _ _ next => Some next
            | _ => None
          end
        else None
      | _ => None
    end.                                                 
  
  (** primitve: set n-th thread's state to be s*)
  Function set_state_spec (n s: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          match (ZMap.get n (tcb adt), ZtoThreadState s) with 
            | (TCBValid _ prev next, Some i) =>
              Some adt {tcb: ZMap.set n (TCBValid i prev next) (tcb adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: set n-th thread's prev to be s*)
  Function set_prev_spec (n s: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          if zle_le 0 s num_proc then
            match (ZMap.get n (tcb adt)) with 
              | TCBValid ts _ next =>
                Some adt {tcb: ZMap.set n (TCBValid ts s next) (tcb adt)}
              | _ => None
            end
          else None
        else None
      | _ => None
    end.

  (** primitve: set n-th thread's next to be s*)
  Function set_next_spec (n s: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          if zle_le 0 s num_proc then
            match (ZMap.get n (tcb adt)) with 
              | TCBValid ts prev _ =>
                Some adt {tcb: ZMap.set n (TCBValid ts prev s) (tcb adt)}
              | _ => None
            end
          else None
        else None
      | _ => None
    end.

  (** primitve: init the n-th TCB*)
  Function tcb_init_spec (n: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          Some adt {tcb: ZMap.set n (TCBValid DEAD num_proc num_proc) (tcb adt)}
        else None
      | _ => None
    end.


  (** primitive: free the n-th page table and the kernel context*)   
  (*Function thread_free_spec (adt: RData) (n:Z) : option RData :=
      match (pg adt, ikern adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if zlt 0 n then
            if zlt n num_proc then
              match (ZMap.get n (pb adt)) with
                | PTTrue => 
                  Some (mkRData (HP adt) (ti adt) (pg adt) (ikern adt) (ihost adt) 
                                (AT adt) (nps adt) (PT adt) (ZMap.set n (real_free_pt (ptpool adt) n) (ptpool adt)) (ipt adt)
                                (ZMap.set n PTFalse (pb adt)) (kctxt adt) (ZMap.set n (TCBValid DEAD num_proc num_proc) (tcb adt)))
                | _ => None
              end
            else None
          else None
        | _ => None
      end.    *)
  
  (** primitive: initialize the allocation table, set up the paging mechanism, and initialize the page table pool*)   
  Function thread_init_spec (mbi_adr:Z) (adt: RData) : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
             {smspool: real_smspool (smspool adt)}
             {tcb: real_tcb (tcb adt)}
      | _ => None
    end.

  (** primitve: get the nth tdqueue's head*)
  Function get_head_spec (n:Z) (adt: RData): option Z := 
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_le 0 n num_chan then
          match ZMap.get n (tdq adt) with
            | TDQValid head _ => Some head
            | _ => None
          end
        else None
      | _ => None
    end. 

  (** primitve: get the nth tdqueue's tail*)
  Function get_tail_spec (n:Z) (adt: RData): option Z := 
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_le 0 n num_chan then
          match ZMap.get n (tdq adt) with
            | TDQValid _ tail => Some tail
            | _ => None
          end
        else None
      | _ => None
    end. 

  (** primitve: set n-th tdqueue's head as s*)
  Function set_head_spec (n s: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_le 0 n num_chan then
          match (ZMap.get n (tdq adt)) with 
            | TDQValid _ tail =>
              Some adt {tdq: ZMap.set n (TDQValid s tail) (tdq adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: set n-th tdqueue's tail as s*)
  Function set_tail_spec (n s: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_le 0 n num_chan then
          match (ZMap.get n (tdq adt)) with 
            | TDQValid head _ =>
              Some adt {tdq: ZMap.set n (TDQValid head s) (tdq adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: initialize the n-th tdqueue's*)
  Function tdq_init_spec (n: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_le 0 n num_chan then
          Some adt {tdq: ZMap.set n (TDQValid num_proc num_proc) (tdq adt)}
        else None
      | _ => None
    end.

  (** primitve: queue remove*)
  Function queue_rmv_spec (n i: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if Queue_arg n i then
          match (ZMap.get i (tcb adt)) with
            | TCBValid st prev next =>
              match (ZMap.get n (tdq adt)) with 
                | TDQValid h t =>
                  if zeq prev num_proc then
                    if zeq next num_proc then
                      Some adt {tdq: ZMap.set n (TDQValid num_proc num_proc) (tdq adt)}
                    else
                      match (ZMap.get next (tcb adt)) with
                        | TCBValid st1 _ next1 =>
                          Some adt {tcb: ZMap.set next (TCBValid st1 num_proc next1) (tcb adt)}
                               {tdq: ZMap.set n (TDQValid next t) (tdq adt)}
                        | _ => None
                      end
                  else
                    match ZMap.get prev (tcb adt)  with
                      | TCBValid st0 prev0 _ =>
                        if zeq next num_proc then
                          Some adt {tcb: ZMap.set prev (TCBValid st0 prev0 num_proc) (tcb adt)}
                               {tdq: ZMap.set n (TDQValid h prev) (tdq adt)}
                        else
                          match ZMap.get next (tcb adt) with 
                            | TCBValid st1 _ next1 =>                       
                              Some adt {tcb: ZMap.set next (TCBValid st1 prev next1)
                                                      (ZMap.set prev (TCBValid st0 prev0 next) (tcb adt))}
                            | _ => None
                          end
                      | _ => None
                    end
                | _ => None
              end
            | _ => None
          end
        else None
      | _ => None
    end.


End OBJ_QUEUE.

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

  Section THREADINIT_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_init}.
    Context {re6: relate_impl_PT}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_idpde}.
    Context {re10: relate_impl_smspool}.
    Context {re11: relate_impl_tcb}.
    Context {re14: relate_impl_vmxinfo}.
    Context {re15: relate_impl_AC}.

    Lemma thread_init_exist:
      forall s habd habd' labd i f,
        thread_init_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', thread_init_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold thread_init_spec; intros. 
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_idpde_eq; eauto.
      exploit relate_impl_tcb_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_smspool_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_tcb_update.
      apply relate_impl_smspool_update.
      apply relate_impl_idpde_update.
      apply relate_impl_ptpool_update.
      apply relate_impl_PT_update.
      apply relate_impl_init_update.
      apply relate_impl_AC_update.
      apply relate_impl_nps_update.
      apply relate_impl_LAT_update.
      apply relate_impl_pg_update. 
      apply relate_impl_vmxinfo_update. 
      assumption.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_ipt}.
    Context {mt3: match_impl_LAT}.
    Context {mt4: match_impl_nps}.
    Context {mt5: match_impl_init}.
    Context {mt6: match_impl_PT}.
    Context {mt7: match_impl_ptpool}.
    Context {mt8: match_impl_idpde}.
    Context {mt9: match_impl_smspool}.
    Context {mt10: match_impl_tcb}.
    Context {mt11: match_impl_vmxinfo}.
    Context {mt12: match_impl_AC}.

    Lemma thread_init_match:
      forall s d d' m i f,
        thread_init_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold thread_init_spec; intros. subdestruct. inv H. 
      eapply match_impl_tcb_update. 
      eapply match_impl_smspool_update.
      eapply match_impl_idpde_update.
      eapply match_impl_ptpool_update. 
      eapply match_impl_PT_update. 
      eapply match_impl_init_update. 
      eapply match_impl_AC_update.
      eapply match_impl_nps_update. 
      eapply match_impl_LAT_update.
      eapply match_impl_pg_update. 
      eapply match_impl_vmxinfo_update. 
      assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) thread_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) thread_init_spec}.

    Lemma thread_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem thread_init_spec)
            (id ↦ gensem thread_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit thread_init_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply thread_init_match; eauto.
    Qed.

  End THREADINIT_SIM.

  Section THREAD_GETTER_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_tcb}.

    Lemma get_state_exist:
      forall s habd labd i z f,
        get_state_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> get_state_spec i labd = Some z.
    Proof.
      unfold get_state_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_tcb_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_state_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_state_spec)
            (id ↦ gensem get_state_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_state_exist; eauto. reflexivity.
    Qed.      

    Lemma get_prev_exist:
      forall s habd labd i z f,
        get_prev_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> get_prev_spec i labd = Some z.
    Proof.
      unfold get_prev_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_tcb_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_prev_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_prev_spec)
            (id ↦ gensem get_prev_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_prev_exist; eauto. reflexivity.
    Qed.      

    Lemma get_next_exist:
      forall s habd labd i z f,
        get_next_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> get_next_spec i labd = Some z.
    Proof.
      unfold get_next_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_tcb_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_next_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_next_spec)
            (id ↦ gensem get_next_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_next_exist; eauto. reflexivity.
    Qed.      

  End THREAD_GETTER_SIM.

  Section SET_PREV_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_tcb}.
    Context {mt1: match_impl_tcb}.

    Lemma set_prev_exist:
      forall s habd habd' labd i z f,
        set_prev_spec i z habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', set_prev_spec i z labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold set_prev_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_tcb_eq; eauto; intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_tcb_update. assumption.
    Qed.

    Lemma set_prev_match:
      forall s d d' m i z f,
        set_prev_spec i z d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold set_prev_spec; intros. subdestruct.
      inv H. eapply match_impl_tcb_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) set_prev_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) set_prev_spec}.

    Lemma set_prev_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem set_prev_spec)
            (id ↦ gensem set_prev_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit set_prev_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply set_prev_match; eauto.
    Qed.

  End SET_PREV_SIM.

  Section SET_NEXT_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_tcb}.
    Context {mt1: match_impl_tcb}.

    Lemma set_next_exist:
      forall s habd habd' labd i z f,
        set_next_spec i z habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', set_next_spec i z labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold set_next_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_tcb_eq; eauto; intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_tcb_update. assumption.
    Qed.

    Lemma set_next_match:
      forall s d d' m i z f,
        set_next_spec i z d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold set_next_spec; intros. subdestruct.
      inv H. eapply match_impl_tcb_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) set_next_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) set_next_spec}.

    Lemma set_next_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem set_next_spec)
            (id ↦ gensem set_next_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit set_next_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply set_next_match; eauto.
    Qed.

  End SET_NEXT_SIM.

  Section SET_STATE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_tcb}.
    Context {mt1: match_impl_tcb}.

    Lemma set_state_exist:
      forall s habd habd' labd i z f,
        set_state_spec i z habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', set_state_spec i z labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold set_state_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_tcb_eq; eauto; intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_tcb_update. assumption.
    Qed.

    Lemma set_state_match:
      forall s d d' m i z f,
        set_state_spec i z d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold set_state_spec; intros. subdestruct.
      inv H. eapply match_impl_tcb_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) set_state_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) set_state_spec}.

    Lemma set_state_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem set_state_spec)
            (id ↦ gensem set_state_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit set_state_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply set_state_match; eauto.
    Qed.

  End SET_STATE_SIM.
  
End OBJ_SIM.
