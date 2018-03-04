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
Require Import ASTExtra.
Require Import ObjVMM.
Require Import ObjThread.
Require Import ObjFlatMem.
Require Import Observation.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import AuxLemma.
Require Import GlobIdent.
Require Import LAsmModuleSemAux.

Section OBJ_SyncIPC.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (** primitive: get the i-th sync_channel's count **)
  Function get_sync_chan_count_spec (i: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (syncchpool adt) with
            | SyncChanValid _ _ c => Some (Int.unsigned c)
            | _ => None
          end
        else None
      | _ => None
    end.

  Function get_sync_chan_to_spec (i: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (syncchpool adt) with
            | SyncChanValid to _ _ => Some (Int.unsigned to)
            | _ => None
          end
        else None
      | _ => None
    end.

  Function get_sync_chan_paddr_spec (i: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (syncchpool adt) with
            | SyncChanValid _ vaddr _ => Some (Int.unsigned vaddr)
            | _ => None
          end
        else None
      | _ => None
    end.

  Function set_sync_chan_count_spec (i count: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (syncchpool adt) with
            | SyncChanValid t v _
                => Some (adt {syncchpool: ZMap.set i (SyncChanValid t v (Int.repr count)) 
                                          (syncchpool adt)})
            | _ => None
          end
        else None
      | _ => None
    end.

  Function set_sync_chan_to_spec (i to: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (syncchpool adt) with
            | SyncChanValid _ v c
                => Some (adt {syncchpool: ZMap.set i (SyncChanValid (Int.repr to) v c) 
                                          (syncchpool adt)})
            | _ => None
          end
        else None
      | _ => None
    end.

  Function set_sync_chan_paddr_spec (i vaddr: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (syncchpool adt) with
            | SyncChanValid t _ c
                => Some (adt {syncchpool: ZMap.set i (SyncChanValid t (Int.repr vaddr) c) 
                                          (syncchpool adt)})
            | _ => None
          end
        else None
      | _ => None
    end.

  Function init_sync_chan_spec (i : Z) (adt : RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          Some adt {syncchpool: 
                      ZMap.set i (SyncChanValid (Int.repr num_chan) (Int.repr 0) (Int.repr 0)) (syncchpool adt)}
        else None
      | _ => None
    end.

  Function is_pid_sending_to_spec (i to: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (syncchpool adt) with
            | SyncChanValid t _ _ 
              => if Int.eq t (Int.repr to) then Some 1 else Some 0
            | _ => None
          end
        else None
      | _ => None
    end.

  Function syncsendto_chan_post_spec (adt : RData) : option (RData * Z) :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        match ZMap.get (cid adt) (syncchpool adt) with
          | SyncChanValid to paddr count =>
            if zeq (Int.unsigned to) num_chan then
              Some (adt, (Int.unsigned count))
            else
              let adt' := adt{syncchpool : 
                                ZMap.set (cid adt) 
                                         (SyncChanValid (Int.repr num_chan) paddr count) (syncchpool adt)} in
                  Some (adt', 1024+3)
          | _ => None
        end
      | _ => None
    end.

  Function get_kernel_pa_spec (pid vaddr : Z) (adt : RData) : option Z :=
    match pg adt with
      | true => match ptRead_spec pid vaddr adt with
                  | Some paddr =>
                    if zeq paddr 0 then None else Some (paddr / PgSize * PgSize + (vaddr mod PgSize))
                  | _ => None
                end
      | _ => None
    end.

  Function syncsendto_chan_pre_spec (chid vaddr scount : Z) (adt : RData) : option (RData * Z) := 
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 chid num_proc then
          match ZMap.get chid (abtcb adt) with
            | AbTCBValid st _ => 
              if ThreadState_dec st DEAD then
                Some (adt, 1024+2)
              else
                match ZMap.get (cid adt) (syncchpool adt) with
                  | SyncChanValid to _ _ =>
                    match get_kernel_pa_spec (cid adt) vaddr adt with
                      | Some skpa =>
                        if zle_le 0 skpa Int.max_unsigned then
                           if zeq (Int.unsigned to) 64 then
                             let asendval := Z.min (scount) (1024) in
                             let adt' := adt {syncchpool : 
                                                ZMap.set (cid adt) 
                                                         (SyncChanValid (Int.repr chid) (Int.repr skpa) (Int.repr asendval))
                                                         (syncchpool adt)} in
                             Some (adt', (cid adt))
                           else
                             None
                        else None
                      | _ => None
                    end
                  | _ => None
                end
            | _ => None
          end
        else None
      | _ => None
    end.
  
  Function syncreceive_chan_spec (fromid vaddr rcount : Z) (adt : RData) : option (RData * Z) :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 fromid num_proc then
          match ZMap.get fromid (abtcb adt) with
            | AbTCBValid st _ => 
              if ThreadState_dec st DEAD then            
                Some (adt, 1024+2)
              else
                match ZMap.get fromid (syncchpool adt) with
                  | SyncChanValid to spaddr scount =>
                    if zeq (Int.unsigned to) (cid adt) then
                      let arecvcount := Z.min (Int.unsigned scount) rcount in
                      match get_kernel_pa_spec (cid adt) vaddr adt with
                        | Some rbuffpa =>
                          match flatmem_copy_spec arecvcount (Int.unsigned spaddr) rbuffpa adt with
                            | Some adt1 =>
                              let adt2 := adt1 
                                            {syncchpool : ZMap.set fromid (SyncChanValid (Int.repr num_chan) Int.zero 
                                                                                         (Int.repr arecvcount)) (syncchpool adt1)} in
                              match thread_wakeup_spec fromid adt2 with
                                | Some adt3 => Some (adt3, arecvcount)
                                | _ => None
                              end
                            | _ => None
                          end
                        | _ => None
                      end
                    else
                      Some (adt, 1024+3)
                  | _ => None
                end
            | _ => None
          end
        else None
      | _ => None
    end.

End OBJ_SyncIPC.


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

  Local Open Scope Z_scope.

  Section IS_PID_SENDING_TO.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_syncchpool}.
    Context {re3: relate_impl_ipt}.

    Lemma is_pid_sending_to_exist:
      forall s pid to habd labd z f,
        is_pid_sending_to_spec pid to habd = Some z
        -> relate_AbData s f habd labd
        -> is_pid_sending_to_spec pid to labd = Some z.
    Proof.
      unfold is_pid_sending_to_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma is_pid_sending_to_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem is_pid_sending_to_spec)
                               (id ↦ gensem is_pid_sending_to_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl.
      erewrite is_pid_sending_to_exist; eauto. reflexivity.
    Qed.

  End IS_PID_SENDING_TO.

  Section GET_SYNC_CHAN_TO.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re5: relate_impl_syncchpool}.

    Lemma get_sync_chan_to_exist:
      forall s f habd labd chid to,
      get_sync_chan_to_spec chid habd = Some to
      -> relate_AbData s f habd labd
      -> get_sync_chan_to_spec chid labd = Some to.
    Proof.
      unfold get_sync_chan_to_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.
      revert H; subrewrite.
    Qed.
      
  End GET_SYNC_CHAN_TO.

  Section GET_SYNC_CHAN_COUNT.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re5: relate_impl_syncchpool}.

    Lemma get_sync_chan_count_exist:
      forall s f habd labd chid count,
      get_sync_chan_count_spec chid habd = Some count
      -> relate_AbData s f habd labd
      -> get_sync_chan_count_spec chid labd = Some count.
    Proof.
      unfold get_sync_chan_count_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.
      revert H; subrewrite.
    Qed.
      
  End GET_SYNC_CHAN_COUNT.

  Section SET_SYNC_CHAN_TO.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re5: relate_impl_syncchpool}.

    Lemma set_sync_chan_to_exist:
      forall s f habd habd' labd chid to,
        set_sync_chan_to_spec chid to habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', set_sync_chan_to_spec chid to labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold set_sync_chan_to_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.
      revert H; subrewrite.
      subdestruct; inv HQ; try (refine_split'; trivial; fail).
      exploit relate_impl_syncchpool_eq; eauto; intros.
      subrewrite'. refine_split'; trivial.      
      eapply relate_impl_syncchpool_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) set_sync_chan_to_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) set_sync_chan_to_spec}.

  End SET_SYNC_CHAN_TO.

  Section SET_SYNC_CHAN_PADDR.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re5: relate_impl_syncchpool}.

    Lemma set_sync_chan_paddr_exist:
      forall s f habd habd' labd chid vaddr,
      set_sync_chan_paddr_spec chid vaddr habd = Some habd'
      -> relate_AbData s f habd labd
      -> exists labd', set_sync_chan_paddr_spec chid vaddr labd = Some labd'
                       /\ relate_AbData s f habd' labd'.
    Proof.
      unfold set_sync_chan_paddr_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.
      revert H; subrewrite.
      subdestruct; inv HQ; try (refine_split'; trivial; fail).
      exploit relate_impl_syncchpool_eq; eauto; intros.
      subrewrite'. refine_split'; trivial.      
      eapply relate_impl_syncchpool_update. assumption.
    Qed.
      
    Context {inv: PreservesInvariants (HD:= data) set_sync_chan_paddr_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) set_sync_chan_paddr_spec}.

  End SET_SYNC_CHAN_PADDR.

  Section GET_KERNEL_PA.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_PT}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.

    Lemma get_kernel_pa_exist:
      forall s f habd labd va chid pa,
      get_kernel_pa_spec chid va habd = Some pa
      -> relate_AbData s f habd labd
      -> get_kernel_pa_spec chid va labd = Some pa.
    Proof.
      unfold get_kernel_pa_spec in *; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_init_eq; eauto. intros.

      revert H; subrewrite.
      subdestruct; inv HQ.
      erewrite ptRead_exist; eauto.
      rewrite Hdestruct1; auto.
    Qed.

  End GET_KERNEL_PA.

  Section SET_SYNC_CHAN_COUNT.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re5: relate_impl_syncchpool}.

    Lemma set_sync_chan_count_exist:
      forall s f habd habd' labd chid count,
      set_sync_chan_count_spec chid count habd = Some habd'
      -> relate_AbData s f habd labd
      -> exists labd', set_sync_chan_count_spec chid count labd = Some labd'
                       /\ relate_AbData s f habd' labd'.
    Proof.
      unfold set_sync_chan_count_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.
      revert H; subrewrite.
      subdestruct; inv HQ; try (refine_split'; trivial; fail).
      exploit relate_impl_syncchpool_eq; eauto; intros.
      subrewrite'. refine_split'; trivial.      
      eapply relate_impl_syncchpool_update. assumption.
    Qed.
  
    Context {inv: PreservesInvariants (HD:= data) set_sync_chan_count_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) set_sync_chan_count_spec}.

  End SET_SYNC_CHAN_COUNT.

  Section SYNCSENDTO_CHAN.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_abtcb}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_syncchpool}.
    Context {re8: relate_impl_abq}.
    Context {re12: relate_impl_init}.
    Context {re7: relate_impl_PT}.
    Context {re9: relate_impl_ptpool}.
    
    Lemma syncsendto_chan_pre_exist:
      forall s f habd habd' labd chid vaddr count i,
        syncsendto_chan_pre_spec chid vaddr count habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', syncsendto_chan_pre_spec chid vaddr count labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.

    Proof.
      unfold syncsendto_chan_pre_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ;
      refine_split'; trivial.
      - erewrite get_kernel_pa_exist; eauto.
        rewrite Hdestruct9.
        reflexivity.
      - eapply relate_impl_syncchpool_update. assumption.
    Qed.

    Lemma syncsendto_chan_post_exist:
      forall s f habd habd' labd i,
        syncsendto_chan_post_spec habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', syncsendto_chan_post_spec labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold syncsendto_chan_post_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.

      revert H. subrewrite.
      subdestruct; inv HQ;
      refine_split'; trivial.      
      eapply relate_impl_syncchpool_update. assumption.
    Qed.

    Context {re13: match_impl_syncchpool}.

    Lemma syncsendto_chan_pre_match:
      forall s d d' m chid vaddr count i f,
        syncsendto_chan_pre_spec chid vaddr count d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold syncsendto_chan_pre_spec; intros.
      subdestruct; inv H; trivial.
      eapply match_impl_syncchpool_update. assumption.
    Qed.

    Lemma syncsendto_chan_post_match:
      forall s d d' m i f,
        syncsendto_chan_post_spec d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold syncsendto_chan_post_spec; intros.
      subdestruct; inv H; trivial.
      eapply match_impl_syncchpool_update. assumption.
    Qed.

    Section PRE.
      
      Context {inv: PreservesInvariants (HD:= data) syncsendto_chan_pre_spec}.
      Context {inv0: PreservesInvariants (HD:= data0) syncsendto_chan_pre_spec}.

      Lemma syncsendto_chan_pre_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem syncsendto_chan_pre_spec)
              (id ↦ gensem syncsendto_chan_pre_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit syncsendto_chan_pre_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply syncsendto_chan_pre_match; eauto.
      Qed.

    End PRE.

    Section POST.

      Context {inv1: PreservesInvariants (HD:= data) syncsendto_chan_post_spec}.
      Context {inv2: PreservesInvariants (HD:= data0) syncsendto_chan_post_spec}.

      Lemma syncsendto_chan_post_sim :
        forall id,
          sim (crel RData RData) (id ↦ gensem syncsendto_chan_post_spec)
              (id ↦ gensem syncsendto_chan_post_spec).
      Proof.
        intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
        exploit syncsendto_chan_post_exist; eauto 1; intros [labd' [HP HM]].
        match_external_states_simpl.
        eapply syncsendto_chan_post_match; eauto.
      Qed.

    End POST.

  End SYNCSENDTO_CHAN.

  Section SYNCRECEIVE_CHAN.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_abtcb}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_syncchpool}.
    Context {re8: relate_impl_abq}.
    Context {re9: relate_impl_PT}.
    Context {re10: relate_impl_ptpool}.
    Context {re11: relate_impl_init}.
    Context {re12: relate_impl_HP}.
    Context {re13: relate_impl_pperm}.

    Lemma syncreceive_chan_exist:
    forall s f habd habd' labd fromid vaddr count i,
      syncreceive_chan_spec fromid vaddr count habd = Some (habd', i)
      -> relate_AbData s f habd labd
      -> exists labd', syncreceive_chan_spec fromid vaddr count labd = Some (labd', i)
                       /\ relate_AbData s f habd' labd'.
    Proof.
      unfold syncreceive_chan_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto; intros.

      revert H. subrewrite;
      subdestruct; inv HQ;
      try (refine_split'; trivial; fail).
      erewrite get_kernel_pa_exist; eauto.
      exploit flatmem_copy_exist; eauto.
      intros (labd' & Hmemcpy2 & Hmemcpy3).
      rewrite Hmemcpy2.
      exploit thread_wakeup_exist; eauto.
      eapply relate_impl_syncchpool_update. 
      instantiate (1:=labd').
      instantiate (1:=f).
      instantiate (1:=s).
      assumption.

      intros (labd'1 & Htwakeup2 & Htwakeup3).
      eapply relate_impl_syncchpool_eq in Hmemcpy3.
      rewrite Hmemcpy3 in Htwakeup2.
      rewrite Htwakeup2.
      refine_split'; trivial.
    Qed.

    Context {mt14: match_impl_abtcb}.
    Context {mt15: match_impl_abq}.
    Context {mt16: match_impl_syncchpool}.
    Context {mt1: match_impl_HP}.

    Lemma syncreceive_chan_match:
      forall s d d' m i f fromid rvaddr count,
      syncreceive_chan_spec fromid rvaddr count d = Some (d', i)
      -> match_AbData s d m f
      -> match_AbData s d' m f.
    Proof.
      unfold syncreceive_chan_spec; intros.
      subdestruct; inv H; trivial;
      eapply thread_wakeup_match; eauto;
      eapply match_impl_syncchpool_update; 
      eapply flatmem_copy_match; eauto.
    Qed.

    Context {inv1: PreservesInvariants (HD:= data) syncreceive_chan_spec}.
    Context {inv2: PreservesInvariants (HD:= data0) syncreceive_chan_spec}.

    Lemma syncreceive_chan_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem syncreceive_chan_spec)
            (id ↦ gensem syncreceive_chan_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      exploit syncreceive_chan_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply syncreceive_chan_match; eauto.
    Qed.

  End SYNCRECEIVE_CHAN.

End OBJ_SIM.
