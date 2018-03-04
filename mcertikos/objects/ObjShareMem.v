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

Require Import ObjLMM.

Section OBJ_ShareMEM.

  Context `{real_params: RealParams}.

  Function shared_mem_arg (pid1 pid2: Z) :=
    if zle_lt 0 pid1 num_proc then
      if zle_lt 0 pid2 num_proc then
        if zeq pid1 pid2 then false
        else true
      else false
    else false.

  Function shared_mem_arg' (pid1 pid2: Z) :=
    if zle_lt 0 pid1 num_proc then
      if zle_lt 0 pid2 num_proc then
        true
      else false
    else false.
  
  Function get_shared_mem_state_spec (pid1 pid2: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid i s vadr => Some (SharedMemInfo2Z i)
          | _ => None
        end 
      | _ => None
    end.

  Function get_shared_mem_seen_spec (pid1 pid2: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid i s vadr => Some (BooltoZ s)
          | _ => None
        end 
      | _ => None
    end.

  Function get_shared_mem_loc_spec (pid1 pid2: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid i s vadr => Some vadr
          | _ => None
        end 
      | _ => None
    end.

  Function set_shared_mem_state_spec (pid1 pid2 n: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match (ZMap.get pid2 (ZMap.get pid1 (smspool adt)), Z2SharedMemInfo n) with
          | (SHRDValid _ s vadr, Some i) =>
            Some adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid i s vadr) 
                                                       (ZMap.get pid1 (smspool adt)))
                                        (smspool adt)}
          | _ => None
        end 
      | _ => None
    end.

  Function set_shared_mem_seen_spec (pid1 pid2 n: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match (ZMap.get pid2 (ZMap.get pid1 (smspool adt)), ZtoBool n) with
          | (SHRDValid i _ vadr, Some s) =>
            Some adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid i s vadr)
                                                       (ZMap.get pid1 (smspool adt)))
                                        (smspool adt)}
          | _ => None
        end
      | _ => None
    end.

  Function set_shared_mem_loc_spec (pid1 pid2 vadr: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid i s _  => 
            Some adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid i s vadr)
                                                       (ZMap.get pid1 (smspool adt)))
                                        (smspool adt)}
          | _ => None
        end 
      | _ => None
    end.

  Function clear_shared_mem_spec (pid1 pid2: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg' pid1 pid2) with
      | (true, true, true, true, true) =>
        Some adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid SHRDDEAD true 0)
                                                   (ZMap.get pid1 (smspool adt)))
                                    (smspool adt)}
      | _ => None
    end.

  Function shared_mem_to_pending_spec (pid1 pid2 vadr: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid _ _ _ => 
            Some adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid SHRDPEND true vadr)
                                                       (ZMap.get pid1 (smspool adt)))
                                        (smspool adt)}
          | _ => None
        end 
      | _ => None
    end.

  Function shared_mem_to_dead_spec (pid1 pid2 vadr: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match (ZMap.get pid2 (ZMap.get pid1 (smspool adt)), ZMap.get pid1 (ZMap.get pid2 (smspool adt))) with
          | (SHRDValid _ _ _, SHRDValid _ _ _) => 
            let smsp := (ZMap.set pid1 (ZMap.set pid2 (SHRDValid SHRDDEAD true 0) (ZMap.get pid1 (smspool adt)))
                                  (smspool adt)) in
            let smsp' := (ZMap.set pid2 (ZMap.set pid1 (SHRDValid SHRDDEAD false 0) (ZMap.get pid2 smsp))
                                   smsp) in
            Some adt {smspool: smsp'}
          | _ => None
        end 
      | _ => None
    end.

  Function shared_mem_to_ready_spec (pid1 pid2 vadr: Z) (adt: RData) : option (RData * Z) :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid _ _ _ =>
            match ZMap.get pid1 (ZMap.get pid2 (smspool adt)) with
              | SHRDValid _ _ vadr' =>
                if zle_lt 0 vadr' adr_max then
                  match ptResv2_spec pid1 vadr PT_PERM_PTU pid2 vadr' PT_PERM_PTU adt with
                    | Some (adt', rest) =>
                      if zeq rest MagicNumber then Some (adt', MagicNumber)
                      else
                        let smsp := (ZMap.set pid1 (ZMap.set pid2 (SHRDValid SHRDREADY true 0) (ZMap.get pid1 (smspool adt')))
                                              (smspool adt')) in
                        let smsp' := (ZMap.set pid2 (ZMap.set pid1 (SHRDValid SHRDREADY false 0) (ZMap.get pid2 smsp))
                                               smsp) in
                        Some (adt' {smspool: smsp'}, rest)
                    | _ => None
                  end
                else None
              | _ => None
            end
          | _ => None
        end 
      | _ => None
    end.

  Function get_shared_mem_status_seen_spec (pid1 pid2: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid1 (ZMap.get pid2 (smspool adt)) with
          | SHRDValid st _ _ => 
            if SharedMemInfo_dec st SHRDPEND then Some SHARED_MEM_PEND
            else
              match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
                | SHRDValid i' _ _ => Some (SharedMemInfo2Z i')
                | _ => None
              end
          | _ => None
        end
      | _ => None
    end.

  Function sharedmem_init_spec (mbi_adr:Z) (adt: RData): option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
             {smspool: real_smspool (smspool adt)}
      | _ => None
    end.

  Function shared_mem_status_spec (pid1 pid2: Z) (adt: RData) : option (RData * Z) :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid i' true _ => 
            match ZMap.get pid1 (ZMap.get pid2 (smspool adt)) with
              | SHRDValid st _ _ => 
                if SharedMemInfo_dec st SHRDPEND then Some (adt, SHARED_MEM_PEND)
                else Some (adt, SharedMemInfo2Z i')
              | _ => None
            end
          | SHRDValid i' false vadr => 
            Some (adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid i' true vadr) 
                                                        (ZMap.get pid1 (smspool adt)))
                                         (smspool adt)}, SharedMemInfo2Z i')
          | _ => None
        end 
      | _ => None
    end.

  Function offer_shared_mem_spec (pid1 pid2 vadr: Z) (adt: RData) : option (RData * Z) :=
    match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
      | (true, true, true, true, true) =>
        match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
          | SHRDValid st _ _ => 
            if SharedMemInfo_dec st SHRDPEND then Some (adt, SHARED_MEM_PEND)
            else
              match ZMap.get pid1 (ZMap.get pid2 (smspool adt)) with
                | SHRDValid st' _ vadr' => 
                  if zle_lt 0 vadr' adr_max then
                    if SharedMemInfo_dec st' SHRDPEND then
                      match ptResv2_spec pid1 vadr PT_PERM_PTU pid2 vadr' PT_PERM_PTU adt with
                        | Some (adt', re) =>
                          if zeq re MagicNumber
                          then
                            let smsp := (ZMap.set pid1 (ZMap.set pid2 (SHRDValid SHRDDEAD true 0) (ZMap.get pid1 (smspool adt)))
                                                  (smspool adt')) in
                            let smsp' := (ZMap.set pid2 (ZMap.set pid1 (SHRDValid SHRDDEAD false 0) (ZMap.get pid2 smsp))
                                                   smsp) in
                            Some (adt' {smspool: smsp'}, SHARED_MEM_DEAD)
                          else
                            let smsp := (ZMap.set pid1 (ZMap.set pid2 (SHRDValid SHRDREADY true 0) (ZMap.get pid1 (smspool adt')))
                                                  (smspool adt')) in
                            let smsp' := (ZMap.set pid2 (ZMap.set pid1 (SHRDValid SHRDREADY false 0) (ZMap.get pid2 smsp))
                                                   smsp) in
                            Some (adt' {smspool: smsp'}, SHARED_MEM_READY)
                        | _ => None
                      end
                    else
                      Some (adt {smspool: ZMap.set pid1 (ZMap.set pid2 (SHRDValid SHRDPEND true vadr) 
                                                                  (ZMap.get pid1 (smspool adt)))
                                                   (smspool adt)}, SHARED_MEM_PEND)
                  else None
                | _ => None
              end
          | _ => None
        end
      | _ => None
    end.

End OBJ_ShareMEM.

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

  Section Shared_MEM_GETTER.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_smspool}.

    Lemma get_shared_mem_state_exists:
      forall s habd labd i1 i2 z f,
      get_shared_mem_state_spec i1 i2 habd = Some z
      -> relate_AbData s f habd labd
      -> get_shared_mem_state_spec i1 i2 labd = Some z.
    Proof.
      unfold get_shared_mem_state_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_smspool_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_shared_mem_seen_exists:
      forall s habd labd i1 i2 z f,
      get_shared_mem_seen_spec i1 i2 habd = Some z
      -> relate_AbData s f habd labd
      -> get_shared_mem_seen_spec i1 i2 labd = Some z.
    Proof.
      unfold get_shared_mem_seen_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_smspool_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_shared_mem_state_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_shared_mem_state_spec)
            (id ↦ gensem get_shared_mem_state_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'.
      match_external_states_simpl. 
      erewrite get_shared_mem_state_exists; eauto. reflexivity.
    Qed.      

    Lemma get_shared_mem_seen_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_shared_mem_seen_spec)
            (id ↦ gensem get_shared_mem_seen_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'.
      match_external_states_simpl. 
      erewrite get_shared_mem_seen_exists; eauto. reflexivity.
    Qed.      

  End Shared_MEM_GETTER.

  Section Shared_MEM_SETTER.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_smspool}.
 
    Lemma set_shared_mem_seen_exists:
      forall s habd habd' labd i1 i2 z f,
        set_shared_mem_seen_spec i1 i2 z habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', set_shared_mem_seen_spec i1 i2 z labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold set_shared_mem_seen_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_smspool_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      apply relate_impl_smspool_update. assumption.
    Qed.

    Context {mt1: match_impl_smspool}.

    Lemma set_shared_mem_seen_match:
      forall s d d' m i1 i2 z f,
        set_shared_mem_seen_spec i1 i2 z d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold set_shared_mem_seen_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_smspool_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) set_shared_mem_seen_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) set_shared_mem_seen_spec}.

    Lemma set_shared_mem_seen_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem set_shared_mem_seen_spec)
            (id ↦ gensem set_shared_mem_seen_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'.
      exploit set_shared_mem_seen_exists; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl. 
      eapply set_shared_mem_seen_match; eauto.
    Qed.      

  End Shared_MEM_SETTER.

  Section Shared_MEM_STATUS.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_smspool}.
 
    Lemma shared_mem_status_exists:
      forall s habd habd' labd i1 i2 z f,
        shared_mem_status_spec i1 i2 habd = Some (habd', z)
        -> relate_AbData s f habd labd
        -> exists labd', shared_mem_status_spec i1 i2 labd = Some (labd', z)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold shared_mem_status_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_smspool_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      apply relate_impl_smspool_update. assumption.
    Qed.

    Context {mt1: match_impl_smspool}.

    Lemma shared_mem_status_match:
      forall s d d' m i1 i2 z f,
        shared_mem_status_spec i1 i2 d = Some (d', z)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold shared_mem_status_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_smspool_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) shared_mem_status_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) shared_mem_status_spec}.

    Lemma shared_mem_status_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem shared_mem_status_spec)
            (id ↦ gensem shared_mem_status_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'.
      exploit shared_mem_status_exists; eauto 1. intros (labd' & HP & HM).
      match_external_states_simpl. 
      eapply shared_mem_status_match; eauto.
    Qed.      

  End Shared_MEM_STATUS.

  Section PT_RESV2_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_HP}.
    Context {re9: relate_impl_AC}.

    Lemma ptResv2_exist:
      forall s habd habd' labd i n v p n' v' p' f,
        ptResv2_spec n v p n' v' p' habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', ptResv2_spec n v p n' v' p' labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptResv2_spec; intros.
      subdestruct. destruct p0.
      - exploit alloc_exist; eauto.
        intros (? & ? & ?).
        subrewrite'. inv H. refine_split'; trivial.
      - exploit alloc_exist; eauto.
        intros (? & ? & ?).
        exploit ptInsert0_exist; eauto.
        intros (? & ? & ?).
        subrewrite'. inv H. refine_split'; trivial.
      - exploit alloc_exist; eauto.
        intros (? & ? & ?).
        revert Hdestruct2; intros Hc.
        exploit ptInsert0_exist; eauto.
        intros (? & ? & ?).
        subrewrite'. clear Hc H3.
        exploit ptInsert0_exist; eauto.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_ptpool}.
    Context {mt4: match_impl_HP}.
    Context {mt5: match_impl_AC}.

    Lemma ptResv2_match:
      forall s d d' m i n v p n' v' p' f,
        ptResv2_spec n v p n' v' p' d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptResv2_spec; intros. subdestruct; inv H; trivial.
      - eapply ptInsert0_match; eauto.
        eapply alloc_match; eauto.
      - eapply ptInsert0_match; eauto.
        eapply ptInsert0_match; eauto.
        eapply alloc_match; eauto.
    Qed.
    
    Context {inv: PreservesInvariants (HD:= data) ptResv2_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptResv2_spec}.

    Lemma ptResv2_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptResv2_spec)
            (id ↦ gensem ptResv2_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ptResv2_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply ptResv2_match; eauto.
    Qed.

  End PT_RESV2_SIM.

  Section Offer_Shared_MEM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_HP}.
    Context {re9: relate_impl_smspool}.
    Context {re10: relate_impl_AC}.
 
    Lemma offer_shared_mem_exists:
      forall s habd habd' labd i1 i2 v z f,
        offer_shared_mem_spec i1 i2 v habd = Some (habd', z)
        -> relate_AbData s f habd labd
        -> exists labd', offer_shared_mem_spec i1 i2 v labd = Some (labd', z)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold offer_shared_mem_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_smspool_eq; eauto; intros.
      exploit relate_impl_ipt_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; try(refine_split'; trivial; fail).
      - exploit ptResv2_exist; eauto.
        intros (? & ? & ?).
        exploit relate_impl_smspool_eq; eauto; intros.
        subrewrite'. refine_split'. trivial.
        apply relate_impl_smspool_update. assumption.        
      - exploit ptResv2_exist; eauto.
        intros (? & ? & ?).      
        exploit relate_impl_smspool_eq; eauto; intros.
        subrewrite'. refine_split'; trivial.
        apply relate_impl_smspool_update. assumption.
      - refine_split'; trivial.
        apply relate_impl_smspool_update. assumption.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_ptpool}.
    Context {mt4: match_impl_HP}.
    Context {mt5: match_impl_smspool}.
    Context {mt6: match_impl_AC}.

    Lemma offer_shared_mem_match:
      forall s d d' m i1 i2 v z f,
        offer_shared_mem_spec i1 i2 v d = Some (d', z)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold offer_shared_mem_spec; intros. subdestruct; inv H; trivial.
      - eapply match_impl_smspool_update.
        eapply ptResv2_match; eauto.
      - eapply match_impl_smspool_update. 
        eapply ptResv2_match; eauto.
      - eapply match_impl_smspool_update. 
        assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) offer_shared_mem_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) offer_shared_mem_spec}.

    Lemma offer_shared_mem_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem offer_shared_mem_spec)
            (id ↦ gensem offer_shared_mem_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'.
      exploit offer_shared_mem_exists; eauto 1. intros (labd' & HP & HM).
      match_external_states_simpl. 
      eapply offer_shared_mem_match; eauto.
    Qed.      

  End Offer_Shared_MEM.
 
  (** ** The low level specifications exist*)
  Section SHAREDMEMINIT_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_init}.
    Context {re6: relate_impl_PT}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_idpde}.
    Context {re9: relate_impl_smspool}.
    Context {re10: relate_impl_vmxinfo}.
    Context {re11: relate_impl_AC}.

    Lemma sharedmem_init_exist:
      forall s habd habd' labd i f,
        sharedmem_init_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', sharedmem_init_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold sharedmem_init_spec; intros. 
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_idpde_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_smspool_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

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
    Context {mt10: match_impl_smspool}.
    Context {mt11: match_impl_vmxinfo}.
    Context {mt12: match_impl_AC}.

    Lemma sharedmem_init_match:
      forall s d d' m i f,
        sharedmem_init_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold sharedmem_init_spec; intros. subdestruct. inv H. 
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

    Context {inv: PreservesInvariants (HD:= data) sharedmem_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) sharedmem_init_spec}.

    Lemma sharedmem_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem sharedmem_init_spec)
            (id ↦ gensem sharedmem_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit sharedmem_init_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply sharedmem_init_match; eauto.
    Qed.

  End SHAREDMEMINIT_SIM.

  Section SHARED_MEM_TO_READY_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_HP}.
    Context {re9: relate_impl_smspool}.
    Context {re10: relate_impl_AC}.

    Lemma shared_mem_to_ready_exist:
      forall s habd habd' labd pid1 pid2 vadr rest f,
        shared_mem_to_ready_spec pid1 pid2 vadr habd = Some (habd', rest)
        -> relate_AbData s f habd labd
        -> exists labd', shared_mem_to_ready_spec pid1 pid2 vadr labd = Some (labd', rest)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold shared_mem_to_ready_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_smspool_eq; eauto. intros.
      revert H. subrewrite.
      subdestruct;
        eapply ptResv2_exist in Hdestruct7; eauto;
        destruct Hdestruct7 as (labd' & -> & rel_labd');
	subrewrite';
        inv HQ; refine_split'; trivial.

      rewrite (relate_impl_smspool_eq _ _ _ _ rel_labd').
      apply relate_impl_smspool_update; assumption.
    Qed.

  End SHARED_MEM_TO_READY_SIM.

  Section SHARED_MEM_TO_PENDING_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_smspool}.

    Lemma shared_mem_to_pending_exist:
      forall s habd habd' labd pid1 pid2 vadr f,
        shared_mem_to_pending_spec pid1 pid2 vadr habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', shared_mem_to_pending_spec pid1 pid2 vadr labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold shared_mem_to_pending_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_smspool_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_smspool_update; assumption.
    Qed.

  End SHARED_MEM_TO_PENDING_SIM.

  Section SHARED_MEM_TO_DEAD_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_smspool}.

    Lemma shared_mem_to_dead_exist:
      forall s habd habd' labd pid1 pid2 vadr f,
        shared_mem_to_dead_spec pid1 pid2 vadr habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', shared_mem_to_dead_spec pid1 pid2 vadr labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold shared_mem_to_dead_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_smspool_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_smspool_update; assumption.
    Qed.

  End SHARED_MEM_TO_DEAD_SIM.

End OBJ_SIM.
