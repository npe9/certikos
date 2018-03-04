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

Section OBJ_Thread.

  Context `{real_params: RealParams}.

  Definition kctxt_ra_spec (adt: RData) (n: Z) (b: block) (ofs: int) : option RData :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zlt_lt 0 n num_proc then
          let rs := (ZMap.get n (kctxt adt))#RA <- (Vptr b ofs) in
          Some adt {kctxt: ZMap.set n rs (kctxt adt)}
        else None
      | _ => None
    end.

  Definition kctxt_sp_spec (adt: RData) (n: Z) (b: block) (ofs: int) : option RData :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zlt_lt 0 n num_proc then
          let rs := (ZMap.get n (kctxt adt))#SP <- (Vptr b ofs) in
          Some adt {kctxt: ZMap.set n rs (kctxt adt)}
        else None
      | _ => None
    end.

  Function kctxt_switch_spec (adt: RData) (n n': Z) (rs: KContext) : option (RData * KContext) :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          if zle_lt 0 n' num_proc then
            if zeq n n' then None
            else 
              Some (adt {kctxt: ZMap.set n rs (kctxt adt)}
                    , ZMap.get n' (kctxt adt))
          else None
        else None
      | _ => None
    end.

  (** ** Semantics of primitives*)
  (** primitive: return the first unused page table (or kctxt) and initialize the kernel context*)   
  Definition kctxt_new_spec (adt: RData) (b: block) (b':block) (ofs': int) id q: option (RData * Z) :=
    let c := ZMap.get id (AC adt) in 
    let i := id * max_children + 1 + Z_of_nat (length (cchildren c)) in
      match (ikern adt, ihost adt, pg adt, ipt adt, cused c, zle_lt 0 i num_id,
             zlt (Z_of_nat (length (cchildren c))) max_children,
             zle_le 0 q (cquota c - cusage c)) with
      | (true, true, true, true, true, left _, left _, left _) =>           
           let ofs := Int.repr ((i + 1) * PgSize -4) in
           let rs := ((ZMap.get i (kctxt adt)) # SP <- (Vptr b ofs)) # RA <- (Vptr b' ofs') in           
           let child := mkContainer q 0 id nil true in
             Some (adt {AC: ZMap.set i child ((AC adt) {usage id := cusage c + q}
                                                       {children id := (i :: cchildren c)})}
                       {kctxt: ZMap.set i rs (kctxt adt)}, i)
      | _ => None
      end.

  Function get_state0_spec (n:Z) (adt: RData): option Z := 
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          match ZMap.get n (abtcb adt) with
            | AbTCBValid s _ => 
              Some (ThreadStatetoZ s)
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: set n-th thread's state to be s*)
  Function set_state0_spec (n s: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_id then
          if cused (ZMap.get n (AC adt)) then
              match (ZMap.get n (abtcb adt), ZtoThreadState s) with 
                | (AbTCBValid _ b, Some i) =>
                  Some adt {abtcb: ZMap.set n (AbTCBValid i b) (abtcb adt)}
                | _ => None
              end
          else None
        else None
      | _ => None
    end.

  (** primitve: set n-th thread's state to be s*)
  Function set_state1_spec (n s: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_proc then
          match cused (ZMap.get n (AC adt)), ZMap.get n (abtcb adt), ZtoThreadState s with 
            | true, AbTCBValid _ b, Some i =>
              if ThreadState_dec i RUN then None
              else
                Some adt {abtcb: ZMap.set n (AbTCBValid i b) (abtcb adt)}
            | _, _ , _ => None
          end
        else None
      | _ => None
    end.        
  
  (** primitve: enqueue*)
  Function enqueue0_spec (n i: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if Queue_arg n i then
          match (ZMap.get n (abq adt), cused (ZMap.get i (AC adt)))  with 
            | (AbQValid l, true) =>
              match (ZMap.get i (abtcb adt)) with
                | AbTCBValid st b =>
                  if zeq b (-1) then
                    Some adt {abtcb: ZMap.set i (AbTCBValid st n) (abtcb adt)}
                         {abq: ZMap.set n (AbQValid (i::l)) (abq adt)}
                  else None                        
                | _ => None
              end
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: dequeue*)
  Function dequeue0_spec (n: Z) (adt: RData): option (RData * Z) :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_le 0 n num_chan then
          match (ZMap.get n (abq adt)) with 
            | AbQValid l =>
              let la := last l num_proc in
              if zeq la num_proc then
                Some (adt, la)
              else
                match (ZMap.get la (abtcb adt)) with
                  | AbTCBValid st _ =>
                    Some (adt {abtcb: ZMap.set la (AbTCBValid st (-1)) (abtcb adt)}
                              {abq: ZMap.set n (AbQValid (remove zeq la l)) (abq adt)}, la)
                  | _ => None
                end
            | _ => None
          end
        else None
      | _ => None
    end.    
  
  (** primitve: queue remove*)
  Function queue_rmv0_spec (n i: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if Queue_arg n i then
          match (ZMap.get n (abq adt)) with 
            | AbQValid l =>
              match (ZMap.get i (abtcb adt)) with
                | AbTCBValid st b =>
                  if zeq n b then
                    Some adt {abtcb: ZMap.set i (AbTCBValid st (-1)) (abtcb adt)}
                         {abq: ZMap.set n (AbQValid (remove zeq i l)) (abq adt)}
                  else
                    None
                | _ => None
              end
            | _ => None
          end
        else None
      | _ => None
    end.
  
  (** primitive: initialize the allocation table, set up the paging mechanism, and initialize the page table pool*)   
  Function tdqueue_init0_spec (mbi_adr: Z) (adt: RData): option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
             {smspool: real_smspool (smspool adt)}
             {abtcb: real_abtcb (abtcb adt)}
             {abq: real_abq (abq adt)}
      | _ => None
    end.

  (** primitive: free the n-th page table and the kernel context*)   
  (*Function thread_free_spec (adt: RData) (n:Z): option RData :=
      match (pg adt, ikern adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if zlt 0 n then
            if zlt n num_proc then
              match (ZMap.get n (pb adt)) with
                | PTTrue => 
                  match ZMap.get n (abtcb adt) with
                    | AbTCBValid _ b =>
                      if zeq b (-1) then
                        Some (mkRData (HP adt) (ti adt) (pg adt) (ikern adt) (ihost adt) 
                                      (AT adt) (nps adt) (PT adt) (ZMap.set n (real_free_pt (ptpool adt) n) (ptpool adt)) (ipt adt)
                                      (ZMap.set n PTFalse (pb adt)) (kctxt adt)
                                      (ZMap.set n (AbTCBValid DEAD (-1)) (abtcb adt)) (abq adt))
                      else None
                    | _ => None
                  end                  
                | _ => None
              end
            else None
          else None
        | _ => None
      end.*)

  (** primitve: get the current thread id*)
  Function get_curid_spec (adt: RData): option Z := 
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => Some (cid adt)
      | _ => None
    end.

  (** primitve: set the currect thread id to be *)
  Function set_curid_spec (i: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_proc then
          Some adt {cid: i}
        else None
      | _ => None
    end.


  (** Primtives used for refinement proof*)
  (** primitive: kill the n-th thread, free page table, the kernel context, and the remove the thread from the thread queue*)   
  (*Function thread_kill_spec (adt: RData) (n tid:Z): option RData :=
      match (pe adt, ikern adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if zlt 0 n then
            if zlt n num_proc then
              match (ZMap.get n (pb adt)) with
                | PTTrue => 
                  match ZMap.get n (abtcb adt) with
                    | AbTCBValid st b =>
                      match (ZMap.get b (abq adt)) with 
                        | AbQValid l =>
                          if zeq b (-1) then
                            None
                          else
                            if zeq n (cid adt) then
                              None
                            else
                              if zeq b tid then
                                Some (mkRData (HP adt) (ti adt) (pe adt) (ikern adt) (ihost adt) (AT adt) (nps adt)
                                              (PT adt) (ZMap.set n (real_free_pt (ptpool adt) n) (ptpool adt)) (ipt adt)
                                              (ZMap.set n PTFalse (pb adt)) (kctxt adt) 
                                              (ZMap.set n (AbTCBValid DEAD (-1)) (abtcb adt)) 
                                              (ZMap.set b (AbQValid (remove zeq n l)) (abq adt)) (cid adt))
                              else None
                        | _ => None
                      end              
                    |_ => None
                  end    
                | _ => None
              end
            else None
          else None
        | _ => None
      end.*)

  (** primitive: return the first unused page table (or kctxt) and initialize the kernel context*)   
  Definition thread_spawn_spec (adt: RData) (b: block) (b':block) (ofs': int) id q : option (RData* Z) :=
    let c := ZMap.get id (AC adt) in 
    let i := id * max_children + 1 + Z_of_nat (length (cchildren c)) in
      match (ikern adt, ihost adt, pg adt, ipt adt, cused c, zle_lt 0 i num_id,
             zlt (Z_of_nat (length (cchildren c))) max_children,
             zle_le 0 q (cquota c - cusage c)) with
      | (true, true, true, true, true, left _, left _, left _) =>
        match (ZMap.get num_chan (abq adt)) with 
          | AbQValid l =>
            let ofs := Int.repr ((i + 1) * PgSize -4) in
            let rs := ((ZMap.get i (kctxt adt)) # SP <- (Vptr b ofs)) # RA <- (Vptr b' ofs') in           
            let child := mkContainer q 0 id nil true in
            Some (adt {AC: ZMap.set i child ((AC adt) {usage id := cusage c + q}
                                                      {children id := (i :: cchildren c)})}
                      {kctxt: ZMap.set i rs (kctxt adt)}
                      {abtcb: ZMap.set i (AbTCBValid READY num_chan) (abtcb adt)}
                      {abq: ZMap.set num_chan (AbQValid (i::l)) (abq adt)}, i)
          | _ => None
        end
      | _ => None
      end.

  (** primitve: dequeue*)
  Function thread_wakeup_spec (n: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_chan then
          match ZMap.get n (abq adt) with 
            | AbQValid l =>
              let la := last l num_proc in
              if zeq la num_proc then
                Some adt
              else
                match ZMap.get la (abtcb adt), ZMap.get num_chan (abq adt) with
                  | AbTCBValid _ _, AbQValid l' =>
                    Some adt {abtcb: ZMap.set la (AbTCBValid READY num_chan) (abtcb adt)}
                         {abq: ZMap.set num_chan (AbQValid (la:: l')) 
                                        (ZMap.set n (AbQValid (remove zeq la l)) (abq adt))}
                  | _, _ => None
                end
            | _ => None
          end
        else None
      | _ => None
    end.
  
  Function thread_sched_spec (adt: RData) (rs: KContext) : option (RData*KContext) :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        match ZMap.get num_chan (abq adt) with 
          | AbQValid l =>
            let la := last l num_proc in
            if zeq la num_proc then
              None
            else
              match cused (ZMap.get la (AC adt)), ZMap.get la (abtcb adt) with
                | true, AbTCBValid _ _ =>
                  match (ZMap.get (cid adt) (abtcb adt)) with
                    | AbTCBValid st _ => 
                      if ThreadState_dec st RUN then None
                      else if zeq (cid adt) la then None
                           else Some (adt {kctxt: ZMap.set (cid adt) rs (kctxt adt)}
                                          {abtcb: ZMap.set la (AbTCBValid RUN (-1)) (abtcb adt)}
                                          {abq: ZMap.set num_chan (AbQValid (remove zeq la l)) (abq adt)}
                                          {cid: la} {ti: (Int.zero, snd (ti adt))}, ZMap.get la (kctxt adt))
                    | _ => None
                  end
                | _, _ => None
              end
          | _ => None
        end
      | _ => None
    end.

  (** primitive: initialize the allocation table, set up the paging mechanism, and initialize the page table pool*)   
  Function sched_init_spec (mbi_adr:Z) (adt: RData) : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
             {smspool: real_smspool (smspool adt)}
             {abtcb: ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb (abtcb adt))}
             {abq: real_abq (abq adt)} {cid: 0}
      | _ => None
    end.

  Function thread_yield_spec (adt: RData) (rs: KContext) : option (RData * KContext) :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        match ZMap.get num_chan (abq adt) with 
          | AbQValid l =>
            let la := last l num_proc in
            if zeq la num_proc then None
            else
              Some (adt {kctxt: ZMap.set (cid adt) rs (kctxt adt)}
                        {abtcb: ZMap.set la (AbTCBValid RUN (-1)) 
                                         (ZMap.set (cid adt) (AbTCBValid READY num_chan) (abtcb adt))}
                        {abq: ZMap.set num_chan (AbQValid (remove zeq la ((cid adt) :: l))) (abq adt)}
                        {cid: la} {ti: (Int.zero, snd (ti adt))}
                    , ZMap.get la (kctxt adt))
          | _ => None
        end
      | _ => None
    end.

  Function thread_sleep_spec (adt: RData) (rs: KContext) (n:Z) : option (RData * KContext) :=
    match (pg adt, ikern adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 n num_chan then
          match ZMap.get num_chan (abq adt), ZMap.get n (abq adt) with 
            | AbQValid l, AbQValid l' =>
              let la := last l num_proc in
              if zeq la num_proc then None
              else
                Some (adt {kctxt: ZMap.set (cid adt) rs (kctxt adt)}
                          {abtcb: ZMap.set la (AbTCBValid RUN (-1)) 
                                           (ZMap.set (cid adt) (AbTCBValid SLEEP n) (abtcb adt))}
                          {abq: ZMap.set num_chan (AbQValid (remove zeq la l)) 
                                         (ZMap.set n (AbQValid ((cid adt)::l')) (abq adt))}
                          {cid: la} {ti: (Int.zero, snd (ti adt))}
                      , ZMap.get la (kctxt adt))
            | _, _ => None
          end
        else None
      | _ => None
    end.

End OBJ_Thread.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import GlobIdent.
Require Import AuxLemma.
Require Import INVLemmaThread.
Require Import Observation.

Local Open Scope Z_scope.

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

  Section GET_STATE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_abtcb}.

    Lemma get_state0_exist:
      forall s habd labd i z f,
        get_state0_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> get_state0_spec i labd = Some z.
    Proof.
      unfold get_state0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma get_state0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_state0_spec)
            (id ↦ gensem get_state0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_state0_exist; eauto. reflexivity.
    Qed.      

  End GET_STATE_SIM.

  Section THREAD_YIELD.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_kctxt}.
    Context {re4: relate_impl_abq}.
    Context {re5: relate_impl_cid}.
    Context {re6: relate_impl_abtcb}.
    Context {re7: relate_impl_trapinfo}.

    Local Opaque remove.

    Context `{high: @high_level_invariant_impl_AbQCorrect_range Obs data_ops}.

    Lemma thread_yield_exists:
      forall s habd habd' labd rs rs' rs0 f,
        thread_yield_spec 
          habd ((Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                     #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA)) = Some (habd', rs')
        -> relate_AbData s f habd labd
        -> @high_level_invariant _ _ data_ops habd
        -> (forall reg : PregEq.t,
              val_inject f (Pregmap.get reg rs) (Pregmap.get reg rs0))
        -> exists labd' rs0' ofs, 
             thread_yield_spec 
               labd ((Pregmap.init Vundef)#ESP <- (rs0#ESP)#EDI <- (rs0#EDI)#ESI <- (rs0#ESI)
                                          #EBX <- (rs0#EBX)#EBP <- (rs0#EBP)#RA <- (rs0#RA)) = Some (labd', rs0') 
             /\ relate_AbData s f habd' labd'
             /\ (forall i r,
                   ZtoPreg i = Some r -> val_inject f (rs'#r) (rs0'#r))
             /\ 0 <= ofs < num_proc
             /\ ZMap.get ofs (kctxt labd) = rs0'.
    Proof.
      unfold thread_yield_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto. 
      exploit relate_impl_trapinfo_eq; eauto. intros.
      specialize (high_level_invariant_impl_AbQCorrect_range_eq _ H1).
      revert H. subrewrite. intros.
      subdestruct; inv HQ. 
      exploit last_range_AbQ; eauto. omega. intros Hrange.
      unfold AbQCorrect_range in *. specialize (H refl_equal (last l num_proc)).
      exploit H; eauto. omega. intros. 
      generalize (relate_impl_kctxt_eq _ _ _ _ H0); eauto. intros.
      refine_split'; eauto. 
      - apply relate_impl_trapinfo_update; [| inv H4; auto].
        apply relate_impl_cid_update. 
        apply relate_impl_abq_update. 
        apply relate_impl_abtcb_update. 
        apply relate_impl_kctxt_update; trivial. 
        kctxt_inj_simpl.
      - intros; eapply H10; eauto. 
    Qed.

    Context {mt1: match_impl_kctxt}.
    Context {mt2: match_impl_cid}.
    Context {mt3: match_impl_abq}.
    Context {mt4: match_impl_abtcb}.
    Context {mt5: match_impl_trapinfo}.

    Lemma thread_yield_match:
      forall s d d' m rs rs' f,
        thread_yield_spec d rs = Some (d', rs')
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold thread_yield_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_trapinfo_update.
      eapply match_impl_cid_update.
      eapply match_impl_abq_update.
      eapply match_impl_abtcb_update.
      eapply match_impl_kctxt_update. assumption.
    Qed.

    Context {inv: ThreadScheduleInvariants (data_ops:= data_ops) thread_yield_spec}.
    Context {inv0: ThreadScheduleInvariants (data_ops:= data_ops0) thread_yield_spec}.

    Context {low1: low_level_invariant_impl}.

    Lemma thread_yield_sim :
      forall id,
        sim (crel RData RData) (id ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= id))
            (id ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= id)).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      inv H. inv H0. inv match_extcall_states.
      exploit thread_yield_exists; eauto 1.
      intros (labd' & rs0' & ofs & HP & HM & Hrinj' & HOS' & Hr). subst. subst rs3.
      exploit low_level_invariant_impl_eq; eauto. inversion 1.
      match_external_states_simpl; try (eapply Hrinj'; eapply PregToZ_correct; reflexivity).
      - eapply kctxt_INJECT; try assumption.
      - eapply kctxt_INJECT; try assumption.
      - eapply thread_yield_match; eauto.
    Qed.      

  End THREAD_YIELD.

  Section THREAD_SLEEP.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_kctxt}.
    Context {re4: relate_impl_abq}.
    Context {re5: relate_impl_cid}.
    Context {re6: relate_impl_abtcb}.
    Context {re7: relate_impl_trapinfo}.

    Local Opaque remove.

    Context `{high: @high_level_invariant_impl_AbQCorrect_range Obs data_ops}.

    Lemma thread_sleep_exists:
      forall s habd habd' labd rs rs' rs0 n f,
        thread_sleep_spec 
          habd ((Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                     #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA)) n = Some (habd', rs')
        -> relate_AbData s f habd labd
        -> @high_level_invariant _ _ data_ops habd
        -> (forall reg : PregEq.t,
              val_inject f (Pregmap.get reg rs) (Pregmap.get reg rs0))
        -> exists labd' rs0' ofs, 
             thread_sleep_spec 
               labd ((Pregmap.init Vundef)#ESP <- (rs0#ESP)#EDI <- (rs0#EDI)#ESI <- (rs0#ESI)
                                          #EBX <- (rs0#EBX)#EBP <- (rs0#EBP)#RA <- (rs0#RA)) n = Some (labd', rs0') 
             /\ relate_AbData s f habd' labd'
             /\ (forall i r,
                   ZtoPreg i = Some r -> val_inject f (rs'#r) (rs0'#r))
             /\ 0 <= ofs < num_proc
             /\ ZMap.get ofs (kctxt labd) = rs0'.
    Proof.
      unfold thread_sleep_spec; intros.
      exploit relate_impl_trapinfo_eq; eauto. inversion 1.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto. intros.
      specialize (high_level_invariant_impl_AbQCorrect_range_eq _ H1).
      revert H. subrewrite. intros.
      subdestruct; inv HQ.
      assert (HQ: 0 <= last l 64 < 64).
      {
        eapply last_range_AbQ; eauto. omega. 
      }
      unfold AbQCorrect_range in *. specialize (H refl_equal (last l num_proc)).
      exploit H; eauto. omega. intros. 
      generalize (relate_impl_kctxt_eq _ _ _ _ H0); eauto. intros.
      refine_split'; eauto. 
      - apply relate_impl_trapinfo_update; auto.
        apply relate_impl_cid_update. 
        apply relate_impl_abq_update. 
        apply relate_impl_abtcb_update. 
        apply relate_impl_kctxt_update; trivial. 
        kctxt_inj_simpl.
      - intros. eapply H10; eauto. 
    Qed.

    Context {mt1: match_impl_kctxt}.
    Context {mt2: match_impl_cid}.
    Context {mt3: match_impl_abq}.
    Context {mt4: match_impl_abtcb}.
    Context {mt5: match_impl_trapinfo}.

    Lemma thread_sleep_match:
      forall s d d' m rs rs' n f,
        thread_sleep_spec d rs n = Some (d', rs')
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold thread_sleep_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_trapinfo_update.
      eapply match_impl_cid_update.
      eapply match_impl_abq_update.
      eapply match_impl_abtcb_update.
      eapply match_impl_kctxt_update. assumption.
    Qed.

    Context {inv: ThreadTransferInvariants (data_ops:= data_ops) thread_sleep_spec}.
    Context {inv0: ThreadTransferInvariants (data_ops:= data_ops0) thread_sleep_spec}.

    Context {low1: low_level_invariant_impl}.

    Lemma thread_sleep_sim :
      forall id,
        sim (crel RData RData) (id ↦ primcall_thread_transfer_compatsem thread_sleep_spec)
            (id ↦ primcall_thread_transfer_compatsem thread_sleep_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      inv H. inv H0. inv match_extcall_states.
      exploit thread_sleep_exists; eauto 1.
      intros (labd' & rs0' & ofs & HP & HM & Hrinj' & HOS' & Hr). subst. subst rs3.
      exploit low_level_invariant_impl_eq; eauto. inversion 1.
      match_external_states_simpl; try (eapply Hrinj'; eapply PregToZ_correct; reflexivity).
      - inv H9. inv H3. simpl in *.
        exploit Mem.loadv_inject; try eassumption.
        val_inject_simpl. unfold Pregmap.get.
        intros (v2 & HL & Hv). inv Hv. assumption.
      - eapply kctxt_INJECT; try assumption.
      - eapply kctxt_INJECT; try assumption.
      - eapply thread_sleep_match; eauto.
    Qed.      

  End THREAD_SLEEP.

  (** ** The low level specifications exist*)
  Section SCHEDINIT_SIM.

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
    Context {re10: relate_impl_abtcb}.
    Context {re11: relate_impl_abq}.
    Context {re12: relate_impl_cid}.
    Context {re13: relate_impl_vmxinfo}.
    Context {re14: relate_impl_AC}.

    Lemma sched_init_exist:
      forall s habd habd' labd i f,
        sched_init_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', sched_init_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold sched_init_spec; intros. 
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_idpde_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_smspool_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_cid_update.
      apply relate_impl_abq_update.
      apply relate_impl_abtcb_update.
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
    Context {mt10: match_impl_abtcb}.
    Context {mt11: match_impl_abq}.
    Context {mt12: match_impl_cid}.
    Context {mt13: match_impl_vmxinfo}.
    Context {mt14: match_impl_AC}.

    Lemma sched_init_match:
      forall s d d' m i f,
        sched_init_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold sched_init_spec; intros. subdestruct. inv H. 
      eapply match_impl_cid_update. 
      eapply match_impl_abq_update. 
      eapply match_impl_abtcb_update. 
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

    Context {inv: PreservesInvariants (HD:= data) sched_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) sched_init_spec}.

    Lemma sched_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem sched_init_spec)
            (id ↦ gensem sched_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit sched_init_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply sched_init_match; eauto.
    Qed.

  End SCHEDINIT_SIM.

  Section THREAD_SPAWN.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_kctxt}.
    Context {re4: relate_impl_abtcb}.
    Context {re5: relate_impl_abq}.
    Context {re6: relate_impl_AC}.

    Lemma thread_spawn_exist:
      forall s habd habd' labd b b' ofs' id q n f,
        thread_spawn_spec habd b b' ofs' id q = Some (habd', n)
        -> relate_AbData s f habd labd
        -> find_symbol s STACK_LOC = Some b
        -> (exists id, find_symbol s id = Some b') 
        -> inject_incr (Mem.flat_inj (genv_next s)) f
        -> exists labd', thread_spawn_spec labd b b' ofs' id q = Some (labd', n) 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold thread_spawn_spec. intros until f; intros HP HR Hsys Hsys' Hincr.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto. 
      exploit relate_impl_abtcb_eq; eauto. 
      exploit relate_impl_abq_eq; eauto. 
      exploit relate_impl_AC_eq; eauto; intros.
      revert HP. subrewrite. subdestruct; inv HQ.
      generalize (relate_impl_kctxt_eq _ _ _ _ HR); eauto. intros.      
      refine_split'; trivial.      
      apply relate_impl_abq_update. 
      apply relate_impl_abtcb_update. 
      apply relate_impl_kctxt_update.      
      - apply relate_impl_AC_update; trivial. 
      - kctxt_inj_simpl.
        + destruct Hsys' as [id' Hsys'].
          eapply stencil_find_symbol_inject'; eauto.
        + rewrite Int.add_zero; trivial.
        + eapply stencil_find_symbol_inject'; eauto.
        + rewrite Int.add_zero; trivial.          
        + eapply H4; eauto.
    Qed.        

    Context {mt1: match_impl_kctxt}.
    Context {mt2: match_impl_abtcb}.
    Context {mt3: match_impl_abq}.
    Context {mt4: match_impl_AC}.

    Lemma thread_spawn_match:
      forall s d d' m b b' ofs id q n f,
        thread_spawn_spec d b b' ofs id q = Some (d', n)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold thread_spawn_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_abq_update. 
      eapply match_impl_abtcb_update. 
      eapply match_impl_kctxt_update. 
      eapply match_impl_AC_update. assumption.
    Qed.

    Context {inv: DNewInvariants (data_ops:= data_ops) thread_spawn_spec}.
    Context {inv0: DNewInvariants (data_ops:= data_ops0) thread_spawn_spec}.

    Lemma thread_spawn_sim :
      forall id,
        sim (crel RData RData) (id ↦ dnew_compatsem thread_spawn_spec)
            (id ↦ dnew_compatsem thread_spawn_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      exploit thread_spawn_exist; eauto 1; intros (labd' & HP & HM).
      destruct H8 as [fun_id Hsys]. 
      exploit stencil_find_symbol_inject'; eauto. intros HFB.
      match_external_states_simpl.
      eapply thread_spawn_match; eauto.
    Qed.      

  End THREAD_SPAWN.

  Section THREAD_WAKEUP_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re4: relate_impl_abq}.
    Context {re5: relate_impl_abtcb}.

    Lemma thread_wakeup_exist:
      forall s habd habd' labd i f,
        thread_wakeup_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', thread_wakeup_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold thread_wakeup_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto; intros.
      revert H; subrewrite. 
      subdestruct; inv HQ; refine_split'; trivial.
      eapply relate_impl_abq_update. 
      eapply relate_impl_abtcb_update. assumption.
    Qed.

    Context {mt1: match_impl_abtcb}.
    Context {mt2: match_impl_abq}.

    Lemma thread_wakeup_match:
      forall s d d' m i f,
        thread_wakeup_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold thread_wakeup_spec; intros. subdestruct; inv H; trivial. 
      eapply match_impl_abq_update.
      eapply match_impl_abtcb_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) thread_wakeup_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) thread_wakeup_spec}.

    Lemma thread_wakeup_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem thread_wakeup_spec)
            (id ↦ gensem thread_wakeup_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit thread_wakeup_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply thread_wakeup_match; eauto.
    Qed.

  End THREAD_WAKEUP_SIM.

  Section GET_CID_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_cid}.

    Lemma get_curid_exist:
      forall s habd labd z f,
        get_curid_spec habd = Some z
        -> relate_AbData s f habd labd
        -> get_curid_spec labd = Some z.
    Proof.
      unfold get_curid_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_cid_eq; eauto. intros.
      revert H; subrewrite.
    Qed.

    Lemma get_curid_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem get_curid_spec)
            (id ↦ gensem get_curid_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite get_curid_exist; eauto. reflexivity.
    Qed.      

  End GET_CID_SIM.

  Section ENQUEUE0_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_abq}.
    Context {re4: relate_impl_abtcb}.
    Context {re5: relate_impl_AC}.

    Lemma enqueue0_exist:
      forall s habd habd' labd i z f,
        enqueue0_spec i z habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', enqueue0_spec i z labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold enqueue0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_AC_eq; eauto; intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_abq_update. 
      eapply relate_impl_abtcb_update. assumption.
    Qed.

    Context {mt1: match_impl_abtcb}.
    Context {mt2: match_impl_abq}.

    Lemma enqueue0_match:
      forall s d d' m i z f,
        enqueue0_spec i z d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold enqueue0_spec; intros. subdestruct. inv H. 
      eapply match_impl_abq_update.
      eapply match_impl_abtcb_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) enqueue0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) enqueue0_spec}.

    Lemma enqueue0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem enqueue0_spec)
            (id ↦ gensem enqueue0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit enqueue0_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply enqueue0_match; eauto.
    Qed.

  End ENQUEUE0_SIM.

  Section KCTXT_NEW.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_kctxt}.
    Context {re4: relate_impl_AC}.

    Lemma kctxt_new_exist:
      forall s habd habd' labd b b' ofs' id q n f,
        kctxt_new_spec habd b b' ofs' id q = Some (habd', n)
        -> relate_AbData s f habd labd
        -> find_symbol s STACK_LOC = Some b
        -> (exists id, find_symbol s id = Some b') 
        -> inject_incr (Mem.flat_inj (genv_next s)) f
        -> exists labd', kctxt_new_spec labd b b' ofs' id q = Some (labd', n) 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold kctxt_new_spec. intros until f; intros HP HR  Hsys Hsys' Hincr.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto. 
      exploit relate_impl_AC_eq; eauto. intros.
      revert HP. subrewrite. subdestruct; inv HQ.
      generalize (relate_impl_kctxt_eq _ _ _ _ HR); eauto. intros.
      refine_split'; trivial.
      apply relate_impl_kctxt_update. 
      - apply relate_impl_AC_update; trivial. 
      - kctxt_inj_simpl.
        + destruct Hsys' as [id' Hsys'].
          eapply stencil_find_symbol_inject'; eauto.
        + rewrite Int.add_zero; trivial.
        + eapply stencil_find_symbol_inject'; eauto.
        + rewrite Int.add_zero; trivial.          
        + eapply H2; eauto.
    Qed.        

    Context {mt1: match_impl_kctxt}.
    Context {mt2: match_impl_AC}.

    Lemma kctxt_new_match:
      forall s d d' m b b' ofs id q n f,
        kctxt_new_spec d b b' ofs id q = Some (d', n)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold kctxt_new_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_kctxt_update. 
      eapply match_impl_AC_update. assumption.
    Qed.

    Context {inv: DNewInvariants (data_ops:= data_ops) kctxt_new_spec}.
    Context {inv0: DNewInvariants (data_ops:= data_ops0) kctxt_new_spec}.

    Lemma kctxt_new_sim :
      forall id,
        sim (crel RData RData) (id ↦ dnew_compatsem kctxt_new_spec)
            (id ↦ dnew_compatsem kctxt_new_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      exploit kctxt_new_exist; eauto 1; intros (labd' & HP & HM).
      destruct H8 as [fun_id Hsys]. 
      exploit stencil_find_symbol_inject'; eauto. intros HFB.
      match_external_states_simpl.
      eapply kctxt_new_match; eauto.
    Qed.      

  End KCTXT_NEW.

  Section KCTXT_SWITCH.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_kctxt}.
 
    Lemma kctxt_switch_exists:
      forall s habd habd' labd i1 i2 rs rs' rs0 f,
        kctxt_switch_spec 
          habd i1 i2 ((Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                           #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA)) = Some (habd', rs')
        -> relate_AbData s f habd labd
        -> (forall reg : PregEq.t,
              val_inject f (Pregmap.get reg rs) (Pregmap.get reg rs0))
        -> let rs0' := ZMap.get i2 (kctxt labd) in
           exists labd', kctxt_switch_spec 
                           labd i1 i2 ((Pregmap.init Vundef)#ESP <- (rs0#ESP)#EDI <- (rs0#EDI)#ESI <- (rs0#ESI)
                                                            #EBX <- (rs0#EBX)#EBP <- (rs0#EBP)#RA <- (rs0#RA))
                         = Some (labd', rs0') /\ relate_AbData s f habd' labd'
                         /\ (forall i r,
                               ZtoPreg i = Some r -> val_inject f (rs'#r) (rs0'#r))
                         /\ 0 <= i2 < num_proc.
    Proof.
      unfold kctxt_switch_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto. intros.
      revert H. subrewrite.
      subdestruct; inv HQ. 
      generalize (relate_impl_kctxt_eq _ _ _ _ H0); eauto. intros.
      refine_split'; trivial.
      - apply relate_impl_kctxt_update; trivial. 
        kctxt_inj_simpl.
      - unfold kctxt_inj, Pregmap.get in *; eauto. 
    Qed.

    Context {mt1: match_impl_kctxt}.

    Lemma kctxt_switch_match:
      forall s d d' m i1 i2 rs rs' f,
        kctxt_switch_spec d i1 i2 rs = Some (d', rs')
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold kctxt_switch_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_kctxt_update. assumption.
    Qed.

    Context {inv: KCtxtSwitchInvariants (data_ops:= data_ops) kctxt_switch_spec}.
    Context {inv0: KCtxtSwitchInvariants (data_ops:= data_ops0) kctxt_switch_spec}.

    Context {low1: low_level_invariant_impl}.

    Lemma kctxt_switch_sim :
      forall id,
        sim (crel RData RData) (id ↦ primcall_kctxt_switch_compatsem kctxt_switch_spec)
            (id ↦ primcall_kctxt_switch_compatsem kctxt_switch_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      inv H. inv H0. inv match_extcall_states.
      exploit kctxt_switch_exists; eauto 1. intros (labd' & HP & HM & Hrinj' & HOS'). subst rs3.
      exploit low_level_invariant_impl_eq; eauto. inversion 1.
      match_external_states_simpl; try (eapply Hrinj'; eapply PregToZ_correct; reflexivity).
      - eapply kctxt_INJECT; try assumption.
      - eapply kctxt_INJECT; try assumption.
      - specialize (match_reg EAX). unfold Pregmap.get in *.
        rewrite N_ARU1 in match_reg. inv match_reg. reflexivity.
      - specialize (match_reg EDX). unfold Pregmap.get in *.
        rewrite N_ARU2 in match_reg. inv match_reg. reflexivity.
      - eapply kctxt_switch_match; eauto.
    Qed.

  End KCTXT_SWITCH.

End OBJ_SIM.
