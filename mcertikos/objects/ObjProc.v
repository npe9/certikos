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

Require Import ObjThread.

Section OBJ_PROC.

  Context `{real_params: RealParams}.

  (*
  (** primitve: get the i-th channel info *)
  Function get_chan_info_spec (i: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (chpool adt) with
            | ChanValid ib _ => Some (Int.unsigned ib)
            | _ => None
          end
        else None
      | _ => None
    end.

  Function get_chan_content_spec (i: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (chpool adt) with
            | ChanValid _ ct => Some (Int.unsigned ct)
            | _ => None
          end
        else None
      | _ => None
    end.

  (** primitve: get the i-th channel info *)
  Function init_chan_spec (i pv1 pv2: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          Some adt {chpool: ZMap.set i (ChanValid (Int.repr pv1) (Int.repr pv2)) (chpool adt)}
        else None
      | _ => None
    end.

  (** primitve: set the i-th channel info *)
  Function set_chan_info_spec (i pv: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (chpool adt) with
            | ChanValid _ ct =>
              Some adt {chpool: ZMap.set i (ChanValid (Int.repr pv) ct) (chpool adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  Function set_chan_content_spec (i: Z) (pv: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (chpool adt) with
            | ChanValid ib _ =>
              Some adt {chpool: ZMap.set i (ChanValid ib (Int.repr pv)) (chpool adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  Function is_chan_ready_spec (adt: RData) :option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        match ZMap.get (cid adt) (chpool adt) with
          | ChanValid ib _ => 
            if Int.eq ib Int.zero then
              Some 0
            else Some 1
          | _ => None
        end
      | _ => None
    end.

  (** primitve: set the i-th channel info *)
  Function sendto_chan_spec (i pv: Z) (adt: RData) : option (RData * Z) :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_chan then
          match ZMap.get i (chpool adt) with
            | ChanValid ib ct =>
              if Int.eq ib Int.zero then
                Some (adt {chpool: ZMap.set i (ChanValid Int.one (Int.repr pv)) (chpool adt)}, 1)
              else Some (adt, 0)  
            | _ => None
          end
        else Some (adt, 0)
      | _ => None
    end.

  (** primitve: set the i-th channel info *)
  Function receive_chan_spec (adt: RData): option (RData * Z) :=
    let i := (cid adt) in 
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        match ZMap.get i (chpool adt) with
          | ChanValid ib ct =>
            if Int.eq ib Int.one then
              match thread_wakeup_spec i adt with
                | Some adt' =>
                  Some (adt' {chpool: ZMap.set i (ChanValid Int.zero Int.zero) (chpool adt')}, Int.unsigned ct)
                | _ => None
              end
            else Some (adt, 0)  
          | _ => None
        end
      | _ => None
    end.*)

  (** Primitive: initialize VMCB and other components *)
  Function proc_init_spec (mbi_adr:Z) (adt: RData) : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)} 
             {smspool: real_smspool (smspool adt)}
             {abtcb: ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb (abtcb adt))}
             {abq: real_abq (abq adt)} {cid: 0} {syncchpool: real_syncchpool (syncchpool adt)}
      | _ => None
    end.

  Function save_uctx_spec (adt: RData) (rs: UContext) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        Some adt {uctxt: ZMap.set (cid adt) rs (uctxt adt)}
      | _ => None
    end.
  
  Function restore_uctx_spec (adt : RData): option (RData * UContext) :=
    match (ikern adt, ipt adt, pg adt, ihost adt, init adt) with
      | (true, false, true, true, true) =>
        let uctx0 := ZMap.get (cid adt) (uctxt adt) in
        Some (adt {ikern: false}, uctx0)
      | _ => None
    end.

  Function uctx_get_spec (i ofs: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_proc then
          if is_UCTXT_ptr ofs then
            None
          else
            match (ZMap.get ofs (ZMap.get i (uctxt adt))) with
              | Vint n => Some (Int.unsigned n)
              | _ => None
            end
        else None
      | _ => None
    end.

  Function uctx_set_spec (i ofs n: Z) (adt : RData)  : option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_proc then
          if is_UCTXT_ptr ofs then
            None
          else
            let uctx := ZMap.get i (uctxt adt) in
            let uctx':= ZMap.set ofs (Vint (Int.repr n)) uctx in
            Some adt {uctxt: ZMap.set i uctx' (uctxt adt)}
        else None
      | _ => None
    end.

  Function uctx_set_eip_spec (adt : RData) (i: Z) (b: block) (ofs: int): option RData :=
    match (ikern adt, pg adt, ihost adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i num_proc then
          let uctx := ZMap.get i (uctxt adt) in
          let uctx':= ZMap.set U_EIP (Vptr b ofs) uctx in
          Some adt {uctxt: ZMap.set i uctx' (uctxt adt)}
        else None
      | _ => None
    end.

  (** primitive: save user context *)
  Function proc_exit_user_spec (adt : RData) (rs : UContext) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (false, true, true) =>
        Some adt {ikern: true} {PT: 0} {ipt: true} {uctxt: ZMap.set (cid adt) rs (uctxt adt)}
      | _ => None
    end.

  Function proc_start_user_spec (adt: RData) : option (RData * UContext) :=
    match (ikern adt, pg adt, ihost adt, ipt adt, init adt) with
      | (true, true, true, true, true) =>
        let uctx0 := ZMap.get (cid adt) (uctxt adt) in
        Some (adt {ikern: false} {ipt: false} {PT: cid adt}, uctx0)
      | _ => None
    end.
  
  Definition proc_create_spec (adt: RData) (b b' buc: block) (ofs_uc: int) q : option (RData * Z) :=
    let c := ZMap.get (cid adt) (AC adt) in 
    let i := (cid adt) * max_children + 1 + Z_of_nat (length (cchildren c)) in
    match (ikern adt, ihost adt, pg adt, ipt adt, zle_lt 0 i num_id,
           zlt (Z_of_nat (length (cchildren c))) max_children,
           zle_le 0 q (cquota c - cusage c)) with
      | (true, true, true, true, left _, left _, left _) =>
        match ZMap.get num_chan (abq adt) with
          | AbQValid l =>
            let ofs := Int.repr ((i + 1) * PgSize -4) in
            let rs := ((ZMap.get i (kctxt adt))#SP <- (Vptr b ofs))#RA <- (Vptr b' Int.zero) in
            let child := mkContainer q 0 (cid adt) nil true in
            let uctx0 := ZMap.get i (uctxt adt) in
            let uctx1 := ZMap.set U_SS CPU_GDT_UDATA
                                  (ZMap.set U_CS CPU_GDT_UCODE 
                                            (ZMap.set U_DS CPU_GDT_UDATA
                                                      (ZMap.set U_ES CPU_GDT_UDATA uctx0))) in
            let uctx2 := ZMap.set U_EIP (Vptr buc ofs_uc) 
                                  (ZMap.set U_EFLAGS FL_IF 
                                            (ZMap.set U_ESP (Vint STACK_TOP) uctx1)) in
            Some (adt {AC: ZMap.set i child ((AC adt) {usage (cid adt) := cusage c + q}
                                                      {children (cid adt) := (i :: cchildren c)})}
                      {kctxt: ZMap.set i rs (kctxt adt)}
                      {abtcb: ZMap.set i (AbTCBValid READY num_chan) (abtcb adt)}
                      {abq: ZMap.set num_chan (AbQValid (i::l)) (abq adt)}
                      {uctxt: ZMap.set i uctx2 (uctxt adt)}, i)
          | _ => None
        end
      | _ => None
    end.

End OBJ_PROC.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import AuxLemma.
Require Import GlobIdent.
Require Import LAsmModuleSemAux.
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

  Local Open Scope Z_scope.

  Section PROC_EXIT_USER_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_cid}.
    Context {re6: relate_impl_PT}.

    Lemma proc_exit_user_exist:
      forall s habd habd' labd rs0 f,
        proc_exit_user_spec habd rs0 = Some habd'
        -> relate_AbData s f habd labd
        -> (forall i,
              0<= i < UCTXT_SIZE -> val_inject f (ZMap.get i rs0) (ZMap.get i rs0))
        -> exists labd', proc_exit_user_spec labd rs0 = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold proc_exit_user_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_cid_eq; eauto. intros.
      revert H. subrewrite. intros.
      subdestruct. inv HQ; refine_split'; trivial.
      apply relate_impl_uctxt_update; eauto.
      apply relate_impl_ipt_update; eauto.
      apply relate_impl_PT_update; eauto.
      apply relate_impl_ikern_update; eauto.
      eapply uctxt_inj_set; eauto.
      eapply relate_impl_uctxt_eq; eauto.
    Qed.

    Context {mt1: match_impl_PT}.
    Context {mt2: match_impl_ipt}.
    Context {mt3: match_impl_iflags}.
    Context {mt4: match_impl_uctxt}.

    Lemma proc_exit_user_match:
      forall s d d' m rs0 f,
        proc_exit_user_spec d rs0 = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold proc_exit_user_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_uctxt_update.
      eapply match_impl_ipt_update.
      eapply match_impl_PT_update.
      eapply match_impl_ikern_update. assumption.
    Qed.

    Context {inv: ExitUserInvariants proc_exit_user_spec (data_ops:= data_ops)}.
    Context {inv0: ExitUserInvariants proc_exit_user_spec (data_ops:= data_ops0)}.

    Context {low1: low_level_invariant_impl}.

    Lemma proc_exit_user_sim :
      forall id,
        sim (crel RData RData) (id ↦ primcall_exit_user_compatsem proc_exit_user_spec)
            (id ↦ primcall_exit_user_compatsem proc_exit_user_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      inv H. inv H0. inv match_extcall_states.
      exploit proc_exit_user_exist; eauto 1. 
      - subst uctx4 uctx3 uctx2 uctx1.
        intros. inv_proc. 
        rewrite ZMap.gi. constructor.
      - intros (labd' & HP & HM). 
        refine_split; eauto 1.
        econstructor; eauto 1.
        + reflexivity.
        + eapply reg_val_inject_defined; eauto 1.
        + intros.
          specialize (match_reg ESP); unfold Pregmap.get in match_reg.
          inv match_reg; try congruence.
          specialize (HESP_STACK _ _ (eq_sym H0)).
          replace b1 with b2 by congruence.
          split.
          * apply Ple_trans with b0;
            [ apply HESP_STACK | apply (match_inject_forward _ _ _ H2) ].
          * apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H2 match_inject).
        + exploit (extcall_args_inject (D1:= HDATAOps) (D2:= LDATAOps)); eauto.
          instantiate (3:= d1').
          apply extcall_args_with_data; eauto.
          instantiate (1:= d2).
          intros [?[? Hinv]]. inv_val_inject.
          apply extcall_args_without_data in H; eauto.
        + eapply reg_symbol_inject; eassumption.
        + econstructor; eauto. econstructor; eauto. 
          eapply proc_exit_user_match; eauto.
          val_inject_simpl.
    Qed.

  End PROC_EXIT_USER_SIM.

  Section PROC_START_USER_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_uctxt}.
    Context {re4: relate_impl_cid}.
    Context {re5: relate_impl_init}.
    Context {re6: relate_impl_PT}.

    Lemma proc_start_user_exist:
      forall s habd habd' labd rs0 f,
        proc_start_user_spec habd = Some (habd', rs0)
        -> relate_AbData s f habd labd
        -> 0 <= cid habd < num_proc
        -> exists labd' r'0, proc_start_user_spec labd = Some (labd', r'0)
                         /\ relate_AbData s f habd' labd'
                         /\ (forall i,
                               0<= i < UCTXT_SIZE -> val_inject f (ZMap.get i rs0) (ZMap.get i r'0))
                         /\ r'0 = ZMap.get (cid labd) (uctxt labd)
                         /\ 0 <= cid labd < 64.
    Proof.
      unfold proc_start_user_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_cid_eq; eauto. intros.
      revert H H1 . subrewrite. intros.
      subdestruct. inv HQ; refine_split'; trivial.
      - apply relate_impl_PT_update; eauto.
        apply relate_impl_ipt_update; eauto.
        apply relate_impl_ikern_update; eauto.
      - intros. eapply relate_impl_uctxt_eq; eauto.
    Qed.

    Context {mt1: match_impl_PT}.
    Context {mt2: match_impl_ipt}.
    Context {mt3: match_impl_iflags}.

    Lemma proc_start_user_match:
      forall s d d' m rs0 f,
        proc_start_user_spec d = Some (d', rs0)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold proc_start_user_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_PT_update.
      eapply match_impl_ipt_update.
      eapply match_impl_ikern_update. assumption.
    Qed.

    Context {inv: StartUserInvariants proc_start_user_spec (data_ops:= data_ops)}.
    Context {inv0: StartUserInvariants proc_start_user_spec (data_ops:= data_ops0)}.

    Context {low1: low_level_invariant_impl}.

    Lemma proc_start_user_sim :
      forall id,
        (forall d1, high_level_invariant (CompatDataOps:= data_ops) d1 -> 0 <= cid d1 < num_proc) ->
        sim (crel RData RData) (id ↦ primcall_start_user_compatsem proc_start_user_spec)
            (id ↦ primcall_start_user_compatsem proc_start_user_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      inv H0. inv H1. inv match_extcall_states.
      exploit proc_start_user_exist; eauto 1. 
      eapply H; assumption.
      intros (labd' & r'0 & HP & HM & Hrinj' & Hr & HOS'). subst r'0.
      exploit low_level_invariant_impl_eq; eauto. inversion 1.
      match_external_states_simpl; try (eapply Hrinj'; omega).
      - intros. eapply uctxt_INJECT; try assumption.
      - intros. eapply uctxt_INJECT; try assumption.
      - eapply proc_start_user_match; eauto.
    Qed.

  End PROC_START_USER_SIM.
 
  Section PROC_CREATE.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_kctxt}.
    Context {re4: relate_impl_abtcb}.
    Context {re5: relate_impl_abq}.
    Context {re6: relate_impl_uctxt}.
    Context {re7: relate_impl_AC}.
    Context {re8: relate_impl_cid}.

    Lemma proc_create_exist:
      forall s habd habd' labd b b' buc ofs' q n f,
        proc_create_spec habd b buc b' ofs' q = Some (habd', n)
        -> relate_AbData s f habd labd
        -> find_symbol s STACK_LOC = Some b
        -> find_symbol s proc_start_user = Some buc
        -> (exists id, find_symbol s id = Some b') 
        -> inject_incr (Mem.flat_inj (genv_next s)) f
        -> exists labd', proc_create_spec labd b buc b' ofs' q = Some (labd', n) 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold proc_create_spec. intros until f; intros HP HR Hsys Hsys' Hsys'' Hincr.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto. 
      exploit relate_impl_abtcb_eq; eauto. 
      exploit relate_impl_abq_eq; eauto. 
      exploit relate_impl_AC_eq; eauto. 
      exploit relate_impl_cid_eq; eauto. intros.
      revert HP. subrewrite. subdestruct; inv HQ.
      generalize (relate_impl_kctxt_eq _ _ _ _ HR); eauto. intros.
      generalize (relate_impl_uctxt_eq _ _ _ _ HR); eauto. intros.
      refine_split'; trivial.
      apply relate_impl_uctxt_update. 
      apply relate_impl_abq_update. 
      apply relate_impl_abtcb_update. 
      apply relate_impl_kctxt_update. 
      apply relate_impl_AC_update; trivial. 
      - kctxt_inj_simpl.
        + eapply stencil_find_symbol_inject'; eauto.
        + rewrite Int.add_zero; trivial.
        + eapply stencil_find_symbol_inject'; eauto.
        + rewrite Int.add_zero; trivial.
        + eapply H5; eauto.
      - eapply uctxt_inj_set; eauto.
        intros. inv_proc.
        econstructor; eauto.
        destruct Hsys'' as [fun_id Hsys''].
        eapply stencil_find_symbol_inject'; eauto.
        rewrite Int.add_zero; trivial.
    Qed.        

    Context {mt1: match_impl_kctxt}.
    Context {mt2: match_impl_abtcb}.
    Context {mt3: match_impl_abq}.
    Context {mt4: match_impl_uctxt}.
    Context {mt5: match_impl_AC}.
    Context {mt6: match_impl_cid}.

    Lemma proc_create_match:
      forall s d d' m b buc b' ofs q n f,
        proc_create_spec d b buc b' ofs q = Some (d', n)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold proc_create_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_uctxt_update. 
      eapply match_impl_abq_update. 
      eapply match_impl_abtcb_update. 
      eapply match_impl_kctxt_update. 
      eapply match_impl_AC_update. assumption.
    Qed.

    Context {inv: PCreateInvariants (data_ops:= data_ops) proc_create_spec}.
    Context {inv0: PCreateInvariants (data_ops:= data_ops0) proc_create_spec}.

    Lemma proc_create_sim :
      forall id,
        sim (crel RData RData) (id ↦ proc_create_compatsem proc_create_spec)
            (id ↦ proc_create_compatsem proc_create_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. simpl; intros.
      exploit proc_create_exist; eauto 1; intros (labd' & HP & HM).
      destruct H9 as [fun_id Hsys].
      exploit stencil_find_symbol_inject'; eauto. intros HFB.
      destruct H10 as [fun_id' Hsys'].
      exploit stencil_find_symbol_inject'; eauto. intros HFB'.
      match_external_states_simpl.
      eapply proc_create_match; eauto.
    Qed.      

  End PROC_CREATE.

  Section UCTX_GET_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_uctxt}.
    Context {re3: relate_impl_ipt}.

    Lemma uctx_get_exist:
      forall s habd labd i1 i2 z f,
        uctx_get_spec i1 i2 habd = Some z
        -> relate_AbData s f habd labd
        -> uctx_get_spec i1 i2 labd = Some z.
    Proof.
      unfold uctx_get_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      apply is_UCTXT_ptr_range in Hdestruct4.
      exploit relate_impl_uctxt_eq; eauto.
      rewrite Hdestruct5. intros HV. inv HV.
      assumption.
    Qed.

    Lemma uctx_get_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem uctx_get_spec)
            (id ↦ gensem uctx_get_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite uctx_get_exist; eauto. reflexivity.
    Qed.

  End UCTX_GET_SIM.

  Section UCTX_SET_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_uctxt}.

    Lemma uctx_set_exist:
      forall s habd habd' labd z1 z2 i f,
        uctx_set_spec i z1 z2 habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', uctx_set_spec i z1 z2 labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold uctx_set_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto. intros.
      revert H. subrewrite.
      subdestruct. inv HQ; refine_split'; trivial.
      apply relate_impl_uctxt_update; eauto.
      eapply uctxt_inj_set; eauto.
      - eapply relate_impl_uctxt_eq; eauto.
      - intros. inv_proc.
        eapply relate_impl_uctxt_eq; eauto.        
    Qed.

    Context {mt1: match_impl_uctxt}.

    Lemma uctx_set_match:
      forall s d d' m z1 z2 i f,
        uctx_set_spec i z1 z2 d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold uctx_set_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_uctxt_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) uctx_set_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) uctx_set_spec}.

    Lemma uctx_set_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem uctx_set_spec)
            (id ↦ gensem uctx_set_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit uctx_set_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply uctx_set_match; eauto.
    Qed.

  End UCTX_SET_SIM.

  (*Section IS_CHAN_READY_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_chpool}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_cid}.

    Lemma is_chan_ready_exist:
      forall s habd labd z f,
        is_chan_ready_spec habd = Some z
        -> relate_AbData s f habd labd
        -> is_chan_ready_spec labd = Some z.
    Proof.
      unfold is_chan_ready_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_chpool_eq; eauto; intros.
      revert H; subrewrite.
    Qed.

    Lemma is_chan_ready_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem is_chan_ready_spec)
            (id ↦ gensem is_chan_ready_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite is_chan_ready_exist; eauto. reflexivity.
    Qed.

  End IS_CHAN_READY_SIM.

  Section SENDTO_CHAN_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_chpool}.

    Lemma sendto_chan_exist:
      forall s habd habd' labd z1 z2 i f,
        sendto_chan_spec z1 z2 habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', sendto_chan_spec z1 z2 labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold sendto_chan_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_chpool_eq; eauto. intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      apply relate_impl_chpool_update. assumption.
    Qed.

    Context {mt1: match_impl_chpool}.

    Lemma sendto_chan_match:
      forall s d d' m z1 z2 i f,
        sendto_chan_spec z1 z2 d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold sendto_chan_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_chpool_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) sendto_chan_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) sendto_chan_spec}.

    Lemma sendto_chan_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem sendto_chan_spec)
            (id ↦ gensem sendto_chan_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit sendto_chan_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply sendto_chan_match; eauto.
    Qed.

  End SENDTO_CHAN_SIM.*)

  Section PROCINIT_SIM.

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
    Context {re13: relate_impl_syncchpool}.
    Context {re14: relate_impl_vmxinfo}.
    Context {re15: relate_impl_AC}.

    Lemma proc_init_exist:
      forall s habd habd' labd i f,
        proc_init_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', proc_init_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold proc_init_spec; intros. 
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_idpde_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_abq_eq; eauto.
      exploit relate_impl_abtcb_eq; eauto.
      exploit relate_impl_syncchpool_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_smspool_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_syncchpool_update.
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
    Context {mt13: match_impl_syncchpool}.
    Context {mt14: match_impl_vmxinfo}.
    Context {mt15: match_impl_AC}.

    Lemma proc_init_match:
      forall s d d' m i f,
        proc_init_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold proc_init_spec; intros. subdestruct. inv H. 
      eapply match_impl_syncchpool_update. 
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

    Context {inv: PreservesInvariants (HD:= data) proc_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) proc_init_spec}.

    Lemma proc_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem proc_init_spec)
            (id ↦ gensem proc_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit proc_init_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply proc_init_match; eauto.
    Qed.

  End PROCINIT_SIM.

  (*Section RECEIVE_CHAN_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re4: relate_impl_abq}.
    Context {re5: relate_impl_abtcb}.
    Context {re6: relate_impl_cid}.
    Context {re7: relate_impl_chpool}.

    Lemma receive_chan_exist:
      forall s habd habd' labd i f,
        receive_chan_spec habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', receive_chan_spec labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold receive_chan_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_cid_eq; eauto.
      exploit relate_impl_chpool_eq; eauto; intros.
      revert H; subrewrite. 
      subdestruct; inv HQ; try (refine_split'; trivial; fail).
      exploit thread_wakeup_exist; eauto. intros (labd' & HP & HR).
      exploit relate_impl_chpool_eq; eauto; intros.
      subrewrite'. refine_split'; trivial.      
      eapply relate_impl_chpool_update. assumption.
    Qed.

    Context {mt1: match_impl_abtcb}.
    Context {mt2: match_impl_abq}.
    Context {mt3: match_impl_chpool}.

    Lemma receive_chan_match:
      forall s d d' m i f,
        receive_chan_spec d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold receive_chan_spec; intros. subdestruct; inv H; trivial. 
      eapply match_impl_chpool_update. 
      eapply thread_wakeup_match; eauto.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) receive_chan_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) receive_chan_spec}.

    Lemma receive_chan_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem receive_chan_spec)
            (id ↦ gensem receive_chan_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit receive_chan_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply receive_chan_match; eauto.
    Qed.

  End RECEIVE_CHAN_SIM.*)

End OBJ_SIM.
