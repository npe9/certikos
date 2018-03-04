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
Require Import CalRealInitPTE.
Section OBJ_LMM.

  (** abstraction of container_alloc to LAT *)
  Function alloc_spec (id: Z) (adt: RData): option (RData * Z) := 
    let c := ZMap.get id (AC adt) in
    match (ikern adt, pg adt, ihost adt, ipt adt, cused c) with
      | (true, true, true, true, true) =>
        if cusage c <? cquota c then
          let cur := mkContainer (cquota c) (cusage c + 1) (cparent c)
                                 (cchildren c) (cused c) in
          match Lfirst_free (LAT adt) (nps adt) with
            | inleft (exist i _) => 
              Some (adt {LAT: ZMap.set i (LATValid true ATNorm nil) (LAT adt)}
                        {pperm: ZMap.set i PGAlloc (pperm adt)}
                        {AC: ZMap.set id cur (AC adt)}, i)
            | _ => None
          end
        else Some (adt, 0)
      | _ => None
    end.

  Section INSERT.
    
    Function ptInsertPTE0_spec (nn vadr padr: Z) (p: PTPerm) (adt: RData): option RData :=
      match (ikern adt, ihost adt, pg adt, ipt adt, pt_Arg nn vadr padr (nps adt)) with
        | (true, true, true, true, true) =>
          let pt := ZMap.get nn (ptpool adt) in
          let pdi := PDX vadr in
          let pti := PTX vadr in
          match (ZMap.get pdi pt, ZMap.get padr (LAT adt), ZMap.get padr (pperm adt))  with
            | (PDEValid pi pdt, LATValid true ATNorm l, PGAlloc) =>
              match ZMap.get pti pdt with
                | PTEValid _ _ => None
                | _ =>
                  let pdt':= ZMap.set pti (PTEValid padr p) pdt in
                  let pt' := ZMap.set pdi (PDEValid pi pdt') pt in
                  if zle_lt 0 (Z.of_nat (length l)) Int.max_unsigned then
                    Some adt {LAT: ZMap.set padr (LATValid true ATNorm (LATO nn pdi pti::l)) (LAT adt)}
                         {ptpool: ZMap.set nn pt' (ptpool adt)}
                  else None
              end
            | _ => None
          end
        | _ => None
      end.

    Function ptAllocPDE0_spec (nn vadr: Z) (adt: RData): option (RData * Z) :=
      let pdi := PDX vadr in
      let c := ZMap.get nn (AC adt) in
      match (ikern adt, ihost adt, pg adt, ipt adt, cused c, pt_Arg' nn vadr) with
        | (true, true, true, true, true, true) =>
          match ZMap.get pdi (ZMap.get nn (ptpool adt)) with
            | PDEUnPresent => 
              if cusage c <? cquota c then
                let cur := mkContainer (cquota c) (cusage c + 1) (cparent c)
                                       (cchildren c) (cused c) in
                match Lfirst_free (LAT adt) (nps adt) with
                  | inleft (exist pi _) => 
                    Some (adt {HP: FlatMem.free_page pi (HP adt)}
                              {LAT: ZMap.set pi (LATValid true ATNorm nil) (LAT adt)}
                              {pperm: ZMap.set pi (PGHide (PGPMap nn pdi)) (pperm adt)}
                              {ptpool: (ZMap.set nn (ZMap.set pdi (PDEValid pi real_init_PTE) 
                                                              (ZMap.get nn (ptpool adt))) (ptpool adt))}
                              {AC: ZMap.set nn cur (AC adt)}
                          , pi)
                  | _ => None
                end
              else Some (adt, 0)
            | _ => None
          end
        | _ => None
      end.

    (** primitve: set the n-th page table with virtual address vadr to (padr + perm)*)    
    (** The pt insert at this layer, is slightly different from the one at MPTComm.
       [0th page map] has been reserved for the kernel thread, which couldn't be modified after the initialization*)
    Function ptInsert0_spec (nn vadr padr perm: Z) (adt: RData) : option (RData * Z) :=
      match (ikern adt, ihost adt, ipt adt, pg adt, pt_Arg nn vadr padr (nps adt)) with
        | (true, true, true, true, true) =>
          match ZtoPerm perm with
            | Some p => 
              let pt := ZMap.get nn (ptpool adt) in
              let pdi := PDX vadr in
              let pti := PTX vadr in
              match ZMap.get pdi pt with
                | PDEValid pi pdt => 
                  match ptInsertPTE0_spec nn vadr padr p adt with 
                    | Some adt' => Some (adt', 0)
                    | _ => None
                  end
                | PDEUnPresent => 
                  match ptAllocPDE0_spec nn vadr adt with
                    | Some (adt', v) =>
                      if zeq v 0 then Some (adt', MagicNumber)
                      else 
                        match ptInsertPTE0_spec nn vadr padr p adt' with
                          | Some adt'' => Some (adt'', v)
                          | _ => None
                        end
                    | _ => None
                  end
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end.

  End INSERT.

  Function ptResv_spec (n vadr perm: Z) (adt: RData): option (RData * Z) :=
    match alloc_spec n adt with
      | Some (abd', b) =>
        if zeq b 0 then Some (adt, MagicNumber)
        else ptInsert0_spec n vadr b perm abd'
      | _ => None
    end.

  Function ptResv2_spec (n vadr perm n' vadr' perm': Z) (adt: RData): option (RData * Z) :=
    match alloc_spec n adt with
      | Some (abd', b) =>
        if zeq b 0 then Some (adt, MagicNumber)
        else
          match ptInsert0_spec n vadr b perm abd' with
            | Some (abd'', v) => 
              if zeq v MagicNumber then Some (abd'', MagicNumber)
              else ptInsert0_spec n' vadr' b perm' abd''
            | _ => None
          end
      | _ => None
    end.

End OBJ_LMM.

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

  Section ALLOC_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_AC}.

    Lemma alloc_exist:
      forall s habd habd' labd i id f,
        alloc_spec id habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', alloc_spec id labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold alloc_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_init_eq; eauto; intros.
      exploit relate_impl_LAT_eq; eauto; intros.
      exploit relate_impl_nps_eq; eauto; intros.
      exploit relate_impl_pperm_eq; eauto; intros.
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_AC_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      apply relate_impl_AC_update.
      apply relate_impl_pperm_update.
      apply relate_impl_LAT_update. assumption.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_AC}.

    Lemma alloc_match:
      forall s d d' m i id f,
        alloc_spec id d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold alloc_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_AC_update.
      eapply match_impl_pperm_update.
      eapply match_impl_LAT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) alloc_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) alloc_spec}.

    Lemma alloc_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem alloc_spec)
            (id ↦ gensem alloc_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit alloc_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply alloc_match; eauto.
    Qed.

  End ALLOC_SIM.

  Section PT_INSERT_PTE0_SIM.
    Context {re1: relate_impl_iflags}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.

    Lemma ptInsertPTE0_exist:
      forall s habd habd' labd n v pa pe f,
        ptInsertPTE0_spec n v pa pe habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptInsertPTE0_spec n v pa pe labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptInsertPTE0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_pperm_eq; eauto.
      intros. revert H.
      subrewrite. subdestruct; inv HQ; refine_split'; trivial;
      apply relate_impl_ptpool_update;
      apply relate_impl_LAT_update; assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_LAT}.

    Lemma ptInsertPTE0_match:
      forall s n v pa pe d d' m f,
        ptInsertPTE0_spec n v pa pe d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptInsertPTE0_spec; intros. 
      subdestruct; inv H; trivial;
      eapply match_impl_ptpool_update;
      eapply match_impl_LAT_update;
      assumption.
    Qed.

  End PT_INSERT_PTE0_SIM.    

  Section PT_ALLOC_PDE0_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_HP}.
    Context {re9: relate_impl_AC}.

    Lemma ptAllocPDE0_exist:
      forall s habd habd' labd i n v f,
        ptAllocPDE0_spec n v habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', ptAllocPDE0_spec n v labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptAllocPDE0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_pperm_eq; eauto.
      exploit relate_impl_AC_eq; eauto.
      intros. revert H.
      subrewrite. subdestruct; inv HQ;
      refine_split'; trivial.
      apply relate_impl_AC_update.
      apply relate_impl_ptpool_update.
      apply relate_impl_pperm_update.
      apply relate_impl_LAT_update.
      apply relate_impl_HP_update.
      assumption.
      apply FlatMem.free_page_inj'.
      eapply relate_impl_HP_eq; eauto.
    Qed.

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_pperm}.
    Context {mt4: match_impl_HP}.
    Context {mt5: match_impl_AC}.

    Lemma ptAllocPDE0_match:
      forall s n v i d d' m f,
        ptAllocPDE0_spec n v d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptAllocPDE0_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_AC_update.
      eapply match_impl_ptpool_update.
      eapply match_impl_pperm_update.
      eapply match_impl_LAT_update.
      eapply match_impl_HP_update.
      assumption.
    Qed.

    (*Context {inv: PreservesInvariants (HD:= data) ptAllocPDE0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptAllocPDE0_spec}.
    
    Lemma ptAllocPDE0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptAllocPDE0_spec)
            (id ↦ gensem ptAllocPDE0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ptAllocPDE0_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply ptAllocPDE0_match; eauto.
    Qed.*)
    
  End PT_ALLOC_PDE0_SIM.

  Section PT_INSERT0_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ptpool}.
    Context {re3: relate_impl_pperm}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_LAT}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_HP}.
    Context {re8: relate_impl_AC}.

    Lemma ptInsert0_exist:
      forall s habd habd' labd i n v pa pe f,
        ptInsert0_spec n v pa pe habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', ptInsert0_spec n v pa pe labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptInsert0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_nps_eq; eauto; intros.
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_ptpool_eq; eauto; intros.
      revert H; subrewrite; subdestruct.
      - exploit ptInsertPTE0_exist; eauto.
        intros (labd' & HptInsert0' & Hre).
        subrewrite'.
        inv HQ; refine_split'; trivial.
      - exploit ptAllocPDE0_exist; eauto.
        intros (labd' & HptInsert0' & Hre).
        subrewrite'.
        inv HQ; refine_split'; trivial.
      - exploit ptAllocPDE0_exist; eauto.
        intros (labd' & HptInsert0' & Hre).
        subrewrite'.
        exploit ptInsertPTE0_exist; eauto.
        intros (labd'0 & HptInsert0'' & Hre').
        subrewrite'.
        inv HQ; refine_split'; trivial.
    Qed.
    
    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_ptpool}.
    Context {mt4: match_impl_HP}.
    Context {mt5: match_impl_AC}.

    Lemma ptInsert0_match:
      forall s n v pa pe d d' m i f,
        ptInsert0_spec n v pa pe d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptInsert0_spec; intros. subdestruct; inv H; trivial.
      - eapply ptInsertPTE0_match; eauto.
      - eapply ptAllocPDE0_match; eauto.
      - eapply ptInsertPTE0_match; eauto.
        eapply ptAllocPDE0_match; eauto.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ptInsert0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptInsert0_spec}.

    Lemma ptInsert0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptInsert0_spec)
            (id ↦ gensem ptInsert0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ptInsert0_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply ptInsert0_match; eauto.
    Qed.
    
  End PT_INSERT0_SIM.

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
        intros (? & ? & ?). revert H.
        exploit ptInsert0_exist; eauto.
        intros (? & ? & ?). intros.
        exploit ptInsert0_exist; eauto.
        intros (? & ? & ?). 
        subrewrite'. refine_split'; trivial.
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

  Section PT_RESV_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_HP}.
    Context {re9: relate_impl_AC}.

    Lemma ptResv_exist:
      forall s habd habd' labd i n v p f,
        ptResv_spec n v p habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', ptResv_spec n v p labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptResv_spec; intros.
      subdestruct. destruct p0.
      - exploit alloc_exist; eauto.
        intros (? & ? & ?).
        subrewrite'. inv H. refine_split'; trivial.
      - exploit alloc_exist; eauto.
        intros (? & ? & ?).
        exploit ptInsert0_exist; eauto.
        intros (? & ? & ?).
        subrewrite'. inv H. refine_split'; trivial.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_ptpool}.
    Context {mt4: match_impl_HP}.
    Context {mt5: match_impl_AC}.

    Lemma ptResv_match:
      forall s d d' m i n v p f,
        ptResv_spec n v p d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptResv_spec; intros. subdestruct; inv H; trivial.
      eapply ptInsert0_match; eauto.
      eapply alloc_match; eauto.
    Qed.
    
    Context {inv: PreservesInvariants (HD:= data) ptResv_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptResv_spec}.

    Lemma ptResv_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptResv_spec)
            (id ↦ gensem ptResv_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ptResv_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply ptResv_match; eauto.
    Qed.

  End PT_RESV_SIM.

End OBJ_SIM.