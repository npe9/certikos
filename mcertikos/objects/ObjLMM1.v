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

Section OBJ_LMM.

  Context `{real_params: RealParams}.

  Function pfree_spec (i: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, pg adt, ipt adt) with
      | (true, true, true, true) =>
        if zle_lt 0 i maxpage then
          match (ZMap.get i (LAT adt), ZMap.get i (pperm adt)) with
            | (LATValid true ATNorm nil, PGAlloc)  =>
              Some adt {LAT: ZMap.set i (LATValid false ATNorm nil) (LAT adt)}
                   {pperm: ZMap.set i PGUndef (pperm adt)}
            | _ => None
          end
        else None
      | _ => None
    end.

  Function setPT_spec (n: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, ipt adt) with
      | (true, true, false) =>
        if zle_lt 0 n num_proc then
          Some adt {PT: n}
        else None
      | _ => None
    end.

  (** primitve: in the kernel mode, after switching to kernel's page table, set ipt to true*)
  Function ptin_spec (adt: RData): option RData :=
    match (ipt adt, ikern adt, ihost adt) with
      | (false, true, true) => 
        if zeq (PT adt) 0 then
          Some adt {ipt: true}
        else None
      | _ => None
    end.

  Remark Freeable_PTE_dec' (pte: PTE):
    {forall i, 0 <= i < PTX (Int.max_unsigned) + 1 -> ZMap.get i pte = PTEUnPresent}
    + {~(forall i, 0 <= i < PTX (Int.max_unsigned) + 1 -> ZMap.get i pte = PTEUnPresent)}.
  Proof.
    eapply general_range_dec.
    intros. destruct (ZMap.get i pte).
    - right; red; intros; congruence.
    - left; trivial.
    - right; red; intros; congruence.
  Qed.

  Remark Freeable_PTE_dec (pte: PTE):
    {forall i, 0 <= i <= PTX (Int.max_unsigned) -> ZMap.get i pte = PTEUnPresent}
    + {~ (forall i, 0 <= i <= PTX (Int.max_unsigned) -> ZMap.get i pte = PTEUnPresent)}.
  Proof.
    pose proof (Freeable_PTE_dec' pte) as HR.
    inv HR.
    - left. intros. apply H; eauto. omega.
    - right. red; intros. elim H; intros.
      apply H0; eauto. omega.
  Defined.    
  
  Function ptFreePDE0_spec (n vadr: Z) (adt: RData): option RData :=
    let pdi := PDX vadr in
    match (ikern adt, ihost adt, pg adt, ipt adt, pt_Arg' n vadr) with
      | (true, true, true, true, true) =>
        match ZMap.get pdi (ZMap.get n (ptpool adt)) with
          | PDEValid pi pte =>
            if Freeable_PTE_dec pte then
              let pt':= ZMap.set pdi PDEUnPresent (ZMap.get n (ptpool adt)) in
              Some adt {LAT: ZMap.set pi (LATValid false ATNorm nil) (LAT adt)}
                   {pperm: ZMap.set pi PGUndef (pperm adt)}
                   {ptpool: ZMap.set n pt' (ptpool adt)}
            else None
          | _ => None
        end
      | _ => None
    end.

  (** primitve: set the n-th page table with virtual address vadr to unpresent*)    
  Function ptRmv0_spec (n vadr: Z) (adt: RData): option (RData * Z) :=
    match (ikern adt, ihost adt, ipt adt, pg adt, pt_Arg' n vadr) with
      | (true, true, true, true, true) =>
        let pt:= ZMap.get n (ptpool adt) in
        let pdi := PDX vadr in
        match ZMap.get pdi pt with
          | PDEValid pi pdt =>
            let pti := PTX vadr in
            match ZMap.get pti pdt with
              | PTEValid padr _ =>
                match ZMap.get padr (LAT adt) with
                  | LATValid true ATNorm l =>
                    let pdt':= ZMap.set pti PTEUnPresent pdt in
                    let pt' := ZMap.set pdi (PDEValid pi pdt') pt in
                    if zle (Z.of_nat (length l)) Int.max_unsigned then
                      Some (adt {LAT: ZMap.set padr (LATValid true ATNorm (Lremove (LATO n pdi pti) l)) (LAT adt)}
                                {ptpool: ZMap.set n pt' (ptpool adt)} , padr)
                    else None
                  | _ => None
                end
              | PTEUnPresent => Some (adt, 0)
              | _ => None
            end
          | _ => None
        end
      | _ => None
    end.

  Function pt_init_spec (mbi_adr:Z) (adt: RData): option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
      | _ => None
    end.

  Function pt_new_spec (id q: Z) (adt: RData): option (RData * Z) :=
    let c := ZMap.get id (AC adt) in 
    let i := id * max_children + 1 + Z_of_nat (length (cchildren c)) in
    match (ikern adt, ihost adt, pg adt, ipt adt, cused c, zle_lt 0 i num_id,
           zlt (Z_of_nat (length (cchildren c))) max_children,
           zle_le 0 q (cquota c - cusage c)) with
    | (true, true, true, true, true, left _, left _, left _) =>
         let child := mkContainer q 0 id nil true in
           Some (adt {AC: ZMap.set i child ((AC adt) {usage id := cusage c + q}
                                                     {children id := (i :: cchildren c)})}, i)
    | _ => None
      end.

  (*
    (** primitive: function to free a used page table at the higher layer, only used in the refinement proof*)   
    Function pt_free_spec (adt: RData) (n:Z): option RData :=
      match (pe adt, ikern adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if zlt 0 n then
            if zlt n num_proc then
              match (ZMap.get n (pb adt)) with
                | PTTrue => 
                  Some (mkRData (HP adt) (ti adt) (pe adt) (ikern adt) (ihost adt) 
                                (AT adt) (nps adt) (PT adt) (ZMap.set n (real_free_pt (ptpool adt) n) (ptpool adt)) (ipt adt)
                                (ZMap.set n PTFalse (pb adt)))
                | _ => None
              end
            else None
          else None
        | _ => None
      end.*)

  (** primitive: initialize the allocation table, all the page tables, 
     set the [0th page table] as the kernel's page table and enable paging*)   
  Function pmap_init_spec (mbi_adr:Z) (adt: RData): option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
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

  Section PT_NEW_SIM.
    
    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ipt}.
    Context {re3: relate_impl_AC}.

    Lemma pt_new_exist:
      forall s habd habd' labd id q i f,
        pt_new_spec id q habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', pt_new_spec id q labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold pt_new_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_AC_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.   
      apply relate_impl_AC_update. assumption.
    Qed.

    Context {mt1: match_impl_AC}.
    
    Lemma pt_new_match:
      forall s d d' m id q i f,
        pt_new_spec id q d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold pt_new_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_AC_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) pt_new_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) pt_new_spec}.

    Lemma pt_new_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem pt_new_spec)
            (id ↦ gensem pt_new_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit pt_new_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply pt_new_match; eauto.
    Qed.
    
  End PT_NEW_SIM.

  Section PT_FREE_PDE0_SIM.
    Context {re1: relate_impl_iflags}.
    Context {re3: relate_impl_LAT}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.

    Lemma ptFreePDE0_exist:
      forall s n v habd habd' labd f,
        ptFreePDE0_spec n v habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptFreePDE0_spec n v labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptFreePDE0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ptpool_eq; eauto; intros.
      exploit relate_impl_LAT_eq; eauto; intros.
      exploit relate_impl_ipt_eq; eauto; intros.
      exploit relate_impl_pperm_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      apply relate_impl_ptpool_update.
      apply relate_impl_pperm_update.
      apply relate_impl_LAT_update.
      assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_pperm}.
    Context {mt3: match_impl_LAT}.

    Lemma ptFreePDE0_match:
      forall s n v d d' m f,
        ptFreePDE0_spec n v d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptFreePDE0_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_ptpool_update.
      eapply match_impl_pperm_update.
      eapply match_impl_LAT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ptFreePDE0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptFreePDE0_spec}.

    Lemma ptFreePDE0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptFreePDE0_spec)
            (id ↦ gensem ptFreePDE0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ptFreePDE0_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply ptFreePDE0_match; eauto.
    Qed.

  End PT_FREE_PDE0_SIM.

  Section PT_RMV0_SIM.
    Context {re1: relate_impl_iflags}.
    Context {re3: relate_impl_LAT}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.

    Lemma ptRmv0_exist:
      forall s n v habd habd' labd i f,
        ptRmv0_spec n v habd = Some (habd', i)
        -> relate_AbData s f habd labd
        -> exists labd', ptRmv0_spec n v labd = Some (labd', i)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptRmv0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ptpool_eq; eauto; intros.
      exploit relate_impl_LAT_eq; eauto; intros.
      exploit relate_impl_ipt_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      apply relate_impl_ptpool_update.
      apply relate_impl_LAT_update.
      assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_pperm}.
    Context {mt3: match_impl_LAT}.

    Lemma ptRmv0_match:
      forall s n v d d' m f i,
        ptRmv0_spec n v d = Some (d', i)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptRmv0_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_ptpool_update.
      eapply match_impl_LAT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ptRmv0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptRmv0_spec}.

    Lemma ptRmv0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptRmv0_spec)
            (id ↦ gensem ptRmv0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ptRmv0_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply ptRmv0_match; eauto.
    Qed.
    
  End PT_RMV0_SIM.

  Section PMAP_INIT_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_init}.
    Context {re5: relate_impl_nps}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_idpde}.
    Context {re10: relate_impl_vmxinfo}.
    Context {re11: relate_impl_AC}.
    
    Lemma pmap_init_exist:
      forall s (habd habd' labd: RData) (n:Z) f,
        pmap_init_spec n habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', pmap_init_spec n labd = Some labd'
                         /\ relate_AbData s f habd' labd'.    
    Proof.
      unfold pmap_init_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_idpde_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
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

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_idpde}.
    Context {mt4: match_impl_PT}.
    Context {mt5: match_impl_init}.
    Context {mt6: match_impl_nps}.
    Context {mt7: match_impl_iflags}.
    Context {mt8: match_impl_vmxinfo}.
    Context {mt9: match_impl_AC}.

    Lemma pmap_init_match:
      forall s n d d' m f,
        pmap_init_spec n d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold pmap_init_spec; intros. subdestruct; inv H; trivial.
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

    Context {inv: PreservesInvariants (HD:= data) pmap_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) pmap_init_spec}.

    Lemma pmap_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem pmap_init_spec)
            (id ↦ gensem pmap_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit pmap_init_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply pmap_init_match; eauto.
    Qed.

  End PMAP_INIT_SIM.

  Section PT_INIT_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_init}.
    Context {re5: relate_impl_nps}.
    Context {re6: relate_impl_ipt}.
    Context {re7: relate_impl_ptpool}.
    Context {re8: relate_impl_idpde}.
    Context {re9: relate_impl_vmxinfo}.
    Context {re10: relate_impl_AC}.
    
    Lemma pt_init_exist:
      forall s (habd habd' labd: RData) (n:Z) f,
        pt_init_spec n habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', pt_init_spec n labd = Some labd'
                         /\ relate_AbData s f habd' labd'.    
    Proof.
      unfold pt_init_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_LAT_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto.
      exploit relate_impl_vmxinfo_eq; eauto.
      exploit relate_impl_idpde_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
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

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_LAT}.
    Context {mt3: match_impl_idpde}.
    Context {mt4: match_impl_PT}.
    Context {mt5: match_impl_init}.
    Context {mt6: match_impl_nps}.
    Context {mt7: match_impl_iflags}.
    Context {mt8: match_impl_vmxinfo}.
    Context {mt9: match_impl_AC}.

    Lemma pt_init_match:
      forall s n d d' m f,
        pt_init_spec n d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold pt_init_spec; intros. subdestruct; inv H; trivial.
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

    Context {inv: PreservesInvariants (HD:= data) pt_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) pt_init_spec}.

    Lemma pt_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem pt_init_spec)
            (id ↦ gensem pt_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit pt_init_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply pt_init_match; eauto.
    Qed.

  End PT_INIT_SIM.

  Section PFREE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_init}.
    Context {re3: relate_impl_LAT}.
    Context {re4: relate_impl_nps}.
    Context {re5: relate_impl_pperm}.
    Context {re6: relate_impl_ipt}.

    Lemma pfree_exist:
      forall s habd habd' labd i f,
        pfree_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', pfree_spec i labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold pfree_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_init_eq; eauto; intros.
      exploit relate_impl_LAT_eq; eauto; intros.
      exploit relate_impl_pperm_eq; eauto; intros.
      exploit relate_impl_ipt_eq; eauto; intros.
      revert H. subrewrite.
      subdestruct; inv HQ; refine_split'; trivial.
      
      apply relate_impl_pperm_update.
      apply relate_impl_LAT_update. assumption.
    Qed.

    Context {mt1: match_impl_pperm}.
    Context {mt2: match_impl_LAT}.

    Lemma pfree_match:
      forall s d d' m i f,
        pfree_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold pfree_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_pperm_update.
      eapply match_impl_LAT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) pfree_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) pfree_spec}.

    Lemma pfree_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem pfree_spec)
            (id ↦ gensem pfree_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit pfree_exist; eauto 1; intros (labd' & HP & HM).
      match_external_states_simpl.
      eapply pfree_match; eauto.
    Qed.

  End PFREE_SIM.

  Section SETPT_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.

    Lemma setPT_exist:
      forall s habd habd' labd i f,
        setPT_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', setPT_spec i labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold setPT_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. 
      subdestruct; inv HQ; refine_split'; trivial.
      eapply relate_impl_PT_update; assumption.
    Qed.

    Context {mt1: match_impl_PT}.

    Lemma setPT_match:
      forall s d d' m i f,
        setPT_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold setPT_spec; intros. subdestruct; trivial.
      inv H. eapply match_impl_PT_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) setPT_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) setPT_spec}.

    Lemma setPT_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem setPT_spec)
            (id ↦ gensem setPT_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit setPT_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply setPT_match; eauto.
    Qed.

  End SETPT_SIM.

  Section PTIN_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.

    Lemma ptin_exist:
      forall s habd habd' labd f,
        ptin_spec habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptin_spec labd = Some labd' /\ 
                         relate_AbData s f habd' labd'.
    Proof.
      unfold ptin_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_PT_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.
      eapply relate_impl_ipt_update. assumption.
    Qed.

    Context {mt1: match_impl_ipt}.

    Lemma ptin_match:
      forall s d d' m f,
        ptin_spec d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptin_spec; intros. subdestruct.
      inv H. eapply match_impl_ipt_update. assumption.
    Qed.

    Context {inv: PrimInvariants (data_ops:= data_ops) ptin_spec}.
    Context {inv0: PrimInvariants (data_ops:= data_ops0) ptin_spec}.

    Lemma ptin_sim :
      forall id,
        sim (crel RData RData) (id ↦ primcall_general_compatsem' ptin_spec (prim_ident:= id))
            (id ↦ primcall_general_compatsem' ptin_spec (prim_ident:= id)).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      inv match_extcall_states.
      exploit ptin_exist; eauto 1. intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ptin_match; eauto.
    Qed.

  End PTIN_SIM.

End OBJ_SIM.
