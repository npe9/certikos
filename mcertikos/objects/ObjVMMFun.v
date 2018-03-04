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
Require Import ObjVMMDef.

Section OBJ_VMM.

  Context `{real_params: RealParams}.

  (** primitve: returns the contents of the n-th page table with the fisrt level index i and second level index vadr *)    
  Function ptInsertPDE_spec (n vadr pi: Z) (adt: RData) : option RData :=
    let pdi := PDX vadr in
    setPDEU_spec n pdi pi adt.
  
  Function ptInsertAux_spec (n vadr padr perm: Z) (adt: RData) : option RData :=
    let pdi := PDX vadr in
    let pti := PTX vadr in
    setPTE_spec n pdi pti padr perm adt.

  Function ptRead_spec (n vadr :Z) (adt: RData) : option Z :=
    let pdi := PDX vadr in
    let pti := PTX vadr in
    getPTE_spec n pdi pti adt.

  Function ptRmvPDE_spec (n vadr: Z) (adt: RData) : option RData :=
    let pdi:= PDX vadr in
    rmvPDE_spec n pdi adt.

  Function idpde_init_spec (mbi_adr:Z) (adt: RData)  : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {AT: real_AT (AT adt)} {nps: real_nps} {AC: real_AC} {init: true}
             {idpde: real_idpde (idpde adt)}
      | _ => None
    end.

  Function ptAllocPDE_spec  (nn vadr: Z) (adt: RData): option (RData * Z) :=
    let pdi := PDX vadr in
    let c := ZMap.get nn (AC adt) in
    match (ikern adt, ihost adt, init adt, ipt adt, cused c, pt_Arg' nn vadr) with
      | (true, true, true, true, true, true) =>
        if zeq nn (PT adt) then None
        else
          match ZMap.get pdi (ZMap.get nn (ptpool adt)) with
            | PDEUnPresent => 
              if (cusage c) <? (cquota c) then
                let cur := mkContainer (cquota c) (cusage c + 1) (cparent c)
                                       (cchildren c) (cused c) in
                match first_free (AT adt) (nps adt) with
                  | inleft (exist pi _) => 
                    Some (adt {HP: FlatMem.free_page pi (HP adt)}
                              {AT: ZMap.set pi (ATValid true ATNorm 0) (AT adt)}
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

  Function ptFreePDE_spec (n vadr: Z) (adt: RData): option RData :=
    let pdi := PDX vadr in
    match (ikern adt, ihost adt, init adt, ipt adt, pt_Arg' n vadr) with
      | (true, true, true, true, true) =>
        if zeq n (PT adt) then None
        else
          match ZMap.get pdi (ZMap.get n (ptpool adt)) with
            | PDEValid pi _ =>
              if zle_lt 0 pi maxpage then
                match ZMap.get pi (pperm adt) with
                  | PGHide (PGPMap _ _)  =>
                    match ZMap.get pi (AT adt) with
                      | ATValid true ATNorm 0 =>
                        let pt':= ZMap.set pdi PDEUnPresent (ZMap.get n (ptpool adt)) in
                        Some adt {AT: ZMap.set pi (ATValid false ATNorm 0) (AT adt)}
                             {pperm: ZMap.set pi PGUndef (pperm adt)}
                             {ptpool: ZMap.set n pt' (ptpool adt)}
                      | _ => None
                    end
                  | _ => None
                end
              else None
            | _ => None
          end
      |_ => None
    end.
  
  (** primitive: initialize the allocation table and the common part of all the page tables*)   
  Function pt_init_comm_spec (mbi_adr:Z) (adt: RData): option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {AT: real_AT (AT adt)}
             {nps: real_nps} {AC: real_AC} {init: true} {ptpool: real_ptp (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
      | _ => None
    end.

  Function ptInsertPTE_spec (nn vadr padr: Z) (p: PTPerm) (adt: RData): option RData :=
    match (ikern adt, ihost adt, init adt) with
      | (true, true, true) =>
        if zeq nn (PT adt) then None
        else
          let pt := ZMap.get nn (ptpool adt) in
          let pdi := PDX vadr in
          let pti := PTX vadr in
          match ZMap.get pdi pt with
            | PDEValid pi pdt => 
              if zlt_lt 0 pi Int.max_unsigned then
                match ZMap.get padr (AT adt) with
                  | ATValid true ATNorm c =>
                    if zle_lt 0 c Int.max_unsigned then
                      let pdt':= ZMap.set pti (PTEValid padr p) pdt in
                      let pt' := ZMap.set pdi (PDEValid pi pdt') pt in
                      Some adt {AT: ZMap.set padr (ATValid true ATNorm (c + 1)) (AT adt)}
                           {ptpool: ZMap.set nn pt' (ptpool adt)}
                    else None
                  | _ => None
                end
              else None
            | _ => None
          end
      | _ => None
    end.

  (** primitve: set the n-th page table with virtual address vadr to (padr + perm)*)    
  (** The pt insert at this layer, is slightly different from the one at MPTComm.
       [0th page map] has been reserved for the kernel thread, which couldn't be modified after the initialization*)
  Function ptInsert_spec (nn vadr padr perm: Z) (adt: RData): option (RData * Z) :=
    match (ikern adt, ihost adt, init adt, ipt adt, pg adt, pt_Arg nn vadr padr (nps adt)) with
      | (true, true, true, true, true, true) =>
        match ZtoPerm perm with
          | Some p => 
            let pt := ZMap.get nn (ptpool adt) in
            let pdi := PDX vadr in
            let pti := PTX vadr in
            match ZMap.get pdi pt with
              | PDEValid pi pdt => 
                match ptInsertPTE_spec nn vadr padr p adt with
                  | Some adt' => Some (adt', 0)
                  | _ => None
                end
              | PDEUnPresent => 
                match ptAllocPDE_spec nn vadr adt with
                  | Some (adt', v) =>
                    if zeq v 0 then Some (adt', MagicNumber)
                    else 
                      match ptInsertPTE_spec nn vadr padr p adt' with
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

  (** primitve: set the n-th page table with virtual address vadr to unpresent*)    
  Function ptRmv_spec (n vadr: Z) (adt: RData): option (RData * Z) :=
    match (ikern adt, ihost adt, init adt, ipt adt, pg adt, pt_Arg' n vadr) with
      | (true, true, true, true, true, true) =>
        if zeq n (PT adt) then None
        else
          let pt:= ZMap.get n (ptpool adt) in
          let pdi := PDX vadr in
          match ZMap.get pdi pt with
            | PDEValid pi pdt =>
              let pti := PTX vadr in
              match ZMap.get pti pdt with
                | PTEValid padr _ => 
                  if zlt_lt 0 padr maxpage then
                    match ZMap.get padr (AT adt) with
                      | ATValid true ATNorm c =>
                        if zlt_le 0 c Int.max_unsigned then 
                          let pdt':= ZMap.set pti PTEUnPresent pdt in
                          let pt' := ZMap.set pdi (PDEValid pi pdt') pt in
                          Some (adt {AT: ZMap.set padr (ATValid true ATNorm (c - 1)) (AT adt)}
                                    {ptpool: ZMap.set n pt' (ptpool adt)}, padr)
                        else None
                      | _ => None
                    end
                  else None
                | PTEUnPresent => Some (adt, 0)
                | _ => None
              end

            | _ => None
          end
      | _ => None
    end.

  (** primitive: initialize the kernel's page table, which will only be used in the refinement proof*)
  Function pt_init_kern_spec (mbi_adr:Z) (adt: RData) : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {AT: real_AT (AT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
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

  Section PT_INSERT_AUX_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.
    Context {re6: relate_impl_nps}.
        
    Lemma ptInsertAux_exist:
      forall s habd habd' labd n vadr padr perm f,
        ptInsertAux_spec n vadr padr perm habd  = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptInsertAux_spec n vadr padr perm labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptInsertAux_spec, setPTE_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_nps_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      subdestruct; inv HQ; refine_split'; trivial.
      eapply relate_impl_ptpool_update; assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.

    Lemma ptInsertAux_match:
      forall s d d' n vadr padr perm m f,
        ptInsertAux_spec n vadr padr perm d  = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptInsertAux_spec, setPTE_spec; intros.
      subdestruct; trivial.
      inv H. eapply match_impl_ptpool_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ptInsertAux_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptInsertAux_spec}.
 
    Lemma ptInsertAux_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptInsertAux_spec)
            (id ↦ gensem ptInsertAux_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. intros.
      exploit ptInsertAux_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ptInsertAux_match; eauto.
    Qed.

  End PT_INSERT_AUX_SIM.

  Section PT_READ_SIM.

    Context {re1: relate_impl_iflags}.

    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.

    Lemma ptRead_exist:
      forall s habd labd n vadr z f,
        ptRead_spec n vadr habd = Some z
        -> relate_AbData s f habd labd
        -> ptRead_spec n vadr labd = Some z.
    Proof.
      unfold ptRead_spec, getPTE_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. 
    Qed.

    Lemma ptRead_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptRead_spec)
            (id ↦ gensem ptRead_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'.
      match_external_states_simpl.
      erewrite ptRead_exist; eauto. reflexivity.
    Qed.

  End PT_READ_SIM.

  Section PT_FREE_PDE_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_PT}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_ptpool}.
    Context {re5: relate_impl_init}.
    Context {re6: relate_impl_AT}.
    Context {re7: relate_impl_pperm}.

    Lemma ptFreePDE_exist:
      forall s habd habd' labd n i f,
        ptFreePDE_spec n i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ptFreePDE_spec n i labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ptFreePDE_spec. intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.
      exploit relate_impl_init_eq; eauto.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_AT_eq; eauto.
      exploit relate_impl_pperm_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      subdestruct; inv HQ; refine_split'; trivial.
      eapply relate_impl_ptpool_update.
      eapply relate_impl_pperm_update.
      eapply relate_impl_AT_update. assumption.
    Qed.

    Context {mt1: match_impl_ptpool}.
    Context {mt2: match_impl_pperm}.
    Context {mt3: match_impl_AT}.

    Lemma ptFreePDE_match:
      forall s d d' n i m f,
        ptFreePDE_spec n i d  = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ptFreePDE_spec. intros.
      subdestruct; trivial.
      inv H. eapply match_impl_ptpool_update. 
      eapply match_impl_pperm_update. 
      eapply match_impl_AT_update. 
      assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ptFreePDE_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ptFreePDE_spec}.
 
    Lemma ptFreePDE_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ptFreePDE_spec)
            (id ↦ gensem ptFreePDE_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl'. intros.
      exploit ptFreePDE_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ptFreePDE_match; eauto.
    Qed.

  End PT_FREE_PDE_SIM.

End OBJ_SIM.
