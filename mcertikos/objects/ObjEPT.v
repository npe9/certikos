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
Require Import CalRealIntelModule.
Require Import liblayers.compat.CompatGenSem.

Section OBJ_EPT.

  Context `{real_params: RealParams}.

  (** primitive: set value of n-th entry of guest page table layer *)
  (** construct nested page table, with the last layer mapping to undef addr *)
  Function setEPML4_spec (pml4: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_le 0 pml4 (EPT_PML4_INDEX Int.max_unsigned) then
          let ept' := ZMap.set pml4 (EPML4EValid (ZMap.init EPDPTEUndef)) (ept adt) in
          Some adt {ept : ept'}
        else None
      | _ => None
    end.

  Function setEPDPTE_spec (pml4 pdpt: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_le 0 pml4 (EPT_PML4_INDEX Int.max_unsigned) then
          if zle_le 0 pdpt (EPT_PDPT_INDEX Int.max_unsigned) then
            match ZMap.get pml4 (ept adt) with
              | EPML4EValid epdpt => 
                let pdpte' := ZMap.set pdpt (EPDPTEValid (ZMap.init EPDTEUndef)) epdpt in
                let ept' := ZMap.set pml4 (EPML4EValid pdpte') (ept adt) in
	        Some adt {ept : ept'}
              | _ => None
            end
          else None
        else None
      | _ => None
    end.

  Function setEPDTE_spec (pml4 pdpt pdir: Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_le 0 pml4 (EPT_PML4_INDEX Int.max_unsigned) then
          if zle_le 0 pdpt (EPT_PDPT_INDEX Int.max_unsigned) then
            if zle_le 0 pdir (EPT_PDIR_INDEX Int.max_unsigned) then
              match ZMap.get pml4 (ept adt) with
                | EPML4EValid epdpt => 
                  match ZMap.get pdpt epdpt with
                    | EPDPTEValid epdt => 
                      let epdt' := ZMap.set pdir (EPDTEValid (ZMap.init EPTEUndef)) epdt in
                      let pdpte' := ZMap.set pdpt (EPDPTEValid epdt') epdpt in
                      let ept' := ZMap.set pml4 (EPML4EValid pdpte') (ept adt) in
	              Some adt {ept : ept'}
                    | _ => None
                  end
                    | _ => None
                  end
            else None
          else None
        else None
      | _ => None
    end.

  Function getEPTE_spec (pml4 pdpt pdir ptab: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_le 0 pml4 (EPT_PML4_INDEX Int.max_unsigned) then
          if zle_le 0 pdpt (EPT_PDPT_INDEX Int.max_unsigned) then
            if zle_le 0 pdir (EPT_PDIR_INDEX Int.max_unsigned) then
              if zle_le 0 ptab (EPT_PTAB_INDEX Int.max_unsigned) then
                  match ZMap.get pml4 (ept adt) with
                    | EPML4EValid epdpt => 
                      match ZMap.get pdpt epdpt with
                        | EPDPTEValid epdt => 
                          match ZMap.get pdir epdt with
                            | EPDTEValid eptab => 
                              match ZMap.get ptab eptab with
                                | EPTEValid hpa => Some hpa
                                | _ => None
                              end
                            | _ => None
                          end
                        | _ => None  
                      end
                    | _ => None
                  end
                else None
              else None
            else None
          else None
      | _ => None
    end.  

  Function setEPTE_spec (pml4 pdpt pdir ptab hpa: Z) (adt: RData): option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) =>
        if zle_le 0 pml4 (EPT_PML4_INDEX Int.max_unsigned) then
          if zle_le 0 pdpt (EPT_PDPT_INDEX Int.max_unsigned) then
            if zle_le 0 pdir (EPT_PDIR_INDEX Int.max_unsigned) then
              if zle_le 0 ptab (EPT_PTAB_INDEX Int.max_unsigned) then
                match ZMap.get pml4 (ept adt) with
                  | EPML4EValid epdpt => 
                    match ZMap.get pdpt epdpt with
                      | EPDPTEValid epdt => 
                        match ZMap.get pdir epdt with
                          | EPDTEValid eptab => 
                            let eptab' := ZMap.set ptab (EPTEValid hpa) eptab in
                            let epdt' := ZMap.set pdir (EPDTEValid eptab') epdt in
                            let pdpte' := ZMap.set pdpt (EPDPTEValid epdt') epdpt in
                            let ept' := ZMap.set pml4 (EPML4EValid pdpte') (ept adt) in
                            Some adt {ept : ept'}
                          | _ => None
                        end
                      | _ => None  
                    end
                  | _ => None
                end
              else None
            else None
          else None
        else None
      | _ => None
    end.

  Definition EPT_PTAB_INDEX' (i:Z) := i mod five_one_two.
  Definition EPT_PDIR_INDEX' (i:Z) := (i/ five_one_two) mod five_one_two.
  Definition EPT_PDPT_INDEX' (i:Z) := (i/ (five_one_two * five_one_two)) mod five_one_two.
  Definition EPT_PML4_INDEX' (i:Z) := (i/ (five_one_two * five_one_two *
                                           five_one_two)) mod five_one_two.

(*
/*
 * Get the last level's EPT page structure entry for the guest address gpa.
 */
static gcc_inline uint64_t 
ept_get_page_entry(uintptr_t gpa)
{
	return ept.ptab[EPT_PDPT_INDEX(gpa)][EPT_PDIR_INDEX(gpa)][EPT_PTAB_INDEX(gpa)];
}*)

  Function ept_get_page_entry_spec (gpa: Z) (adt: RData) : option Z :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => 
        if zle_lt 0 gpa maxpage then
          let pml4 := EPT_PML4_INDEX' gpa in
          let pdpt := EPT_PDPT_INDEX' gpa in
          let pdir := EPT_PDIR_INDEX' gpa in
          let ptab := EPT_PTAB_INDEX' gpa in
          match ZMap.get pml4 (ept adt) with
            | EPML4EValid epdpt => 
              match ZMap.get pdpt epdpt with
                | EPDPTEValid epdt => 
                  match ZMap.get pdir epdt with
                    | EPDTEValid eptab => 
                      match ZMap.get ptab eptab with
                        | EPTEValid hpa => Some hpa
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

(*
/*
 * Set the last level's EPT page structure entry for the guest address gpa.
 */
static gcc_inline void 
ept_set_page_entry(uintptr_t gpa, uint64_t val)
{
	ept.ptab[EPT_PDPT_INDEX(gpa)][EPT_PDIR_INDEX(gpa)][EPT_PTAB_INDEX(gpa)] = val;
}
*)
  Function ept_set_page_entry_spec (gpa hpa : Z) (adt: RData) : option RData :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => 
        if zle_lt 0 gpa maxpage then
          if zle_lt 0 hpa maxpage then
            let pml4 := EPT_PML4_INDEX' gpa in
            let pdpt := EPT_PDPT_INDEX' gpa in
            let pdir := EPT_PDIR_INDEX' gpa in
            let ptab := EPT_PTAB_INDEX' gpa in
            match ZMap.get pml4 (ept adt) with
              | EPML4EValid epdpt => 
                match ZMap.get pdpt epdpt with
                  | EPDPTEValid epdt => 
                    match ZMap.get pdir epdt with
                      | EPDTEValid eptab => 
                        let eptab' := ZMap.set ptab (EPTEValid hpa) eptab in
                        let epdt' := ZMap.set pdir (EPDTEValid eptab') epdt in
                        let pdpte' := ZMap.set pdpt (EPDPTEValid epdt') epdpt in
                        let ept' := ZMap.set pml4 (EPML4EValid pdpte') (ept adt) in
                        Some adt {ept: ept'}
                      | _ => None
                    end
                  | _ => None  
                end
              | _ => None
            end
          else None
        else None
      | _ => None
    end. 

(*
/*
 * Add page structures which map the guest physical address gpa to the host
 * physical address hpa. 
 */
int
ept_add_mapping(uintptr_t gpa, uint64_t hpa, uint32_t mem_type) // I change the type of mem_type
{
    ept.ptab[EPT_PDPT_INDEX(gpa)][EPT_PDIR_INDEX(gpa)][EPT_PTAB_INDEX(gpa)] = (hpa & EPT_ADDR_MASK) |
			EPT_PG_IGNORE_PAT | EPT_PG_EX | EPT_PG_WR | EPT_PG_RD |
			EPT_PG_MEMORY_TYPE(mem_type);

    EPT_DEBUG("Add 4KB mapping: gpa 0x%08x ==> hpa 0x%llx.\n", gpa, hpa);

	return 0;
}

#define	EPT_ADDR_MASK			((uint32_t)-1 << 12)
#define	EPT_PG_RD			(1 << 0)
#define	EPT_PG_WR			(1 << 1)
#define	EPT_PG_EX			(1 << 2)
#define	EPT_PG_IGNORE_PAT		(1 << 6)
#define	EPT_PG_MEMORY_TYPE(x)		((x) << 3)

*)

  Function ept_add_mapping_spec (gpa hpa : Z) (memtype: Z) (adt: RData) : option (RData * Z) :=
    match (ikern adt, pg adt, ihost adt) with
      | (true, true, true) => 
        if zle_lt 0 gpa maxpage then
          if zle_lt 0 hpa maxpage then
            if zle_lt 0 memtype 4096 then
              let pml4 := EPT_PML4_INDEX' gpa in
              let pdpt := EPT_PDPT_INDEX' gpa in
              let pdir := EPT_PDIR_INDEX' gpa in
              let ptab := EPT_PTAB_INDEX' gpa in
              match ZMap.get pml4 (ept adt) with
                | EPML4EValid epdpt => 
                  match ZMap.get pdpt epdpt with
                    | EPDPTEValid epdt => 
                      match ZMap.get pdir epdt with
                        | EPDTEValid eptab => 
                          let va := Z.lor (Z.lor (Z.land hpa EPT_ADDR_MASK) EPT_PG_IGNORE_PAT_or_PERM) 
                                          (Z.shiftl memtype EPT_PG_MEMORY_TYPE) in
                          let eptab' := ZMap.set ptab (EPTEValid va) eptab in
                          let epdt' := ZMap.set pdir (EPDTEValid eptab') epdt in
                          let pdpte' := ZMap.set pdpt (EPDPTEValid epdt') epdpt in
                          let ept' := ZMap.set pml4 (EPML4EValid pdpte') (ept adt) in
                          Some (adt {ept: ept'}, 0)
                        | _ => None
                      end
                    | _ => None  
                  end
                | _ => None
              end
            else None
          else None
        else None
      | _ => None
    end. 

(*

/*
 * Invalidate the EPT TLB.
 */
void
ept_invalidate_mappings(uint64_t pml4ept)
{
	invept(INVEPT_TYPE_SINGLE_CONTEXT, EPTP(pml4ept));
}
 *)
  Function ept_invalidate_mappings_spec (adt: RData) := 
    match (ikern adt, ihost adt) with
      | (true, true) => Some 0
      | _ => None
    end.

(*
/*
 * Convert the guest physical address to the host physical address.
 */

#define EPT_PAGE_OFFSET(gpa)		((gpa) & EPT_ADDR_OFFSET_MASK)
#define EPT_ADDR_OFFSET_MASK		((1 << 12) - 1)

uint64_t
ept_gpa_to_hpa(uintptr_t gpa)
{
    uint64_t entry;

    entry = ept_get_page_entry(gpa);

    if (!(entry & (EPT_PG_RD | EPT_PG_WR | EPT_PG_EX)))
        return 0;

    return ((entry & EPT_ADDR_MASK) | EPT_PAGE_OFFSET(gpa));
}*)

  Function ept_gpa_to_hpa_spec (gpa: Z) (adt: RData) : option Z :=
    match ept_get_page_entry_spec gpa adt with
      | Some hpa =>
        if zle_le 0 hpa Int.max_unsigned then
          if zeq (Z.land hpa EPTEPERM) 0 then (Some 0)
          else let va := Z.lor (Z.land hpa EPT_ADDR_MASK)
                             (Z.land gpa EPT_ADDR_OFFSET_MASK) in
             Some va
        else None
      | _ => None
    end. 

(*
int
ept_mmap(uintptr_t gpa, uint64_t hpa, uint8_t mem_type)
{
	uint64_t pg_entry;

	/*
	 * XXX: ASSUME 4KB pages are used in both the EPT and the host page
	 *      structures.
	 */
	KERN_ASSERT(gpa == ROUNDDOWN(gpa, PAGESIZE));
	KERN_ASSERT(hpa == ROUNDDOWN(hpa, PAGESIZE));

	pg_entry = ept_get_page_entry(gpa);

	if (((pg_entry) & (EPT_PG_RD | EPT_PG_WR | EPT_PG_EX)))
	{
		KERN_WARN("Guest page 0x%08x is already mapped to 0x%llx.\n",
			  gpa, (pg_entry & EPT_ADDR_MASK));
		return 1;
	}

	return ept_add_mapping(gpa, hpa, mem_type);
}*)

  Function ept_mmap_spec (gpa hpa : Z) (memtype: Z) (adt: RData) : option (RData * Z) :=
    match ept_get_page_entry_spec gpa adt with
      | Some hpa' =>
        if (zle_le 0 hpa' Int.max_unsigned) then
              if zle_lt 0 memtype 4096 then

                (if zeq (Z.land hpa' EPTEPERM) 0 
                 then ept_add_mapping_spec gpa hpa memtype adt
                 else Some (adt, 1))
              else None
        else None
      | _ => None
    end.

(*
/*
 * Set the access permission of the guest physical address gpa.
 */
void
ept_set_permission(uintptr_t gpa, uint32_t perm): Change the type of perm
{
	uint64_t entry;

	entry = ept_get_page_entry(gpa);

	ept_set_page_entry(gpa, (entry & ~(uint64_t) 0x7) | (perm & 0x7));

	return;
}*)

  Function ept_set_permission_spec (gpa perm: Z) (adt: RData) : option RData :=
    match ept_get_page_entry_spec gpa adt with
      | Some hpa' =>
        if (zle_le 0 hpa' Int.max_unsigned) then
        (let hpa := Z.lor (Z.land hpa' EPT_NO_PERM) 
                         (Z.land perm EPTEPERM) in
        ept_set_page_entry_spec gpa hpa adt)
        else None
      | _ => None
    end.

  Function ept_init_spec (mbi_adr:Z) (adt: RData) : option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {LAT: real_LAT (LAT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
             {smspool: real_smspool (smspool adt)}
             {abtcb: ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb (abtcb adt))}
             {abq: real_abq (abq adt)} {cid: 0} {syncchpool: real_syncchpool (syncchpool adt)}
             {ept: real_ept (ept adt)}
      | _ => None
    end.

End OBJ_EPT.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import AuxLemma.

Section OBJ_SIM.

  Context `{data : CompatData RData}.
  Context `{data0 : CompatData RData}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_prf := data) RData).
  Notation LDATAOps := (cdata (cdata_prf := data0) RData).

  Context `{rel_prf: CompatRel _ (memory_model_ops:= memory_model_ops) _
                               (stencil_ops:= stencil_ops) HDATAOps LDATAOps}.

  Section EPT_GET_PAGE_ENTRY_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ept}.

    Lemma ept_get_page_entry_exist:
      forall s habd labd gpa hpa f,
        ept_get_page_entry_spec gpa habd = Some hpa
        -> relate_AbData s f habd labd
        -> ept_get_page_entry_spec gpa labd = Some hpa.
    Proof.
      unfold ept_get_page_entry_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ept_eq; eauto. intros.
      revert H. subrewrite.
    Qed.

  End EPT_GET_PAGE_ENTRY_SIM.

  Section EPT_SET_PAGE_ENTRY_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_ept}.

    Lemma ept_set_page_entry_exist:
      forall s habd habd' labd gpa hpa' f,
        ept_set_page_entry_spec gpa hpa' habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ept_set_page_entry_spec gpa hpa' labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ept_set_page_entry_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ept_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_ept_update. assumption.
    Qed.

  End EPT_SET_PAGE_ENTRY_SIM.

  Section EPT_ADD_MAPPING_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2 : relate_impl_ept}.

    Lemma ept_add_mapping_exist:
      forall s habd habd' labd gpa hpa' memtype n f,
        ept_add_mapping_spec gpa hpa' memtype habd = Some (habd', n)
        -> relate_AbData s f habd labd
        -> exists labd', ept_add_mapping_spec gpa hpa' memtype labd = Some (labd', n)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.shiftl.

      unfold ept_add_mapping_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_ept_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_ept_update. assumption.
    Qed.

    Context {mt1: match_impl_iflags}.
    Context {mt2: match_impl_ept}.

    Lemma ept_add_mapping_match:
      forall s d d' m gpa hpa' memtype n f,
        ept_add_mapping_spec gpa hpa' memtype d = Some (d', n)
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ept_add_mapping_spec; intros. subdestruct; inv H; trivial.
      eapply match_impl_ept_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) ept_add_mapping_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ept_add_mapping_spec}.

    Lemma ept_add_mapping_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ept_add_mapping_spec)
            (id ↦ gensem ept_add_mapping_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ept_add_mapping_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ept_add_mapping_match; eauto.
    Qed.

  End EPT_ADD_MAPPING_SIM.

  Section EPT_GPA_TO_HPA_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2 : relate_impl_ept}.

    Lemma ept_gpa_to_hpa_exist:
      forall s habd labd gpa va f,
        ept_gpa_to_hpa_spec gpa habd = Some va
        -> relate_AbData s f habd labd
        -> ept_gpa_to_hpa_spec gpa labd = Some va.
    Proof.
      Local Opaque Z.land Z.lor.

      unfold ept_gpa_to_hpa_spec. intros.
      destruct (ept_get_page_entry_spec gpa habd) eqn:Hdestruct; try discriminate.
      exploit ept_get_page_entry_exist; eauto. intros.
      revert H. subrewrite.
    Qed.

  End EPT_GPA_TO_HPA_SIM.

  Section EPT_MMAP_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2 : relate_impl_ept}.

    Lemma ept_mmap_exist:
      forall s habd habd' labd gpa hpa' memtype n f,
        ept_mmap_spec gpa hpa' memtype habd = Some (habd', n)
        -> relate_AbData s f habd labd
        -> exists labd', ept_mmap_spec gpa hpa' memtype labd = Some (labd', n)
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.land.

      unfold ept_mmap_spec; intros.
      destruct (ept_get_page_entry_spec gpa habd) eqn:Hdestruct; try discriminate.
      exploit ept_get_page_entry_exist; eauto. intros.
      revert H. subrewrite. subdestruct.

      - eapply ept_add_mapping_exist; eassumption.
      - inv HQ; refine_split'; trivial.
    Qed.

  End EPT_MMAP_SIM.

  Section EPT_SET_PERMISSION_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2 : relate_impl_ept}.

    Lemma ept_set_permission_exist:
      forall s habd habd' labd gpa perm f,
        ept_set_permission_spec gpa perm habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ept_set_permission_spec gpa perm labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      Local Opaque Z.land Z.lor.

      unfold ept_set_permission_spec; intros.
      destruct (ept_get_page_entry_spec gpa habd) eqn:Hdestruct; try discriminate.
      exploit ept_get_page_entry_exist; eauto. intros.
      subrewrite'. subdestruct.

      eapply ept_set_page_entry_exist; eassumption.
    Qed.

  End EPT_SET_PERMISSION_SIM.

  Section EPT_INIT_SIM.

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
    Context {re15: relate_impl_ept}.
    Context {re16: relate_impl_AC}.

    Lemma ept_init_exist:
      forall s habd habd' labd mbi_adr f,
        ept_init_spec mbi_adr habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', ept_init_spec mbi_adr labd = Some labd'
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold ept_init_spec; intros.
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
      exploit relate_impl_smspool_eq; eauto.
      exploit relate_impl_ept_eq; eauto. intros.
      revert H. subrewrite. subdestruct.
      inv HQ; refine_split'; trivial.

      apply relate_impl_ept_update.
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
    Context {mt15: match_impl_ept}.
    Context {mt16: match_impl_AC}.

    Lemma ept_init_match:
      forall s d d' m  mbi_adr f,
        ept_init_spec mbi_adr d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold ept_init_spec; intros. subdestruct. inv H.
      eapply match_impl_ept_update.
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

    Context {inv: PreservesInvariants (HD:= data) ept_init_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) ept_init_spec}.

    Lemma ept_init_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem ept_init_spec)
            (id ↦ gensem ept_init_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit ept_init_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply ept_init_match; eauto.
    Qed.

  End EPT_INIT_SIM.

  Section EPT_INV_SIM.

    Context {re1: relate_impl_iflags}.

    Lemma ept_invalidate_mappings_exists:
      forall habd labd z s f,
        ept_invalidate_mappings_spec habd = Some z ->
        relate_AbData s f habd labd ->
        ept_invalidate_mappings_spec labd = Some z.
    Proof.
      unfold ept_invalidate_mappings_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      revert H. subrewrite. 
    Qed.

    Lemma ept_invalidate_mappings_sim:
      forall id,
        sim (crel RData RData) (id ↦ gensem ept_invalidate_mappings_spec)
            (id ↦ gensem ept_invalidate_mappings_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      match_external_states_simpl.
      erewrite ept_invalidate_mappings_exists; eauto.
      reflexivity.
    Qed.

  End EPT_INV_SIM.

End OBJ_SIM.
