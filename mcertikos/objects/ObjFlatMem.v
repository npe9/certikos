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
Require Import ASTExtra.
Require Import Constant.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import Observation.

Section OBJ_FLATMEM.

  Local Open Scope Z_scope.

  (** primitve: store to the heap*)
  Function flatmem_store' (adt: RData) (chunk: memory_chunk) (addr: Z) (v: val): option RData :=
    Some adt {HP: FlatMem.store chunk (HP adt) addr v}.

  Function flatmem_store (adt: RData) (chunk: memory_chunk) (addr: Z) (v: val): option RData :=
    match ZMap.get (PageI addr) (pperm adt) with
      | PGAlloc => Some adt {HP: FlatMem.store chunk (HP adt) addr v}
      | _ => None
    end.
  
  (** primitve: store to the heap*)
  Function fstore'_spec (addr v: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) => 
        if zle_lt 0 addr adr_low then
          flatmem_store' adt Mint32 (addr * 4) (Vint (Int.repr v))
        else None
      | _ => None
    end.

  Function fstore0_spec (addr v: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt) with
      | (true, true) => 
        if zle_lt 0 addr adr_low then
          flatmem_store adt Mint32 (addr * 4) (Vint (Int.repr v))
        else None
      | _ => None
    end.

  Function fstore_spec (addr v: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt, ipt adt) with
      | (true, true, true) => 
        if zle_lt 0 addr adr_low then
          flatmem_store adt Mint32 (addr * 4) (Vint (Int.repr v))
        else None
      | _ => None
    end.

  Function fload'_spec (addr: Z) (adt: RData): option Z :=
    match (ikern adt, ihost adt) with
      | (true, true) => 
        if zle_lt 0 addr adr_low then
          match FlatMem.load Mint32 (HP adt) (addr * 4) with
            | Vint n => Some (Int.unsigned n)
            | _ => None
          end
        else None
      | _ => None
    end.

  Function fload_spec (addr: Z) (adt: RData): option Z :=
    match (ikern adt, ihost adt, ipt adt) with
      | (true, true, true) => 
        if zle_lt 0 addr adr_low then
          match (ZMap.get (PageI (addr * 4)) (pperm adt),
                 FlatMem.load Mint32 (HP adt) (addr * 4)) with
            | (PGAlloc, Vint n) => Some (Int.unsigned n)
            | _ => None
          end
        else None
      | _ => None
    end.

  Fixpoint flatmem_copy_aux (n: nat) (from to: Z) (h: flatmem) :=
    match n with
      | O => Some h
      | S n' =>
        match FlatMem.load Mint32 h from with
          | Vint v => 
            flatmem_copy_aux n' (from + 4) (to + 4)  (FlatMem.store Mint32 h to (Vint v))
          | _ => None
        end
    end.

  Section COPY_INV.

    Lemma PageI_monotonic:
      forall a b,
        a <= b ->
        PageI a <= PageI b.
    Proof.
      unfold PageI.
      intros. eapply Z_div_le; eauto.
      omega.
    Qed.

    Lemma PageI_range:
      forall a b c,
        a <= b <= c->
        PageI a = PageI c ->
        PageI b = PageI a.
    Proof.
      intros.
      assert (HR1: PageI a <= PageI b) by (eapply PageI_monotonic; try omega).
      assert (HR2: PageI b <= PageI c) by (eapply PageI_monotonic; try omega).
      omega.
    Qed.

    Lemma to_range:
      forall to n,
        to <= to + 4 <= to + Z.of_nat (S (n + 1)) * 4 - 4.
    Proof.
      intros.
      erewrite Nat2Z.inj_succ.
      replace ((n + 1)%nat) with (S n) by omega. 
      erewrite Nat2Z.inj_succ.
      pose proof (Nat2Z.is_nonneg n).
      omega.
    Qed.

    Lemma to_mod_le:
      forall to,
        (4 | to) ->
        to mod 4096 <= 4092.
    Proof.
      intros.
      destruct H as (i & He).
      subst.
      change 4096 with (4 * 1024) in *.
      replace (i * 4) with (4 * i) by omega.
      rewrite Zmult_mod_distr_l in *.
      assert (i mod 1024 < 1024).
      {
        eapply Z_mod_lt. omega.
      }        
      omega.
    Qed.

    Lemma to_add_divide:
      forall to,
        (4 | to) ->
        (4 | to + 4).
    Proof.
      intros.
      destruct H as (i & He).
      subst.
      exists (i + 1). omega.
    Qed.

    Lemma PageI_eq:
      forall to n,
        PageI to = PageI (to + Z.of_nat (S (n + 1)) * 4 - 4) ->
        PageI (to + 4) = PageI (to + 4 + Z.of_nat (n + 1) * 4 - 4).
    Proof.
      intros. 
      rewrite Nat2Z.inj_succ in H.
      replace ((n + 1)%nat) with (S n) in * by omega.
      rewrite Nat2Z.inj_succ in *.
      pose proof (Nat2Z.is_nonneg n).      
      erewrite (PageI_range to (to + 4 + Z.succ (Z.of_nat n) * 4 - 4)); eauto.
      erewrite (PageI_range to (to + 4)); eauto.
      omega.
      omega.
    Qed.

    Lemma dirty_ppage_gss_copy_plus:
      forall n h h' pp from to,
        ZMap.get (PageI to) pp = PGAlloc ->
        (4 | to) ->
        PageI to = PageI (to + (Z.of_nat (n + 1)) * 4 - 4) ->
        dirty_ppage pp h ->
        flatmem_copy_aux (n + 1) from to h = Some h' ->
        dirty_ppage pp h'.
    Proof.
      intros until n.
      induction n.
      - simpl; intros. 
        subdestruct. inv H3.
        eapply dirty_ppage_store_unmaped'; eauto.
        eapply to_mod_le; eauto.
      - simpl; intros. subdestruct.
        eapply (IHn (FlatMem.store Mint32 h to (Vint i)));
          try eapply H3.        
        + erewrite PageI_range; eauto.
          eapply to_range.
        + apply to_add_divide; eauto.
        + eapply PageI_eq; eauto.
        + eapply dirty_ppage_store_unmaped'; eauto.
          eapply to_mod_le; eauto.
    Qed.

    Lemma PageI_divide':
      forall to n,
        (4096 | to) ->
        1 <= n <= 1024 ->
        PageI to = PageI (to + n * 4 - 4).
    Proof.
      intros. destruct H as (i & He). subst.
      unfold PageI.
      assert (4096 > 0) by omega.
      replace (i * 4096 + n * 4 - 4)
      with (n * 4 - 4 + i * 4096) by omega.
      rewrite Z_div_plus; trivial.
      rewrite Z_div_mult; trivial.
      rewrite Zdiv_small; trivial.
      omega.
    Qed.

    Lemma PageI_divide:
      forall to n,
        (4096 | to) ->
        Z.of_nat (n + 1) <= 1024 ->
        PageI to = PageI (to + Z.of_nat (n + 1) * 4 - 4).
    Proof.
      intros. eapply PageI_divide'; eauto. 
      replace ((n + 1)%nat) with (S n) in * by omega.
      rewrite Nat2Z.inj_succ in *.
      pose proof (Nat2Z.is_nonneg n).      
      omega.
    Qed.

    Lemma dirty_ppage_gss_copy':
      forall n h h' pp from to,
        ZMap.get (PageI to) pp = PGAlloc ->
        (PgSize | to)  ->
        Z.of_nat n <= one_k ->
        dirty_ppage pp h ->
        flatmem_copy_aux n from to h = Some h' ->
        dirty_ppage pp h'.
    Proof.
      destruct n; intros.
      - simpl in *. inv H3. assumption.
      - replace (S n) with ((n + 1)%nat) in * by omega.
        eapply dirty_ppage_gss_copy_plus; eauto.
        destruct H0 as (i & He).
        exists (i * 1024).
        subst. omega.
        eapply PageI_divide; eauto.
    Qed.

    Lemma dirty_ppage_gss_copy:
      forall n h h' pp from to,
        flatmem_copy_aux (Z.to_nat n) from to h = Some h' ->
        ZMap.get (PageI to) pp = PGAlloc ->
        (PgSize | to)  ->
        0 <= n <= one_k ->
        dirty_ppage pp h ->
        dirty_ppage pp h'.
    Proof.
      intros.
      eapply dirty_ppage_gss_copy'; eauto.
      rewrite Z2Nat.id; try omega.
    Qed.

  End COPY_INV.

  Function flatmem_copy'_spec (count: Z) (from to: Z) (adt: RData) :=
    match (ikern adt, ihost adt) with
      | (true, true) => 
        if zle_lt 0 to adr_low then
          if zle_lt 0 from adr_low then
            if zle_le 0 count one_k then
              if Zdivide_dec PgSize to HPS then
                if Zdivide_dec PgSize from HPS then
                  match flatmem_copy_aux (Z.to_nat count) from to (HP adt) with
                    | Some h => Some adt {HP: h}
                    | _ => None
                  end
                else None
              else None
            else None
          else None
        else None
      | _ => None
    end.

  Function flatmem_copy0_spec (count: Z) (from to: Z) (adt: RData) :=
    match (ikern adt, ihost adt) with
      | (true, true) => 
        if zle_lt 0 to adr_low then
          if zle_lt 0 from adr_low then
            if zle_le 0 count one_k then
              if Zdivide_dec PgSize to HPS then
                if Zdivide_dec PgSize from HPS then
                  
                  match (ZMap.get (PageI from) (pperm adt), ZMap.get (PageI to) (pperm adt)) with
                    | (PGAlloc, PGAlloc) => 
                      match flatmem_copy_aux (Z.to_nat count) from to (HP adt) with
                        | Some h => Some adt {HP: h}
                        | _ => None
                      end
                    | _ => None
                  end
                else None
              else None
            else None
          else None
        else None
      | _ => None
    end.
 
  Function flatmem_copy_spec (count: Z) (from to: Z) (adt: RData) :=
    match (ikern adt, ihost adt, ipt adt) with
      | (true, true, true) => 
        if zle_lt 0 to adr_low then
          if zle_lt 0 from adr_low then
            if zle_le 0 count one_k then
              if Zdivide_dec PgSize to HPS then
                if Zdivide_dec PgSize from HPS then
                  
                  match (ZMap.get (PageI from) (pperm adt), ZMap.get (PageI to) (pperm adt)) with
                    | (PGAlloc, PGAlloc) => 
                      match flatmem_copy_aux (Z.to_nat count) from to (HP adt) with
                        | Some h => Some adt {HP: h}
                        | _ => None
                      end
                    | _ => None
                  end
                else None
              else None
            else None
          else None
        else None
      | _ => None
    end.

End OBJ_FLATMEM.

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


  Section FSTORE'_SIM.

    Context {re2: relate_impl_HP}.
  
    Lemma flatmem_store'_exists:
      forall s hadt ladt hadt' t addr v v' f,
        flatmem_store' hadt t addr v = Some hadt'
        -> relate_AbData s f hadt ladt
        -> val_inject f v v'
        -> exists ladt',
             flatmem_store' ladt t addr v' = Some ladt'
             /\ relate_AbData s f hadt' ladt'.
    Proof.
      unfold flatmem_store'. intros.
      revert H. subrewrite. inv HQ.
      refine_split'; eauto.
      eapply relate_impl_HP_update; eauto.
      eapply (FlatMem.store_mapped_inj f); trivial.
      eapply relate_impl_HP_eq; eauto. assumption.
    Qed.

    Context {re1: relate_impl_iflags}.

    Lemma fstore'_exist:
      forall s habd habd' labd i v f,
        fstore'_spec i v habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', fstore'_spec i v labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold fstore'_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.         
      revert H. subrewrite. 
      subdestruct. eapply flatmem_store'_exists; eauto.
    Qed.

    Context {mt1: match_impl_HP}.

    Lemma fstore'_match:
      forall s d d' m i v f,
        fstore'_spec i v d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold fstore'_spec, flatmem_store'; intros. subdestruct.
      inv H. eapply match_impl_HP_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) fstore'_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) fstore'_spec}.

    Lemma fstore'_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem fstore'_spec)
            (id ↦ gensem fstore'_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit fstore'_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply fstore'_match; eauto.
    Qed.

  End FSTORE'_SIM.

  Section FSTORE0_SIM.

    Context {re1: relate_impl_HP}.
    Context {re2: relate_impl_pperm}.

    Lemma flatmem_store_exists:
      forall s hadt ladt hadt' t addr v v' f,
        flatmem_store hadt t addr v = Some hadt'
        -> relate_AbData s f hadt ladt
        -> val_inject f v v'
        -> exists ladt',
             flatmem_store ladt t addr v' = Some ladt'
             /\ relate_AbData s f hadt' ladt'.
    Proof.
      unfold flatmem_store. intros.
      exploit relate_impl_pperm_eq; eauto. intros. 
      revert H. subrewrite. subdestruct. inv HQ.
      refine_split'; eauto.
      eapply relate_impl_HP_update; eauto.
      eapply (FlatMem.store_mapped_inj f); trivial.
      eapply relate_impl_HP_eq; eauto. assumption.
    Qed.

    Context {re3: relate_impl_iflags}.

    Lemma fstore0_exist:
      forall s habd habd' labd i v f,
        fstore0_spec i v habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', fstore0_spec i v labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold fstore0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      revert H. subrewrite. 
      subdestruct. eapply flatmem_store_exists; eauto.
    Qed.

    Context {mt1: match_impl_HP}.

    Lemma flatmem_store_match:
      forall s d d' m i v t f,
        flatmem_store d t i v = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold flatmem_store; intros. subdestruct.
      inv H. eapply match_impl_HP_update. assumption.
    Qed.

    Lemma fstore0_match:
      forall s d d' m i v f,
        fstore0_spec i v d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold fstore0_spec, flatmem_store; intros. subdestruct.
      inv H. eapply match_impl_HP_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) fstore0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) fstore0_spec}.

    Lemma fstore0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem fstore0_spec)
            (id ↦ gensem fstore0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit fstore0_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply fstore0_match; eauto.
    Qed.

  End FSTORE0_SIM.

  Section FSTORE_SIM.

    Context {re1: relate_impl_HP}.
    Context {re2: relate_impl_pperm}.
    Context {re3: relate_impl_iflags}.
    Context {re4: relate_impl_ipt}.

    Lemma fstore_exist:
      forall s habd habd' labd i v f,
        fstore_spec i v habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', fstore_spec i v labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold fstore_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.         
      exploit relate_impl_ipt_eq; eauto. intros.
      revert H. subrewrite. 
      subdestruct. eapply flatmem_store_exists; eauto.
    Qed.

    Context {mt1: match_impl_HP}.

    Lemma fstore_match:
      forall s d d' m i v f,
        fstore_spec i v d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold fstore_spec, flatmem_store; intros. subdestruct.
      inv H. eapply match_impl_HP_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) fstore_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) fstore_spec}.

    Lemma fstore_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem fstore_spec)
            (id ↦ gensem fstore_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit fstore_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply fstore_match; eauto.
    Qed.

  End FSTORE_SIM.

  Section FLOAD'_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_HP}.

    Lemma fload'_exist:
      forall s habd labd i z f,
        fload'_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> fload'_spec i labd = Some z.
    Proof.
      unfold fload'_spec; intros.
      exploit relate_impl_iflags_eq; eauto.
      inversion 1. 
      pose proof (relate_impl_HP_eq _ _ _ _ H0) as Hre.
      specialize (FlatMem.load_inj _ _ Mint32 (i * 4) _ f Hre refl_equal).
      revert H. subrewrite.
      subdestruct. intros (v2 & HLD & HVAL).
      rewrite HLD. inv HVAL. assumption.
    Qed.

    Lemma fload'_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem fload'_spec) (id ↦ gensem fload'_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite fload'_exist; eauto.
      reflexivity.
    Qed.

  End FLOAD'_SIM.

  Section FLOAD_SIM.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_HP}.
    Context {re3: relate_impl_ipt}.
    Context {re4: relate_impl_pperm}.

    Lemma fload_exist:
      forall s habd labd i z f,
        fload_spec i habd = Some z
        -> relate_AbData s f habd labd
        -> fload_spec i labd = Some z.
    Proof.
      unfold fload_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      exploit relate_impl_ipt_eq; eauto.  
      exploit relate_impl_pperm_eq; eauto. intros. 
      pose proof (relate_impl_HP_eq _ _ _ _ H0) as Hre.
      specialize (FlatMem.load_inj _ _ Mint32 (i * 4) _ f Hre refl_equal).
      revert H. subrewrite.
      subdestruct. intros (v2 & HLD & HVAL).
      rewrite HLD. inv HVAL. assumption.
    Qed.

    Lemma fload_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem fload_spec) (id ↦ gensem fload_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData).
      match_external_states_simpl. 
      erewrite fload_exist; eauto.
      reflexivity.
    Qed.

  End FLOAD_SIM.

  Section MEM_COPY_AUX_SIM.

    Context {re1: relate_impl_HP}.
  
    Lemma flatmem_copy_aux_exists:
      forall n hh hh' lh from to (f: meminj),
        flatmem_copy_aux n from to hh = Some hh' ->
        FlatMem.flatmem_inj hh lh ->
        exists lh',
          flatmem_copy_aux n from to lh = Some lh'
          /\ FlatMem.flatmem_inj hh' lh'.
    Proof.
      induction n.
      - simpl. intros. inv H.
        refine_split'; trivial.
      - intros. simpl in *.
        subdestruct.
        specialize (FlatMem.load_inj _ _ Mint32 from _ f H0 Hdestruct).
        intros (v' & HLD & HVA).
        rewrite HLD. inv HVA.
        set (hh0:= FlatMem.store Mint32 hh to (Vint i)) in *.
        set (lh0:=FlatMem.store Mint32 lh to (Vint i)).
        assert (HF_INJ: FlatMem.flatmem_inj hh0 lh0).
        {
          subst hh0 lh0.
          eapply (FlatMem.store_mapped_inj f); eauto.
        }
        exploit IHn; eauto.
    Qed.

  End MEM_COPY_AUX_SIM.

  Section MEM_COPY'_SIM.

    Context {re1: relate_impl_HP}.
    Context {re3: relate_impl_iflags}.

    Lemma flatmem_copy'_exist:
      forall s habd habd' labd i from to f,
        flatmem_copy'_spec i from to habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', flatmem_copy'_spec i from to labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold flatmem_copy'_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.         
      revert H. subrewrite. 
      subdestruct. inv HQ.
      exploit flatmem_copy_aux_exists; eauto.
      eapply relate_impl_HP_eq; eauto.
      intros (lh' & HCopy' & Hinj).
      rewrite HCopy'. refine_split'; trivial.
      eapply relate_impl_HP_update; eauto.
    Qed.

    Context {mt1: match_impl_HP}.

    Lemma flatmem_copy'_match:
      forall s d d' m i from to f,
        flatmem_copy'_spec i from to d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold flatmem_copy'_spec; intros. subdestruct.
      inv H. eapply match_impl_HP_update. assumption.
    Qed.

    (* This simulation proof is not necessary*)
    Context {inv: PreservesInvariants (HD:= data) flatmem_copy'_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) flatmem_copy'_spec}.

    Lemma flatmem_copy'_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem flatmem_copy'_spec)
            (id ↦ gensem flatmem_copy'_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit flatmem_copy'_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply flatmem_copy'_match; eauto.
    Qed.

  End MEM_COPY'_SIM.

  Section MEM_COPY0_SIM.

    Context {re1: relate_impl_HP}.
    Context {re2: relate_impl_pperm}.
    Context {re3: relate_impl_iflags}.

    Lemma flatmem_copy0_exist:
      forall s habd habd' labd i from to f,
        flatmem_copy0_spec i from to habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', flatmem_copy0_spec i from to labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold flatmem_copy0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.         
      exploit relate_impl_pperm_eq; eauto. intros. 
      revert H. subrewrite. 
      subdestruct. inv HQ.
      exploit flatmem_copy_aux_exists; eauto.
      eapply relate_impl_HP_eq; eauto.
      intros (lh' & HCopy0 & Hinj).
      rewrite HCopy0. refine_split'; trivial.
      eapply relate_impl_HP_update; eauto.
    Qed.

    Context {mt1: match_impl_HP}.

    Lemma flatmem_copy0_match:
      forall s d d' m i from to f,
        flatmem_copy0_spec i from to d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold flatmem_copy0_spec; intros. subdestruct.
      inv H. eapply match_impl_HP_update. assumption.
    Qed.

    (* This simulation proof is not necessary*)
    Context {inv: PreservesInvariants (HD:= data) flatmem_copy0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) flatmem_copy0_spec}.

    Lemma flatmem_copy0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem flatmem_copy0_spec)
            (id ↦ gensem flatmem_copy0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit flatmem_copy0_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply flatmem_copy0_match; eauto.
    Qed.

  End MEM_COPY0_SIM.

  Section MEM_COPY_SIM.

    Context {re1: relate_impl_HP}.
    Context {re2: relate_impl_pperm}.
    Context {re3: relate_impl_iflags}.
    Context {re4: relate_impl_ipt}.

    Lemma flatmem_copy_exist:
      forall s habd habd' labd i from to f,
        flatmem_copy_spec i from to habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', flatmem_copy_spec i from to labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold flatmem_copy_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.         
      exploit relate_impl_pperm_eq; eauto. intros. 
      exploit relate_impl_ipt_eq; eauto. intros.
      revert H. subrewrite. 
      subdestruct. inv HQ.
      exploit flatmem_copy_aux_exists; eauto.
      eapply relate_impl_HP_eq; eauto.
      intros (lh' & HCopy & Hinj).
      rewrite HCopy. refine_split'; trivial.
      eapply relate_impl_HP_update; eauto.
    Qed.

    Context {mt1: match_impl_HP}.

    Lemma flatmem_copy_match:
      forall s d d' m i from to f,
        flatmem_copy_spec i from to d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold flatmem_copy_spec; intros. subdestruct.
      inv H. eapply match_impl_HP_update. assumption.
    Qed.

    (* This simulation proof is not necessary*)
    Context {inv: PreservesInvariants (HD:= data) flatmem_copy_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) flatmem_copy_spec}.

    Lemma flatmem_copy_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem flatmem_copy_spec)
            (id ↦ gensem flatmem_copy_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit flatmem_copy_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply flatmem_copy_match; eauto.
    Qed.

  End MEM_COPY_SIM.

End OBJ_SIM.