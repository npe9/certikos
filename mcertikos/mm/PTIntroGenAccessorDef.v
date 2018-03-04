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
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Refinement proof for PTIntro layer                         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MAL layer and MPTIntro layer*)
Require Import PTIntroGenDef.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Lemma flatmem_store_exists:
      forall hadt ladt hadt' t v v' f m s ofs,
        flatmem_store hadt t ofs v = Some hadt'
        -> relate_RData f hadt ladt
        -> match_RData s hadt m f
        -> val_inject f v v'
        -> ofs mod PgSize <= PgSize - size_chunk t
        -> exists ladt',
             flatmem_store ladt t ofs v' = Some ladt'
             /\ relate_RData f hadt' ladt'
             /\ PT hadt' = PT hadt
             /\ ptpool hadt' = ptpool hadt
             /\ CR3 ladt' = CR3 ladt
             /\ pperm hadt' = pperm hadt
             /\ idpde hadt' = idpde hadt.
    Proof.
      unfold flatmem_store, flatmem_store. intros.
      revert H. inv H0. subrewrite. pose proof pperm_re as Hpp.
      specialize (pperm_re (PageI ofs)).
      destruct (ZMap.get (PageI ofs) (pperm hadt)) eqn:Hp'; contra_inv.
      assert (HW: ZMap.get (PageI ofs) (pperm ladt) = PGAlloc (*PGFreeable*)).
      {
        inv pperm_re; reflexivity.
      }
      rewrite HW. inv HQ; simpl.
      refine_split'; eauto.
      constructor; trivial; simpl. 
      - (* flatmem *)
        eapply (FlatMem.store_mapped_inj f); eauto 1.
      - (* PMap *)
        constructor; intros. inv relate_PMap_re.
        erewrite FlatMem.load_store_other; eauto 2. simpl.
        assert (~ pi * PgSize + vadr * 4 - size_chunk t < ofs < pi * PgSize + vadr * 4 + 4).
        {
          red; intros.
          assert (PageI ofs = pi).
          {
            revert H7 H5 H3. clear; intros.
            exploit  (Z_mod_lt ofs PgSize). omega.
            intros Hofs.
            rewrite (Z_div_mod_eq ofs PgSize) in H7 |-*; try omega.
            assert (HW: (ofs / 4096) = pi).
            {
              destruct (zeq pi (ofs / 4096)); subst; trivial.
              destruct (zle (pi + 1) (ofs / 4096)); rewrite_omega.
            }
            subst. unfold PageI.
            replace (PgSize * (ofs / PgSize)) with ((ofs / PgSize) * PgSize) by omega.
            rewrite Z_div_plus_full_l; [| omega].
            rewrite (Zdiv_small (ofs mod PgSize) PgSize); omega.
          }
          subst.
          inv H1. inv H8.
          specialize (H1 _ H). inv H1.
          specialize (H8 _ H0). destruct H8 as (v0 & _ & _ & HMAT).
          unfold PMap, ZMap.t, PMap.t in H4, HMAT. rewrite H4 in HMAT.
          inv HMAT. congruence.
        }
        omega.
    Qed.

    Lemma fstore_exist:
      forall habd habd' labd i v f m s,
        fstore_spec i v habd = Some habd'
        -> relate_RData f habd labd
        -> match_RData s habd m f
        -> exists labd', fstore0_spec i v labd = Some labd' /\ relate_RData f habd' labd'
                         /\ PT habd' = PT habd
                         /\ ptpool habd' = ptpool habd
                         /\ CR3 labd' = CR3 labd
                         /\ pperm habd' = pperm habd
                         /\ idpde habd' = idpde habd.
    Proof.
      unfold fstore_spec, fstore0_spec; intros.
      revert H. pose proof H0 as HR.
      inv H0. subrewrite. 
      subdestruct.  
      eapply flatmem_store_exists; eauto. 
      change 4096 with (1024 * 4).
      rewrite Zmult_mod_distr_r. 
      apply mod_chunk.
    Qed.

    Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
    Proof.
      accessor_prop_tac.
      - exploit flatmem_store_exists; eauto.  
        intros (ladt' & HST & Hre & _).
        refine_split'; eauto.
      - functional inversion H6. constructor; simpl; assumption.
    Qed.

  End WITHMEM.

End Refinement.