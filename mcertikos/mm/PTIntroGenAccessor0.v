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
Require Export PTIntroGenAccessorDef.

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    
    Require Import LoadStoreSem1.
    Require Import XOmega.
    Require Import HostAccess1.
    Require Import GuestAccessIntel1.
    Require Import HostAccess2.
    Require Import LoadStoreGeneral.

    Notation lLoad := (fun F V => exec_loadex1 (F:=F) (V:=V)).
    Notation hLoad := (fun F V => exec_loadex2 (F:=F) (V:=V)).

    Lemma load_correct:
      load_accessor_sim_def HDATAOps LDATAOps (one_crel HDATA LDATA) hLoad lLoad.
    Proof.
      unfold load_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. inv match_extcall_states.

      unfold exec_loadex2 in *. 
      unfold exec_loadex1. 
      unfold exec_host_load1, exec_host_load2 in *. inv H4.
      exploit (eval_addrmode_correct ge1 ge2 a); eauto. intros HW.
      Local Opaque Z.sub.
      simpl in *. revert H1. inv match_related. subrewrite''. intros HLoad.
      destruct (eval_addrmode ge1 a rs1) eqn: Hev; contra_inv.
      - (* addr is Vint*)
        inv HW. destruct (ihost d2) eqn:HPH; contra_inv.
        destruct (pg d2) eqn:HPE; contra_inv.
        destruct (ikern d2) eqn:HPK; contra_inv.
        specialize (valid_PT refl_equal).
        + (* host *)
          generalize match_match; intros HM. inv match_match. 
          inv H1. inv relate_PT_re. 
          * (* PT = -1 *)
            rewrite <- H7 in valid_PT; omega.  
          * assert (HFB: Genv.find_symbol ge2 PTPool_LOC = Some b).
            {
              inv H0. congruence.
            }
            rewrite HFB. lift_trivial. subrewrite'.
            assert (valid_PT': 0 <= PT d1 < 64) by omega.
            specialize (H5 _ valid_PT').
            set (pt := (ZMap.get (PT d1) (ptpool d1))) in *. inv H5.
            assert (HI: 0<= PDX (Int.unsigned i) <= PDX Int.max_unsigned).
            {
              specialize (Int.unsigned_range_2 i).
              clear. unfold PDX. Local Transparent Z.sub.
              xomega. Local Opaque Z.sub.
            }
            specialize (H7 _ HI).
            destruct H7 as [v[HLD [_ HP]]].    
            assert (HI1: 0<= PTX (Int.unsigned i) <= PTX Int.max_unsigned).
            {
              unfold PTX; change ((Int.max_unsigned / 4096) mod 1024) with 1023.
              specialize (Z_mod_lt (Int.unsigned i/PgSize) one_k).
              omega.
            }
            (*unfold PMap, ZMap.t, PMap.t in *.*)
            inv HP; try rewrite <- H9 in HLoad; try rewrite <- H5 in HLoad; contra_inv.
            pose proof relate_PMap_re as HPP.
            inv HPP. specialize (H9 _ valid_PT' _ HI pi pdx).
            rewrite H5 in H9. specialize (H9 refl_equal _ HI1).
            destruct H9 as [v1[HLD1 HP]].
            rewrite Int.unsigned_repr; [|rewrite_omega]. 
            rewrite HLD, H7.
            rewrite Z_div_plus_full_l; [|omega].
            rewrite (Zdiv_small PT_PERM_PTU); [|omega].
            rewrite Z.add_0_r. rewrite HLD1. clear HLD1.
            destruct (zle (Int.unsigned i mod 4096) (4096 - size_chunk chunk)); contra_inv.
            destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned i mod 4096)
                                  (Memdata.align_chunk_pos chunk)); contra_inv.
            inv HP; try rewrite <- H11 in HLoad; contra_inv. 
            {
              change (Int.unsigned Int.zero mod 4096) with 0; simpl.
              eapply pagefault_correct; eauto.
            }
            {
              rewrite <- H9 in HLoad; contra_inv. rewrite H12.
              assert (HW1: (padr * PgSize + v) mod PgSize = v mod PgSize).
              {
                rewrite Zplus_mod.
                rewrite Z_mod_mult.
                rewrite Z.add_0_l.
                apply Zmod_mod.
              }
              assert (HW2: (padr * PgSize + v) / PgSize = padr).
              {
                rewrite Z_div_plus_full_l; [|omega].
                rewrite (Zdiv_small v). omega.
                functional inversion H11; subst; omega.
              }
              rewrite HW1, HW2.
              functional inversion H11; rewrite <- H13 in HLoad; contra_inv;
              (rewrite Zmod_small; trivial; [|omega]; simpl;
               eapply exec_flatmem_load_correct; eauto).
            }
        + (* guest *)
          eapply guest_intel_load_correct1; eauto.
      - (* adr is (b,ofs) *)
        inv HW; subdestruct; eapply loadl_correct; eauto.
    Qed.

  End WITHMEM.

End Refinement.