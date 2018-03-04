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
(*          Refinement proof for MALInit layer                         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MBoot layer and MALInit layer*)
Require Import BootGenDef.
Require Import BootGenLemma.
Require Import BootGenAccessorDef.
Require Import GuestAccessIntelRef0.

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).
    
    Notation hLoad := (fun F V => exec_loadex1 (F:=F) (V:=V)).
    Notation lLoad := (fun F V => exec_loadex0 (F:=F) (V:=V)).

    Require Import XOmega.
    Require Import HostAccess0.
    Require Import HostAccess1.

    Lemma exec_flatmem_load_correct0:
      forall {F V: Type} (ge2: Genv.t F V) (s: stencil) ι (m1 m2 m1': mem) rs1 rs2 rs1' (d1 d1': HDATAOps) d2 r chunk n,
        exec_flatmem_load chunk (m1, d1) n rs1 r =
        Next rs1' (m1', d1') ->
        MatchPrimcallStates (one_crel (CompatRelOps0:= rel_ops) HDATAOps LDATAOps) s ι rs1 m1 d1 rs2 m2 d2 ->
        stencil_matches s ge2 ->
        0 <= n <= adr_max - size_chunk chunk ->
        (align_chunk chunk | n) ->
        exists rs2' m2' d2',
          Asm.exec_load (mem:= mwd LDATAOps) ge2 chunk (m2, d2)
                        (Addrmode None None (inr (FlatMem_LOC, Int.repr n)))
                        rs2 r = Next rs2' (m2', d2') /\
          MatchPrimcallStates (one_crel (CompatRelOps0:= rel_ops) HDATAOps LDATAOps) s ι rs1' m1' d1' rs2' m2' d2'.
    Proof.
      intros. inv H0.
      pose proof match_extcall_states as Hmatch.
      inv match_extcall_states.
      inv match_match. inv H0.
      unfold Asm.exec_load. simpl.
      assert (Hsym': Genv.find_symbol ge2 FlatMem_LOC = Some b).
      {
        inv H1. congruence.
      }
      unfold symbol_offset. rewrite Hsym'.
      Opaque Z.sub.
      unfold exec_flatmem_load in *.
      exploit flatmem_load_correct0; eauto.
      simpl. lift_trivial.
      repeat rewrite Int.add_zero.          
      intros (v' & HLoad & HVal).
      Transparent Z.sub.
      pose proof (size_chunk_pos chunk) as HOS3.
      rewrite Int.unsigned_repr; [|rewrite_omega].
      rewrite HLoad. inv H.
      refine_split'; eauto 1.
      constructor; eauto.
      val_inject_simpl.
    Qed.

    Opaque align_chunk Z.mul Z.div Z.sub. 

    Require Import LoadStoreGeneral.

    Lemma load_correct:
      load_accessor_sim_def HDATAOps LDATAOps (one_crel HDATAOps LDATAOps) hLoad lLoad.
    Proof.
      unfold load_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. pose proof match_extcall_states as Hext. inv match_extcall_states.

      unfold exec_loadex1 in *. 
      unfold exec_loadex0. 
      unfold exec_host_load0, exec_host_load1 in *.
      unfold exec_host_load_snd0.
      inv H4.
      exploit (eval_addrmode_correct ge1 ge2 a); eauto. simpl; intros HW.
      revert H1. simpl in *.
      inv match_related. subrewrite''. intros HLoad.
      destruct (eval_addrmode ge1 a rs1) eqn: H1; contra_inv.
      - (* addr is Vint*)
        inv HW. 
        destruct (ihost d2) eqn: HPH; contra_inv.
        destruct (pg d2) eqn: HPE; contra_inv.      
        + (* host *)
          destruct (CR3 d2); contra_inv.
          destruct (Genv.find_symbol ge1 b) eqn:Hsymol; contra_inv.
          assert (HFB: Genv.find_symbol ge2 b = Some b0).
          {
            inv H. inv H0. congruence.
          }
          rewrite HFB. 
          revert HLoad.
          lift_trivial. intros HLoad.
          exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
          destruct (Mem.load Mint32 m1 b0 (Int.unsigned (Int.repr (Int.unsigned ofs + PDX (Int.unsigned i) * 4))))
                   eqn: HLD; contra_inv.
          exploit Mem.load_inject; eauto.
          rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
          rewrite HLD1. clear HLD HLD1.
          destruct v; contra_inv. inv HVAL.
          inv match_match. inv H2.
          assert (HFB': Genv.find_symbol ge2 FlatMem_LOC = Some b1).
          {
            inv H. inv H0. congruence.
          }
          rewrite HFB'.
          destruct (FlatMem.load Mint32 (HP d1)
                                 (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4))
                   eqn: HLD; contra_inv.
          pose proof (PTX_Addr_range i0 i) as HPTX_Range.
          pose proof (PTX_Addr_divide i0 i) as HPTX_Divide.
          exploit flatmem_load_correct0; eauto.
          simpl; lift_trivial.
          intros (v' & HLD' & HVAL). inv HVAL.
          pose proof (PTX_Addr_range' i0 i) as HPTX_Range'.
          rewrite Int.unsigned_repr; trivial.
          rewrite HLD'.
          destruct (zle (Int.unsigned i mod 4096) (4096 - size_chunk chunk)); contra_inv.
          destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned i mod 4096)
                                (Memdata.align_chunk_pos chunk)); contra_inv.
          pose proof (PTADDR_range (Int.unsigned i) i1 chunk l) as HOS1.
          pose proof (PTADDR_divide (Int.unsigned i) i1 chunk d) as HOS2.
          subdestruct.
          * eapply exec_flatmem_load_correct0; eauto 1.
          * eapply exec_flatmem_load_correct0; eauto 1.
          * eapply pagefault_correct; eauto.
        + eapply guest_intel_correct1; eauto.
          unfold GuestAccessIntel1.load_accessor1, GuestAccessIntel0.load_accessor0. 
          intros. subdestruct.
          eapply exec_flatmem_load_correct0; eauto 1.
          * eapply PTADDR_range; assumption.
          * eapply PTADDR_divide; assumption.  
      - (* adr is (b,ofs) *)
        inv HW; subdestruct. eapply loadl_correct; eauto.
    Qed.

  End WITHMEM.

End Refinement.