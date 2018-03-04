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
(*              General Semantics for Primitives                       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the general semantics for primitives at all layers*)

Require Import Coqlib.
Require Import Maps.
Require Import Globalenvs.
Require Import AsmX.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import AST.
Require Import AuxStateDataType.
Require Import Constant.
Require Import FlatMemory.
Require Import GlobIdent.
Require Import Integers.
Require Import Conventions.
Require Import LAsm.
Require Import CommonTactic.
Require Import AuxLemma.

Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import mCertiKOSType.

Section Semantics.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context {RData} `{HD: CompatData RData}.

  Section uctxseteip.

    Variable uctx_set_eip_spec : RData -> Z -> block -> int -> option RData.

    Inductive extcall_uctxseteip_sem (s: stencil) (WB: block -> Prop):
      list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
    | extcall_uctxseteip_sem_intro: 
        forall m adt adt' i b ofs,
          uctx_set_eip_spec adt (Int.unsigned i) b ofs = Some adt'
          -> (exists fun_id, find_symbol s fun_id = Some b) 
          -> extcall_uctxseteip_sem s WB (Vint i:: Vptr b ofs :: nil) (m, adt) Vundef (m, adt').

    Definition extcall_uctxseteip_info: sextcall_info :=
      {|
        sextcall_step := extcall_uctxseteip_sem;
        sextcall_csig := mkcsig (type_of_list_type (Tint32::Tpointer Tvoid noattr::nil)) Tvoid;
        sextcall_valid s := true
      |}.

    Class UCTXSetEIPInvariants :=
      {
        uctx_set_eip_low_level_invariant n i b ofs d d':
          uctx_set_eip_spec d i b ofs = Some d' ->
          Mem.flat_inj n b = Some (b, 0%Z) ->
          low_level_invariant n d ->
          low_level_invariant n d';
        uctx_set_eip_high_level_invariant b i ofs d d':
          uctx_set_eip_spec d i b ofs = Some d' ->
          high_level_invariant d ->
          high_level_invariant d';
        uctx_set_eip_kernel_mode b i ofs d d':
          uctx_set_eip_spec d i b ofs = Some d' ->
          kernel_mode d'
      }.

    Context `{inv: UCTXSetEIPInvariants}.

    Instance extcall_uctxseteip_invs:
      ExtcallInvariants extcall_uctxseteip_info.
    Proof.
      constructor; intros; inv H.
      - (* low level invariant *)
        eapply uctx_set_eip_low_level_invariant; eauto.
        destruct H8 as [fun_id Hsym].
        eapply stencil_find_symbol_inject'; eauto.
        eapply flat_inj_inject_incr. assumption.
      - (* high level invariant *)
        eapply uctx_set_eip_high_level_invariant; eauto.
      - (* kernel mode*)
        eapply uctx_set_eip_kernel_mode; eauto.
      - (* nextblock *)
        reflexivity.
      - (* inject neutral *)
        split; auto.
      - (* well typed *)
        simpl; trivial.
    Qed.

    Instance extcall_uctxseteip_props:
      ExtcallProperties extcall_uctxseteip_info.
    Proof.
      constructor; intros.
      - (* well typed *)
        inv H. simpl. trivial.
      - (* valid_block *)
        inv H. unfold Mem.valid_block in *.
        lift_unfold. trivial.
      - (* perm *)
        inv H. lift_unfold. trivial.
      - (* unchanges *)
        inv H. simpl. apply Mem.unchanged_on_refl.
      - (* extend *)
        inv H. inv_val_inject. lift_simpl.
        destruct H0 as [HT1 HT2].
        destruct m1' as [? ?]. simpl in *. subst.
        exists Vundef, (m0, adt'). 
        refine_split; eauto.
        + econstructor; eauto.
        + lift_unfold. split; trivial.
        + simpl. apply Mem.unchanged_on_refl.
      - (* inject *)
        inv H0. pose proof H4 as Hsymbol. 
        destruct H4 as [fun_id Hsymbol'].
        apply H in Hsymbol'. 
        inv_val_inject.
        lift_simpl. destruct H1 as [HT1 HT2].
        destruct m1' as [? ?]. simpl in *. subst.
        refine_split; eauto.
        + econstructor; eauto.
        + lift_unfold. split; trivial.
        + apply Mem.unchanged_on_refl.
        + simpl. apply Mem.unchanged_on_refl.
        + constructor; congruence.
      - (* deterministic*)
        inv H. inv H0. 
        split; congruence.
      - (* WB *)
        inv H0. econstructor; eauto.
      - (* load *)
        inv H. lift_unfold. trivial.
    Qed.

    Definition uctx_set_eip_compatsem : compatsem (cdata RData) :=
      compatsem_inl {|
          sextcall_primsem_step := extcall_uctxseteip_info;
          sextcall_props := OK _;
          sextcall_invs := OK _
        |}.

  End uctxseteip.

  Section saveuctx.

    Variable save_uctx_spec : RData -> UContext -> option RData.

    Inductive extcall_saveuctx_sem  (s: stencil) (WB: block -> Prop):
      list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
    | extcall_saveuctx_sem_intro: 
        forall m adt adt' uctx0 vargs v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
          let uctx1:= ZMap.set U_EBX (Vint v4)
                               (ZMap.set U_OESP (Vint v3)
                                         (ZMap.set U_EBP (Vint v2)
                                                   (ZMap.set U_ESI (Vint v1) 
                                                             (ZMap.set U_EDI (Vint v0) (ZMap.init Vundef))))) in
          let uctx2:= ZMap.set U_ES (Vint v8)
                               (ZMap.set U_EAX (Vint v7)
                                         (ZMap.set U_ECX (Vint v6) 
                                                   (ZMap.set U_EDX (Vint v5) uctx1))) in
          let uctx3:= ZMap.set U_EIP (Vint v12)
                               (ZMap.set U_ERR (Vint v11) 
                                         (ZMap.set U_TRAPNO (Vint v10) 
                                                   (ZMap.set U_DS (Vint v9) uctx2))) in
          let uctx4:= ZMap.set U_SS (Vint v16) 
                               (ZMap.set U_ESP (Vint v15) 
                                         (ZMap.set U_EFLAGS (Vint v14)
                                                   (ZMap.set U_CS (Vint v13) uctx3))) in
          save_uctx_spec adt uctx0 = Some adt'
          -> uctx0 = uctx4
          -> vargs = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v4 :: Vint v5 :: Vint v6
                           :: Vint v7 :: Vint v8 :: Vint v9:: Vint v10 :: Vint v11 :: Vint v12
                           :: Vint v13 :: Vint v14 :: Vint v15:: Vint v16 ::nil)
          -> extcall_saveuctx_sem s WB vargs (m, adt) Vundef (m, adt').

    Definition extcall_saveuctx_info: sextcall_info :=
      {|
        sextcall_step := extcall_saveuctx_sem;
        sextcall_csig := mkcsig (type_of_list_type 
                                   (Tint32::Tint32::Tint32::Tint32::
                                          Tint32::Tint32::Tint32::Tint32::
                                          Tint32::Tint32::Tint32::Tint32::
                                          Tint32::Tint32::Tint32::Tint32::
                                          Tint32::nil)) Tvoid;
        sextcall_valid s := true
      |}.


    Class SaveUCtxInvariants :=
      {
        save_uctx_low_level_invariant n v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 d d':
          let uctx1:= ZMap.set U_EBX (Vint v4)
                               (ZMap.set U_OESP (Vint v3)
                                         (ZMap.set U_EBP (Vint v2)
                                                   (ZMap.set U_ESI (Vint v1) 
                                                             (ZMap.set U_EDI (Vint v0) (ZMap.init Vundef))))) in
          let uctx2:= ZMap.set U_ES (Vint v8)
                               (ZMap.set U_EAX (Vint v7)
                                         (ZMap.set U_ECX (Vint v6) 
                                                   (ZMap.set U_EDX (Vint v5) uctx1))) in
          let uctx3:= ZMap.set U_EIP (Vint v12)
                               (ZMap.set U_ERR (Vint v11) 
                                         (ZMap.set U_TRAPNO (Vint v10) 
                                                   (ZMap.set U_DS (Vint v9) uctx2))) in
          let uctx4:= ZMap.set U_SS (Vint v16) 
                               (ZMap.set U_ESP (Vint v15) 
                                         (ZMap.set U_EFLAGS (Vint v14)
                                                   (ZMap.set U_CS (Vint v13) uctx3))) in
          save_uctx_spec d uctx4 = Some d' ->
          low_level_invariant n d ->
          low_level_invariant n d';
        save_uctx_high_level_invariant uctxt4 d d':
          save_uctx_spec d uctxt4 = Some d' ->
          high_level_invariant d ->
          high_level_invariant d';
        save_uctx_kernel_mode uctxt4 d d':
          save_uctx_spec d uctxt4 = Some d' ->
          kernel_mode d'
      }.

    Context `{inv: SaveUCtxInvariants}.

    Instance extcall_saveuctx_invs:
      ExtcallInvariants extcall_saveuctx_info.
    Proof.
      constructor; intros; inv H.
      - (* low level invariant *)
        eapply save_uctx_low_level_invariant; eauto.
      - (* high level invariant *)
        eapply save_uctx_high_level_invariant; eauto.
      - (* kernel mode*)
        eapply save_uctx_kernel_mode; eauto.
      - (* nextblock *)
        reflexivity.
      - (* inject neutral *)
        split; auto.
      - (* well typed *)
        simpl; trivial.
    Qed.

    Instance extcall_saveuctx_props:
      ExtcallProperties extcall_saveuctx_info.
    Proof.
      constructor; intros.
      - (* well typed *)
        inv H. simpl. trivial.
      - (* valid_block *)
        inv H. unfold Mem.valid_block in *.
        lift_unfold. trivial.
      - (* perm *)
        inv H. lift_unfold. trivial.
      - (* unchanges *)
        inv H. simpl. apply Mem.unchanged_on_refl.
      - (* extend *)
        inv H. inv_val_inject. lift_simpl.
        destruct H0 as [HT1 HT2].
        destruct m1' as [? ?]. simpl in *. subst.
        refine_split; eauto.
        + econstructor; eauto.
          reflexivity.
        + lift_unfold. split; trivial.
        + simpl. apply Mem.unchanged_on_refl.
      - (* inject *)
        inv H0. inv_val_inject.
        lift_simpl. destruct H1 as [HT1 HT2].
        destruct m1' as [? ?]. simpl in *. subst.
        refine_split; eauto.
        + econstructor; eauto.
          reflexivity.
        + lift_unfold. split; trivial.
        + apply Mem.unchanged_on_refl.
        + simpl. apply Mem.unchanged_on_refl.
        + constructor; congruence.
      - (* deterministic*)
        inv H. inv H0. 
        subst uctx8 uctx7 uctx6 uctx5 uctx4 uctx3 uctx2 uctx1.
        inv H8. split; congruence.
      - (* WB *)
        inv H0. econstructor; eauto.
        reflexivity.
      - (* load *)
        inv H. lift_unfold. trivial.
    Qed.

    Definition save_uctx_compatsem : compatsem (cdata RData) :=
      compatsem_inl {|
          sextcall_primsem_step := extcall_saveuctx_info;
          sextcall_props := OK _;
          sextcall_invs := OK _
        |}.

  End saveuctx.

  Section RestoreUCtx.
    
    Local Open Scope Z_scope.
    Require Import Conventions.

    Variable restore_uctx_spec : RData -> option (RData * UContext).
    Variable cid : RData -> Z.

    Inductive primcall_restoreuctx_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_restoreuctx_sem_intro: 
        forall m rs rs' adt adt' sig n b,
          find_symbol s restore_uctx = Some b ->
          rs PC = Vptr b Int.zero ->
          restore_uctx_spec adt = Some (adt', rs') ->
          sig = mksignature (AST.Tint::nil) None cc_default ->
          extcall_arguments rs m sig (Vint n ::nil) ->
          cid adt = Int.unsigned n ->
          forall N_TYPE: (forall i, 0 <= i < UCTXT_SIZE ->
                                    let v:= (ZMap.get i rs') in
                                    Val.has_type v AST.Tint),
          forall N_INJECT_NEUTRAL: (forall i, 0 <= i < UCTXT_SIZE ->
                                              let v:= (ZMap.get i rs') in
                                              val_inject (Mem.flat_inj (Mem.nextblock m)) v v),
            let rs0 := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                                       :: IR ECX :: IR EAX :: RA :: nil) 
                                   (undef_regs (List.map preg_of destroyed_at_call) rs))
                         # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                         # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                         # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                         # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                         # PC <- (ZMap.get U_EIP rs') in
            primcall_restoreuctx_sem s rs (m, adt) rs0 (m, adt').

    Section WithInv.

      Class RestoreUCtxInvariants :=
        {
          restore_uctx_low_level_invariant n rs d d':
            restore_uctx_spec d = Some (d', rs) ->
            low_level_invariant n d ->
            low_level_invariant n d';
          restore_uctx_high_level_invariant rs d d':
            restore_uctx_spec d = Some (d', rs) ->
            high_level_invariant d ->
            high_level_invariant d'
        }.

      Local Instance primcall_restoreuctx_sem_propertes:
        PrimcallProperties primcall_restoreuctx_sem.
      Proof.
        constructor; intros; inv H.
        - (* deterministic *)
          inv H0. split; congruence.
      Qed.

      Context `{inv: RestoreUCtxInvariants}.

      Local Instance primcall_restoreuctx_sem_invariants:
        PrimcallInvariants primcall_restoreuctx_sem.
      Proof.
        constructor; intros; inv H; trivial.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto.
            val_inject_simpl;
              try (eapply N_INJECT_NEUTRAL; omega).
          + (* wt_regset*)
            repeat apply set_reg_wt; try eapply N_INJECT_NEUTRAL; 
            try constructor; try assumption; simpl;
            eapply N_TYPE; omega.
        - (* low level invariant*)
          eapply restore_uctx_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply restore_uctx_high_level_invariant; eauto.
      Qed.

      Definition primcall_restoreuctx_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_restoreuctx_sem;
                sprimcall_sig := mksignature (AST.Tint::nil) None cc_default;
                sprimcall_valid s := true
              |};
            sprimcall_name := None;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End RestoreUCtx.

  Section ELFLOAD.

    (** * Prove that the semantics of primitives satisfy the requirements of Compcert's external function calls *)
    Inductive extcall_elf_load_sem  (s: stencil) (WB: block -> Prop):
      list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
    | extcall_elf_load_sem_intro: 
        forall m n be ofse,
          (exists elf_id, find_symbol s elf_id = Some be) 
          -> kernel_mode (snd m)
          -> extcall_elf_load_sem s WB (Vptr be ofse:: Vint n ::nil) m Vundef m.

    Definition extcall_elf_load_info: sextcall_info :=
      {|
        sextcall_step := extcall_elf_load_sem;
        sextcall_csig := mkcsig (type_of_list_type (Tpointer Tvoid noattr::Tint32::nil)) Tvoid;
        sextcall_valid s := true
      |}.

    Instance extcall_elf_load_invs:
      ExtcallInvariants extcall_elf_load_info.
    Proof.
      constructor; intros; inv H; trivial.
      - (* nextblock *)
        reflexivity.
      - (* inject neutral *)
        split; auto.
      - (* well typed *)
        simpl; trivial.
    Qed.

    Instance extcall_elf_load_props:
      ExtcallProperties extcall_elf_load_info.
    Proof.
      constructor; intros; try (inv H; simpl; trivial).
      - (* unchanges *)
        apply Mem.unchanged_on_refl.
      - (* extend *)
        inv_val_inject. lift_simpl.
        destruct H0 as [HT1 HT2].
        destruct m1' as [? ?]. simpl in *. subst.
        refine_split; eauto.
        + econstructor; eauto.
        + lift_unfold. split; trivial.
        + simpl. apply Mem.unchanged_on_refl.
      - (* inject *)
        inv H0. pose proof H3 as Hsymbol. 
        destruct H3 as [fun_id Hsymbol'].
        apply H in Hsymbol'. 
        inv_val_inject.
        lift_simpl. destruct H1 as [HT1 HT2].
        destruct m1' as [? ?]. simpl in *. subst.
        refine_split; eauto.
        + econstructor; eauto.
        + lift_unfold. split; trivial.
        + apply Mem.unchanged_on_refl.
        + simpl. apply Mem.unchanged_on_refl.
        + constructor; congruence.
      - (* deterministic*)
        inv H0. split; congruence.
      - (* WB *)
        inv H0. econstructor; eauto.
    Qed.

    Definition elf_load_compatsem : compatsem (cdata RData) :=
      compatsem_inl {|
          sextcall_primsem_step := extcall_elf_load_info;
          sextcall_props := OK _;
          sextcall_invs := OK _
        |}.

  End ELFLOAD.

End Semantics.