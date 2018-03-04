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
Require Export mCertiKOSType.

Section Semantics.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context {RData} `{HD: CompatData RData}.

  Section set_cr3.

    Variable setCR3: RData -> globalpointer -> option RData.

    Inductive extcall_setcr3_sem  (s: stencil) (WB: block -> Prop):
      list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
    | extcall_setcr3_sem_intro: 
        forall m adt adt' id ofs b,
          setCR3 adt (GLOBP id ofs) = Some adt'
          -> find_symbol s id = Some b
          -> extcall_setcr3_sem s WB ((Vptr b ofs) :: nil) (m, adt) Vundef (m, adt').

    Definition extcall_setcr3_info: sextcall_info :=
      {|
        sextcall_step := extcall_setcr3_sem;
        sextcall_csig := mkcsig (type_of_list_type (Tpointer Tvoid noattr::nil)) Tvoid;
        sextcall_valid s := true
      |}.

    Class SetCR3Invariants :=
      {
        setcr3_low_level_invariant n d gp d':
          setCR3 d gp = Some d' ->
          low_level_invariant n d ->
          low_level_invariant n d';
        setcr3_high_level_invariant d gp d':
          setCR3 d gp = Some d' ->
          high_level_invariant d ->
          high_level_invariant d';
        setcr3_kernel_mode d gp d':
          setCR3 d gp = Some d' ->
          kernel_mode d ->
          kernel_mode d'
      }.

    Section WithInv.

      Context`{inv_ops: SetCR3Invariants}.

      Instance extcall_setcr3_invs:
        ExtcallInvariants extcall_setcr3_info.
      Proof.
        constructor; intros; inv H.
        - (* low level invariant *)
          eapply setcr3_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply setcr3_high_level_invariant; eauto.
        - (* kernel mode*)
          eapply setcr3_kernel_mode; eauto.
        - (* nextblock *)
          reflexivity.
        - (* inject neutral *)
          split; auto.
        - (* well typed *)
          simpl; trivial.
      Qed.

      Instance extcall_setcr3_props:
        ExtcallProperties extcall_setcr3_info.
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
          inv H0. pose proof H4 as Hsymbol. apply H in H4. 
          inv_val_inject.
          lift_simpl. destruct H1 as [HT1 HT2].
          destruct m1' as [? ?]. simpl in *. subst.
          exists f, Vundef, (m0, adt'). 
          refine_split; eauto.
          + econstructor; eauto.
          + lift_unfold. split; trivial.
          + apply Mem.unchanged_on_refl.
          + simpl. apply Mem.unchanged_on_refl.
          + constructor; congruence.
        - (* deterministic*)
          inv H. inv H0. 
          specialize (genv_vars_inj _ _ _ _ H2 H9). 
          intros; subst. split; congruence.
        - (* WB *)
          inv H0. econstructor; eauto.
        - (* load *)
          inv H. lift_unfold. trivial.
      Qed.

      Definition setCR3_compatsem : compatsem (cdata RData) :=
        compatsem_inl {|
            sextcall_primsem_step := extcall_setcr3_info;
            sextcall_props := OK _;
            sextcall_invs := OK _
          |}.

    End WithInv.

  End set_cr3.

  Section Prim_Generic.

    Variable prim_generic: RData -> option RData.

    Context `{prim_ident: ident}.

    (** XXX: this should be using CompatGenSem.v eventually (is is
      somewhat duplicated) -- jeremie 2014-06-17 *)

    Inductive primcall_general_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_general_sem_intro: 
        forall m adt adt' rs,
          prim_generic adt = Some adt' ->
          primcall_general_sem s rs (m, adt) (rs#PC <- (rs RA)) (m, adt').

    Inductive primcall_general_sem' (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_general_sem_intro': 
        forall m adt adt' rs b,
          find_symbol s prim_ident = Some b ->
          rs PC = Vptr b Int.zero ->
          prim_generic adt = Some adt' ->
          primcall_general_sem' s rs (m, adt) (rs#RA <- Vundef#PC <- (rs RA)) (m, adt').

    Class PrimInvariants :=
      {
        prim_low_level_invariant n d d':
          prim_generic d = Some d' ->
          low_level_invariant n d ->
          low_level_invariant n d';
        prim_high_level_invariant d d':
          prim_generic d = Some d' ->
          high_level_invariant d ->
          high_level_invariant d'
      }.

    Section WithInv.

      Context`{inv_ops: PrimInvariants}.

      Local Instance primcall_general_sem_propertes:
        PrimcallProperties primcall_general_sem.
      Proof.
        constructor; intros; inv H; simpl.
        - (* deterministic *)
          inv H0. split; congruence.
      Qed.

      Local Instance primcall_general_sem_invariants:
        PrimcallInvariants primcall_general_sem.
      Proof.
        constructor; intros; inv H.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto.
            apply set_reg_inject; auto.
          + (* wt_regset*)
            apply set_reg_wt; eauto.
            simpl. apply inv_reg_wt.
        - (* low level invariant*)
          eapply prim_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply prim_high_level_invariant; eauto.
      Qed.

      Definition primcall_general_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_general_sem;
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := None;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

      Local Instance primcall_general_sem_propertes':
        PrimcallProperties primcall_general_sem'.
      Proof.
        constructor; intros; inv H; simpl.
        - (* deterministic *)
          inv H0. split; congruence.
      Qed.

      Local Instance primcall_general_sem_invariants':
        PrimcallInvariants primcall_general_sem'.
      Proof.
        constructor; intros; inv H; simpl.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto.
            apply set_reg_inject; auto.
            apply undef_reg_inject; auto.
          + (* wt_regset*)
            apply set_reg_wt; eauto.
            simpl. apply inv_reg_wt.
            apply undef_reg_wt; auto.
        - (* low level invariant*)
          eapply prim_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply prim_high_level_invariant; eauto.
      Qed.

      Definition primcall_general_compatsem' : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_general_sem';
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := Some prim_ident;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End Prim_Generic.

  Section Trap_Get.

    Variable trap_info_get: RData -> int.

    Inductive primcall_trap_info_get_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_trap_info_get_sem_intro: 
        forall m adt n rs,
          trap_info_get adt = n
          -> primcall_trap_info_get_sem s rs (m, adt) (rs # EAX <- (Vint n) # PC <- (rs RA)) (m, adt).

    Section WithInv.

      Local Instance primcall_trap_info_get_sem_propertes:
        PrimcallProperties primcall_trap_info_get_sem.
      Proof.
        constructor; intros; inv H; simpl.
        - (* deterministic *)
          inv H0. split; congruence.
      Qed.

      Local Instance primcall_trap_info_get_sem_invariants:
        PrimcallInvariants primcall_trap_info_get_sem.
      Proof.
        constructor; intros; inv H; trivial.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto.
            val_inject_simpl.
          + (* wt_regset*)
            apply set_reg_wt; eauto.
            simpl. apply inv_reg_wt.
            apply set_reg_wt; eauto.
            simpl; trivial.
      Qed.

      Definition primcall_trap_info_get_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_trap_info_get_sem;
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := None;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End Trap_Get.

  Section Trap_Ret.

    Variable trap_info_ret: RData -> val.

    Inductive primcall_trap_info_ret_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_trap_info_ret_sem_intro: 
        forall m adt n rs,
          trap_info_ret adt = n
          -> forall N_TYPE: Val.has_type n (typ_of_preg PC),
             forall N_INJECT_NEUTRAL: val_inject (Mem.flat_inj (Mem.nextblock m)) n n,
               primcall_trap_info_ret_sem s rs (m, adt) (rs # PC <- n) (m, adt).

    Section WithInv.

      Local Instance primcall_trap_info_ret_sem_propertes:
        PrimcallProperties primcall_trap_info_ret_sem.
      Proof.
        constructor; intros; inv H; simpl.
        - (* deterministic *)
          inv H0. split; congruence.
      Qed.

      Local Instance primcall_trap_info_ret_sem_invariants:
        PrimcallInvariants primcall_trap_info_ret_sem.
      Proof.
        constructor; intros; inv H; trivial.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto.
            val_inject_simpl.
          + (* wt_regset*)
            apply set_reg_wt; eauto.
      Qed.

      Definition primcall_trap_info_ret_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_trap_info_ret_sem;
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := None;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End Trap_Ret.

  Section KCtxt_Switch.

    Variable kctxt_switch: RData -> Z -> Z -> regset -> option (RData * regset).

    Inductive primcall_kctxt_switch_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_kctxtswitch_sem_intro: 
        forall m (rs rs' rs1: regset) n n' adt adt' b,
          kctxt_switch adt (Int.unsigned n) (Int.unsigned n') rs1 = Some (adt', rs') 
          -> forall N_TYPE: (forall v r, ZtoPreg v = Some r -> Val.has_type (rs'#r) AST.Tint),
             forall N_INJECT_NEUTRAL: (forall v r, ZtoPreg v = Some r 
                                                   -> val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)),
             forall N_ADT_ARU: rs1 = (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                                          #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA),
             forall N_ARU1: rs EAX = Vint n,
             forall N_ARU2: rs EDX = Vint n',
             forall Hsymbol: find_symbol s GlobIdent.kctxt_switch = Some b,
             forall HPC: rs PC = Vptr b Int.zero,
               let rs0 := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                         :: IR EDX :: IR ECX :: IR EAX :: RA :: nil) rs) in
               primcall_kctxt_switch_sem s rs (m, adt) 
                                         (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                                             #EBP <- (rs'#EBP)#PC <- (rs'#RA)) (m, adt').

    Class KCtxtSwitchInvariants :=
      {
        kctxt_switch_low_level_invariant s m n1 n2 rs rs' d d':
          kctxt_switch d n1 n2 (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                       #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA) = Some (d', rs') ->
          asm_invariant s rs m -> 
          low_level_invariant (Mem.nextblock m) d ->
          low_level_invariant (Mem.nextblock m) d';
        kctxt_switch_high_level_invariant n1 n2 rs rs' d d':
          kctxt_switch d n1 n2 rs = Some (d', rs') ->
          high_level_invariant d ->
          high_level_invariant d'
      }.

    Section WithInv.

      Context`{inv_ops: KCtxtSwitchInvariants}.

      Local Instance primcall_kctxt_switch_sem_propertes:
        PrimcallProperties primcall_kctxt_switch_sem.
      Proof.
        constructor; intros; inv H.
        - (* deterministic *)
          inv H0.  subst rs0 rs2. split; congruence.
      Qed.

      Local Instance primcall_kctxt_switch_sem_invariants:
        PrimcallInvariants primcall_kctxt_switch_sem.
      Proof.
        constructor; intros; inv H; trivial.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto.
            subst rs2.
            val_inject_simpl;
              try (eapply N_INJECT_NEUTRAL;
                   apply PregToZ_correct; simpl; reflexivity).
          + (* wt_regset*)
            repeat apply set_reg_wt; try eapply N_INJECT_NEUTRAL; 
            try constructor; try assumption; simpl;
            eapply N_TYPE; apply PregToZ_correct; simpl; reflexivity.
        - (* low level invariant*)
          eapply kctxt_switch_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply kctxt_switch_high_level_invariant; eauto.
      Qed.

      Definition primcall_kctxt_switch_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_kctxt_switch_sem;
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := Some GlobIdent.kctxt_switch;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End KCtxt_Switch.

  Section DNew.

    Variable dnew: RData -> block -> block -> int -> Z -> Z -> option (RData* Z).
    
    Inductive extcall_dnew_sem  (s: stencil) (WB: block -> Prop):
      list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
    | extcall_dnew_sem_intro: 
        forall m adt adt' n b b' ofs' id q,
          dnew adt b b' ofs' (Int.unsigned id) (Int.unsigned q) = Some (adt', Int.unsigned n)
          -> find_symbol s STACK_LOC = Some b 
          -> (exists fun_id, find_symbol s fun_id = Some b') 
          -> extcall_dnew_sem s WB (Vptr b' ofs' :: Vint id :: Vint q :: nil) 
                              (m, adt) (Vint n) (m, adt').

    Definition extcall_dnew_info: sextcall_info :=
      {|
        sextcall_step := extcall_dnew_sem;
        sextcall_csig := mkcsig (type_of_list_type (Tpointer Tvoid noattr::Tint32::Tint32::nil)) Tint32;
        sextcall_valid s := true
      |}.

    Class DNewInvariants :=
      {
        dnew_low_level_invariant n d d' b b' ofs' id q n':
          dnew d b b' ofs' id q = Some (d', n') ->
          low_level_invariant n d ->
          Mem.flat_inj n b = Some (b, 0%Z) ->
          Mem.flat_inj n b' = Some (b', 0%Z) ->
          low_level_invariant n d';
        dnew_high_level_invariant d d' b b' ofs' id q n':
          dnew d b b' ofs' id q = Some (d', n') ->
          high_level_invariant d ->
          high_level_invariant d';
        dnew_kernel_mode d d'  b b' ofs' id q n':
          dnew d b b' ofs' id q = Some (d', n') ->
          kernel_mode d ->
          kernel_mode d'
      }.

    Section WithInv.

      Context`{inv_ops: DNewInvariants}.

      Instance extcall_dnew_invs:
        ExtcallInvariants extcall_dnew_info.
      Proof.
        constructor; intros; inv H.
        - (* low level invariant *)
          eapply dnew_low_level_invariant; eauto.
          + eapply stencil_find_symbol_inject'; eauto.
            eapply flat_inj_inject_incr. assumption.
          + destruct H9 as [fun_id Hsymbol].
            eapply stencil_find_symbol_inject'; eauto.
            eapply flat_inj_inject_incr. assumption.            
        - (* high level invariant *)
          eapply dnew_high_level_invariant; eauto.
        - (* kernel mode*)
          eapply dnew_kernel_mode; eauto.
        - (* nextblock *)
          reflexivity.
        - (* inject neutral *)
          split; auto.
        - (* well typed *)
          simpl; trivial.
      Qed.

      Instance extcall_dnew_props:
        ExtcallProperties extcall_dnew_info.
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
          + lift_unfold. split; trivial.
          + simpl. apply Mem.unchanged_on_refl.
        - (* inject *)
          inv H0. pose proof H4 as Hsymbol. apply H in H4. 
          pose proof H5 as Hsymbols'.
          destruct H5 as [fun_id Hfun].
          apply H in Hfun. 
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
          rewrite <- Int.repr_unsigned with n.
          rewrite <- Int.repr_unsigned with n0.
          split; congruence.
        - (* WB *)
          inv H0. econstructor; eauto.
        - (* load *)
          inv H. lift_unfold. trivial.
      Qed.

      Definition dnew_compatsem : compatsem (cdata RData) :=
        compatsem_inl {|
            sextcall_primsem_step := extcall_dnew_info;
            sextcall_props := OK _;
            sextcall_invs := OK _
          |}.

    End WithInv.

  End DNew.

  Section Thread_Schedule.

    Variable thread_schedule: RData -> regset -> option (RData * regset).

    Context `{prim_ident: ident}.

    Inductive primcall_thread_schedule_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_threadschedule_sem_intro: 
        forall m rs rs' rs1 adt adt' b,
          thread_schedule adt rs1 = Some (adt', rs') 
          -> forall N_TYPE: (forall v r, ZtoPreg v = Some r -> Val.has_type (rs'#r) AST.Tint),
             forall N_INJECT_NEUTRAL: (forall v r, ZtoPreg v = Some r 
                                                   -> val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)),
             forall N_ADT_ARU: rs1 = (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                                          #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA),
             forall Hsymbol: find_symbol s prim_ident = Some b,
             forall HPC: rs PC = Vptr b Int.zero,
               let rs0 := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                          :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                                      (undef_regs (List.map preg_of destroyed_at_call) rs)) in
               primcall_thread_schedule_sem s rs (m, adt) 
                                            (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                                                #EBP <- (rs'#EBP)#PC <- (rs'#RA)) (m, adt').

    Class ThreadScheduleInvariants :=
      {
        thread_schedule_low_level_invariant s m rs rs' d d':
          thread_schedule d (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                          #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA) = Some (d', rs') ->
          asm_invariant s rs m -> 
          low_level_invariant (Mem.nextblock m) d ->
          low_level_invariant (Mem.nextblock m) d';
        thread_schedule_high_level_invariant rs rs' d d':
          thread_schedule d rs = Some (d', rs') ->
          high_level_invariant d ->
          high_level_invariant d'
      }.

    Section WithInv.

      Context`{inv_ops: ThreadScheduleInvariants}.

      Local Instance primcall_thread_schedule_sem_propertes:
        PrimcallProperties primcall_thread_schedule_sem.
      Proof.
        constructor; intros; inv H.
        - (* deterministic *)
          inv H0. subst rs0 rs2. split; congruence.
      Qed.

      Local Instance primcall_thread_schedule_sem_invariants:
        PrimcallInvariants primcall_thread_schedule_sem.
      Proof.
        constructor; intros; inv H; trivial.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto. subst rs2.
            val_inject_simpl;
              try (eapply N_INJECT_NEUTRAL;
                   apply PregToZ_correct; simpl; reflexivity).
          + (* wt_regset*)
            repeat apply set_reg_wt; try eapply N_INJECT_NEUTRAL; 
            try constructor; try assumption; simpl;
            eapply N_TYPE; apply PregToZ_correct; simpl; reflexivity.
        - (* low level invariant*)
          eapply thread_schedule_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply thread_schedule_high_level_invariant; eauto.
      Qed.

      Definition primcall_thread_schedule_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_thread_schedule_sem;
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := Some prim_ident;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End Thread_Schedule.

  Section Thread_Transfer.

    Variable thread_transfer: RData -> regset -> Z -> option (RData * regset).

    Inductive primcall_thread_transfer_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_threadtransfer_sem_intro: 
        forall m rs rs' rs1 n adt adt' sig b,
          thread_transfer adt rs1 (Int.unsigned n) = Some (adt', rs') 
          -> sig = mksignature (AST.Tint::nil) None cc_default
          -> extcall_arguments rs m sig (Vint n ::nil) 
          -> forall N_TYPE: (forall v r, ZtoPreg v = Some r -> Val.has_type (rs'#r) AST.Tint),
             forall N_INJECT_NEUTRAL: (forall v r, ZtoPreg v = Some r 
                                                   -> val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)),
             forall N_ADT_ARU: rs1 = (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                                          #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA),
             forall Hsymbol: find_symbol s thread_sleep = Some b,
             forall HPC: rs PC = Vptr b Int.zero,
             let rs0 := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                               :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                                           (undef_regs (List.map preg_of destroyed_at_call) rs)) in
               primcall_thread_transfer_sem s rs (m, adt) 
                                            (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                                                #EBP <- (rs'#EBP)#PC <- (rs'#RA)) (m, adt').

    Class ThreadTransferInvariants :=
      {
        thread_transfer_low_level_invariant s m n' rs rs' d d':
          thread_transfer d (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
                          #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA) n' = Some (d', rs') ->
          asm_invariant s rs m -> 
          low_level_invariant (Mem.nextblock m) d ->
          low_level_invariant (Mem.nextblock m) d';
        thread_transfer_high_level_invariant n' rs rs' d d':
          thread_transfer d rs n' = Some (d', rs') ->
          high_level_invariant d ->
          high_level_invariant d'
      }.

    Section WithInv.

      Context`{inv_ops: ThreadTransferInvariants}.

      Local Instance primcall_thread_transfer_sem_propertes:
        PrimcallProperties primcall_thread_transfer_sem.
      Proof.
        constructor; intros; inv H.
        - (* deterministic *)
          inv H0.
          specialize (extcall_arguments_determ _ _ _ _ _ H3 H9).
          intros HF; inv HF. subst rs0 rs2.
          split; try congruence.
      Qed.

      Local Instance primcall_thread_transfer_sem_invariants:
        PrimcallInvariants primcall_thread_transfer_sem.
      Proof.
        constructor; intros; inv H; trivial.
        - (* asm invariant *)
          inv H0. 
          constructor; eauto.
          + (* inject_neutral *)
            inv inv_inject_neutral.
            constructor; eauto. subst rs2.
            val_inject_simpl;
              try (eapply N_INJECT_NEUTRAL;
                   apply PregToZ_correct; simpl; reflexivity).
          + (* wt_regset*)
            repeat apply set_reg_wt; try eapply N_INJECT_NEUTRAL; 
            try constructor; try assumption; simpl;
            eapply N_TYPE; apply PregToZ_correct; simpl; reflexivity.
        - (* low level invariant*)
          eapply thread_transfer_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply thread_transfer_high_level_invariant; eauto.
      Qed.

      Definition primcall_thread_transfer_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_thread_transfer_sem;
                sprimcall_sig := mksignature (AST.Tint::nil) None cc_default;
                sprimcall_valid s := true
              |};
            sprimcall_name := Some thread_sleep;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End Thread_Transfer.

  Section StartUser.

    Variable start_user: RData -> option (RData * UContext).
    
    Local Open Scope Z_scope.

    Inductive primcall_startuser_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_startuser_sem_intro: 
        forall m rs rs' adt adt' b,
          start_user adt = Some (adt', rs')
          -> forall N_TYPE: (forall i, 0 <= i < UCTXT_SIZE ->
                                       let v:= (ZMap.get i rs') in
                                       Val.has_type v AST.Tint),
             forall N_INJECT_NEUTRAL: (forall i, 0 <= i < UCTXT_SIZE ->
                                                 let v:= (ZMap.get i rs') in
                                                 val_inject (Mem.flat_inj (Mem.nextblock m)) v v),
             forall Hsymbol: find_symbol s proc_start_user = Some b,
             forall HPC: rs PC = Vptr b Int.zero,
               let rs0 := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                                               :: IR ECX :: IR EAX :: RA :: nil) 
                                           (undef_regs (List.map preg_of destroyed_at_call) rs))
                            # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                            # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                            # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                            # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                            # PC <- (ZMap.get U_EIP rs') in
               primcall_startuser_sem s rs (m, adt) rs0 (m, adt').
    
    Class StartUserInvariants :=
      {
        start_user_low_level_invariant n rs d d':
          start_user d = Some (d', rs) ->
          low_level_invariant n d ->
          low_level_invariant n d';
        start_user_high_level_invariant rs d d':
          start_user d = Some (d', rs) ->
          high_level_invariant d ->
          high_level_invariant d'
      }.

    Section WithInv.

      Context`{inv_ops: StartUserInvariants}.

      Local Instance primcall_startuser_sem_propertes:
        PrimcallProperties primcall_startuser_sem.
      Proof.
        constructor; intros; inv H.
        - (* deterministic *)
          inv H0. split; congruence.
      Qed.

      Local Instance primcall_startuser_sem_invariants:
        PrimcallInvariants primcall_startuser_sem.
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
          eapply start_user_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply start_user_high_level_invariant; eauto.
      Qed.

      Definition primcall_start_user_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_startuser_sem;
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := Some proc_start_user;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End StartUser.

  Section ExitUser.

    Variable exit_user: RData -> UContext -> option RData.
    
    Local Open Scope Z_scope.

    Definition exit_sig :=
      mksignature (AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                   AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                   AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                   AST.Tint::nil) None cc_default.

    Inductive primcall_exituser_sem (s: stencil):
      regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_exituser_sem_intro: 
        forall m adt adt' (rs: regset) uctx0 vargs sg v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 b,
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
          exit_user adt uctx0 = Some adt'
          -> uctx0 = uctx4
          -> rs ESP <> Vundef
          -> forall HESP_STACK:
               forall b1 o,
               rs ESP = Vptr b1 o ->
               Ple (genv_next s) b1 /\ Plt b1 (Mem.nextblock m),
             vargs = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v4 :: Vint v5 :: Vint v6
                           :: Vint v7 :: Vint v8 :: Vint v9:: Vint v10 :: Vint v11 :: Vint v12
                           :: Vint v13 :: Vint v14 :: Vint v15:: Vint v16 ::nil)
          (* signature *)
          -> sg = exit_sig
          -> extcall_arguments rs m sg vargs
          -> forall Hsymbol: find_symbol s proc_exit_user = Some b,
             forall HPC: rs PC = Vptr b Int.zero,
               primcall_exituser_sem s rs (m, adt) 
                                     ((undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: IR EBX :: RA :: nil) 
                                                  (undef_regs (List.map preg_of destroyed_at_call) rs)) #PC <- (rs#RA))
                                     (m, adt').
    
    Class ExitUserInvariants :=
      {
        exit_user_low_level_invariant n d d' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16:
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
          exit_user d uctx4 = Some d' ->
          low_level_invariant n d ->
          low_level_invariant n d';
        exit_user_high_level_invariant rs d d':
          exit_user d rs = Some d' ->
          high_level_invariant d ->
          high_level_invariant d'
      }.

    Section WithInv.

      Context`{inv_ops: ExitUserInvariants}.

      Local Instance primcall_exituser_sem_propertes:
        PrimcallProperties primcall_exituser_sem.
      Proof.
        constructor; intros; inv H.
        - (* deterministic *)
          inv H0. subst uctx1 uctx2 uctx3 uctx4 uctx5 uctx6 uctx7 uctx8.
          specialize (extcall_arguments_determ _ _ _ _ _ H6 H13).
          intros HF; inv HF.
          split; congruence.
      Qed.

      Local Instance primcall_exituser_sem_invariants:
        PrimcallInvariants primcall_exituser_sem.
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
            apply set_reg_wt.
            simpl. apply inv_reg_wt.
            repeat apply undef_regs_wt; auto.
        - (* low level invariant*)
          eapply exit_user_low_level_invariant; eauto.
        - (* high level invariant *)
          eapply exit_user_high_level_invariant; eauto.
      Qed.

      Definition primcall_exit_user_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_exituser_sem;
                sprimcall_sig := exit_sig;
                sprimcall_valid s := true
              |};
            sprimcall_name := Some proc_exit_user;
            sprimcall_props := OK _;
            sprimcall_invs := OK _
          |}.

    End WithInv.

  End ExitUser.

    Section ProcCreate.

      Variable pcreate: RData -> block -> block -> block -> int -> Z -> option (RData* Z).

      Inductive extcall_proccreate_sem  (s: stencil) (WB: block -> Prop):
        list val -> (mwd (cdata RData)) -> val -> (mwd (cdata RData)) -> Prop :=
      | extcall_proccreate_sem_intro: 
          forall m adt adt' n b b' buc ofs_uc be ofse q,
            pcreate adt b b' buc ofs_uc (Int.unsigned q) = Some (adt', Int.unsigned n)
            -> find_symbol s STACK_LOC = Some b 
            -> find_symbol s proc_start_user = Some b'
            -> (exists fun_id, find_symbol s fun_id = Some buc) 
            -> (exists elf_id, find_symbol s elf_id = Some be) 
            -> extcall_proccreate_sem s WB (Vptr be ofse :: Vptr buc ofs_uc :: Vint q :: nil) (m, adt) (Vint n) (m, adt').

      Definition extcall_proccreate_info: sextcall_info :=
        {|
          sextcall_step := extcall_proccreate_sem;
          sextcall_csig := mkcsig (type_of_list_type (Tpointer Tvoid noattr::Tpointer Tvoid noattr::Tint32::nil)) Tint32;
          sextcall_valid s := true
        |}.

      Class PCreateInvariants :=
        {
          pcreate_low_level_invariant n d d' b b' buc ofs' q n':
            pcreate d b b' buc ofs' q = Some (d', n') ->
            low_level_invariant n d ->
            Mem.flat_inj n b = Some (b, 0%Z) ->
            Mem.flat_inj n b' = Some (b', 0%Z) ->
            Mem.flat_inj n buc = Some (buc, 0%Z) ->
            low_level_invariant n d';
          pcreate_high_level_invariant d d' b b' buc ofs' q n':
            pcreate d b b' buc ofs' q = Some (d', n') ->
            high_level_invariant d ->
            high_level_invariant d';
          pcreate_kernel_mode d d'  b b' ofs' q n' buc:
            pcreate d b b' buc ofs' q = Some (d', n') ->
            kernel_mode d ->
            kernel_mode d'
        }.

      Section WithInv.

        Context`{inv_ops: PCreateInvariants}.

        Instance extcall_proccreate_invs:
          ExtcallInvariants extcall_proccreate_info.
        Proof.
          constructor; intros; inv H.
          - (* low level invariant *)
            eapply pcreate_low_level_invariant; eauto.
            + eapply stencil_find_symbol_inject'; eauto.
              eapply flat_inj_inject_incr. assumption.
            + eapply stencil_find_symbol_inject'; eauto.
              eapply flat_inj_inject_incr. assumption.            
            + destruct H10 as [fun_id Hsym].
              eapply stencil_find_symbol_inject'; eauto.
              eapply flat_inj_inject_incr. assumption.            
          - (* high level invariant *)
            eapply pcreate_high_level_invariant; eauto.
          - (* kernel mode*)
            eapply pcreate_kernel_mode; eauto.
          - (* nextblock *)
            reflexivity.
          - (* inject neutral *)
            split; auto.
          - (* well typed *)
            simpl; trivial.
        Qed.

        Instance extcall_proccreate_props:
          ExtcallProperties extcall_proccreate_info.
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
            + lift_unfold. split; trivial.
            + simpl. apply Mem.unchanged_on_refl.
          - (* inject *)
            inv H0. generalize H4 H5 H6 H7. 
            apply H in H4. apply H in H5.
            destruct H6 as [fun_id H6]. apply H in H6.
            destruct H7 as [elf_id H7]. apply H in H7.
            intros.
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
            rewrite <- Int.repr_unsigned with n.
            rewrite <- Int.repr_unsigned with n0.
            split; congruence.
          - (* WB *)
            inv H0. econstructor; eauto.
          - (* load *)
            inv H. lift_unfold. trivial.
        Qed.

        Definition proc_create_compatsem : compatsem (cdata RData) :=
          compatsem_inl {|
              sextcall_primsem_step := extcall_proccreate_info;
              sextcall_props := OK _;
              sextcall_invs := OK _
            |}.

      End WithInv.

    End ProcCreate.

End Semantics.
