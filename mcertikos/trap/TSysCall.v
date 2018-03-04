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
(*              Layers of Trap: Syscall                                *)
(*                                                                     *)
(*          Provide the system calls of the kernel                     *)
(*                                                                     *)
(*          Haozhong Zhang <haozhong.zhang@yale.edu>                   *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)


(** This file defines the general semantics for primitives at all layers*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.

Require Import compcert.cfrontend.Ctypes.
Require Import Conventions.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealSMSPool.
Require Import CalRealProcModule.

Require Import INVLemmaMemory.
Require Import INVLemmaThread.
Require Import INVLemmaProc.
(*Require Import INVLemmaIntel.*)

Require Import AbstractDataType.

Require Import LoadStoreSem2.
Require Export TDispatch.

(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section Prim.

    Definition trap_into_kernel_spec id s m rs labd labd0 vargs sg b
               v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16:=
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
      (* signature *)
      vargs = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v4 :: Vint v5 :: Vint v6
                    :: Vint v7 :: Vint v8 :: Vint v9:: Vint v10 :: Vint v11 :: Vint v12
                    :: Vint v13 :: Vint v14 :: Vint v15:: Vint v16 ::nil)
      /\ sg = mksignature (AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                   AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                   AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::
                                   AST.Tint::nil) None cc_default
      /\ extcall_arguments rs m sg vargs
      /\ find_symbol s id = Some b
      /\ rs PC = Vptr b Int.zero
      
      (* trapinto the kernel*)
      /\ proc_exit_user_spec labd uctx4 = Some labd0
      /\ rs ESP <> Vundef
      /\ (forall b0 o,
            rs ESP = Vptr b0 o ->
            Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)).

    Definition syscall_spec id s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
               v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16:=
      (* trapinto the kernel*)
      trap_into_kernel_spec id s m rs labd labd0 vargs sg b
                            v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
      (* trapout the kernel*)
      /\ proc_start_user_spec labd1 = Some (labd', rs')
      /\ rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                               :: IR ECX :: IR EAX :: RA :: nil) 
                           (undef_regs (List.map preg_of destroyed_at_call) rs))
                 # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                 # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                 # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                 # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                 # PC <- (ZMap.get U_EIP rs')
      /\ (forall i, 0 <= i < UCTXT_SIZE ->
                    let v:= (ZMap.get i rs') in
                    Val.has_type v AST.Tint)
      /\ (forall i, 0 <= i < UCTXT_SIZE ->
                    let v:= (ZMap.get i rs') in
                    val_inject (Mem.flat_inj (Mem.nextblock m)) v v).


    Lemma proc_start_user_spec_asm_inv :
      forall s m0 labd labd' (rs:regset) rs' rs0,
        proc_start_user_spec labd = Some (labd', rs') ->
        rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                                :: IR ECX :: IR EAX :: RA :: nil) 
                            (undef_regs (List.map preg_of destroyed_at_call) rs))
                  # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                  # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                  # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                  # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                  # PC <- (ZMap.get U_EIP rs') ->
        (forall i, 0 <= i < UCTXT_SIZE ->
                   let v:= (ZMap.get i rs') in
                    Val.has_type v AST.Tint) ->
        (forall i, 0 <= i < UCTXT_SIZE ->
                   let v:= (ZMap.get i rs') in
                   val_inject (Mem.flat_inj (Mem.nextblock m0)) v v) ->
        asm_invariant (mem:= mwd (cdata RData)) s rs (m0, labd) ->
        asm_invariant (mem:= mwd (cdata RData)) s rs0 (m0, labd').
    Proof.
      intros. inv H3.
      constructor; eauto.
      + (* inject_neutral *)
        inv inv_inject_neutral.
        constructor; eauto.
        lift_unfold.
        val_inject_simpl;
          try (eapply H2; omega).
      + (* wt_regset*)
        repeat apply set_reg_wt; 
        try constructor; try assumption; simpl;
        eapply H1; omega.
    Qed.

    Lemma syscall_spec_asm_inv :
      forall s m0 labd labd' labd0 labd1 rs0  (rs:regset) rs' v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b id,
        syscall_spec id s m0 rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                     v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        asm_invariant (mem:= mwd (cdata RData)) s rs (m0, labd) ->
        asm_invariant (mem:= mwd (cdata RData)) s rs0 (m0, labd').
    Proof.
      intros. inv H. destruct H2 as [Hp [Hr[Hv1 Hv2]]].
      eapply proc_start_user_spec_asm_inv; eauto.
      inv H0.
      constructor; eauto.
      inv inv_inject_neutral.
      constructor; eauto.
    Qed.

    Lemma trap_into_kernel_low_inv:
      forall id s m0 rs labd labd0 vargs sg b
             v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 n,
      trap_into_kernel_spec id s m0 rs labd labd0 vargs sg b
                            v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      low_level_invariant n labd ->
      low_level_invariant n labd0.
    Proof.
      intros. inv H.
      destruct H2 as (_ & _ & _ & _ & HT & _).
      destruct proc_exit_user_inv.
      eapply exit_user_low_level_invariant; eauto.
    Qed.

    Lemma syscall_spec_low_inv:
      forall s m0 labd labd' labd0 labd1 rs0  (rs:regset) rs' v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b n id,
        syscall_spec id s m0 rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                     v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        asm_invariant s rs m0 ->
        low_level_invariant n labd ->
        (low_level_invariant n labd0 -> low_level_invariant n labd1) ->
        low_level_invariant n labd'.
    Proof.
      intros. destruct H as (HT1 & HT2 & _).
      destruct proc_start_user_inv.        
      eapply start_user_low_level_invariant; eauto.
      eapply H2.
      eapply trap_into_kernel_low_inv; eauto.
    Qed.

    Lemma trap_into_kernel_high_inv:
      forall id s m0 rs labd labd0 vargs sg b
             v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
      trap_into_kernel_spec id s m0 rs labd labd0 vargs sg b
                            v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
      high_level_invariant labd ->
      high_level_invariant labd0.
    Proof.
      intros. inv H.
      destruct H2 as (_ & _ & _ & _ & HT & _).
      destruct proc_exit_user_inv.
      eapply exit_user_high_level_invariant; eauto.
    Qed.

    Lemma syscall_spec_high_inv :
      forall s m0 labd labd' labd0 labd1 rs0  (rs:regset) rs' v0 v1 v2 v3 v5 v6 
             v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b id,
        syscall_spec id s m0 rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                     v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
        high_level_invariant labd ->
        (high_level_invariant labd0 -> high_level_invariant labd1) ->
        high_level_invariant labd'.
    Proof.
      intros. destruct H as (HT1 & HT2 & _).
      destruct proc_start_user_inv.        
      eapply start_user_high_level_invariant; eauto.
      eapply H1.
      eapply trap_into_kernel_high_inv; eauto.
    Qed.

    Lemma trap_into_kernel_det :
      forall id s m0 rs labd labd0 vargs sg b
             v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
             labd0' vargs' sg' b' v0' v1' v2' v3' v4' v5' v6' v7' v8' v9' 
             v10' v11' v12' v13' v14' v15' v16',
      trap_into_kernel_spec id s m0 rs labd labd0 vargs sg b v0
                            v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 
                            v13 v14 v15 v16 ->
      trap_into_kernel_spec id s m0 rs labd labd0' vargs' sg' b' v0'
                            v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' 
                            v11' v12' v13' v14' v15' v16' ->
      labd0 = labd0'.
    Proof.
      intros.
      inv H; inv H0.
      decompose [and] H1; clear H1.
      decompose [and] H2; clear H2.
      assert (Hsg: sg = sg') by (subst; auto).
      rewrite <- Hsg in H3; eapply extcall_arguments_determ in H3; eauto; inv H3.
      rewrites; auto.
    Qed.

    Lemma syscall_det :
      forall id s m0 r rs' r1 labd labd0 labd1 labd'
             vargs sg b v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
             rs'' r1' labd0' labd1' labd'' vargs' sg' b' v0' v1' v2' v3' v4' v5' 
             v6' v7' v8' v9' v10' v11' v12' v13' v14' v15' v16',
        syscall_spec id s m0 r rs' r1 labd labd0 labd1 labd'
                     vargs sg b v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 
                     v11 v12 v13 v14 v15 v16 ->
        syscall_spec id s m0 r rs'' r1' labd labd0' labd1' labd''
                     vargs' sg' b' v0' v1' v2' v3' v4' v5' v6' v7' v8' 
                     v9' v10' v11' v12' v13' v14' v15' v16' ->
        labd0 = labd0' /\ (labd1 = labd1' -> labd' = labd'' /\ r1 = r1').
    Proof.
      intros.
      inv H; inv H0; split.
      eapply trap_into_kernel_det in H; eauto.
      decompose [and] H2; clear H2.
      decompose [and] H3; clear H3.
      intros; subst; rewrites; auto.
    Qed.

    Inductive primcall_sys_sendto_chan_post_sem 
              (s: stencil): regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_sys_sendto_chan_post_sem_intro:
        forall m labd labd' labd1 rs0  (rs:regset) rs' b,
          trap_sendtochan_post_spec labd = Some labd1 ->
          proc_start_user_spec labd1 = Some (labd', rs') ->
          rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                                :: IR ECX :: IR EAX :: RA :: nil) 
                            (undef_regs (List.map preg_of destroyed_at_call) rs))
                  # EDI <- (ZMap.get U_EDI rs')# ESI <- (ZMap.get U_ESI rs')
                  # EBP <- (ZMap.get U_EBP rs')# ESP <- (ZMap.get U_ESP rs')
                  # EBX <- (ZMap.get U_EBX rs')# EDX <- (ZMap.get U_EDX rs')
                  # ECX <- (ZMap.get U_ECX rs')# EAX <- (ZMap.get U_EAX rs')
                  # PC <- (ZMap.get U_EIP rs') ->
          (forall i, 0 <= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     Val.has_type v AST.Tint) ->
          (forall i, 0 <= i < UCTXT_SIZE ->
                     let v:= (ZMap.get i rs') in
                     val_inject (Mem.flat_inj (Mem.nextblock m)) v v) ->
          find_symbol s sys_sendtochan_post = Some b ->
          rs PC = Vptr b Int.zero ->
          rs ESP <> Vundef ->
          (forall b0 o,
             rs ESP = Vptr b0 o ->
             Ple (genv_next s) b0 /\ Plt b0 (Mem.nextblock m)) ->
          primcall_sys_sendto_chan_post_sem s rs (m, labd) rs0 (m, labd').

    Global Instance primcall_sys_sendto_chan_post_invariants:
      PrimcallInvariants primcall_sys_sendto_chan_post_sem.
    Proof.
      constructor; intros; inv H.
      - (* asm invariant *)
        eapply proc_start_user_spec_asm_inv; eauto.
        inv H0. econstructor; eauto.
        inv inv_inject_neutral; constructor; eauto.
      - (* low level invariant*)
        eapply start_user_low_level_invariant; eauto.
        exact proc_start_user_inv.
        eapply trap_sendtochan_post_low_inv; eauto. 
      - (* high level invariant *)
        eapply start_user_high_level_invariant; eauto.
        exact proc_start_user_inv.
        eapply trap_sendtochan_post_high_inv; eauto. 
    Qed.

    Global Instance primcall_sys_sendto_chan_post_properties:
      PrimcallProperties primcall_sys_sendto_chan_post_sem.
    Proof.
      constructor; intros; inv H.
      - (* deterministic *)
        inv H0; rewrites; auto.
    Qed.

    Definition primcall_sys_sendto_chan_post_compatsem : compatsem (cdata RData) :=
      compatsem_inr
        {|
          sprimcall_primsem_step :=
            {|
              sprimcall_step := primcall_sys_sendto_chan_post_sem;
              sprimcall_sig := null_signature;
              sprimcall_valid s := true
            |};
          sprimcall_name := Some sys_sendtochan_post;
          sprimcall_props := OK primcall_sys_sendto_chan_post_properties;
          sprimcall_invs := OK primcall_sys_sendto_chan_post_invariants
        |}.

    (*
- SysSync: wrapper of syscall_dispatch
  mksignature nil Some Tint
     *)

    Inductive primcall_sys_dispatch_c_sem 
              (s: stencil): regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_sys_dispatch_c_sem_intro:
        forall m labd labd' labd0 labd1 rs0  (rs:regset) rs' v0 v1 v2 v3 v5 v6 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,

          syscall_spec syscall_dispatch s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                       v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->
          
          (* call kernel function*)
          sys_dispatch_c_spec s m labd0 = Some labd1 ->

          primcall_sys_dispatch_c_sem s rs (m, labd) rs0 (m, labd').

    Global Instance primcall_sys_dispatch_c_invariants:
      PrimcallInvariants primcall_sys_dispatch_c_sem.
    Proof.
      destruct sys_dispatch_c_inv.
      constructor; intros; inv H.
      - (* asm invariant *)
        eapply syscall_spec_asm_inv; eauto.
      - (* low level invariant*)
        eapply syscall_spec_low_inv; eauto. intros.
        inv H0. inv inv_inject_neutral.
        eapply trap_proc_create_low_inv; eauto.
      - (* high level invariant *)
        eapply syscall_spec_high_inv; eauto. intros.
        eapply trap_proc_create_high_inv; eauto.
    Qed.

    Global Instance primcall_sys_dispatch_c_properties:
      PrimcallProperties primcall_sys_dispatch_c_sem.
    Proof.
      constructor; intros; inv H.
      - (* deterministic *)
        inv H0.
        eapply syscall_det in H1; eauto.
        destruct H1; subst; rewrites.
        destruct H0; auto; subst; split; auto.
    Qed.

    Definition primcall_sys_dispatch_c_compatsem : compatsem (cdata RData) :=
      compatsem_inr
        {|
          sprimcall_primsem_step :=
            {|
              sprimcall_step := primcall_sys_dispatch_c_sem;
              sprimcall_sig := null_signature;
              sprimcall_valid s := true
            |};
          sprimcall_name := Some syscall_dispatch;
          sprimcall_props := OK primcall_sys_dispatch_c_properties;
          sprimcall_invs := OK primcall_sys_dispatch_c_invariants
        |}.

    (*

  page fault handler

     *)

    Inductive primcall_pagefault_handler_sem
              (s: stencil): regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_pagefault_handler_sem_intro:
        forall m labd labd0 labd1 labd' rs0 vadr (rs:regset) rs' v0 v1 v2 v3 v5 v6 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs sg b,

          syscall_spec pgf_handler s m rs rs' rs0 labd labd0 labd1 labd' vargs sg b
                       v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

          (* call kernel function*)
          (* read argument *)
          vadr = fst (ti labd0) ->
          ptfault_resv_spec (Int.unsigned vadr) labd0 = Some labd1 ->

          primcall_pagefault_handler_sem s rs (m, labd) rs0 (m, labd').


    Global Instance primcall_pgf_handler_sem_invariants:
      PrimcallInvariants primcall_pagefault_handler_sem.
    Proof.
      constructor; intros; inv H.
      - (* asm invariant *)
        eapply syscall_spec_asm_inv; eauto.
      - (* low level invariant*)
        eapply syscall_spec_low_inv; eauto. intros.
        destruct ptfault_resv_inv.
        eapply semprops_low_level_invariant.
        constructor_gen_sem_intro. assumption.
      - (* high level invariant *)
        eapply syscall_spec_high_inv; eauto. intros.
        destruct ptfault_resv_inv.
        eapply semprops_high_level_invariant.
        constructor_gen_sem_intro. assumption.
    Qed.

    Global Instance primcall_pgf_handler_sem_properties:
      PrimcallProperties primcall_pagefault_handler_sem.
    Proof.
      constructor; intros; inv H.
      - (* deterministic *)
        inv H0.
        eapply syscall_det in H1; eauto.
        destruct H1; subst; rewrites.
        destruct H0; auto; subst; split; auto.
    Qed.

    Definition primcall_pagefault_handler_compatsem : compatsem (cdata RData) :=
      compatsem_inr
        {|
          sprimcall_primsem_step :=
            {|
              sprimcall_step := primcall_pagefault_handler_sem;
              sprimcall_sig := null_signature;
              sprimcall_valid s := true
            |};
          sprimcall_name := Some pgf_handler;
          sprimcall_props := OK primcall_pgf_handler_sem_properties;
          sprimcall_invs := OK primcall_pgf_handler_sem_invariants
        |}.

      (*

- SysYield: wrapper of proc_yield
  mksignature nil None

  unzipped semantics

       *)

    Inductive primcall_sys_yield_sem
              (s: stencil): regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_sys_yield_sem_intro:
        forall m labd labd0 labd' rs0 rs' rs2  (rs:regset) v0 v1 v2 v3 v5 v6 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 v7 vargs rs_yield bs sg b,

          trap_into_kernel_spec sys_yield s m rs labd labd0 vargs sg b
                                v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

          (* call kernel function*)
          (* yield *)          
          find_symbol s proc_start_user = Some bs ->
          rs_yield = (Pregmap.init Vundef) #ESP <- (rs#ESP) #EDI <- (rs#EDI) #ESI <- (rs#ESI)
                                           #EBX <- Vundef #EBP <- (rs#EBP) #RA <- (Vptr bs Int.zero)->
          thread_yield_spec labd0 rs_yield = Some (labd', rs') ->
          (*cid labd' <> 0 ->*)
          
          (* restore registers *)          
          rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                            (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
          rs2 = (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                    #EBP <- (rs'#EBP)#PC <- (rs'#RA))  ->

          forall N_TYPE: (forall v r, ZtoPreg v = Some r -> Val.has_type (rs'#r) AST.Tint),
          forall N_INJECT_NEUTRAL: (forall v r, ZtoPreg v = Some r 
                                                -> val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)),

            primcall_sys_yield_sem s rs (m, labd) rs2 (m, labd').

    Import AsmImplLemma.

    Lemma asm_invariant_symbol:
      forall (s: stencil) rs m' bs id,
        asm_invariant (mem:= mem) s rs m' ->
        find_symbol s id = Some bs ->
        asm_invariant (mem:= mem) s (rs # EBX <- Vundef) # RA <- (Vptr bs Int.zero) m'.
    Proof.
      intros. eapply stencil_find_symbol_inject' in H0; eauto.
      inv H. constructor.
      * inv inv_inject_neutral.
        econstructor; eauto.
        val_inject_simpl.
        econstructor; eauto.
        eapply flat_inj_inject_incr; eassumption.
        rewrite Int.add_zero; reflexivity.
      * repeat eapply set_reg_wt; try econstructor; assumption.
    Qed.

    Global Instance primcall_sys_yield_sem_invariants:
      PrimcallInvariants primcall_sys_yield_sem.
    Proof.
      constructor; intros; inv H.
      - (* asm invariant *)
        inv H0. 
        constructor; eauto.
        + (* inject_neutral *)
          inv inv_inject_neutral.
          constructor; eauto. 
          val_inject_simpl;
            try (eapply N_INJECT_NEUTRAL;
                 apply PregToZ_correct; simpl; reflexivity).
        + (* wt_regset*)
          repeat apply set_reg_wt; try eapply N_INJECT_NEUTRAL; 
          try constructor; try assumption; simpl;
          eapply N_TYPE; apply PregToZ_correct; simpl; reflexivity.

      - (* low level invariant*)
        destruct thread_yield_inv.
        
        eapply (thread_schedule_low_level_invariant _ _ (rs#EBX <- Vundef#RA <- (Vptr bs Int.zero))).
        + repeat simpl_Pregmap.
          eassumption.
        + eapply asm_invariant_symbol; eauto.
        + eapply trap_into_kernel_low_inv; eauto.

      - (* high level invariant *)
        destruct thread_yield_inv.
        
        eapply (thread_schedule_high_level_invariant).
        + eassumption.
        + eapply trap_into_kernel_high_inv; eauto.
    Qed.

    Global Instance primcall_sys_yield_sem_properties:
      PrimcallProperties primcall_sys_yield_sem.
    Proof.
      constructor; intros; inv H.
      - (* deterministic *)
        inv H0.
        eapply trap_into_kernel_det in H1; eauto.
        rewrites; auto.
    Qed.

    Definition primcall_sys_yield_compatsem : compatsem (cdata RData) :=
      compatsem_inr
        {|
          sprimcall_primsem_step :=
            {|
              sprimcall_step := primcall_sys_yield_sem;
              sprimcall_sig := null_signature;
              sprimcall_valid s := true
            |};
          sprimcall_name := Some sys_yield;
          sprimcall_props := OK primcall_sys_yield_sem_properties;
          sprimcall_invs := OK primcall_sys_yield_sem_invariants
        |}.

      (*

- SysYield: wrapper of wait_chan
  mksignature (Tint::nil) None

  unzipped semantics

       *)

    Inductive primcall_sys_sendto_chan_pre_sem
              (s: stencil): regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
    | primcall_sys_sendto_chan_pre_sem_intro:
        forall m (rs:regset) chanid labd labd0 labd1 labd' rs0 rs' rs2 v0 v1 v2 v3 v5 v6 
               v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 vargs rs_yield bs sg b,

          trap_into_kernel_spec sys_sendtochan_pre s m rs labd labd0 vargs sg b
                                v0 v1 v2 v3 v4 v5 v6 chanid v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

          (* call kernel function*)
          trap_sendtochan_pre_spec labd0 = Some (labd1, Int.unsigned chanid) ->
          (* yield *)          
          find_symbol s sys_sendtochan_post = Some bs ->
          rs_yield = (Pregmap.init Vundef)#ESP <- (Val.add (rs ESP) (Vint (Int.repr 28)))
                                          #EDI <- (rs#EDI)#ESI <- (rs#ESI)
                                          #EBX <- Vundef#EBP <- (rs#EBP)#RA <- (Vptr bs Int.zero) ->
          thread_sleep_spec labd1 rs_yield (Int.unsigned chanid) = Some (labd', rs') ->

          rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                            (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
          rs2 = (rs0#ESP<- (rs'#ESP)#EDI <- (rs'#EDI)#ESI <- (rs'#ESI)#EBX <- (rs'#EBX)
                    #EBP <- (rs'#EBP)#PC <- (rs'#RA))  ->

          forall N_TYPE: (forall v r, ZtoPreg v = Some r -> Val.has_type (rs'#r) AST.Tint),
          forall N_INJECT_NEUTRAL: (forall v r, ZtoPreg v = Some r 
                                                -> val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)),

            primcall_sys_sendto_chan_pre_sem s rs (m, labd) rs2 (m, labd').

    Global Instance primcall_sys_sendto_chan_pre_sem_invariants:
      PrimcallInvariants primcall_sys_sendto_chan_pre_sem.
    Proof.
      constructor; intros; inv H.
      - (* asm invariant *)
        inv H0. 
        constructor; eauto.
        + (* inject_neutral *)
          inv inv_inject_neutral.
          constructor; eauto. 
          val_inject_simpl;
            try (eapply N_INJECT_NEUTRAL;
                 apply PregToZ_correct; simpl; reflexivity).
        + (* wt_regset*)
          repeat apply set_reg_wt; try eapply N_INJECT_NEUTRAL; 
          try constructor; try assumption; simpl;
          eapply N_TYPE; apply PregToZ_correct; simpl; reflexivity.

      - (* low level invariant*)
        destruct thread_sleep_inv.        
        eapply (thread_transfer_low_level_invariant _ _ _ (rs#EBX <- Vundef
                                                             #ESP <- (Val.add (rs ESP) (Vint (Int.repr 28)))
                                                             #RA <- (Vptr bs Int.zero))).
        + repeat simpl_Pregmap.
          eassumption.
        + eapply stencil_find_symbol_inject' in H8; eauto.
          inv H0. constructor.
          * inv inv_inject_neutral.
            econstructor; eauto.
            val_inject_simpl.
            econstructor; eauto.
            eapply flat_inj_inject_incr; eassumption.
            rewrite Int.add_zero; reflexivity.
          * repeat eapply set_reg_wt; try econstructor; try assumption. 
            destruct (rs ESP); simpl; try econstructor.
        + eapply trap_sendtochan_pre_low_inv; eauto.
          eapply trap_into_kernel_low_inv; eauto.
      - (* high level invariant *)
        destruct thread_sleep_inv.
        eapply (thread_transfer_high_level_invariant).
        + eassumption.
        + eapply trap_sendtochan_pre_high_inv; eauto.
          eapply trap_into_kernel_high_inv; eauto.
    Qed.

    Global Instance primcall_sys_sendto_chan_pre_sem_properties:
      PrimcallProperties primcall_sys_sendto_chan_pre_sem.
    Proof.
      constructor; intros; inv H.
      - (* deterministic *)
        inv H0.
        eapply trap_into_kernel_det in H1; eauto.
        rewrites.
        apply f_equal with (f:= Int.repr) in H1.
        rewrite 2 Int.repr_unsigned in H1; subst; rewrites; auto.
    Qed.

    Definition primcall_sys_sendto_chan_pre_compatsem : compatsem (cdata RData) :=
      compatsem_inr
        {|
          sprimcall_primsem_step :=
            {|
              sprimcall_step := primcall_sys_sendto_chan_pre_sem;
              sprimcall_sig := null_signature;
              sprimcall_valid s := true
            |};
          sprimcall_name := Some sys_sendtochan_pre;
          sprimcall_props := OK primcall_sys_sendto_chan_pre_sem_properties;
          sprimcall_invs := OK primcall_sys_sendto_chan_pre_sem_invariants
        |}.

(*
      (*

- SysRunVM: wrapper of Sys Run
  mksignature (Tint::nil) None

  unzipped semantics

       *)

      Inductive primcall_sys_run_vm_sem
              (s: stencil): regset -> (mwd (cdata RData)) -> regset -> (mwd (cdata RData)) -> Prop :=
      | primcall_sys_run_vm_sem_intro:
          forall m (rs:regset) labd labd0 labd' rs' rs0 rs01 rs2  v0 v1 v2 v3 v5 v6 v7
                 v8 v9 v10 v11 v12 v13 v14 v15 v16 v4 vargs sg b,

          trap_into_kernel_spec sys_run_vm s m rs labd labd0 vargs sg b
                                v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 ->

          rs01 = (Pregmap.init Vundef) #EDI <- (rs EDI) #EBP <- (rs EBP) ->
          vm_run_spec rs01 labd0 = Some (labd', rs') ->

          rs0 = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: RA :: nil) 
                                 (undef_regs (List.map preg_of destroyed_at_call) rs))  ->

          rs2 = (rs0#EAX<- (rs'#EAX)#EBX <- (rs'#EBX)#EDX <- (rs'#EDX)
                     #ESI <- (rs'#ESI)#EDI <- (rs'#EDI)#EBP <- (rs'#EBP)
                     #PC <- (rs'#RA)) ->

          forall N_TYPE: (forall r, Val.has_type (rs'#r) AST.Tint),
          forall N_INJECT_NEUTRAL: (forall r, val_inject (Mem.flat_inj (Mem.nextblock m)) (rs'#r) (rs'#r)),

          primcall_sys_run_vm_sem s rs (m, labd) rs2 (m, labd').

    Global Instance primcall_sys_run_vm_sem_invariants:
      PrimcallInvariants primcall_sys_run_vm_sem.
    Proof.
      constructor; intros; inv H.
      - (* asm invariant *)
        inv H0. 
        constructor; eauto.
        + (* inject_neutral *)
          inv inv_inject_neutral.
          constructor; eauto. 
          val_inject_simpl;
            try (eapply N_INJECT_NEUTRAL; simpl; reflexivity).
        + (* wt_regset*)
          repeat apply set_reg_wt; try eapply N_INJECT_NEUTRAL; 
          try constructor; try assumption; simpl;
          eapply N_TYPE; simpl; reflexivity.

      - (* low level invariant*)
        exploit vmx_enter_low_level_invariant; eauto.
        intros. inv H0.  inv inv_inject_neutral. 
        inv H; try (split; [apply inv_reg_wt| apply inv_reg_inject_neutral]).
        eapply trap_into_kernel_low_inv; eauto.

      - (* high level invariant *)
        exploit vmx_enter_high_level_invariant; eauto.
        eapply trap_into_kernel_high_inv; eauto.
    Qed.

      Definition primcall_sys_run_vm_compatsem : compatsem (cdata RData) :=
        compatsem_inr
          {|
            sprimcall_primsem_step :=
              {|
                sprimcall_step := primcall_sys_run_vm_sem;
                sprimcall_sig := null_signature;
                sprimcall_valid s := true
              |};
            sprimcall_name := Some sys_run_vm;
            sprimcall_props := Error nil;
            sprimcall_invs := OK primcall_sys_run_vm_sem_invariants
          |}.*)

  End Prim.

  (** * Layer Definition *)
  Definition tsyscall_fresh : compatlayer (cdata RData) :=
    ∅ ⊕
    syscall_dispatch  ↦ primcall_sys_dispatch_c_compatsem
               ⊕ pgf_handler  ↦ primcall_pagefault_handler_compatsem
               ⊕ sys_yield  ↦ primcall_sys_yield_compatsem
               (*⊕ sys_sendtochan_pre  ↦ primcall_sys_sendto_chan_pre_compatsem
               ⊕ sys_sendtochan_post  ↦ primcall_sys_sendto_chan_post_compatsem*)
               (*⊕ sys_run_vm  ↦ primcall_sys_run_vm_compatsem*).

  (** * Layer Definition *)
  Definition tsyscall_passthrough : compatlayer (cdata RData) :=
    (*fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ shared_mem_status ↦ gensem shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec
          ⊕ get_curid ↦ gensem get_curid_spec
          ⊕ thread_wakeup ↦ gensem thread_wakeup_spec

          ⊕ syncsendto_chan_post ↦ gensem syncsendto_chan_post_spec

          ⊕ uctx_get ↦ gensem uctx_get_spec
          ⊕ uctx_set ↦ gensem uctx_set_spec
          (*⊕ vmx_return_from_guest ↦ primcall_vmx_return_compatsem vmx_return_from_guest_spec vmx_return_from_guest
          ⊕ vmx_init ↦ vmcs_set_defaults_compatsem vmx_init_spec*)

          ⊕*) 
    (*print ↦ gensem print_spec
          ⊕*) proc_init ↦ gensem proc_init_spec
          ⊕ proc_start_user ↦ primcall_start_user_compatsem proc_start_user_spec
(*
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
          ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec*)
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  (** * Layer Definition *)
  Definition tsyscall : compatlayer (cdata RData) := tsyscall_fresh ⊕ tsyscall_passthrough.

End WITHMEM.