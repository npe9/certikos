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

Require Import AbstractDataType.
Require Import TSysCall.
Require Import I64Layer.
Require Import LoadStoreSem2.
Require Import MakeProgram.

Require Import SecurityCommon.
Require Import ProofIrrelevance.

(* This file proves that some new state invariants are preserved by each step 
   of the tsyscall layer. Note that we do not specify whether these invariants hold
   on the initial state here, we only prove that they are preserved. The invariants are:
   1.) we are in host mode (this version of mCertiKOS does not support virtualization)
   2.) the return address pseudoregister RA in each process's saved register context
       always points to the code entry point of the proc_start_user primitive
   3.) the usermode predicate, which consists of three interdependent properties that
       essentially say that we are always in user mode. The only exceptions to being
       in user mode are when the special kernel process 0 is executing (initialization
       setup only), or when we just called yield and are about to re-enter user mode in
       a single step. The three properties are:
       a.) if we are in kernel mode, then the instruction pointer register must be 
           pointing to the code entry point of the proc_start_user primitive
       b.) the currently-running process is not process 0
       c.) the ready queue is nonempty, and process 0 is never on the ready queue
   Paper Reference: Section 5 *)

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Local Instance : ExternalCallsOps (mwd (cdata RData)) := 
    CompatExternalCalls.compatlayer_extcall_ops tsyscall_layer.
  Local Instance : LayerConfigurationOps := compatlayer_configuration_ops tsyscall_layer.

  Section IHOST_INV.

    Lemma exec_loadex_ihost_inv {F V} :
      forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd,
        exec_loadex(F:=F)(V:=V) ge chunk (m,d) a rs rd = Next rs' (m',d') ->
        ihost d = true -> ihost d' = true.
    Proof.
      unfold exec_loadex, exec_loadex2; intros; subdestruct; rename H into Hexec.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - unfold HostAccess2.exec_host_load2 in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in *; subdestruct; inv H1; auto.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - simpl in *; rewrites.
      - simpl in *; rewrites.
    Qed.

    Lemma exec_storeex_ihost_inv {F V} :
      forall ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd rds,
        exec_storeex(F:=F)(V:=V) ge chunk (m,d) a rs rd rds = Next rs' (m',d') ->
        ihost d = true -> ihost d' = true.
    Proof.
      unfold exec_storeex, exec_storeex2; intros; subdestruct; rename H into Hexec.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - unfold HostAccess2.exec_host_store2 in Hexec; subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in Hexec; subdestruct; inv Hexec; auto.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - simpl in *; rewrites.
      - simpl in *; rewrites.
    Qed.

    Lemma proc_start_user_host_inv:
      forall d d' rs,
        proc_start_user_spec d = Some (d', rs) ->
        ihost d' = true.
    Proof.
      unfold proc_start_user_spec. intros. subdestruct.
      inv H. trivial.
    Qed.

    Lemma ihost_inv :
      forall ge rs rs' (m m' : mem) (d d' : cdata RData) t,
        LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) ->         
        ihost d = true -> ihost d' = true.
    Proof.
      intros.
      eapply (step_P (fun d d' : cdata RData => 
                        ihost d = true -> ihost d' = true)) in H; eauto.
      - simpl; intros; eapply exec_loadex_ihost_inv; eauto.
      - simpl; intros; eapply exec_storeex_ihost_inv; eauto.
      - (* Case 2: EF_external *)
        intros. inv H1.
        destruct H3 as [σ [Hl [s [σ' [Hmatch [Hsem [? [? ?]]]]]]]]; subst.
        inv_layer Hl; inv Hsem; try assumption; gensem_simpl.
        (*+ functional inversion H3. trivial.*)
        + unfold proc_init_spec, ret in *; subdestruct; inv_somes; auto.
      - (* Case 3: prim_call step *)
        intros. destruct H1 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
        inv_layer Hl; inv Hsem; simpl in *.
        {
          (* dispatch *)
          inv H4. inv H9.
          eapply proc_start_user_host_inv.
          eapply H4.
        }
        {
          (* pagefault *)
          inv H4. inv H10.
          eapply proc_start_user_host_inv.
          eapply H4.
        }
        {
          (* yield *)
          inv H4.
          inv_spec; inv_somes; auto.
        }
        {
          (* proc_start_user *)
          inv H4.
          eapply proc_start_user_host_inv; eauto.
        }
    Qed.

  End IHOST_INV.

  Ltac fun_inv_spec :=
    match goal with
      | H: _ = Some ?a |- context[?a] =>
        try (functional inversion H; clear H)
    end.

  Section WITHIMPL.

    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Variables (b : block).

    Definition RA_startuser d :=
      forall id,
        id <> 0 -> cused (ZMap.get id (AC d)) = true ->
        ZMap.get id (kctxt d) RA = Vptr b Int.zero.

    Lemma exec_loadex_RA_startuser_inv :
      forall {F V} ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd,
        exec_loadex (F:=F) (V:=V) ge chunk (m,d) a rs rd = Next rs' (m',d') ->
        ihost d = true -> RA_startuser d -> RA_startuser d'.
    Proof.
      unfold exec_loadex, exec_loadex2; intros; subdestruct; rename H into Hexec.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - unfold HostAccess2.exec_host_load2 in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in *; subdestruct; inv H2; auto.
      - unfold Asm.exec_load in Hexec; subdestruct; inv Hexec; auto.
      - simpl in *; rewrites.
      - simpl in *; rewrites.
    Qed.

    Lemma exec_storeex_RA_startuser_inv:
      forall {F V} ge chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd rds,
        exec_storeex(F:=F)(V:=V) ge chunk (m,d) a rs rd rds = Next rs' (m',d') ->
        ihost d = true -> RA_startuser d -> RA_startuser d'.
    Proof.
      unfold exec_storeex, exec_storeex2; intros; subdestruct; rename H into Hexec.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - unfold HostAccess2.exec_host_store2 in Hexec; subdestruct.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; subdestruct; inv Hexec; auto.
        unfold PageFault.exec_pagefault in Hexec; subdestruct; inv Hexec; auto.
      - unfold Asm.exec_store in Hexec; subdestruct; inv Hexec.
        unfold Mem.storev in *; unfold_lift; subdestruct; inv Hdestruct3; auto.
      - simpl in *; rewrites.
      - simpl in *; rewrites.
    Qed.

    Variables (s : stencil) (M : module) (ge : genv).

    Hypothesis (Hmake : make_globalenv s M tsyscall_layer = OK ge).
    Hypothesis (Hpsu : Genv.find_symbol ge proc_start_user = Some b).

    (* needed so that the inv_spec tactic doesn't interpret find_symbol as a spec *)
    Opaque Genv.find_symbol find_symbol.

    Let local_stencil_matches : stencil_matches s ge.
    Proof.
      eapply make_globalenv_stencil_matches; eauto.
    Qed.

    Let local_find_symbol : find_symbol s proc_start_user = Some b.
    Proof.
      erewrite <- stencil_matches_symbols; eauto.
    Qed.

    Section YIELD_RA_INV.
    
      Lemma trap_into_kernel_RA_startuser_inv :
      forall id s' m' rs d d' vargs sg0 b0 v0
             v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
        trap_into_kernel_spec id s' m' rs d d' vargs sg0 b0 v0
          v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> 
        RA_startuser d -> RA_startuser d'.
      Proof.
        intros until v16; intro Hspec; inv Hspec.
        decompose [and] H0; inv_spec; inv_somes; auto.
      Qed.

      Lemma ptInsertPTE0_RA_startuser_inv:
        forall i vadr padr pm d d',
          ptInsertPTE0_spec i vadr padr pm d = Some d' ->
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros; inv_spec; inv_somes; simpl; auto. 
      Qed.

      Lemma ptAllocPDE0_RA_startuser_inv:
        forall i1 i2 n d d',
          ptAllocPDE0_spec i1 i2 d = Some (d', n) ->
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros. functional inversion H; subst; auto; simpl;clear H.
        unfold RA_startuser in *; simpl in *. intros.
        destruct (zeq id i1); subst.
        - rewrite ZMap.gss in H1. subst cur c. simpl in *.
          eapply H0; eauto.
        - rewrite ZMap.gso in H1; eauto.
      Qed.

      Lemma ptInsert0_RA_startuser_inv:
        forall i1 i2 b i3 d d' v,
          ptInsert0_spec i1 i2 b i3 d = Some (d', v) ->
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros; inv_spec; inv_somes; clear Hdestruct4.
        - eapply ptInsertPTE0_RA_startuser_inv; eauto.
        - eapply ptAllocPDE0_RA_startuser_inv; eauto.
        - eapply ptInsertPTE0_RA_startuser_inv; eauto.
          eapply ptAllocPDE0_RA_startuser_inv; eauto.
      Qed.

      Lemma palloc_RA_startuser_inv:
        forall i r d d',
          alloc_spec i d = Some (d', r) ->
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros; inv_spec; inv_somes; auto; simpl.
        unfold RA_startuser in *; simpl in *. intros.
        destruct (zeq id i); subst.
        - rewrite ZMap.gss in H1. simpl in *.
          eapply H0; eauto.
        - rewrite ZMap.gso in H1; eauto.
      Qed.

      Lemma ptResv2_RA_startuser_inv :
        forall i2 i3 i5 i6 n d d',
          ptResv2_spec 1 i2 i3 2 i5 i6 d = Some (d', n) ->
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros. functional inversion H; subst; clear H; trivial.
        - eapply ptInsert0_RA_startuser_inv; eauto.
          eapply palloc_RA_startuser_inv; eauto.
        - eapply ptInsert0_RA_startuser_inv; eauto.
          eapply ptInsert0_RA_startuser_inv; eauto.
          eapply palloc_RA_startuser_inv; eauto.
      Qed.

      Lemma sys_dispatch_RA_startuser_inv :
        forall s m d d',
          stencil_matches s ge ->
          sys_dispatch_c_spec s m d = Some d' -> 
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros; inv_spec; fun_inv_spec;
        inv_somes; auto.       
        - repeat inv_spec;
          inv_somes; simpl in *; auto;
          unfold RA_startuser in *; simpl in *.
          intros id Hn0 Hused; zmap_solve.
          + rewrite Pregmap.gss.
            rewrite (stencil_matches_unique _ _ _ H local_stencil_matches) in Hdestruct14. 
            rewrites; reflexivity.
          + unfold update_cchildren, update_cusage in Hused; simpl in Hused.
            zmap_solve; subst; auto.

        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
        - unfold RA_startuser in *.
          functional inversion H2; subst. clear H2.
          subst uctx uctx'. simpl.
          functional inversion H7; subst; simpl in *. clear H7.
          subst uctx uctx'.
          functional inversion H6; subst; simpl in *; auto; clear H6.
          eapply ptResv2_RA_startuser_inv; eauto.
          eapply ptResv2_RA_startuser_inv; eauto.
        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
      Qed.

      Lemma ptfault_resv_RA_startuser_inv :
        forall v d d',
          ptfault_resv_spec v d = Some d' -> 
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros v d d' Hspec.
        inv_spec; inv_somes; auto.
        inv_spec; inv_somes; simpl; eauto.
        intros.
        unfold RA_startuser in *; simpl in *.
        eapply ptInsert0_RA_startuser_inv; eauto.
        eapply palloc_RA_startuser_inv; eauto.
      Qed.

      Lemma proc_start_user_RA_startuser_inv :
        forall rs d d',
          proc_start_user_spec d = Some (d', rs) -> 
          RA_startuser d -> RA_startuser d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
      Qed.

      Ltac solve_RA_startuser_inv :=
        repeat match goal with
        | [ H : appcontext [syscall_spec] |- _ ] => inv H
        | [ H : proc_start_user_spec _ = _ /\ _ |- _ ] => destruct H
        | [ H : appcontext [trap_into_kernel_spec _ _ _ _ _ ?d] |- RA_startuser ?d ] => 
          eapply trap_into_kernel_RA_startuser_inv; eauto
        | [ H : appcontext [proc_start_user_spec _ = Some (?d,_)] |- RA_startuser ?d ] => 
          eapply proc_start_user_RA_startuser_inv; eauto
        | [ H : appcontext [sys_dispatch_c_spec _ _ _ = Some ?d] |- RA_startuser ?d ] => 
          eapply sys_dispatch_RA_startuser_inv; eauto
        | [ H : appcontext [ptfault_resv_spec _ _ = Some ?d] |- RA_startuser ?d ] => 
          eapply ptfault_resv_RA_startuser_inv; eauto      
        end.

      Lemma RA_startuser_inv :
        forall rs rs' (m m' : mem) (d d' : cdata RData) t,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) ->         
          ihost d = true -> RA_startuser d -> RA_startuser d'.
      Proof.
        intros.
        eapply (step_P (fun d d' : cdata RData => 
                          ihost d = true -> RA_startuser d -> RA_startuser d')) in H; eauto.
        - simpl; intros; eapply exec_loadex_RA_startuser_inv; eauto.
        - simpl; intros; eapply exec_storeex_RA_startuser_inv; eauto.
        - (* Case 2: EF_external *)
          intros. inv H2.
          destruct H5 as [σ [Hl [s' [σ' [Hmatch [Hsem [? [? ?]]]]]]]]; subst.
          inv_layer Hl; inv Hsem; try assumption; gensem_simpl.
          (*+ functional inversion H5. trivial.*)
          + unfold proc_init_spec, ret in *; subdestruct; inv_somes.
            unfold RA_startuser; simpl; intros id Hn0 Hused.
            unfold real_AC in Hused; zmap_solve; inv Hused.
        - (* Case 3: prim_call step *) 
          intros. destruct H2 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
          inv_layer Hl; inv Hsem; simpl in *; inv H6; solve_RA_startuser_inv.
          unfold thread_yield_spec in *; subdestruct; inv_somes; unfold RA_startuser; simpl; intros; zmap_solve.
          {
            rewrite Pregmap.gss; f_equal.
            assert (Heq:= stencil_matches_unique _ _ _ local_stencil_matches H5); congruence.
          }
          {
            eapply trap_into_kernel_RA_startuser_inv in H6; eauto.
          }
          {
            rewrite Pregmap.gss; f_equal.
            assert (Heq:= stencil_matches_unique _ _ _ local_stencil_matches H5); congruence.
          }
          {
            eapply trap_into_kernel_RA_startuser_inv in H6; eauto.
          }
      Qed.

    End YIELD_RA_INV.

    Section USERMODE_INV.

      Notation abq_inv d := (forall l,
                              ZMap.get num_id (abq d) = AbQValid l ->
                              l <> nil /\ forall id, In id l -> 0 < id).

      Record usermode (rs : regset) (d : cdata RData) := 
        {
          usermode_ikern: ikern d = true -> rs PC = Vptr b Int.zero;
          usermode_cid: 0 < cid d;
          usermode_abq: abq_inv d
        }.

      Lemma startuser_step :
        forall rs rs' (m m' : mem) (d d' : cdata RData) t,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
          rs PC = Vptr b Int.zero ->
          primcall_startuser_sem proc_start_user_spec s rs (m,d) rs' (m',d') /\ t = E0.
      Proof.        
        intros rs rs' m m' d d' t Hstep Hpc.
        assert (Hmake': make_globalenv s M tsyscall_layer = ret ge) by auto.
        clear Hmake; rename Hmake' into Hmake; unfold tsyscall_layer in Hmake; inv_make_globalenv Hmake.
        unfold tsyscall, tsyscall_passthrough in HLge0; inv_make_globalenv HLge0.
        assert (b1 = b).
        {
          inv HLge0le.
          specialize (genv_le_find_symbol proc_start_user).
          rewrite Hb1fs, Hpsu in genv_le_find_symbol; inv genv_le_find_symbol; auto.
        }
        subst.
        assert (Genv.find_funct_ptr ge b = Some (External (EF_external proc_start_user null_signature))).
        {
          inv HLge0le.
          specialize (genv_le_find_funct_ptr b).
          rewrite Hb1fp in genv_le_find_funct_ptr; inv genv_le_find_funct_ptr; auto.
        }
        assert (Heq: get_layer_primitive proc_start_user tsyscall_layer 
                     = OK (Some (primcall_start_user_compatsem proc_start_user_spec))) by reflexivity.
        rename H into Hbfp; inv Hstep; rewrites.
        - inv H7.
          inv H.
          destruct H0 as [Hl Hsem].
          inv Hsem.
          destruct H as [σ' [Hmatch' [Hsem [Hcon _]]]]; subst.
          unfold ident in *.
          rewrite Heq in Hl. inv Hl.
        - inv H6.
          destruct H as [sg [σ [Hext [Hl Hsem]]]]; inv Hext.
          unfold ident in *.
          rewrite Heq in Hl. inv Hl.
          inv Hsem; simpl in *.
          rewrite (stencil_matches_unique _ _ _ local_stencil_matches H0); auto.
      Qed.

      Lemma startuser_step_d :
        forall rs rs' (m m' : mem) (d d' : cdata RData) t,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) -> 
          rs PC = Vptr b Int.zero ->
          d' = d {ikern: false} {ipt: false} {PT: cid d}.
      Proof.
        intros rs rs' m m' d d' t Hstep Hpc.
        destruct (startuser_step _ _ _ _ _ _ _ Hstep Hpc) as [Hsem ?]; inv Hsem.
        inv_spec; inv_rewrite.
      Qed.

      Lemma exec_loadex_usermode_inv :
        forall chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd,
          exec_loadex ge chunk (m,d) a rs rd = Next rs' (m',d') ->
          ikern d = false -> ihost d = true -> usermode rs d -> usermode rs' d'.
      Proof.
        unfold exec_loadex, exec_loadex2; intros; subdestruct; rename H into Hexec.
        - destruct H2.
          unfold HostAccess2.exec_host_load2 in Hexec; subdestruct;
            try solve [inv Hexec; constructor; intros; rewrites; eauto].
          unfold PageFault.exec_pagefault in *; subdestruct; inv Hexec.
          constructor; simpl; auto; intros; rewrites.
        - simpl in *; rewrites.
      Qed.

      Lemma exec_storeex_usermode_inv :
        forall chunk rs rs' (m m' : mem) (d d' : cdata RData) a rd rds,
          exec_storeex ge chunk (m,d) a rs rd rds = Next rs' (m',d') ->
          ikern d = false -> ihost d = true -> usermode rs d -> usermode rs' d'.
      Proof.
        unfold exec_storeex, exec_storeex2; intros; subdestruct; rename H into Hexec.
        - destruct H2.
          unfold HostAccess2.exec_host_store2 in Hexec; subdestruct;
            try solve [unfold FlatLoadStoreSem.exec_flatmem_store, flatmem_store in Hexec; 
                       subdestruct; inv Hexec; constructor; simpl; eauto; intros; rewrites].
          unfold PageFault.exec_pagefault in Hexec; subdestruct; inv Hexec.
          constructor; simpl; auto; intros; rewrites.
        - simpl in *; rewrites.
      Qed.

      Lemma trap_into_kernel_usermode_cid :
        forall id s' m' rs d d' vargs sg0 b0 v0
             v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
          trap_into_kernel_spec id s' m' rs d d' vargs sg0 b0 v0
            v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> 
          cid d = cid d'.
      Proof.
        intros until v16; intro Hspec; inv Hspec.
        decompose [and] H0; inv_spec; inv_somes; auto.
      Qed.

      Lemma trap_into_kernel_usermode_abq :
        forall id s' m' rs d d' vargs sg0 b0 v0
             v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
          trap_into_kernel_spec id s' m' rs d d' vargs sg0 b0 v0
            v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 -> 
          abq d = abq d'.
      Proof.
        intros until v16; intro Hspec; inv Hspec.
        decompose [and] H0; inv_spec; inv_somes; auto.
      Qed.

      Lemma ptInsertPTE0_cid:
        forall i1 vadr padr pm d d',
          ptInsertPTE0_spec i1 vadr padr pm d = Some d' ->
          cid d = cid d'
          /\ (0 < cid d -> abq_inv d -> abq_inv d').
      Proof.
        intros; inv_spec; inv_somes; simpl; auto. 
      Qed.

      Lemma ptAllocPDE0_cid:
        forall i1 i2 n d d',
          ptAllocPDE0_spec i1 i2 d = Some (d', n) ->
          cid d = cid d'
          /\ (0 < cid d -> abq_inv d -> abq_inv d').
      Proof.
        intros. functional inversion H; subst; auto; simpl;clear H.
      Qed.

      Definition Q d d' :=
        cid d = cid d'
        /\ (0 < cid d -> abq_inv d -> abq_inv d').

      Lemma Q_trans:
        forall d1 d2 d3,
          Q d1 d2 ->
          Q d2 d3 ->
          Q d1 d3.
      Proof.
        unfold Q. intros d1 d2 d3.
        intros (He & Hi) (He' & Hi').
        split. congruence. 
        intros Hle Habq.
        eapply Hi'. rewrite <- He; trivial.
        eapply Hi; assumption.
      Qed.
          
      Lemma ptInsert0_cid:
        forall i1 i2 b i3 d d' v,
          ptInsert0_spec i1 i2 b i3 d = Some (d', v) ->
          cid d = cid d'
          /\ (0 < cid d -> abq_inv d -> abq_inv d').
      Proof.
        intros; inv_spec; inv_somes; clear Hdestruct4.
        - eapply ptInsertPTE0_cid; eauto.
        - eapply ptAllocPDE0_cid; eauto. 
        - exploit ptInsertPTE0_cid; eauto.
          exploit ptAllocPDE0_cid; eauto. intros.
          eapply Q_trans; eauto.
      Qed.

      Lemma alloc_cid:
        forall i1 d d' b,
          alloc_spec i1 d = Some (d', b) ->
          Q d d'.
      Proof.
        intros. unfold Q.
        functional inversion H; auto.
      Qed.

      Lemma ptResv2_cid :
        forall i1 i4 i2 i3 i5 i6 n d d',
          ptResv2_spec i1 i2 i3 i4 i5 i6 d = Some (d', n) ->
          cid d = cid d'
          /\ (0 < cid d -> abq_inv d -> abq_inv d').
      Proof.
        intros. functional inversion H; subst; clear H.
        - auto.
        - exploit ptInsert0_cid; eauto; intros.
          eapply Q_trans; eauto.
          eapply alloc_cid; eauto.
        - exploit ptInsert0_cid; eauto; intros.
          eapply Q_trans; eauto.
          clear H0.
          exploit ptInsert0_cid; eauto; intros.
          eapply Q_trans; eauto.
          eapply alloc_cid; eauto.
      Qed.

      Lemma sys_dispatch_usermode :
        forall s m d d',
          sys_dispatch_c_spec s m d = Some d' -> 
          cid d = cid d'
          /\ (0 < cid d -> abq_inv d -> abq_inv d').
      Proof.
        intros; inv_spec; fun_inv_spec;
        inv_somes; auto.      
        - repeat inv_spec;
          inv_somes; simpl in *; auto.
          rewrite ZMap.gss. split; trivial.
          intros. destruct (H0 l1); inv H1; auto. split; [discriminate|].
          intro id; specialize (H3 id); simpl; intuition.
        - repeat inv_spec;
          inv_somes; simpl in *; auto.      

        - functional inversion H0; subst. clear H0.
          subst uctx uctx'. simpl.
          functional inversion H5; subst; simpl in *. clear H5.
          subst uctx uctx'.
          functional inversion H4; subst; simpl in *; auto; clear H4.
          eapply ptResv2_cid; eauto.
          eapply ptResv2_cid; eauto.

        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
        - repeat inv_spec;
          inv_somes; simpl in *; auto.      
      Qed.

      Lemma ptfault_resv_usermode:
        forall v d d',
          ptfault_resv_spec v d = Some d' -> 
          Q d d'.
      Proof.
        intros v d d' Hspec.
        inv_spec; inv_somes.
        inv_spec; inv_somes; simpl; auto; unfold Q; simpl; eauto.
        exploit alloc_cid; eauto. intros.
        eapply Q_trans; eauto.
        eapply ptInsert0_cid; eauto.
        unfold Q; auto.
      Qed.

      Lemma thread_yield_usermode_ikern :
        forall rs rs' d d',
          thread_yield_spec d rs = Some (d', rs') -> 
          high_level_invariant d -> RA_startuser d -> abq_inv d -> 
          rs' RA = Vptr b Int.zero.
      Proof.
        unfold RA_startuser; intros rs rs' d d' Hspec Hinv Hra Habq.
        repeat inv_spec; inv_somes; simpl.
        assert (Hin: In (last l num_id) l) by (apply last_correct; auto); apply Hra.
        assert (0 < last l 64) by (eapply Habq; eauto); omega.
        destruct (cused (ZMap.get (last l num_id) (AC d))) eqn:Hused; auto.
        assert (0 <= last l num_id < num_id).
        {
          destruct (valid_TDQ _ Hinv Hdestruct num_id) as [l' [? Hrange]]; try omega.
          apply Hrange; rewrites; auto.
        }
        eapply (valid_inQ _ Hinv) in Hdestruct3; eauto; try omega.
        destruct (Hdestruct3 Hin) as [st Htcb].
        apply (valid_notinQ _ Hinv) in Htcb; auto; try omega.
      Qed.

      Lemma thread_yield_usermode_cid :
        forall rs rs' d d',
          thread_yield_spec d rs = Some (d', rs') -> 
          abq_inv d -> 0 < cid d'. 
      Proof.
        intros; repeat inv_spec; inv_somes; simpl.
        apply (H0 l); auto.
        apply last_correct; auto.
      Qed.

      Lemma thread_yield_usermode_abq :
        forall rs rs' d d',
          high_level_invariant d ->
          thread_yield_spec d rs = Some (d', rs') -> 
          0 < cid d -> abq_inv d -> abq_inv d'.
      Proof.
        intros rs rs' d d' Hinv; intros; repeat inv_spec; inv_somes; simpl in *.
        zmap_simpl; inv H2.
        destruct (zeq (last l0 num_id) (cid d)).
        - (* show by contradiction that cid cannot be in the ready queue *)
          edestruct (valid_inQ _ Hinv); eauto; try omega.
          eapply valid_curid; eauto.
          rewrite <- e; apply last_correct; auto.
          edestruct (valid_TCB _ Hinv) as [? [? [? [? _]]]]; eauto.
          eapply valid_curid; eauto.
          edestruct (correct_curid _ Hinv); eauto; rewrites.
        - split; [discriminate|].
          destruct (H1 l0); subst; auto.
          simpl; intros ? [?|?]; try congruence.
          eapply INVLemmaThread.remove_property; eauto.
      Qed.

      Lemma proc_start_user_usermode_ikern :
        forall rs d d',
          proc_start_user_spec d = Some (d', rs) -> 
          ikern d' = false.
      Proof.
        intros; inv_spec; inv_somes; auto.
      Qed.

      Lemma proc_start_user_usermode_cid :
        forall rs d d',
          proc_start_user_spec d = Some (d', rs) -> 
          cid d = cid d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
      Qed.

      Lemma proc_start_user_usermode_abq :
        forall rs d d',
          proc_start_user_spec d = Some (d', rs) -> 
          abq d = abq d'.
      Proof.
        intros; inv_spec; inv_somes; auto.
      Qed.

      Ltac solve_usermode_inv :=
        repeat match goal with
        | [ H : appcontext [syscall_spec] |- _ ] => inv H
        | [ H : proc_start_user_spec _ = _ /\ _ |- _ ] => destruct H
(*
        | [ H : appcontext [trap_into_kernel_spec] |- _ ] => 
          apply trap_into_kernel_usermode_inv in H
        | [ H : appcontext [proc_start_user_spec] |- _ ] => 
          apply proc_start_user_usermode_inv in H
        | [ H : appcontext [sys_dispatch_c_spec] |- _ ] => 
          apply sys_dispatch_usermode_inv in H
        | [ H : appcontext [ptfault_resv_spec] |- _ ] => 
          apply ptfault_resv_usermode_inv in H     *)   
        end(*; try congruence*).

      Ltac sapply H :=
        match goal with
          | [H' : _ |- _] => apply H in H'
        end.

      Ltac seapply H :=
        match goal with
          | [H' : _ |- _] => eapply H in H'
        end.

      Lemma abq_inv_trans:
        forall d d',
          abq_inv d ->
          abq d = abq d' ->
          abq_inv d'.
      Proof.
        intros. rewrite <- H0 in H1.
        exploit H; eauto.
      Qed.

      Lemma usermode_inv :
        forall rs rs' (m m' : mem) (d d' : cdata RData) t,
          LAsm.step ge (State rs (m,d)) t (State rs' (m',d')) ->         
          high_level_invariant d -> ihost d = true -> RA_startuser d -> 
          usermode rs d -> usermode rs' d'.
      Proof.
        intros rs rs' m m' d d' t Hstep Hinv Hhost Hra Huser.
        destruct (ikern d) eqn:Hkern.
        destruct Huser; erewrite startuser_step_d; eauto.
        constructor; auto; discriminate.
        inv Hstep; try solve [simpl in *; destruct EXT_ALLOWED; rewrites].
        {
          (* Case 1: internal step (assembly command) *)
          rename H7 into Hexec.
          destruct Huser; destruct i; simpl in *;
          try solve [inv Hexec; constructor; auto; rewrite Hkern; discriminate |
                     eapply exec_loadex_usermode_inv; eauto; constructor; auto |
                     eapply exec_storeex_usermode_inv; eauto; constructor; auto].
          destruct i; simpl in *; 
          try solve [inv Hexec; constructor; auto; rewrite Hkern; discriminate |
                     eapply exec_loadex_usermode_inv; eauto; constructor; auto |
                     eapply exec_storeex_usermode_inv; eauto; constructor; auto |                      
                     unfold goto_label in *; subdestruct; inv Hexec; 
                       constructor; auto; rewrite Hkern; discriminate |
                     unfold lift in *; simpl in *; subdestruct; inv Hexec; 
                       constructor; auto; rewrite Hkern; discriminate].
        }
        {
          (* Case 2: prim_call step *)
          destruct H6 as [x [sg [σ [Hef [Hl Hsem]]]]]; subst.
          inv_layer Hl; inv Hsem; simpl in *; inv H1; solve_usermode_inv.
          - (* dispatch *)
            destruct Huser; constructor.
            + sapply proc_start_user_usermode_ikern; congruence.
            + sapply trap_into_kernel_usermode_cid.
              sapply proc_start_user_usermode_cid.
              sapply sys_dispatch_usermode. destruct H10 as (HP & _ ). congruence.            
            + assert (0 < cid labd0) by (sapply trap_into_kernel_usermode_cid; congruence).
              sapply trap_into_kernel_usermode_abq.
              sapply proc_start_user_usermode_abq.
              sapply sys_dispatch_usermode; destruct H10 as [? Habq].
              rewrite <- H1; apply Habq; auto.
              rewrite <- H; auto.
          - (* pagefault *)
            destruct Huser; constructor.
            + sapply proc_start_user_usermode_ikern; congruence.
            + sapply trap_into_kernel_usermode_cid.
              sapply proc_start_user_usermode_cid.
              sapply ptfault_resv_usermode. destruct H11 as (HP & _). congruence.            
            + exploit trap_into_kernel_usermode_cid; eauto. intros Heq.
              sapply trap_into_kernel_usermode_abq.
              sapply proc_start_user_usermode_abq.
              sapply ptfault_resv_usermode. destruct H11 as (HP1 & HP2).
              eapply abq_inv_trans; [|eassumption].
              eapply HP2; eauto.
              {
                rewrite <- Heq. trivial.
              }
              eapply abq_inv_trans; eauto.

          - (* yield *)
            destruct Huser; constructor.
            + rewrite Pregmap.gss.
              intro; eapply thread_yield_usermode_ikern; eauto.
              eapply trap_into_kernel_high_inv; eauto.
              eapply trap_into_kernel_RA_startuser_inv; eauto.
              sapply trap_into_kernel_usermode_abq.
              intros l'; intros; apply (usermode_abq0 l'); congruence.              
            + eapply thread_yield_usermode_cid; eauto.
              sapply trap_into_kernel_usermode_abq.
              intros l'; intros; apply (usermode_abq0 l'); congruence.
            + eapply thread_yield_usermode_abq; [|eauto|..].
              eapply trap_into_kernel_high_inv; eauto.
              sapply trap_into_kernel_usermode_cid; congruence.
              sapply trap_into_kernel_usermode_abq.
              intros l'; intros; apply (usermode_abq0 l'); congruence.
          - (* proc_start_user *)
            destruct Huser; constructor.
            + sapply proc_start_user_usermode_ikern; congruence.
            + sapply proc_start_user_usermode_cid; congruence.       
            + sapply proc_start_user_usermode_abq.
              intros l'; intros; apply (usermode_abq0 l'); congruence.
        }
      Qed.

    End USERMODE_INV.

  End WITHIMPL.

End WITHMEM.