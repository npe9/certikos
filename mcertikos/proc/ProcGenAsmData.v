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
(*           Layers of PM: Assembly Verification for Proc              *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Locations.
Require Import AuxStateDataType.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import FlatMemory.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import Constant.
Require Import AsmImplLemma.
Require Import AsmImplTactic.
Require Import GlobIdent.
Require Import CommonTactic.

Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compcertx.MakeProgram.
Require Import LAsmModuleSem.
Require Import LAsm.
Require Import liblayers.compat.CompatGenSem.
Require Import PrimSemantics.
Require Import Conventions.

Require Import PUCtxtIntro.
Require Import ProcGenAsmSource.
Require Import AbstractDataType.

Section ASM_DATA.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.
  Notation LDATAOps := (cdata LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Section ExitUser.

      Lemma exituser_generate:
        forall labd labd' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
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
          proc_exit_user_spec labd uctx4 = Some labd' ->
          high_level_invariant labd ->
          ihost labd = true /\
          exists labd0,
            trapin_spec labd = Some labd0
            /\ exists labd1,
                 save_uctx_spec labd0 uctx4 = Some labd1
                 /\ exists labd2,
                         setPT_spec 0 labd1 = Some labd2
                         /\ ptin_spec labd2 = Some labd'
                         /\ ikern labd0 = true
                         /\ ihost labd0 = true
                         /\ ikern labd1 = true
                         /\ ihost labd1 = true
                         /\ ikern labd2 = true
                         /\ ihost labd2 = true
                         /\ ikern labd' = true
                         /\ ihost labd' = true.
      Proof.
        intros. unfold trapin_spec.
        functional inversion H; subst.
        eapply valid_iptf in H0; trivial.        
        subrewrite'. split; [reflexivity | esplit; split].
        reflexivity.
        unfold save_uctx_spec; simpl.
        subrewrite'. esplit; split.
        reflexivity.        
        simpl. unfold setPT_spec; simpl.
        subrewrite'. esplit; split.
        reflexivity.        
        simpl.
        unfold ptin_spec; simpl.
        subrewrite'.        
        repeat split; reflexivity.
      Qed.

    End ExitUser.

    Section StartUser.

      Lemma startuser_generate:
          forall m0 labd labd' r'0,
            proc_start_user_spec labd  = Some (labd', r'0) ->
            low_level_invariant (Mem.nextblock m0) labd ->
            high_level_invariant labd ->
            0 <= cid labd < 64
            /\ get_curid_spec labd = Some (cid labd)
            /\ exists labd0,
                 ptout_spec labd = Some labd0
                 /\ exists labd1,
                      setPT_spec (cid labd) labd0 = Some labd1
                      /\ cid labd1 = cid labd
                      /\ restore_uctx_spec labd1 = Some (labd', r'0)
                      /\(forall i, 0<= i < UCTXT_SIZE ->
                                   let v:= (ZMap.get i r'0) in
                                   Val.has_type v Tint)
                      /\(forall i, 0<= i < UCTXT_SIZE ->
                                   let v:= (ZMap.get i r'0) in
                                   val_inject (Mem.flat_inj (Mem.nextblock m0)) v v)
                      /\ ikern labd = true
                      /\ ihost labd = true
                      /\ ikern labd0 = true
                      /\ ihost labd0 = true
                      /\ ikern labd1 = true
                      /\ ihost labd1 = true.
      Proof.
        intros. eapply valid_curid in H1.
        split; trivial.
        functional inversion H; subst.
        clear H3.
        unfold get_curid_spec. unfold ptout_spec.
        subrewrite'. split; trivial.
        esplit. split.
        reflexivity. simpl.
        unfold setPT_spec; simpl.
        subrewrite'.
        rewrite zle_lt_true; trivial.
        esplit. split.
        reflexivity. simpl.
        split; trivial.
        unfold restore_uctx_spec; simpl.
        subrewrite'.
        split. reflexivity.
        inv H0.
        refine_split'; trivial; intros;
        eapply uctxt_INJECT; eauto.
      Qed.

    End StartUser.

    Lemma Hget_curid: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm puctxtintro = ret ge ->
        (exists b_get_curid, Genv.find_symbol ge get_curid = Some b_get_curid
                             /\ Genv.find_funct_ptr ge b_get_curid = 
                                Some (External (EF_external get_curid get_curid_sig)))
        /\ get_layer_primitive get_curid puctxtintro = OK (Some (gensem get_curid_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive get_curid puctxtintro = OK (Some (gensem get_curid_spec)))
        by reflexivity.
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma HsetPT: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm puctxtintro = ret ge ->
        (exists b_setPT, Genv.find_symbol ge set_pt = Some b_setPT
                             /\ Genv.find_funct_ptr ge b_setPT = 
                                Some (External (EF_external set_pt set_pt_sig)))
        /\ get_layer_primitive set_pt puctxtintro = OK (Some (gensem setPT_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive set_pt puctxtintro = OK (Some (gensem setPT_spec)))
        by reflexivity.
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Hpt_out: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm puctxtintro = ret ge ->
        (exists b_pt_out, Genv.find_symbol ge pt_out = Some b_pt_out
                             /\ Genv.find_funct_ptr ge b_pt_out = 
                                Some (External (EF_external pt_out null_signature)))
        /\ get_layer_primitive pt_out puctxtintro = OK (Some (primcall_general_compatsem' ptout_spec (prim_ident:= pt_out))).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive pt_out puctxtintro = 
                     OK (Some (primcall_general_compatsem' ptout_spec (prim_ident:= pt_out))))
        by reflexivity.
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Hpt_in: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm puctxtintro = ret ge ->
        (exists b_pt_in, Genv.find_symbol ge pt_in = Some b_pt_in
                             /\ Genv.find_funct_ptr ge b_pt_in = 
                                Some (External (EF_external pt_in null_signature)))
        /\ get_layer_primitive pt_in puctxtintro = OK (Some (primcall_general_compatsem' ptin_spec (prim_ident:= pt_in))).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive pt_in puctxtintro =
                     OK (Some (primcall_general_compatsem' ptin_spec (prim_ident:= pt_in))))
        by reflexivity.
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Htrap_in: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm puctxtintro = ret ge ->
        (exists b_trap_in, Genv.find_symbol ge trap_in = Some b_trap_in
                             /\ Genv.find_funct_ptr ge b_trap_in = 
                                Some (External (EF_external trap_in null_signature)))
        /\ get_layer_primitive trap_in puctxtintro = OK (Some (primcall_general_compatsem trapin_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive trap_in puctxtintro = OK (Some (primcall_general_compatsem trapin_spec)))
        by reflexivity.
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Hrestore_uctx: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm puctxtintro = ret ge ->
        (exists b_restore_uctx, Genv.find_symbol ge restore_uctx = Some b_restore_uctx
                             /\ Genv.find_funct_ptr ge b_restore_uctx = 
                                Some (External (EF_external restore_uctx restore_uctx_sig)))
        /\ get_layer_primitive restore_uctx puctxtintro = OK (Some (primcall_restoreuctx_compatsem restore_uctx_spec cid)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive restore_uctx puctxtintro = 
                     OK (Some (primcall_restoreuctx_compatsem restore_uctx_spec cid)))
        by reflexivity.
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Hsave_uctx: 
      forall MCode_Asm s ge,
        make_globalenv s MCode_Asm puctxtintro = ret ge ->
        (exists b_save_uctx, Genv.find_symbol ge save_uctx = Some b_save_uctx
                             /\ Genv.find_funct_ptr ge b_save_uctx = 
                                Some (External (EF_external save_uctx exit_sig)))
        /\ get_layer_primitive save_uctx puctxtintro = OK (Some (save_uctx_compatsem save_uctx_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive save_uctx puctxtintro = OK (Some (save_uctx_compatsem save_uctx_spec)))
        by reflexivity.
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma Hproc_start_user:
      forall ge s b,
        make_globalenv s (proc_start_user ↦ proc_start_user_function) puctxtintro = ret ge ->
        find_symbol s proc_start_user = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal proc_start_user_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function proc_start_user (proc_start_user ↦ proc_start_user_function)
                       = OK (Some proc_start_user_function)) by
          reflexivity.
      assert (HInternal: make_internal proc_start_user_function = OK (AST.Internal proc_start_user_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.

    Lemma Hproc_exit_user:
      forall ge s b,
        make_globalenv s (proc_exit_user ↦ proc_exit_user_function) puctxtintro = ret ge ->
        find_symbol s proc_exit_user = Some b ->
        stencil_matches s ge ->
        Genv.find_funct_ptr ge b = Some (Internal proc_exit_user_function).
    Proof.
      intros.
      assert (Hmodule: get_module_function proc_exit_user (proc_exit_user ↦ proc_exit_user_function) 
                       = OK (Some proc_exit_user_function)) by
          reflexivity.
      assert (HInternal: make_internal proc_exit_user_function = OK (AST.Internal proc_exit_user_function)) by reflexivity.
      eapply make_globalenv_get_module_function in H; eauto.
      destruct H as [?[Hsymbol ?]].
      inv H1.
      rewrite stencil_matches_symbols in Hsymbol.
      rewrite H0 in Hsymbol. inv Hsymbol.
      assumption.
    Qed.
    
  End WITHMEM.

End ASM_DATA.