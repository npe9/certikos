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
(*           Layers of PM: Assembly Verification for PKContext         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
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
(*Require Import LAsmModuleSem.*)
Require Import LAsm.

Require Import MContainer.
Require Import PTIntroGenSpec.
Require Import PTIntroGenAsmSource.
Require Import LAsmModuleSemSpec.
Require Import LinkTactic.

Require Import AbstractDataType.

Section ASM_VERIFICATION.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATA := RData. 
  Notation LDATAOps := (cdata (cdata_ops := mcontainer_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Lemma pt_in_code_correct:
      asm_spec_le (pt_in ↦ pt_in_spec_low)
                  (〚pt_in ↦ ptin_function 〛 mcontainer).
    Proof.
      eapply asm_sem_intro; try reflexivity; simpl.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal ptin_function)).
      {
        assert (Hmodule: get_module_function pt_in (pt_in ↦ ptin_function) = OK (Some ptin_function)) by
            reflexivity.
        assert (HInternal: make_internal ptin_function = OK (AST.Internal ptin_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }
      refine_split'.
      - reflexivity.
      - econstructor; eauto.
        one_step_forward 0.
        + reflexivity.
        + econstructor.
        + reflexivity.
      - reflexivity.
      - inv H4. inv inv_inject_neutral.
        eapply Mem.neutral_inject in inv_mem_inject_neutral.
        assumption.
      - lift_trivial.
        reflexivity.
      - intros reg.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.
        constructor.
      - esplit; reflexivity.
    Qed.

    Lemma pt_out_code_correct:
      asm_spec_le (pt_out ↦ pt_out_spec_low)
                  (〚pt_out ↦ ptout_function 〛 mcontainer).
    Proof.
      eapply asm_sem_intro; try reflexivity; simpl.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal ptout_function)).
      {
        assert (Hmodule: get_module_function pt_out (pt_out ↦ ptout_function) = OK (Some ptout_function)) by
            reflexivity.
        assert (HInternal: make_internal ptout_function = OK (AST.Internal ptout_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }
      refine_split'.
      - reflexivity.
      - econstructor; eauto.
        one_step_forward 0.
        + reflexivity.
        + econstructor.
        + reflexivity.
      - reflexivity.
      - inv H4. inv inv_inject_neutral.
        eapply Mem.neutral_inject in inv_mem_inject_neutral.
        assumption.
      - lift_trivial.
        reflexivity.
      - intros reg.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.     
        constructor.
      - esplit; reflexivity.
    Qed.

  End WITHMEM.

End ASM_VERIFICATION.