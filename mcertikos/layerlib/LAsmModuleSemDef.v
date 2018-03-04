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
(** This file provide the semantics for the [Asm] instructions. Since we introduce paging mechanisms, the semantics of memory load and store are different from [Compcert Asm]*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import AsmX.
Require Import Conventions.
Require Import Machregs.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import CompCertBuiltins.
Require Import LAsm.
Require Import MemoryExtra.
Require Import Observation.

(** ** Definitions of Semantics of LAsm modules *)

Section ModuleSemantics.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Global Instance lasm_program_format_ops:
    ProgramFormatOps function Ctypes.type fundef unit :=
    {
      make_internal κ := OK (AST.Internal κ);
      make_external D i σ := OK (AST.External (EF_external i (compatsem_sig σ)));
      make_varinfo τ := tt
    }.

  Global Instance lasm_program_format_prf:
    ProgramFormat function Ctypes.type fundef unit.
  Proof.
    split.
    * intros D i1 i2 Hi σ1 σ2 Hσ; subst.
      simpl.
      f_equal.
      f_equal.
      inversion Hσ; subst.
      + destruct H as [[Hstep Hsig Hvalid] Hinvs].
        destruct x; simpl in *; subst.
        destruct y; simpl in *; subst.
        unfold sextcall_sig.
        rewrite Hsig.
        reflexivity.
      + destruct H as [[Hstep Hsig Hvalid] Hinvs].
        destruct x; destruct y; simpl in *; subst; simpl in *.
        rewrite Hsig.
        reflexivity.
  Qed.

  Global Instance lasm_make_external_sim_monotonic:
    Proper
      (∀ R, - ==> sim R ++> res_le eq)
      (fun D => make_external (D := D)).
  Proof.
    intros D1 D2 R i p1 p2 Hsim.
    destruct R; try solve_monotonic.
    inversion Hsim; subst.
    * destruct H as [Hstep Hcsig Hvalid Hinvs]; simpl.
      unfold sextcall_sig.
      rewrite Hcsig.
      reflexivity.
    * destruct H as [Hstep Hsig Hvalid Hinvs]; simpl.
      rewrite Hsig.
      reflexivity.
    * destruct H as [Hstep Hsig Hvalid Hinvs]; simpl.
      rewrite Hsig.
      reflexivity.
  Qed.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Instance LC: forall {D} (L: compatlayer D)
                      `{acc_def_prf: !AccessorsDefined L},
                 LAsm.LayerConfigurationOps (ec_ops := compatlayer_extcall_ops L).
  Proof.
    intros. eapply compatlayer_configuration_ops; assumption.
  Defined. 

  Inductive lasm_step {D}
            (M: module) 
            (L: compatlayer D)
            (i: ident) (s: stencil)
            (rs: regset) (m: mwd D) (rs': regset) (m': mwd D): Prop :=
  | lasm_step_intro

      (** TODO: move this check somewhere else *)
      (acc_def_prf: AccessorsDefined L)

      (*(extinv: ExtcallInvariantsDefined L)
      (priminv: PrimcallInvariantsDefined L)*)

      (ge: genv)
      (b: block)
      (Hsymb: find_symbol s i = Some b)
      (Hge: make_globalenv s M L = ret ge)
      (PC_VAL: rs PC = Values.Vptr b Integers.Int.zero)

    (** semantics *)
    (** Potential problem: for an arbitrary primitive call, e.g. context switch, we are not capable of
        correctly characterizing the "final state" of the function execution *)
    (** We have to make sure that LAsm takes at least one step. *)
    (STAR: plus (LAsm.step (lcfg_ops := LC L))
                ge (State rs m) E0 (State rs' m'))
  .

  Local Existing Instance extcall_invariants_defined_dec.
  Local Existing Instance primcall_invariants_defined_dec.

  Local Existing Instance prim_valid_dec.

(*
  Local Instance lasm_step_sem_invariants `{D: compatdata} {L: compatlayer D} {M} {i}:
    PrimcallInvariants (lasm_step M L i).
  Proof.
    (*constructor; intros; inv H; simpl.
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
      eapply prim_high_level_invariant; eauto.*)
  Qed.*)

  Definition accessors_weak_defined `{D: compatdata} (L: compatlayer D) : bool :=
    match cl_exec_load L with
      | Errors.OK _ =>
        match cl_exec_store L with
          | Errors.OK _ => true
          | _ => false
        end
      | _ => false
    end.

  Definition lasm_primsem {D: compatdata} (M: module) (L: compatlayer D) (i: ident) (f: function): compatsem D :=
    inr {|
        sprimcall_primsem_step :=
          {|
            sprimcall_step := lasm_step M L i;
            sprimcall_sig := fn_sig f;
            sprimcall_valid s :=
              if decide (ExtcallInvariantsDefined L) then
                if decide (PrimcallInvariantsDefined L) then
                 if decide (LayerNamesMatch D L) then
                  if decide (get_layer_prim_valid L s) then
                    if accessors_weak_defined L then
                      match make_program s M L with
                        | OK _ =>
                          true
                        | Error _ => false
                      end
                    else false
                  else false
                 else false
                else false
              else false
          |};
        sprimcall_name := Some i;
        sprimcall_props := Error nil;
        sprimcall_invs := Error nil
      |}.
  
  (** * Semantics of whole modules *)

  Global Instance lasm_ptree_sem_ops: FunctionSemanticsOps _ _ _ _ _ _ :=
    {
      semof_fundef D M L i f := OK (lasm_primsem M L i f)
    }.

End ModuleSemantics.
