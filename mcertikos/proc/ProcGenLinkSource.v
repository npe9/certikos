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
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.
Require Import LAsmModuleSemDef.
Require Import CompCertiKOS.
Require Import GlobIdent.
Require Import CDataTypes.
Require Import PUCtxtIntroCSource.
Require Import ProcGenAsmSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PUCtxtIntro.

Section WITHCOMPCERTIKOS.

Context `{compcertikos_prf: CompCertiKOS}.
Context `{real_params_prf : RealParams}.

Definition PProc_impl: res LAsm.module :=
  M_proc_create <- CompCertiKOS.transf_module (proc_create ↦ f_proc_create);
  (** watch out parentheses here: *)
  M <- ret (
      ( (** group primitives according to the global variables that they use *)
        M_proc_create
        ⊕ ((proc_start_user ↦ proc_start_user_function) ⊕ (proc_exit_user ↦ proc_exit_user_function))
      ) ⊕ ∅ (** for L64 and other passthrough primitives *)
    );
  _ <- eassert nil (LayerOK (〚M 〛 (puctxtintro ⊕ L64) ⊕ puctxtintro ⊕ L64));
  ret M.

End WITHCOMPCERTIKOS.
