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
Require Export liblayers.compat.CompatLayers.
Require Export liblayers.compat.CompatClightSem.
Require Export LAsmModuleSemDef.
Require Export CompCertiKOS.
Require Export CompCertiKOSproof.
Require Export RealParams.
Require Export I64Layer.
Require Export GlobIdent.

(** The generic linking code works based on a description of the code at
  a given layer: C functions, assembly functions, and global variables. *)

Record link_cfunction :=
  lcf {
      lcf_id: AST.ident;
      lcf_fun: Clight.function
    }.

Record link_asmfunction :=
  laf {
      laf_id: AST.ident;
      laf_fun: LAsm.function
    }.

Record link_globvar :=
  lgv {
      lgv_id: AST.ident;
      lgv_type: AST.globvar Ctypes.type
    }.

Record link_module :=
  {
    lm_cfun: list link_cfunction;
    lm_asmfun: list link_asmfunction;
    lm_gvar: list link_globvar
  }.

(** From the description above, we can construct the assembly module
  for a given layer: we need to compile all C functions, then add the
  assembly functions and global variables.

  The module should be constructed in a strategic way: fresh layer
  primitives are listed with C-implemented function first, then
  assembly. Furthermore, before any proof we will want to apply
  [transfer_variable] as needed. Hence, our module should have the
  general form:
  [(⋯(((cf1 ⊕ cf2 ⊕ ⋯ ⊕ af1 ⊕ af2 ⊕ ⋯ ⊕ ∅) ⊕ v1) ⊕ v2) ⊕ ⋯) ⊕ vn].

  The following code builds this module from the lists in the
  corresponding [link_module] object. *)

Section LINK_IMPL.

  Require ObservationImpl.

  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.
  Context {HDATA LDATA: compatdata} {R: compatrel HDATA LDATA}.

  Definition link_add_cfunction (f: link_cfunction) (M: res LAsm.module) :=
    Mr <- M;
    Mf <- CompCertiKOS.transf_module (lcf_id f ↦ lcf_fun f);
    ret (Mf ⊕ Mr).

  Definition link_impl_c (lm: link_module) (M: LAsm.module): res LAsm.module :=
    fold_right
      link_add_cfunction
      (ret M)
      (lm_cfun lm).

  Definition link_impl_asm (lm: link_module): LAsm.module :=
    fold_right
      (fun f M => laf_id f ↦ laf_fun f ⊕ M)
      ∅
      (lm_asmfun lm).

  Definition link_impl_add_gvar_specs vs L: compatlayer LDATA :=
    fold_right (fun v L => L ⊕ lgv_id v ↦ lgv_type v) L vs.

  Definition link_impl_add_gvar_defs: _ -> _ -> LAsm.module :=
    fold_left (fun M v => M ⊕ lgv_id v ↦ lgv_type v).

  Fixpoint link_impl_add_gvars (vs: list link_globvar) M L: res LAsm.module :=
    _ <- eassert nil (LayerOK (〚M〛 (link_impl_add_gvar_specs vs L ⊕ L64) ⊕ (link_impl_add_gvar_specs vs L ⊕ L64)));
    match vs with
      | nil =>
        ret M
      | v::vs =>
        link_impl_add_gvars vs (M ⊕ lgv_id v ↦ lgv_type v) L
    end.

  Definition link_impl_gvar (lm: link_module) ll M: res LAsm.module :=
    link_impl_add_gvars (lm_gvar lm) M ll.

  Definition link_impl (lm: link_module) (ll: compatlayer LDATA) :=
    Mc <- link_impl_c lm ∅;
    M  <- link_impl_gvar lm ll (Mc ⊕ link_impl_asm lm);
    _  <- eassert nil (LayerOK (〚M ⊕ ∅〛 (ll ⊕ L64) ⊕ ll ⊕ L64));
    ret (M ⊕ ∅).

End LINK_IMPL.
