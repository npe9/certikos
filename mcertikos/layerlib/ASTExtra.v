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
Require Export AST.

(** * Mimic the old prototype's changes to AST.v *)

(*
Section COMPAT.
  Definition external_fun' `{ef_ops: ExtFunOps} := external_function.

  Section External_fun.
    Context `{SyntaxConfiguration}.
    Context {primitive: Type}.

    Inductive abstract_prim :=
      mkap (efd: primitive) (sig: signature) (should_inline: bool).

    Definition external_fun :=
      (external_fun' + abstract_prim)%type.

    Definition EF' x: external_fun :=
      inl x.

    Definition EF_ABSTRACT efd sig si: external_fun :=
      inr (mkap efd sig si).
  End External_fun.
End COMPAT.

Arguments External {_ _ _} F ef.

Notation Internal x := (Internal (external_function := external_fun) x).
Notation External x := (External (external_function := external_fun) x).
*)
