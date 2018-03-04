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
(*              From CompCertX AsmX to per-function LAsm               *)
(*                                                                     *)
(*          Tahina Ramananandro <tahina.ramananandro@yale.edu>         *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provides the compiler from CompCertX [AsmX] (in fact,
    syntactically, from CompCert [Asm]) to the [LAsm] instructions. *)

Require AST.

Require Asm.
Require LAsm.

Definition transf_code: forall (c: Asm.code), LAsm.code :=
  List.map LAsm.asm_instruction.

Definition transf_function (f: Asm.function): LAsm.function :=
  {|
    LAsm.fn_sig := Asm.fn_sig f;
    LAsm.fn_code := transf_code (Asm.fn_code f)
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program:
  Asm.program -> LAsm.program
 := AST.transform_program transf_fundef.

