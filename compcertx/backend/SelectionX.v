Require compcert.backend.Selection.
Require I64helpers.

Import AST.
Export Selection.

(** In this file, we define per-function/module instruction selection,
without any proof. *)

Definition sel_function := sel_function (fun _ => None) I64helpers.hf.

Definition sel_fundef := sel_fundef (fun _ => None) I64helpers.hf.

Definition sel_program := transform_program (V := unit) sel_fundef.
