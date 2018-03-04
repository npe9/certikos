Require Import Errors.
Require Import AST.
Require Import Globalenvs.
Require Import Cminor.
Require Import SelectLong.
Require Import SelectLongproof.
Require Import EventsImpl.

Parameter get_helper: forall F V: Type, Genv.t (AST.fundef F) V -> String.string -> signature -> res ident.
Parameter get_builtin: String.string -> signature -> res ident.

Global Instance i64_helpers : I64helpers :=
  {
    get_helper := get_helper;
    get_builtin := get_builtin
  }.

Existing Instance Events.writable_block_always_ops.

Axiom get_helpers_correct:
  forall (ge: Cminor.genv) hf, get_helpers ge = OK hf -> i64_helpers_correct ge hf.
