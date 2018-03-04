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
(*              C level types for mCertiKOS                            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import compcert.cfrontend.Ctypes.
Require Import Coqlib.

Notation Tint32:= (Tint I32 Unsigned (mk_attr false None)).
Notation Tint64 := (Tlong Unsigned noattr).

Fixpoint type_of_list_type (params: list type) : typelist :=
  match params with
    | nil => Ctypes.Tnil
    | ty :: rem => Ctypes.Tcons ty (type_of_list_type rem)
  end.