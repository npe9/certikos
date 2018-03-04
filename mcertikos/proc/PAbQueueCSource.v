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
(*                       mCertiKOS C Source Code                       *)
(*                                                                     *)
(*                        Xiongnan (Newman) Wu                         *)
(*                                                                     *)
(*                          Yale University                            *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Cop.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.



(** 
<<
      extern unsigned int CURID_LOC;

      unsigned int get_curid()
      {
          return CURID_LOC;
      }
>>
 *)

Definition get_curid_body : statement := 
  Sreturn (Some (Evar CURID_LOC tint)).

Definition f_get_curid := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := nil;
                           fn_temps := nil;
                           fn_body := get_curid_body
                         |}.



(** 
<<
      extern unsigned int CURID_LOC;

      void set_curid(unsigned int curid)
      {
          CURID_LOC = curid;
      }
>>
 *)

Let tcurid: ident := 1 % positive.

Definition set_curid_body : statement := 
  Sassign (Evar CURID_LOC tint) (Etempvar tcurid tint).

Definition f_set_curid := {|
                           fn_return := Tvoid;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tcurid, tint) :: nil);
                           fn_temps := nil;
                           fn_body := set_curid_body
                         |}.