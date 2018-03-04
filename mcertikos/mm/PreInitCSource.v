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
      #define adr_low 1073741824

      extern unsigned int FlatMem_LOC[adr_low];

      unsigned int fload(unsigned int addr)
      {
        return FlatMem_LOC[addr];
      }
>>
 *)

Let taddr: ident := 1 % positive.

Definition fload_body : statement := 
  (Sreturn (Some (Ederef
                 (Ebinop Oadd (Evar FlatMem_LOC (tarray tint 1073741824))
                   (Etempvar taddr tint) (tptr tint)) tint)))
.

Definition f_fload := {|
                        fn_return := tint;
                        fn_callconv := cc_default;
                        fn_params := ((taddr, tint) :: nil);
                        fn_vars := nil;
                        fn_temps := nil;
                        fn_body := fload_body
                      |}.


(** 
<<
      #define adr_low 1073741824

      extern unsigned int FlatMem_LOC[adr_low];

      void fload(unsigned int addr, unsigned int val)
      {
        FlatMem_LOC[addr] = val;
      }
>>
 *)

Let tval: ident := 2 % positive.

Definition fstore_body: statement := 
  (Sassign
     (Ederef
        (Ebinop Oadd (Evar FlatMem_LOC (tarray tint 1073741824))
                (Etempvar taddr tint) (tptr tint)) tint) (Etempvar tval tint))
.

Definition f_fstore := {|
                        fn_return := Tvoid;
                        fn_callconv := cc_default;
                        fn_params := ((taddr, tint) :: (tval, tint) :: nil);
                        fn_vars := nil;
                        fn_temps := nil;
                        fn_body := fstore_body
                      |}.
