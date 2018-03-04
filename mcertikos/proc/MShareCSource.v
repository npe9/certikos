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
     #define num_proc 64

     struct KCtxtStruct {
         void * ESP;
         void * EDI;
         void * ESI;
         void * EBX;
         void * EBP;
         void * RA;
     };

     extern struct KCtxtStruct KCtxtPool_LOC[num_proc];

     void set_RA(unsigned int proc_index, void * entry)
     {
         KCtxtPool_LOC[proc_index].RA = entry;
     }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index: ident := 1.
Let tentry: ident := 2.

Local Open Scope Z_scope.

Definition set_RA_body : statement := 
  (Sassign (Efield (Ederef
                      (Ebinop Oadd (Evar KCtxtPool_LOC (tarray t_struct_KCtxt num_proc))
                              (Etempvar tproc_index tint) (tptr t_struct_KCtxt))
                      t_struct_KCtxt) RA (tptr tvoid)) (Etempvar tentry (tptr tvoid))).

Definition f_set_RA := {|
                        fn_return := tvoid;
                        fn_callconv := cc_default;
                        fn_vars := nil;
                        fn_params := ((tproc_index, tint) :: (tentry, tptr tvoid) :: nil);
                        fn_temps := nil;
                        fn_body := set_RA_body
                      |}.



(** 
<<
     #define num_proc 64

     struct KCtxtStruct {
         void * ESP;
         void * EDI;
         void * ESI;
         void * EBX;
         void * EBP;
         void * RA;
     };

     extern struct KCtxtStruct KCtxtPool_LOC[num_proc];

     void set_SP(unsigned int proc_index, void * esp)
     {
         KCtxtPool_LOC[proc_index].ESP = esp;
     }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tesp: ident := 2.

Local Open Scope Z_scope.

Definition set_SP_body : statement := 
  (Sassign (Efield (Ederef
                      (Ebinop Oadd (Evar KCtxtPool_LOC (tarray t_struct_KCtxt num_proc))
                              (Etempvar tproc_index tint) (tptr t_struct_KCtxt))
                      t_struct_KCtxt) ESP (tptr tvoid)) (Etempvar tesp (tptr tvoid))).

Definition f_set_SP := {|
                        fn_return := tvoid;
                        fn_callconv := cc_default;
                        fn_vars := nil;
                        fn_params := ((tproc_index, tint) :: (tesp, tptr tvoid) :: nil);
                        fn_temps := nil;
                        fn_body := set_SP_body
                      |}.
