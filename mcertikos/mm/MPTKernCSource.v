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
      extern void pt_init_kern(unsigned int);
      extern void set_pg(void);
      extern void set_pt(unsigned int);

      void pt_init(unsigned int mbi_adr)
      {
          pt_init_kern(mbi_adr);
          set_pt(0);
          set_pg();
      }
>>
 *)

Let tmbi_adr: ident := 1 % positive.

Definition pt_init_body : statement := 
  (Ssequence
     (Scall None (Evar pt_init_kern (Tfunction (Tcons tint Tnil) Tvoid cc_default)) ((Etempvar tmbi_adr tint)::nil))
     (Ssequence
        (Scall None (Evar set_pt (Tfunction (Tcons tint Tnil) Tvoid cc_default))
               ((Econst_int (Int.repr 0) tint) :: nil))
        (Scall None (Evar set_pg (Tfunction Tnil Tvoid cc_default)) nil)))
.

Definition f_pt_init := {|
                         fn_return := tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tmbi_adr, tint)::nil);
                         fn_temps := nil;
                         fn_body := pt_init_body
                       |}.