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
(*                                                                     *)
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
(*Require Import Constant.*)

(*
 * SHRDMEMPOOL_LOC, size = num_proc * N
 *)
(*
 * Tstruct : ident -> fieldlist -> attr -> type
 * Fnil : fieldlist | Fcons : ident -> type -> fieldlist -> fieldlist
 *
 * arraytype = (tarray type size)
 * pointer = (Ebinop Oadd array_base offset (tptr pointee_type))
 * (Ederef pointer type)
 * (Efield struct field_name type)
 *)

(*temp ids *)

Let smsp_struct: ident := 3400%positive.
Let smsp_state: ident := 3500%positive.
Let smsp_seen: ident := 3600%positive.
Let smsp_loc: ident := 3700%positive.
Let t_smsp_struct :=
  Tstruct smsp_struct
          (Fcons smsp_loc tint
          (Fcons smsp_state tint
          (Fcons smsp_seen tint Fnil)))
          noattr.

(**)

Definition smspool_loc_type : globvar type :=
  {|
    gvar_info := (tarray (tarray t_smsp_struct num_proc) num_proc);
    gvar_init := ((Init_space 49152)::nil);
    gvar_readonly := false;
    gvar_volatile := false
  |}.

(*******************************) 

Definition _source : ident := 1%positive.
Definition _dest : ident := 2%positive.
(*Definition _ret_value : ident := 6%positive.
Definition _sd_seen : ident := 11%positive.*)

(********)


(**
<<
    void clear_shared_mem(int source, int dest)
    {
        array[source][dest].smsp_loc = 0;
        array[source][dest].smsp_state = 2;
        array[source][dest].smsp_seen = 1;
    }

>>
*)

Definition clear_shared_mem_body: statement :=
(Ssequence
  (Sassign
    (Efield
      (Ederef
        (Ebinop Oadd
          (Ederef
            (Ebinop Oadd
              (Evar SHRDMEMPOOL_LOC (tarray (tarray t_smsp_struct 64) 64))
              (Etempvar _source tint)
              (tptr (tarray t_smsp_struct 64)))
            (tarray t_smsp_struct 64)) (Etempvar _dest tint)
          (tptr t_smsp_struct)) t_smsp_struct) smsp_loc tint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef
          (Ebinop Oadd
            (Ederef
              (Ebinop Oadd
                (Evar SHRDMEMPOOL_LOC (tarray (tarray t_smsp_struct 64) 64))
                (Etempvar _source tint)
                (tptr (tarray t_smsp_struct 64)))
              (tarray t_smsp_struct 64)) (Etempvar _dest tint)
            (tptr t_smsp_struct)) t_smsp_struct) smsp_state
        tint) (Econst_int (Int.repr 2) tint))
    (Sassign
      (Efield
        (Ederef
          (Ebinop Oadd
            (Ederef
              (Ebinop Oadd
                (Evar SHRDMEMPOOL_LOC (tarray (tarray t_smsp_struct 64) 64))
                (Etempvar _source tint)
                (tptr (tarray t_smsp_struct 64)))
              (tarray t_smsp_struct 64)) (Etempvar _dest tint)
            (tptr t_smsp_struct)) t_smsp_struct) smsp_seen
        tint) (Econst_int (Int.repr 1) tint))))
.

Definition f_clear_shared_mem := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := clear_shared_mem_body
|}.

(**)

Definition get_shared_mem_loc_body: statement :=
  let arr :=
      (Ederef
         (Ebinop Oadd
                 (Evar SHRDMEMPOOL_LOC
                       (tarray (tarray t_smsp_struct num_proc) num_proc))
                 (Etempvar _source tint)
                 (tptr (tarray t_smsp_struct num_proc)))
         (tarray t_smsp_struct num_proc)) in
  (Sreturn
     (Some (Efield
              (Ederef
                 (Ebinop Oadd
                         arr
                         (Etempvar _dest tint)
                         (tptr t_smsp_struct))
                 t_smsp_struct)
              smsp_loc tint))).

Definition f_get_shared_mem_loc := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := get_shared_mem_loc_body

|}.

(**)

Definition _loc : ident := 3%positive.

Definition set_shared_mem_loc_body: statement :=
  (Sassign
     (Efield
        (Ederef
           (Ebinop Oadd
                   (Ederef
                      (Ebinop Oadd
                              (Evar SHRDMEMPOOL_LOC
                                    (tarray (tarray t_smsp_struct num_proc)
                                            num_proc))
                              (Etempvar _source tint)
                              (tptr (tarray t_smsp_struct 64)))
                      (tarray t_smsp_struct 64))
                   (Etempvar _dest tint)
                   (tptr t_smsp_struct))
           t_smsp_struct)
        smsp_loc tint)
     (Etempvar _loc tint)).

Definition f_set_shared_mem_loc := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: (_loc, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := set_shared_mem_loc_body
|}.

(********)

Definition get_shared_mem_state_body: statement :=
  let arr :=
      (Ederef
         (Ebinop Oadd
                 (Evar SHRDMEMPOOL_LOC
                       (tarray (tarray t_smsp_struct num_proc) num_proc))
                 (Etempvar _source tint)
                 (tptr (tarray t_smsp_struct num_proc)))
         (tarray t_smsp_struct num_proc)) in
  (Sreturn
     (Some (Efield
              (Ederef
                 (Ebinop Oadd
                         arr
                         (Etempvar _dest tint)
                         (tptr t_smsp_struct))
                 t_smsp_struct)
              smsp_state tint))).

Definition f_get_shared_mem_state := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := get_shared_mem_state_body

|}.

(**)

Definition _state : ident := 4%positive.

Definition set_shared_mem_state_body: statement :=
  (Sassign
     (Efield
        (Ederef
           (Ebinop Oadd
                   (Ederef
                      (Ebinop Oadd
                              (Evar SHRDMEMPOOL_LOC
                                    (tarray (tarray t_smsp_struct num_proc)
                                            num_proc))
                              (Etempvar _source tint)
                              (tptr (tarray t_smsp_struct 64)))
                      (tarray t_smsp_struct 64))
                   (Etempvar _dest tint)
                   (tptr t_smsp_struct))
           t_smsp_struct)
        smsp_state tint)
     (Etempvar _state tint)).

Definition f_set_shared_mem_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: (_state, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := set_shared_mem_state_body
|}.

(********)

Definition get_shared_mem_seen_body: statement :=
  let arr :=
      (Ederef
         (Ebinop Oadd
                 (Evar SHRDMEMPOOL_LOC
                       (tarray (tarray t_smsp_struct num_proc) num_proc))
                 (Etempvar _source tint)
                 (tptr (tarray t_smsp_struct num_proc)))
         (tarray t_smsp_struct num_proc)) in
  (Sreturn
     (Some (Efield
              (Ederef
                 (Ebinop Oadd
                         arr
                         (Etempvar _dest tint)
                         (tptr t_smsp_struct))
                 t_smsp_struct)
              smsp_seen tint))).

Definition f_get_shared_mem_seen := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := get_shared_mem_seen_body

|}.


(**)

Definition _seen : ident := 5%positive.

Definition set_shared_mem_seen_body: statement :=
  (Sassign
     (Efield
        (Ederef
           (Ebinop Oadd
                   (Ederef
                      (Ebinop Oadd
                              (Evar SHRDMEMPOOL_LOC
                                    (tarray (tarray t_smsp_struct num_proc)
                                            num_proc))
                              (Etempvar _source tint)
                              (tptr (tarray t_smsp_struct 64)))
                      (tarray t_smsp_struct 64))
                   (Etempvar _dest tint)
                   (tptr t_smsp_struct))
           t_smsp_struct)
        smsp_seen tint)
     (Etempvar _seen tint)).

Definition f_set_shared_mem_seen := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: (_seen, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := set_shared_mem_seen_body
|}.