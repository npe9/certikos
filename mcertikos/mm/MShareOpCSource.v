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
Require Import Constant.


Definition _source : ident := 1%positive.
Definition _dest : ident := 2%positive.
Definition _ret_value : ident := 6%positive.
Definition _sd_seen : ident := 11%positive.



Definition shared_mem_status_body: statement :=
  (Ssequence
     (Scall (Some _sd_seen)
            (Evar get_shared_mem_seen (Tfunction (Tcons tint (Tcons tint Tnil))
                                                 tint cc_default))
            ((Etempvar _source tint) :: (Etempvar _dest tint) :: nil))
  (Ssequence
     (Sifthenelse (Etempvar _sd_seen tint)
         (Scall (Some _ret_value)
            (Evar get_shared_mem_status_seen (Tfunction (Tcons tint (Tcons tint Tnil))
                                                 tint cc_default))
            ((Etempvar _source tint) :: (Etempvar _dest tint) :: nil))

         (Ssequence
            (Scall None
                   (Evar set_shared_mem_seen (Tfunction
                                                (Tcons tint
                                                       (Tcons tint (Tcons tint Tnil)))
                                                tvoid cc_default))
                   ((Etempvar _source tint) :: (Etempvar _dest tint) ::
                                          (Econst_int (Int.repr 1) tint) :: nil))
            (Scall (Some _ret_value)
                   (Evar get_shared_mem_state (Tfunction (Tcons tint (Tcons tint Tnil))
                                                         tint cc_default))
                   ((Etempvar _source tint) :: (Etempvar _dest tint) :: nil))
         )
     )
     (Sreturn (Some (Etempvar _ret_value tint)))
  )).

Definition f_shared_mem_status := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_sd_seen, tint) :: (_ret_value, tint) :: nil);
  fn_body := shared_mem_status_body

|}.


(**)

Definition _dest_va : ident := 3%positive.
Definition _sd_state : ident := 4%positive.
Definition _ds_state : ident := 5%positive.
Definition _source_va : ident := 7%positive.
Definition _ds_state' : ident := 8%positive.
Definition _sd_state' : ident := 9%positive.
Definition _is_ready : ident := 10%positive.



Definition offer_shared_mem_body: statement :=
  (Ssequence
     (Scall (Some _sd_state')
            (Evar get_shared_mem_state (Tfunction (Tcons tint (Tcons tint Tnil))
                                                  tint cc_default))
            ((Etempvar _source tint) :: (Etempvar _dest tint) :: nil))
  (Ssequence
     (Sset _sd_state (Etempvar _sd_state' tint))
  (Ssequence
     (Sifthenelse (Ebinop Oeq (Etempvar _sd_state tint)
                          (Econst_int (Int.repr 1) tint) tint)
         (Sset _ret_value (Econst_int (Int.repr 1) tint))

         (Ssequence
            (Scall (Some _ds_state')
                   (Evar get_shared_mem_state (Tfunction
                                                 (Tcons tint (Tcons tint Tnil)) tint
                                                 cc_default))
                   ((Etempvar _dest tint) :: (Etempvar _source tint) :: nil))
         (Ssequence
            (Sset _ds_state (Etempvar _ds_state' tint))

            (Sifthenelse (Ebinop Oeq (Etempvar _ds_state tint) (Econst_int (Int.repr 1) tint) tint)
                (Ssequence
                   (Scall (Some _is_ready)
                          (Evar shared_mem_to_ready (Tfunction
                                                       (Tcons tint
                                                              (Tcons tint (Tcons tint Tnil)))
                                                           tint cc_default))
                          ((Etempvar _source tint) :: (Etempvar _dest tint) ::
                                                   (Etempvar _source_va tint) :: nil))
                   (Sifthenelse (Ebinop Oeq (Etempvar _is_ready tint)
                                        (Econst_int (Int.repr MagicNumber) tint) tint)
                       (Ssequence
                          (Scall None (Evar shared_mem_to_dead
                                            (Tfunction
                                               (Tcons tint
                                                      (Tcons tint (Tcons tint Tnil)))
                                               tvoid cc_default))
                                 ((Etempvar _source tint) :: (Etempvar _dest tint) ::
                                                          (Etempvar _source_va tint) :: nil))
                          ((Sset _ret_value (Econst_int (Int.repr 2) tint))))

                       (Sset _ret_value (Econst_int (Int.repr 0) tint))))

                (Ssequence
                   (Scall None
                          (Evar shared_mem_to_pending (Tfunction
                                                         (Tcons tint
                                                                (Tcons tint
                                                                       (Tcons tint Tnil)))
                                                         tvoid cc_default))
                          ((Etempvar _source tint) :: (Etempvar _dest tint) ::
                                                   (Etempvar _source_va tint) :: nil))
                   (Sset _ret_value (Econst_int (Int.repr 1) tint)))
              ))))
      (Sreturn (Some (Etempvar _ret_value tint)))))).

(*
            (Sifthenelse (Ebinop Oeq (Etempvar _ds_state tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sset 64%positive (Econst_int (Int.repr 1) tint))
                    (Ssequence
                       (Sset 65%positive
                             (Ecast
                                (Ebinop Oeq (Etempvar _ds_state tint)
                                        (Econst_int (Int.repr 2) tint) tint) tint))
                       (Sset 64%positive (Ecast (Etempvar 65%positive tint) tint))))
                (Sifthenelse (Etempvar 64%positive tint)
                    (Ssequence
                       (Scall None
                              (Evar shared_mem_to_pending (Tfunction
                                                             (Tcons tint
                                                                    (Tcons tint
                                                                           (Tcons tint (Tcons tint Tnil))))
                                                             tvoid cc_default))
                              ((Etempvar _source tint) :: (Etempvar _dest tint) ::
                                                       (Etempvar _source_va tint) :: nil))
                       (Sset _ret_value (Econst_int (Int.repr 1) tint)))

                    (Ssequence
                       (Scall (Some _is_ready)
                              (Evar shared_mem_to_ready (Tfunction
                                                           (Tcons tint
                                                                  (Tcons tint (Tcons tint Tnil)))
                                                           tint cc_default))
                              ((Etempvar _source tint) :: (Etempvar _dest tint) ::
                                                       (Etempvar _source_va tint) :: nil))
                       (Sifthenelse (Ebinop Oeq (Etempvar _is_ready tint)
                                            (Econst_int (Int.repr MagicNumber) tint) tint)
                           (Ssequence
                              (Scall None (Evar shared_mem_to_dead
                                                (Tfunction
                                                   (Tcons tint
                                                          (Tcons tint (Tcons tint Tnil)))
                                                   tvoid cc_default))
                                     ((Etempvar _source tint) :: (Etempvar _dest tint) ::
                                                              (Etempvar _source_va tint) :: nil))
                                     ((Sset _ret_value (Econst_int (Int.repr 2) tint))))

                              (Sset _ret_value (Econst_int (Int.repr 0) tint))))
              ))))))
      (Sreturn (Some (Etempvar _ret_value tint))))).*)


Definition f_offer_shared_mem := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_source, tint) :: (_dest, tint) :: (_source_va, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_sd_state, tint) :: (_ds_state, tint) ::
               (_ret_value, tint) :: (_ds_state', tint) ::
               (_sd_state', tint) :: (_is_ready, tint) :: nil);
  fn_body := offer_shared_mem_body

|}.


