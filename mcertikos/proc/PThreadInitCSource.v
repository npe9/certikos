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
      #define num_chan 64
      
      struct TDQ {
          unsigned int head;
          unsigned int tail;
      };
      
      extern struct TDQ TDQPool_LOC[num_chan + 1];
      
      unsigned int get_head(unsigned int chan_index)
      {
          return TDQPool_LOC[chan_index].head;
      }
>>
 *)
(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tchan_index: ident := 1.

Local Open Scope Z_scope.

Definition get_head_body : statement := 
  (Sreturn (Some (Efield
                    (Ederef
                       (Ebinop Oadd (Evar TDQPool_LOC (tarray t_struct_TDQ (num_chan + 1)))
                               (Etempvar tchan_index tint) (tptr t_struct_TDQ))
                       t_struct_TDQ) head tint))).

Definition f_get_head := {|
                          fn_return := tint;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tchan_index, tint) :: nil);
                          fn_temps := nil;
                          fn_body := get_head_body
                        |}.



(** 
<<
      #define num_chan 64
      
      struct TDQ {
          unsigned int head;
          unsigned int tail;
      };
      
      extern struct TDQ TDQPool_LOC[num_chan + 1];
      
      unsigned int get_tail(unsigned int chan_index)
      {
          return TDQPool_LOC[chan_index].tail;
      }
>>
 *)


Definition get_tail_body : statement := 
  (Sreturn (Some (Efield
                    (Ederef
                       (Ebinop Oadd (Evar TDQPool_LOC (tarray t_struct_TDQ (num_chan + 1)))
                               (Etempvar tchan_index tint) (tptr t_struct_TDQ))
                       t_struct_TDQ) tail tint))).

Definition f_get_tail := {|
                          fn_return := tint;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tchan_index, tint) :: nil);
                          fn_temps := nil;
                          fn_body := get_tail_body
                        |}.



(** 
<<
      #define num_chan 64
      
      struct TDQ {
          unsigned int head;
          unsigned int tail;
      };
      
      extern struct TCB TDQPool_LOC[num_chan + 1];
      
      void set_head(unsigned int chan_index, unsigned int head)
      {
          TDQPool_LOC[chan_index].head = head;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let thead: ident := 2.

Local Open Scope Z_scope.

Definition set_head_body : statement := 
  (Sassign (Efield(Ederef
                     (Ebinop Oadd (Evar TDQPool_LOC (tarray t_struct_TDQ (num_chan + 1)))
                             (Etempvar tchan_index tint) (tptr t_struct_TDQ)) t_struct_TDQ) head
                  tint) (Etempvar thead tint)).

Definition f_set_head := {|
                          fn_return := tvoid;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tchan_index, tint) :: (thead, tint) :: nil);
                          fn_temps := nil;
                          fn_body := set_head_body
                        |}.



(** 
<<
      #define num_chan 64
      #define num_proc 64
      
      struct TDQ {
          unsigned int head;
          unsigned int tail;
      };
      
      extern struct TCB TDQPool_LOC[num_chan + 1];
      
      void set_tail(unsigned int chan_index, unsigned int tail)
      {
          TDQPool_LOC[chan_index].tail = tail;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let ttail: ident := 3.

Local Open Scope Z_scope.

Definition set_tail_body : statement := 
  (Sassign (Efield(Ederef
                     (Ebinop Oadd (Evar TDQPool_LOC (tarray t_struct_TDQ (num_chan + 1)))
                             (Etempvar tchan_index tint) (tptr t_struct_TDQ)) t_struct_TDQ) tail
                  tint) (Etempvar ttail tint)).

Definition f_set_tail := {|
                          fn_return := tvoid;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tchan_index, tint) :: (ttail, tint) :: nil);
                          fn_temps := nil;
                          fn_body := set_tail_body
                        |}.



(** 
<<
      #define num_chan 64
      
      struct TDQ {
          unsigned int head;
          unsigned int tail;
      };
      
      extern struct TCB TDQPool_LOC[num_chan + 1];
      
      void tdq_init(unsigned int chan_index)
      {
          TDQPool_LOC[chan_index].head = num_proc;
          TDQPool_LOC[chan_index].tail = num_proc;
      }
>>
 *)

Definition tdq_init_body : statement := 
  (Ssequence
     (Sassign (Efield(Ederef
                        (Ebinop Oadd (Evar TDQPool_LOC (tarray t_struct_TDQ (num_chan + 1)))
                                (Etempvar tchan_index tint) (tptr t_struct_TDQ)) t_struct_TDQ) head
                     tint) (Econst_int (Int.repr num_proc) tint))
     (Sassign (Efield(Ederef
                        (Ebinop Oadd (Evar TDQPool_LOC (tarray t_struct_TDQ (num_chan + 1)))
                                (Etempvar tchan_index tint) (tptr t_struct_TDQ)) t_struct_TDQ) tail
                     tint) (Econst_int (Int.repr num_proc) tint))).

Definition f_tdq_init := {|
                          fn_return := tvoid;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tchan_index, tint) :: nil);
                          fn_temps := nil;
                          fn_body := tdq_init_body
                        |}.