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
      
      struct TCB {
          unsigned int state;
          unsigned int prev;
          unsigned int next;
      };
      
      extern struct TCB TCBPool_LOC[num_proc];
      
      unsigned int get_state(unsigned int proc_index)
      {
          return TCBPool_LOC[proc_index].state;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index: ident := 1.

Local Open Scope Z_scope.

Definition get_state_body : statement := 
  (Sreturn (Some (Efield
                    (Ederef
                       (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                               (Etempvar tproc_index tint) (tptr t_struct_TCB))
                       t_struct_TCB) state tint))).

Definition f_get_state := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tproc_index, tint) :: nil);
                           fn_temps := nil;
                           fn_body := get_state_body
                         |}.



(** 
<<
      #define num_proc 64
      
      struct TCB {
          unsigned int state;
          unsigned int prev;
          unsigned int next;
      };
      
      extern struct TCB TCBPool_LOC[num_proc];
      
      unsigned int get_prev(unsigned int proc_index)
      {
          return TCBPool_LOC[proc_index].prev;
      }
>>
 *)

Definition get_prev_body : statement := 
  (Sreturn (Some (Efield
                    (Ederef
                       (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                               (Etempvar tproc_index tint) (tptr t_struct_TCB))
                       t_struct_TCB) prev tint))).

Definition f_get_prev := {|
                          fn_return := tint;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tproc_index, tint) :: nil);
                          fn_temps := nil;
                          fn_body := get_prev_body
                        |}.



(** 
<<
      #define num_proc 64
      
      struct TCB {
          unsigned int next;
          unsigned int prev;
          unsigned int next;
      };
      
      extern struct TCB TCBPool_LOC[num_proc];
      
      unsigned int get_next(unsigned int proc_index)
      {
          return TCBPool_LOC[proc_index].next;
      }
>>
 *)

Definition get_next_body : statement := 
  (Sreturn (Some (Efield
                    (Ederef
                       (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                               (Etempvar tproc_index tint) (tptr t_struct_TCB))
                       t_struct_TCB) next tint))).

Definition f_get_next := {|
                          fn_return := tint;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tproc_index, tint) :: nil);
                          fn_temps := nil;
                          fn_body := get_next_body
                        |}.



(** 
<<
      #define num_proc 64
      
      struct TCB {
          unsigned int state;
          unsigned int prev;
          unsigned int next;
      };
      
      extern struct TCB TCBPool_LOC[num_proc];
      
      void set_state(unsigned int proc_index, unsigned int state)
      {
          TCBPool_LOC[proc_index].state = state;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tstate: ident := 2.

Local Open Scope Z_scope.

Definition set_state_body : statement := 
  (Sassign (Efield(Ederef
                     (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                             (Etempvar tproc_index tint) (tptr t_struct_TCB)) t_struct_TCB) state
                  tint) (Etempvar tstate tint)).

Definition f_set_state := {|
                           fn_return := tvoid;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tproc_index, tint) :: (tstate, tint) :: nil);
                           fn_temps := nil;
                           fn_body := set_state_body
                         |}.



(** 
<<
      #define num_proc 64
      
      struct TCB {
          unsigned int prev;
          unsigned int prev;
          unsigned int next;
      };
      
      extern struct TCB TCBPool_LOC[num_proc];
      
      void set_prev(unsigned int proc_index, unsigned int prev)
      {
          TCBPool_LOC[proc_index].prev = prev;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tprev: ident := 3.

Local Open Scope Z_scope.

Definition set_prev_body : statement := 
  (Sassign (Efield(Ederef
                     (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                             (Etempvar tproc_index tint) (tptr t_struct_TCB)) t_struct_TCB) prev
                  tint) (Etempvar tprev tint)).

Definition f_set_prev := {|
                          fn_return := tvoid;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tproc_index, tint) :: (tprev, tint) :: nil);
                          fn_temps := nil;
                          fn_body := set_prev_body
                        |}.



(** 
<<
      #define num_proc 64
      
      struct TCB {
          unsigned int next;
          unsigned int next;
          unsigned int next;
      };
      
      extern struct TCB TCBPool_LOC[num_proc];
      
      void set_next(unsigned int proc_index, unsigned int next)
      {
          TCBPool_LOC[proc_index].next = next;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tnext: ident := 4.

Local Open Scope Z_scope.

Definition set_next_body : statement := 
  (Sassign (Efield(Ederef
                     (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                             (Etempvar tproc_index tint) (tptr t_struct_TCB)) t_struct_TCB) next
                  tint) (Etempvar tnext tint)).

Definition f_set_next := {|
                          fn_return := tvoid;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tproc_index, tint) :: (tnext, tint) :: nil);
                          fn_temps := nil;
                          fn_body := set_next_body
                        |}.



(** 
<<
      #define num_proc 64
      
      struct TCB {
          unsigned int prev;
          unsigned int prev;
          unsigned int next;
      };
      
      extern struct TCB TCBPool_LOC[num_proc];
      
      void tcb_init(unsigned int proc_index)
      {
          TCBPool_LOC[proc_index].state = 3;
          TCBPool_LOC[proc_index].prev = num_proc;
          TCBPool_LOC[proc_index].next = num_proc;
      }
>>
 *)

Definition tcb_init_body : statement := 
  (Ssequence
     (Sassign (Efield (Ederef
                         (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                                 (Etempvar tproc_index tint) (tptr t_struct_TCB)) t_struct_TCB)
                      state tint) (Econst_int (Int.repr 3) tint))
     (Ssequence
        (Sassign (Efield (Ederef
                            (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                                    (Etempvar tproc_index tint) (tptr t_struct_TCB)) t_struct_TCB)
                         prev tint)
                 (Econst_int (Int.repr num_proc) tint))
        (Sassign (Efield (Ederef
                            (Ebinop Oadd (Evar TCBPool_LOC (tarray t_struct_TCB num_proc))
                                    (Etempvar tproc_index tint) (tptr t_struct_TCB)) t_struct_TCB)
                         next tint)
                 (Econst_int (Int.repr num_proc) tint)))).

Definition f_tcb_init := {|
                          fn_return := tvoid;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tproc_index, tint) :: nil);
                          fn_temps := nil;
                          fn_body := tcb_init_body
                        |}.