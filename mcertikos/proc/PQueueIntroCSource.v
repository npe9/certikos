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
      
      extern void set_prev(unsigned int, unsigned int);
      extern void set_next(unsigned int, unsigned int);
      extern unsigned int get_tail(unsigned int);
      extern void set_head(unsigned int, unsigned int);
      extern void set_tail(unsigned int, unsigned int);
      
      void enqueue(unsigned int chan_index, unsigned int proc_index)
      {
          unsigned int tail;
          tail = get_tail(chan_index);
          if(tail == num_proc)
          {
              set_prev(proc_index, num_proc);
              set_next(proc_index, num_proc);
              set_head(chan_index, proc_index);
              set_tail(chan_index, proc_index);
          }
          else
          {
              set_next(tail, proc_index);
              set_prev(proc_index, tail);
              set_next(proc_index, num_proc);
              set_tail(chan_index, proc_index);
          }
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tchan_index: ident := 1.
Let tproc_index: ident := 2.
Let ttail: ident := 3.

Local Open Scope Z_scope.

Definition enqueue_body : statement := 
  (Ssequence
     (Scall (Some ttail)
            (Evar get_tail (Tfunction (Tcons tint Tnil) tint cc_default))
            ((Etempvar tchan_index tint) :: nil))
     (Sifthenelse (Ebinop Oeq (Etempvar ttail tint)
                          (Econst_int (Int.repr num_proc) tint) tint)
                  (Ssequence
                     (Scall None (Evar set_prev (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                            ((Etempvar tproc_index tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                     (Ssequence
                        (Scall None (Evar set_next (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                               ((Etempvar tproc_index tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                        (Ssequence 
                           (Scall None (Evar set_head (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                  ((Etempvar tchan_index tint) :: (Etempvar tproc_index tint) :: nil))
                           (Scall None (Evar set_tail (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                  ((Etempvar tchan_index tint) :: (Etempvar tproc_index tint) :: nil)))))
                  (Ssequence
                     (Scall None (Evar set_next (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                            ((Etempvar ttail tint) :: (Etempvar tproc_index tint) :: nil))
                     (Ssequence
                        (Scall None (Evar set_prev (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                               ((Etempvar tproc_index tint) :: (Etempvar ttail tint) :: nil))
                        (Ssequence
                           (Scall None (Evar set_next (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                  ((Etempvar tproc_index tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                           (Scall None (Evar set_tail (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                  ((Etempvar tchan_index tint) :: (Etempvar tproc_index tint) :: nil))))))).

Definition f_enqueue := {|
                         fn_return := tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tchan_index, tint) :: (tproc_index, tint) :: nil);
                         fn_temps := ((ttail, tint) :: nil);
                         fn_body := enqueue_body
                       |}.



(** 
<<
      #define num_proc 64
      
      extern void set_prev(unsigned int, unsigned int);
      extern unsigned int get_head(unsigned int);
      extern unsigned int get_next(unsigned int);
      extern void set_head(unsigned int, unsigned int);
      extern void set_tail(unsigned int, unsigned int);
      
      unsigned int dequeue(unsigned int chan_index)
      {
          unsigned int head, next, proc_index;
          proc_index = num_proc;
          head = get_head(chan_index);
          if(head != num_proc)
          {
              proc_index = head;
              next = get_next(head);
              if(next == num_proc)
              {
                  set_head(chan_index, num_proc);
                  set_tail(chan_index, num_proc);
              }
              else
              {
                  set_prev(next, num_proc);
                  set_head(chan_index, next);
              }
          }
          return proc_index;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let thead: ident := 4.
Let tnext: ident := 5.

Local Open Scope Z_scope.

Definition dequeue_body : statement := 
  (Ssequence
     (Sset tproc_index (Econst_int (Int.repr num_proc) tint))
     (Ssequence
        (Scall (Some thead) (Evar get_head (Tfunction (Tcons tint Tnil) tint cc_default))
               ((Etempvar tchan_index tint) :: nil))
        (Ssequence
           (Sifthenelse (Ebinop One (Etempvar thead tint)
                                (Econst_int (Int.repr num_proc) tint) tint)
                        (Ssequence
                           (Sset tproc_index (Etempvar thead tint))
                           (Ssequence
                              (Scall (Some tnext) (Evar get_next (Tfunction (Tcons tint Tnil) tint cc_default))
                                     ((Etempvar thead tint) :: nil))
                              (Sifthenelse (Ebinop Oeq (Etempvar tnext tint)
                                                   (Econst_int (Int.repr num_proc) tint) tint)
                                           (Ssequence
                                              (Scall None (Evar set_head (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                                     ((Etempvar tchan_index tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                                              (Scall None (Evar set_tail (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                                     ((Etempvar tchan_index tint) :: (Econst_int (Int.repr num_proc) tint) :: nil)))
                                           (Ssequence
                                              (Scall None (Evar set_prev (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                                     ((Etempvar tnext tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                                              (Scall None (Evar set_head (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                                     ((Etempvar tchan_index tint) :: (Etempvar tnext tint) :: nil))))))
                        Sskip)
           (Sreturn (Some (Etempvar tproc_index tint)))))).

Definition f_dequeue := {|
                         fn_return := tint;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tchan_index, tint) :: nil);
                         fn_temps := ((tproc_index, tint) :: (thead, tint) :: (tnext, tint) :: nil);
                         fn_body := dequeue_body
                       |}.



(** 
<<
      #define num_proc 64
      
      extern void set_prev(unsigned int, unsigned int);
      extern void set_next(unsigned int, unsigned int);
      extern unsigned int get_prev(unsigned int);
      extern unsigned int get_next(unsigned int);
      extern void set_head(unsigned int, unsigned int);
      extern void set_tail(unsigned int, unsigned int);
      
      void queue_rmv(unsigned int chan_index, unsigned int proc_index)
      {
          unsigned int prev, next;
          prev = get_prev(proc_index);
          next = get_next(proc_index);
          if(prev == num_proc)
          {
              if(next == num_proc)
              {
                  set_head(chan_index, num_proc);
                  set_tail(chan_index, num_proc);
              }
              else
              {
                  set_prev(next, num_proc);
                  set_head(chan_index, next);
              }
          }
          else
          {
              if(next == num_proc)
              {
                  set_next(prev, num_proc);
                  set_tail(chan_index, prev);
              }
              else
              {
                  if(prev != next)
                      set_next(prev, next);
                  set_prev(next, prev);
              }
          }
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tprev: ident := 6.

Local Open Scope Z_scope.

Definition queue_rmv_body : statement := 
  (Ssequence
     (Scall (Some tprev) (Evar get_prev (Tfunction (Tcons tint Tnil) tint cc_default))
            ((Etempvar tproc_index tint) :: nil))
     (Ssequence
        (Scall (Some tnext) (Evar get_next (Tfunction (Tcons tint Tnil) tint cc_default))
               ((Etempvar tproc_index tint) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar tprev tint)
                             (Econst_int (Int.repr num_proc) tint) tint)
                     (Sifthenelse (Ebinop Oeq (Etempvar tnext tint)
                                          (Econst_int (Int.repr num_proc) tint) tint)
                                  (Ssequence 
                                     (Scall None (Evar set_head (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                            ((Etempvar tchan_index tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                                     (Scall None (Evar set_tail (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                            ((Etempvar tchan_index tint) :: (Econst_int (Int.repr num_proc) tint) :: nil)))
                                  (Ssequence
                                     (Scall None (Evar set_prev (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                            ((Etempvar tnext tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                                     (Scall None (Evar set_head (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                            ((Etempvar tchan_index tint) :: (Etempvar tnext tint) :: nil))))
                     (Sifthenelse (Ebinop Oeq (Etempvar tnext tint)
                                          (Econst_int (Int.repr num_proc) tint) tint)
                                  (Ssequence
                                     (Scall None (Evar set_next (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                            ((Etempvar tprev tint) :: (Econst_int (Int.repr num_proc) tint) :: nil))
                                     (Scall None (Evar set_tail (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                            ((Etempvar tchan_index tint) :: (Etempvar tprev tint) :: nil)))
                                  (Ssequence
                                     (Sifthenelse (Ebinop One (Etempvar tprev tint) (Etempvar tnext tint) tint)
                                                  (Scall None (Evar set_next (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                                         ((Etempvar tprev tint) :: (Etempvar tnext tint) :: nil))
                                                  Sskip)
                                     (Scall None (Evar set_prev (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                            ((Etempvar tnext tint) :: (Etempvar tprev tint) :: nil))))))).

Definition f_queue_rmv := {|
                           fn_return := tvoid;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tchan_index, tint) :: (tproc_index, tint) :: nil);
                           fn_temps := ((tprev, tint) :: (tnext, tint) :: nil);
                           fn_body := queue_rmv_body
                         |}.



(** 
<<
      #define num_chan 64
      
      extern void thread_init(unsigned int);
      extern void tdq_init(unsigned int);
      
      void tdqueue_init(unsigned int mbi_adr)
      {
          unsigned int i;
          thread_init(mbi_adr);
          i = 0;
          while (i <= num_chan)
          {
              tdq_init(i);
              i++;
          }
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let ti: ident := 7.
Let tmbi_adr: ident := 8.

Local Open Scope Z_scope.


Definition tdqueue_init_while_condition : expr := (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr (num_chan + 1)) tint) tint).

Definition tdqueue_init_while_body : statement := 
  (Ssequence
     (Scall None (Evar tdq_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar ti tint) :: nil))
     (Sset ti
           (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint) tint))).

Definition tdqueue_init_body : statement := 
  (Ssequence
     (Scall None (Evar thread_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar tmbi_adr tint) :: nil))
     (Ssequence
        (Sset ti (Econst_int (Int.repr 0) tint))
        (Swhile tdqueue_init_while_condition tdqueue_init_while_body))).

Definition f_tdqueue_init := {|
                              fn_return := tvoid;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tmbi_adr, tint) :: nil);
                              fn_temps := ((ti, tint) :: nil);
                              fn_body := tdqueue_init_body
                            |}.