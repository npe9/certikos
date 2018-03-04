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
      #define READY 0
      #define num_chan 64
      
      extern unsigned int kctxt_new(void *, unsigned int, unsigned int);
      extern void set_state(unsigned int, unsigned int);
      extern void enqueue(unsigned int, unsigned int);
      
      unsigned int thread_spawn(void * entry, unsigned int id, unsigned int quota)
      {
          unsigned int i;
          i = kctxt_new(entry, id, quota);
          set_state(i, READY);
          enqueue(num_chan, i);
          return i;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tentry: ident := 1.
Let ti: ident := 2.
Let tid: ident := 3.
Let tquota: ident := 4.

Local Open Scope Z_scope.

Definition thread_spawn_body : statement := 
  (Ssequence
     (Scall (Some ti) (Evar kctxt_new 
            (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil))) tint cc_default))
            ((Etempvar tentry (tptr tvoid)) :: (Etempvar tid tint) :: (Etempvar tquota tint) :: nil))
     (Ssequence
        (Scall None (Evar set_state (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
               ((Etempvar ti tint) :: (Econst_int (Int.repr TSTATE_READY) tint) :: nil))
        (Ssequence
           (Scall None (Evar enqueue (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                  ((Econst_int (Int.repr num_chan) tint) :: (Etempvar ti tint) :: nil))
           (Sreturn (Some (Etempvar ti tint)))))).

Definition f_thread_spawn := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_vars := nil;
    fn_params := ((tentry, tptr tvoid) :: (tid, tint) :: (tquota, tint) :: nil);
    fn_temps := ((ti, tint) :: nil);
    fn_body := thread_spawn_body
  |}.



(** 
<<
      #define TSTATE_RUN 1
      
      extern void tdqueue_init(unsigned int);
      extern void set_curid(unsigned int);
      extern void set_state(unsigned int, unsigned int);
            
      void sched_init(unsigned int mbi_adr)
      {
          tdqueue_init(mbi_adr);
          set_curid(0);
          set_state(0, TSTATE_RUN);
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tmbi_adr: ident := 1.

Local Open Scope Z_scope.

Definition sched_init_body : statement := 
  (Ssequence
     (Scall None (Evar tdqueue_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar tmbi_adr tint) :: nil))
     (Ssequence
        (Scall None (Evar set_curid (Tfunction (Tcons tint Tnil) tvoid cc_default))
               ((Econst_int (Int.repr 0) tint) :: nil))
        (Scall None (Evar set_state (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
               ((Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr TSTATE_RUN) tint) :: nil)))).

Definition f_sched_init := {|
                            fn_return := tvoid;
                            fn_callconv := cc_default;
                            fn_vars := nil;
                            fn_params := ((tmbi_adr, tint) :: nil);
                            fn_temps := nil;
                            fn_body := sched_init_body
                          |}.



(** 
<<
      #define TSTATE_DEAD 3
      
      extern void set_state(unsigned int, unsigned int);
      extern void queue_rmv(unsigned int, unsigned int);
      extern void thread_free(unsigned int);
      
      void thread_kill(unsigned int proc_index, unsigned int chan_index)
      {
          set_state(proc_index, TSTATE_DEAD);
          queue_rmv(chan_index, proc_index);
          thread_free(proc_index);
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index: ident := 1.
Let tchan_index: ident := 2.

Local Open Scope Z_scope.

Definition thread_kill_body : statement := 
  (Ssequence
     (Scall None (Evar set_state (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
            ((Etempvar tproc_index tint) :: (Econst_int (Int.repr TSTATE_DEAD) tint) :: nil))
     (Ssequence
        (Scall None (Evar queue_rmv (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
               ((Etempvar tchan_index tint) :: (Etempvar tproc_index tint) :: nil))
        (Scall None (Evar thread_free (Tfunction (Tcons tint Tnil) tvoid cc_default))
               ((Etempvar tproc_index tint) :: nil)))).

Definition f_thread_kill := {|
                             fn_return := tvoid;
                             fn_callconv := cc_default;
                             fn_vars := nil;
                             fn_params := ((tproc_index, tint) :: (tchan_index, tint) :: nil);
                             fn_temps := nil;
                             fn_body := thread_kill_body
                           |}.



(** 
<<
      #define TSTATE_READY 0
      #define num_chan 64
      #define num_proc 64
      
      extern unsigned int dequeue(unsigned int);
      extern void set_state(unsigned int, unsigned int);
      extern void enqueue(unsigned int, unsigned int);
      
      void thread_wakeup(unsigned int chan_index)
      {
          unsigned int proc_index;
          proc_index = dequeue(chan_index);
          if(proc_index != num_proc)
          {
              set_state(proc_index, TSTATE_READY);
              enqueue(num_chan, proc_index);
          }
      }
>>
 *)

Definition thread_wakeup_body : statement := 
  (Ssequence
     (Scall (Some tproc_index) (Evar dequeue (Tfunction (Tcons tint Tnil) tint cc_default))
            ((Etempvar tchan_index tint) :: nil))
     (Sifthenelse (Ebinop One (Etempvar tproc_index tint) (Econst_int (Int.repr num_proc) tint) tint)
                  (Ssequence
                     (Scall None (Evar set_state (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                            ((Etempvar tproc_index tint) :: (Econst_int (Int.repr TSTATE_READY) tint) :: nil))
                     (Scall None (Evar enqueue (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                            ((Econst_int (Int.repr num_chan) tint) :: (Etempvar tproc_index tint) :: nil)))
                  Sskip)).

Definition f_thread_wakeup := {|
                               fn_return := tvoid;
                               fn_callconv := cc_default;
                               fn_vars := nil;
                               fn_params := ((tchan_index, tint) :: nil);
                               fn_temps := ((tproc_index, tint) :: nil);
                               fn_body := thread_wakeup_body
                             |}.