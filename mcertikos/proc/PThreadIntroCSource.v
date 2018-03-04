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
      extern void pt_free(unsigned int);
      extern void tcb_init(unsigned int);
      
      void thread_free(unsigned int proc_index)
      {
          pt_free(proc_index);
          tcb_init(proc_index);
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index: ident := 1.

Local Open Scope Z_scope.

Definition thread_free_body : statement := 
  (Ssequence
     (Scall None (Evar pt_free (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar tproc_index tint) :: nil))
     (Scall None (Evar tcb_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar tproc_index tint) :: nil))).

Definition f_thread_free := {|
                             fn_return := tvoid;
                             fn_callconv := cc_default;
                             fn_vars := nil;
                             fn_params := ((tproc_index, tint) :: nil);
                             fn_temps := nil;
                             fn_body := thread_free_body
                           |}.



(** 
<<
      #define num_proc 64
      
      extern void sharedmem_init(unsigned int);
      extern void tcb_init(unsigned int);
      
      void thread_init(unsigned int mbi_adr)
      {
          unsigned int i;
          sharedmem_init(mbi_adr);
          i = 0;
          while (i < num_proc)
          {
              tcb_init(i);
              i++;
          }
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let ti: ident := 1.
Let tmbi_adr: ident := 2.

Local Open Scope Z_scope.

Definition thread_init_while_condition : expr := (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr num_proc) tint) tint).

Definition thread_init_while_body : statement := 
  (Ssequence
     (Scall None (Evar tcb_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar ti tint) :: nil))
     (Sset ti
           (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint) tint))).

Definition thread_init_body : statement := 
  (Ssequence
     (Scall None (Evar shared_mem_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar tmbi_adr tint) :: nil))
     (Ssequence
        (Sset ti (Econst_int (Int.repr 0) tint))
        (Swhile thread_init_while_condition thread_init_while_body))).

Definition f_thread_init := {|
                             fn_return := tvoid;
                             fn_callconv := cc_default; 
                             fn_vars := nil;
                             fn_params := ((tmbi_adr, tint) :: nil);
                             fn_temps := ((ti, tint) :: nil);
                             fn_body := thread_init_body
                           |}.