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
      
      extern unsigned int pt_new(unsigned int, unsigned int);
      extern void set_RA(unsigned int, void * );
      extern void set_SP(unsigned int, void * );
      
      extern void * STACK_LOC[num_proc][1024];

      unsigned int kctxt_new(void * entry, unsigned int id, unsigned int quota)
      {
          /* unsigned int proc_index;
          proc_index = pt_new(id, quota);
          set_SP(proc_index, STACK_LOC[proc_index][1023]);
          set_RA(proc_index, entry);
          return proc_index; */
          
          unsigned int proc_index;
          proc_index = pt_new(id, quota);
          if (proc_index == num_proc){
    	      return num_proc;
          }else{
    	      set_SP(proc_index, & STACK_LOC[proc_index][PgSize - 4]);
	      set_RA(proc_index, entry);
	      return proc_index;
          }
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tentry: ident := 1.
Let tproc_index: ident := 2.
Let tid: ident := 3.
Let tquota: ident := 4.

Local Open Scope Z_scope.

(* Definition kctxt_new_body : statement := 
  (Ssequence
     (Scall (Some tproc_index) (Evar pt_new (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall None (Evar set_SP (Tfunction (Tcons tint (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
               ((Etempvar tproc_index tint) :: (Ecast
                                                  (Ebinop Oadd
                                                          (Ecast
                                                             (Ebinop Oadd
                                                                     (Eaddrof (Evar STACK_LOC (tarray (tarray (tptr tvoid) 1024) 64)) (tarray (tarray (tptr tvoid) 1024) 64))
                                                                     (Etempvar tproc_index tint)
                                                                     (tptr (tarray (tptr tvoid) 1024))) (tptr (tptr tvoid)))
                                                          (Econst_int (Int.repr 1023) tint) (tptr (tptr tvoid)))
                                                  (tptr tvoid)) :: nil))
        (Ssequence
           (Scall None (Evar set_RA (Tfunction (Tcons tint (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
                  ((Etempvar tproc_index tint) :: (Etempvar tentry (tptr tvoid)) :: nil))
           (Sreturn (Some (Etempvar tproc_index tint)))))). *)

Definition kctxt_new_body : statement :=
(Ssequence
  (Scall (Some tproc_index) (Evar pt_new (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default)) 
                                                    (Etempvar tid tint :: Etempvar tquota tint :: nil))
  (Sifthenelse (Ebinop Oeq (Etempvar tproc_index tint)
                 (Econst_int (Int.repr 64) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 64) tint)))
    (Ssequence
      (Scall None
        (Evar set_SP (Tfunction (Tcons tint (Tcons (tptr tvoid) Tnil))
                        tvoid cc_default))
        ((Etempvar tproc_index tint) :: (Ecast
                                              (Ebinop Oadd
                                                          (Ecast
                                                             (Ebinop Oadd
                                                                     (Eaddrof (Evar STACK_LOC (tarray (tarray (tptr tvoid) 1024) 64)) (tarray (tarray (tptr tvoid) 1024) 64))
                                                                     (Etempvar tproc_index tint)
                                                                     (tptr (tarray (tptr tvoid) 1024))) (tptr (tptr tvoid)))
                                                          (Econst_int (Int.repr 1023) tint) (tptr (tptr tvoid)))
                                                  (tptr tvoid)) :: nil))
      (Ssequence
        (Scall None
          (Evar set_RA (Tfunction (Tcons tint (Tcons (tptr tvoid) Tnil))
                          tvoid cc_default))
          ((Etempvar tproc_index tint) :: (Etempvar tentry (tptr tvoid)) ::
           nil))
        (Sreturn (Some (Etempvar tproc_index tint))))))).


Definition f_kctxt_new := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tentry, tptr tvoid) :: (tid, tint) :: (tquota, tint) :: nil);
                           fn_temps := ((tproc_index, tint) :: nil);
                           fn_body := kctxt_new_body
                         |}.