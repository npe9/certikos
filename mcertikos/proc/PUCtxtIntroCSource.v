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
      #define U_ES 8
      #define U_DS 9
      #define U_CS 13
      #define U_EFLAGS 14
      #define U_ESP 15
      #define U_SS 16
      #define kern_high 983040
      #define PgSize 4096
      
      extern unsigned int thread_spawn(void *, unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      extern void uctx_set(unsigned int, unsigned int, unsigned int);
      extern void uctx_set_eip(unsigned int, void * );
      extern void proc_start_user(void);
      extern void elf_load(void *, unsigned int);
      
      unsigned int proc_create(void * elf_addr, void * fun_adr, unsigned int quota)
      {
          unsigned int proc_index, id;
          id = get_curid();
          proc_index = thread_spawn((void * )proc_start_user, id, quota);
          elf_load(elf_addr, proc_index);
          uctx_set(proc_index, U_ES, 35);
          uctx_set(proc_index, U_DS, 35);
          uctx_set(proc_index, U_CS, 27);
          uctx_set(proc_index, U_SS, 35);
          uctx_set(proc_index, U_ESP, kern_high * PgSize);
          uctx_set(proc_index, U_EFLAGS, 512);
          uctx_set_eip(proc_index, fun_adr);
      
          return proc_index;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let telf_addr: ident:= 1.
Let tfun_addr: ident:= 2.
Let tproc_index: ident := 3.
Let tid: ident := 4.
Let tquota: ident := 5.

Local Open Scope Z_scope.

Definition proc_create_body : statement := 
  (Ssequence
     (Scall (Some tid)
            (Evar get_curid (Tfunction Tnil tint cc_default)) nil)            
     (Ssequence
        (Scall (Some tproc_index)
               (Evar thread_spawn (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil))) tint cc_default))
               ((Eaddrof (Evar proc_start_user (tptr tvoid)) (tptr tvoid)) :: 
                                                  (Etempvar tid tint) :: (Etempvar tquota tint) :: nil))
        (Ssequence
           (Scall None
                  (Evar elf_load (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar telf_addr (tptr tvoid)) :: (Etempvar tproc_index tint) :: nil))
           (Ssequence
              (Scall None
                     (Evar uctx_set (Tfunction
                                       (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
                     ((Etempvar tproc_index tint) :: (Econst_int (Int.repr 8) tint) ::
                                                  (Econst_int (Int.repr 35) tint) :: nil))
              (Ssequence
                 (Scall None
                        (Evar uctx_set (Tfunction
                                          (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                          tvoid cc_default))
                        ((Etempvar tproc_index tint) :: (Econst_int (Int.repr 9) tint) ::
                                                     (Econst_int (Int.repr 35) tint) :: nil))
                 (Ssequence
                    (Scall None
                           (Evar uctx_set (Tfunction
                                             (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                             tvoid cc_default))
                           ((Etempvar tproc_index tint) :: (Econst_int (Int.repr 13) tint) ::
                                                        (Econst_int (Int.repr 27) tint) :: nil))
                    (Ssequence
                       (Scall None
                              (Evar uctx_set (Tfunction
                                                (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                                tvoid cc_default))
                              ((Etempvar tproc_index tint) ::
                                                           (Econst_int (Int.repr 16) tint) ::
                                                           (Econst_int (Int.repr 35) tint) :: nil))
                       (Ssequence
                          (Scall None
                                 (Evar uctx_set (Tfunction
                                                   (Tcons tint
                                                          (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
                                 ((Etempvar tproc_index tint) ::
                                                              (Econst_int (Int.repr 15) tint) ::
                                                              (Ebinop Omul (Econst_int (Int.repr 983040) tint)
                                                                      (Econst_int (Int.repr 4096) tint) tint) :: nil))
                          (Ssequence
                             (Scall None
                                    (Evar uctx_set (Tfunction
                                                      (Tcons tint
                                                             (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
                                    ((Etempvar tproc_index tint) ::
                                                                 (Econst_int (Int.repr 14) tint) ::
                                                                 (Econst_int (Int.repr 512) tint) :: nil))
                             (Ssequence
                                (Scall None
                                       (Evar uctx_set_eip (Tfunction
                                                             (Tcons tint
                                                                    (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
                                       ((Etempvar tproc_index tint) ::
                                                                    (Etempvar tfun_addr (tptr tvoid)) :: nil))
                                (Sreturn (Some (Etempvar tproc_index tint))))))))))))).

Definition f_proc_create := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_vars := nil;
    fn_params := ((telf_addr, tptr tvoid) :: (tfun_addr, tptr tvoid) :: 
                                          (tquota, tint) :: nil);
    fn_temps := ((tproc_index, tint) :: (tid, tint) :: nil);
    fn_body := proc_create_body
  |}.