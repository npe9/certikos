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
      #define PgSize 4096
      #define PT_PERM_PTU 7

      extern unsigned int get_curid(void);
      extern unsigned int pt_read(unsigned int, unsigned int);
      extern void pt_resv(unsigned int, unsigned int, unsigned int);

      unsigned int la2pa_resv(unsigned int va)
      {
          unsigned int cur_pid;
          unsigned int pa;
          cur_pid = get_curid();
          pa = pt_read(cur_pid, va);

          if (pa == 0) {
              pt_resv(cur_pid, va, PT_PERM_PTU);
              pa = pt_read(cur_pid, va);
          }

          pa = pa / PgSize * PgSize + (va % PgSize);

          return pa;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tva: ident := 1.
Let tcur_pid: ident := 2.
Let tpa: ident := 3.

Local Open Scope Z_scope.

Definition la2pa_resv_body : statement := 
  (Ssequence
     (Scall (Some tcur_pid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall (Some tpa)
               (Evar pt_read (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
               ((Etempvar tcur_pid tint) :: (Etempvar tva tint) :: nil))
        (Ssequence
           (Sifthenelse (Ebinop Oeq (Etempvar tpa tint)
                                (Econst_int (Int.repr 0) tint) tint)
                        (Ssequence
                           (Scall None
                                  (Evar pt_resv (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
                                  ((Etempvar tcur_pid tint) :: (Etempvar tva tint) ::
                                                            (Econst_int (Int.repr 7) tint) :: nil))
                           (Scall (Some tpa)
                                  (Evar pt_read (Tfunction (Tcons tint (Tcons tint Tnil))
                                                           tint cc_default))
                                  ((Etempvar tcur_pid tint) :: (Etempvar tva tint) :: nil)))
                        Sskip)
           (Ssequence
              (Sset tpa
                    (Ebinop Oadd
                            (Ebinop Omul
                                    (Ebinop Odiv (Etempvar tpa tint)
                                            (Econst_int (Int.repr PgSize) tint) tint)
                                    (Econst_int (Int.repr PgSize) tint) tint)
                            (Ebinop Omod (Etempvar tva tint)
                                    (Econst_int (Int.repr PgSize) tint) tint) tint))
              (Sreturn (Some (Etempvar tpa tint))))))).

Definition f_la2pa_resv := {|
                            fn_return := tint;
                            fn_callconv := cc_default;
                            fn_vars := nil;
                            fn_params := ((tva, tint) :: nil);
                            fn_temps := ((tcur_pid, tint) :: (tpa, tint) :: nil);
                            fn_body := la2pa_resv_body
                          |}.



(** 
<<
      #define U_EAX 7
      
      extern unsigned int uctx_get(unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      unsigned int uctx_arg1()
      {
          unsigned int curid;
          unsigned int arg;
          curid = get_curid();
          arg = uctx_get(curid, U_EAX);
          return arg;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tcurid: ident := 1.
Let targ: ident := 2.

Local Open Scope Z_scope.

Definition uctx_arg1_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall (Some targ)
               (Evar uctx_get (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
               ((Etempvar tcurid tint) :: (Econst_int (Int.repr 7) tint) :: nil))
        (Sreturn (Some (Etempvar targ tint))))).

Definition f_uctx_arg1 := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := nil;
                           fn_temps := ((tcurid, tint) :: (targ, tint) :: nil);
                           fn_body := uctx_arg1_body
                         |}.



(** 
<<
      #define U_EBX 4
      
      extern unsigned int uctx_get(unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      unsigned int uctx_arg2()
      {
          unsigned int curid;
          unsigned int arg;
          curid = get_curid();
          arg = uctx_get(curid, U_EBX);
          return arg;
      }
>>
 *)

Definition uctx_arg2_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall (Some targ)
               (Evar uctx_get (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
               ((Etempvar tcurid tint) :: (Econst_int (Int.repr 4) tint) :: nil))
        (Sreturn (Some (Etempvar targ tint))))).

Definition f_uctx_arg2 := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := nil;
                           fn_temps := ((tcurid, tint) :: (targ, tint) :: nil);
                           fn_body := uctx_arg2_body
                         |}.



(** 
<<
      #define U_ECX 6
      
      extern unsigned int uctx_get(unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      unsigned int uctx_arg3()
      {
          unsigned int curid;
          unsigned int arg;
          curid = get_curid();
          arg = uctx_get(curid, U_ECX);
          return arg;
      }
>>
 *)

Definition uctx_arg3_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall (Some targ)
               (Evar uctx_get (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
               ((Etempvar tcurid tint) :: (Econst_int (Int.repr 6) tint) :: nil))
        (Sreturn (Some (Etempvar targ tint))))).

Definition f_uctx_arg3 := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := nil;
                           fn_temps := ((tcurid, tint) :: (targ, tint) :: nil);
                           fn_body := uctx_arg3_body
                         |}.



(** 
<<
      #define U_EDX 5
      
      extern unsigned int uctx_get(unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      unsigned int uctx_arg4()
      {
          unsigned int curid;
          unsigned int arg;
          curid = get_curid();
          arg = uctx_get(curid, U_EDX);
          return arg;
      }
>>
 *)

Definition uctx_arg4_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall (Some targ)
               (Evar uctx_get (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
               ((Etempvar tcurid tint) :: (Econst_int (Int.repr 5) tint) :: nil))
        (Sreturn (Some (Etempvar targ tint))))).

Definition f_uctx_arg4 := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := nil;
                           fn_temps := ((tcurid, tint) :: (targ, tint) :: nil);
                           fn_body := uctx_arg4_body
                         |}.



(** 
<<
      #define U_ESI 1
      
      extern unsigned int uctx_get(unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      unsigned int uctx_arg5()
      {
          unsigned int curid;
          unsigned int arg;
          curid = get_curid();
          arg = uctx_get(curid, U_ESI);
          return arg;
      }
>>
 *)

Definition uctx_arg5_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall (Some targ)
               (Evar uctx_get (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
               ((Etempvar tcurid tint) :: (Econst_int (Int.repr 1) tint) :: nil))
        (Sreturn (Some (Etempvar targ tint))))).

Definition f_uctx_arg5 := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := nil;
                           fn_temps := ((tcurid, tint) :: (targ, tint) :: nil);
                           fn_body := uctx_arg5_body
                         |}.

(** 
<<
#define U_EDI 0
      
      extern unsigned int uctx_get(unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      unsigned int uctx_arg6()
      {
          unsigned int curid;
          unsigned int arg;
          curid = get_curid();
          arg = uctx_get(curid, U_EDI);
          return arg;
      }
>>
 *)

Definition uctx_arg6_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Scall (Some targ)
               (Evar uctx_get (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
               ((Etempvar tcurid tint) :: (Econst_int (Int.repr 0) tint) :: nil))
        (Sreturn (Some (Etempvar targ tint))))).

Definition f_uctx_arg6 := {|
                           fn_return := tint;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := nil;
                           fn_temps := ((tcurid, tint) :: (targ, tint) :: nil);
                           fn_body := uctx_arg6_body
                         |}.



(** 
<<
      #define U_EAX 7
      
      extern void uctx_set(unsigned int, unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      void uctx_set_errno(unsigned int errno)
      {
          unsigned int curid;
          curid = get_curid();
          uctx_set(curid, U_EAX, errno);
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let terrno: ident := 3.

Local Open Scope Z_scope.

Definition uctx_set_errno_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Scall None
            (Evar uctx_set (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
            ((Etempvar tcurid tint) :: (Econst_int (Int.repr 7) tint) ::
                                    (Etempvar terrno tint) :: nil))).

Definition f_uctx_set_errno := {|
                                fn_return := tvoid;
                                fn_callconv := cc_default;
                                fn_vars := nil;
                                fn_params := ((terrno, tint) :: nil);
                                fn_temps := ((tcurid, tint) :: nil);
                                fn_body := uctx_set_errno_body
                              |}.



(** 
<<
      #define U_EBX 4
      
      extern void uctx_set(unsigned int, unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      void uctx_set_retval1(unsigned int retval)
      {
          unsigned int curid;
          curid = get_curid();
          uctx_set(curid, U_EBX, retval);
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tretval: ident := 4.

Local Open Scope Z_scope.

Definition uctx_set_retval1_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Scall None
            (Evar uctx_set (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
            ((Etempvar tcurid tint) :: (Econst_int (Int.repr 4) tint) ::
                                    (Etempvar tretval tint) :: nil))).

Definition f_uctx_set_retval1 := {|
                                  fn_return := tvoid;
                                  fn_callconv := cc_default;
                                  fn_vars := nil;
                                  fn_params := ((tretval, tint) :: nil);
                                  fn_temps := ((tcurid, tint) :: nil);
                                  fn_body := uctx_set_retval1_body
                                |}.

(** 
<<
      #define U_ECX 6
      
      extern void uctx_set(unsigned int, unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      void uctx_set_retval2(unsigned int retval)
      {
          unsigned int curid;
          curid = get_curid();
          uctx_set(curid, U_ECX, retval);
      }
>>
 *)

Definition uctx_set_retval2_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Scall None
            (Evar uctx_set (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
            ((Etempvar tcurid tint) :: (Econst_int (Int.repr 6) tint) ::
                                    (Etempvar tretval tint) :: nil))).

Definition f_uctx_set_retval2 := {|
                                  fn_return := tvoid;
                                  fn_callconv := cc_default;
                                  fn_vars := nil;
                                  fn_params := ((tretval, tint) :: nil);
                                  fn_temps := ((tcurid, tint) :: nil);
                                  fn_body := uctx_set_retval2_body
                                |}.

(** 
<<
      #define U_EDX 5
      
      extern void uctx_set(unsigned int, unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      void uctx_set_retval3(unsigned int retval)
      {
          unsigned int curid;
          curid = get_curid();
          uctx_set(curid, U_EDX, retval);
      }
>>
 *)

Definition uctx_set_retval3_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Scall None
            (Evar uctx_set (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
            ((Etempvar tcurid tint) :: (Econst_int (Int.repr 5) tint) ::
                                    (Etempvar tretval tint) :: nil))).

Definition f_uctx_set_retval3 := {|
                                  fn_return := tvoid;
                                  fn_callconv := cc_default;
                                  fn_vars := nil;
                                  fn_params := ((tretval, tint) :: nil);
                                  fn_temps := ((tcurid, tint) :: nil);
                                  fn_body := uctx_set_retval3_body
                                |}.

(** 
<<
      #define U_ESI 1
      
      extern void uctx_set(unsigned int, unsigned int, unsigned int);
      extern unsigned int get_curid(void);
      
      void uctx_set_retval1(unsigned int retval)
      {
          unsigned int curid;
          curid = get_curid();
          uctx_set(curid, U_ESI, retval);
      }
>>
 *)

Definition uctx_set_retval4_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Scall None
            (Evar uctx_set (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
            ((Etempvar tcurid tint) :: (Econst_int (Int.repr 1) tint) ::
                                    (Etempvar tretval tint) :: nil))).

Definition f_uctx_set_retval4 := {|
                                  fn_return := tvoid;
                                  fn_callconv := cc_default;
                                  fn_vars := nil;
                                  fn_params := ((tretval, tint) :: nil);
                                  fn_temps := ((tcurid, tint) :: nil);
                                  fn_body := uctx_set_retval4_body
                                |}.
