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
      unsigned int get_nps()
      {
          return NPS_LOC;
      }
>>
 *)

Definition get_nps_body : statement :=
  Sreturn (Some (Evar NPS_LOC tint)).

Definition f_get_nps := {|
                         fn_return := tint;
                         fn_callconv := cc_default;
                         fn_params := nil;
                         fn_vars := nil;
                         fn_temps := nil;
                         fn_body := get_nps_body
                       |}.


(** 
<<
      void set_nps(unsigned int newnps)
      {
          NPS_LOC = newnps;
      }
>>
 *)

Let tnewnps: ident := 1 % positive.

Definition set_nps_body : statement := 
  Sassign (Evar NPS_LOC tint) (Etempvar tnewnps tint).

Definition f_set_nps := {|
                         fn_return := Tvoid;
                         fn_callconv := cc_default;
                         fn_params := ((tnewnps, tint) :: nil);
                         fn_vars := nil;
                         fn_temps := nil;
                         fn_body := set_nps_body
                       |}.



(** 
<<
      struct A {
          unsigned int isnorm;
          unsigned int allocated;
          unsigned int c;
      };

      extern struct A AT_LOC[maxpage];

      unsigned int is_norm (unsigned int is_norm_index)
      {
          unsigned int tisnorm;
          
          tisnorm = AT_LOC[is_norm_index].isnorm;
          if (tisnorm != 0)
          {
              if (tisnorm == 1)
                  tisnorm = 0;
              else
                  tisnorm = 1;
          }

          return tisnorm;
      }
>>
 *)

Let tisnorm: ident := 2 % positive.
Let tis_norm_index: ident := 3 % positive. (* parameter *)

Definition is_norm_body : statement := 
  (Ssequence
     (Sset tisnorm (Efield (Ederef
                              (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                      (Etempvar tis_norm_index tint) (tptr t_struct_A)) t_struct_A)
                           A_isnorm_ident tint)
     )
     (Ssequence
        (Sifthenelse 
           (Ebinop One (Etempvar tisnorm tint) (Econst_int (Int.repr 0) tint) tint)
           (Sifthenelse 
              (Ebinop Oeq (Etempvar tisnorm tint) (Econst_int (Int.repr 1) tint) tint)
              (Sset tisnorm (Econst_int (Int.repr 0) tint))
              (Sset tisnorm (Econst_int (Int.repr 1) tint))
           )
           Sskip
        )
        (Sreturn (Some (Etempvar tisnorm tint)))))
.

Definition f_is_norm := {|
                         fn_return := tint;
                         fn_callconv := cc_default;
                         fn_params := ((tis_norm_index, tint) :: nil);
                         fn_vars := nil;
                         fn_temps := ((tisnorm, tint) :: nil);
                         fn_body := is_norm_body
                       |}.


(** 
<<
      struct A {
          unsigned int isnorm;
          unsigned int allocated;
          unsigned int c;
      };
    
      extern struct A AT_LOC[maxpage];

      void set_norm (unsigned int set_norm_index, unsigned int norm_val)
      {   
          AT_LOC[set_norm_index].isnorm = norm_val;
          AT_LOC[set_norm_index].allocated = 0;
          AT_LOC[set_norm_index].c = 0;
      }
>>
 *)

Let tset_norm_index: ident := 4 % positive.
Let tnorm_val: ident := 5 % positive.

Definition set_norm_body: statement := 
  (Ssequence
     (Sassign (Efield (Ederef (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                      (Etempvar tset_norm_index tint) (tptr t_struct_A)) t_struct_A) A_isnorm_ident tint) (Etempvar tnorm_val tint))
  (Ssequence
     (Sassign (Efield (Ederef (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                      (Etempvar tset_norm_index tint) (tptr t_struct_A)) t_struct_A) A_allocated_ident tint) (Econst_int (Int.repr 0) tint))
     (Sassign (Efield (Ederef (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                      (Etempvar tset_norm_index tint) (tptr t_struct_A)) t_struct_A) A_c_ident tint) (Econst_int (Int.repr 0) tint))
  ))
.

Definition f_set_norm := {|
                          fn_return := Tvoid;
                          fn_callconv := cc_default;
                          fn_params := ((tset_norm_index, tint) :: (tnorm_val, tint) :: nil);
                          fn_vars := nil;
                          fn_temps := nil;
                          fn_body := set_norm_body
                        |}.


(** 
<<
      struct A {
          unsigned int isnorm;
          unsigned int allocated;
          unsigned int c;
      };
      
      extern struct A AT_LOC[maxpage];
      
      unsigned int at_get (unsigned int at_get_index)
      {
          unsigned int allocated;
          
          allocated = AT_LOC[at_get_index].allocated;
          if (allocated != 0)
              allocated = 1;
          
          return allocated;
      } 
>>
 *)

Let tallocated: ident := 6 % positive.
Let tat_get_index: ident := 7 % positive. (* parameter *)

Definition at_get_body : statement := 
  (Ssequence
     (Sset tallocated (Efield (Ederef (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                              (Etempvar tat_get_index tint) (tptr t_struct_A)) t_struct_A) A_allocated_ident tint))
     (Ssequence
        (Sifthenelse 
           (Ebinop One (Etempvar tallocated tint) (Econst_int (Int.repr 0) tint) tint)
           (Sset tallocated (Econst_int (Int.repr 1) tint))
           Sskip)
        (Sreturn (Some (Etempvar tallocated tint)))))
.

Definition f_at_get := {|
                        fn_return := tint;
                        fn_callconv := cc_default;
                        fn_params := ((tat_get_index, tint) :: nil);
                        fn_vars := nil;
                        fn_temps := ((tallocated, tint) :: nil);
                        fn_body := at_get_body
                      |}.


(** 
<<
      struct A {
          int isnorm;
          int allocated;
          unsigned int c;
      };
      
      extern struct A AT_LOC[1048576];
      
      void at_set (unsigned int at_set_index, unsigned int allocated_val)
      {
          AT_LOC[at_set_index].allocated = allocated_val;
      }
>>
 *)

Let tat_set_index: ident := 8 % positive.
Let tallocated_val: ident := 9 % positive.

Definition at_set_body: statement := 
  (Sassign (Efield (Ederef (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                   (Etempvar tat_set_index tint) (tptr t_struct_A)) t_struct_A) A_allocated_ident tint) (Etempvar tallocated_val tint))
.

Definition f_at_set := {|
                        fn_return := Tvoid;
                        fn_callconv := cc_default;
                        fn_params := ((tat_set_index, tint) :: (tallocated_val, tint) :: nil);
                        fn_vars := nil;
                        fn_temps := nil;
                        fn_body := at_set_body
                      |}.



(** 
<<
      struct A {
          unsigned int isnorm;
          unsigned int allocated;
          unsigned int c;
      };
      
      extern struct A AT_LOC[maxpage];
      
      unsigned int at_get_c (unsigned int at_get_c_index)
      {
          unsigned int c;
          
          c = AT_LOC[at_get_c_index].c;
          
          return c;
      } 
>>
 *)

Let tc: ident := 10 % positive.
Let tat_get_c_index: ident := 11 % positive. (* parameter *)

Definition at_get_c_body : statement := 
  (Ssequence
     (Sset tc (Efield (Ederef (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                              (Etempvar tat_get_c_index tint) (tptr t_struct_A)) t_struct_A) A_c_ident tint))
     (Sreturn (Some (Etempvar tc tint))))
.

Definition f_at_get_c := {|
                        fn_return := tint;
                        fn_callconv := cc_default;
                        fn_params := ((tat_get_c_index, tint) :: nil);
                        fn_vars := nil;
                        fn_temps := ((tc, tint) :: nil);
                        fn_body := at_get_c_body
                      |}.


(** 
<<
      struct A {
          int isnorm;
          int allocated;
          unsigned int c;
      };
      
      extern struct A AT_LOC[1048576];
      
      void at_set_c (unsigned int at_set_c_index, unsigned int c_val)
      {
          AT_LOC[at_set_c_index].c = c_val;
      }
>>
 *)

Let tat_set_c_index: ident := 12 % positive.
Let tc_val: ident := 13 % positive.

Definition at_set_c_body: statement := 
  (Sassign (Efield (Ederef (Ebinop Oadd (Evar AT_LOC (tarray t_struct_A maxpage))
                                   (Etempvar tat_set_c_index tint) (tptr t_struct_A)) t_struct_A) A_c_ident tint) (Etempvar tc_val tint))
.

Definition f_at_set_c := {|
                        fn_return := Tvoid;
                        fn_callconv := cc_default;
                        fn_params := ((tat_set_c_index, tint) :: (tc_val, tint) :: nil);
                        fn_vars := nil;
                        fn_temps := nil;
                        fn_body := at_set_c_body
                      |}.
