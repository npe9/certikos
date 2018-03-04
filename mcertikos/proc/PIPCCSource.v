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
      #define UCTXT_SIZE 17
      
      extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];
      
      unsigned int uctx_get(unsigned int proc_index, unsigned int ofs)
      {
          return UCTX_LOC[proc_index][ofs];
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index: ident := 1.
Let tofs: ident := 2.

Local Open Scope Z_scope.

Definition uctx_get_body : statement := 
  (Sreturn (Some (Ederef
                    (Ebinop Oadd
                            (Ederef
                               (Ebinop Oadd
                                       (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                       (Etempvar tproc_index tint) (tptr (tarray tint 17)))
                               (tarray tint 17)) (Etempvar tofs tint) (tptr tint))
                    tint))).

Definition f_uctx_get := {|
                          fn_return := tint;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tproc_index, tint) :: (tofs, tint) :: nil);
                          fn_temps := nil;
                          fn_body := uctx_get_body
                        |}.



(** 
<<
      #define num_proc 64
      #define UCTXT_SIZE 17
      
      extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];
      
      void uctx_set(unsigned int proc_index, unsigned int ofs, unsigned int val)
      {
          UCTX_LOC[proc_index][ofs] = val;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tval: ident := 3.

Local Open Scope Z_scope.

Definition uctx_set_body : statement := 
  (Sassign (Ederef (Ebinop Oadd (Ederef
                                   (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                           (Etempvar tproc_index tint) (tptr (tarray tint 17)))
                                   (tarray tint 17)) (Etempvar tofs tint) (tptr tint)) tint)
           (Etempvar tval tint)).

Definition f_uctx_set := {|
                          fn_return := tvoid;
                          fn_callconv := cc_default;
                          fn_vars := nil;
                          fn_params := ((tproc_index, tint) :: (tofs, tint) :: (tval, tint) :: nil);
                          fn_temps := nil;
                          fn_body := uctx_set_body
                        |}.



(** 
<<
      #define num_proc 64
      #define UCTXT_SIZE 17
      #define U_EIP 12
      
      extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];
      
      void uctx_set_eip(unsigned int proc_index, void * val)
      {
          UCTX_LOC[proc_index][U_EIP] = (int) val;
      }
>>
 *)

Definition uctx_set_eip_body : statement := 
  (Sassign (Ederef (Ebinop Oadd (Ederef
                                   (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                           (Etempvar tproc_index tint) (tptr (tarray tint 17)))
                                   (tarray tint 17)) (Econst_int (Int.repr U_EIP) tint) (tptr tint)) tint)
           (Ecast (Etempvar tval tint) tint)).

Definition f_uctx_set_eip := {|
                              fn_return := tvoid;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tproc_index, tint) :: (tval, tint) :: nil);
                              fn_temps := nil;
                              fn_body := uctx_set_eip_body
                            |}.



(** 
<<
      #define num_proc 64
      #define UCTXT_SIZE 17
      
      extern unsigned int UCTX_LOC[num_proc][UCTXT_SIZE];
      extern int get_curid(void);
      
      void save_uctx(int u0, int u1, int u2, int u3, int u4, int u5, int u6, int u7, int u8, int u9, int u10, int u11, int u12, int u13, int u14, int u15, int u16)
      {
          int curid;
          curid = get_curid();
          UCTX_LOC[curid][0] = u0;
          UCTX_LOC[curid][1] = u1;
          UCTX_LOC[curid][2] = u2;
          UCTX_LOC[curid][3] = u3;
          UCTX_LOC[curid][4] = u4;
          UCTX_LOC[curid][5] = u5;
          UCTX_LOC[curid][6] = u6;
          UCTX_LOC[curid][7] = u7;
          UCTX_LOC[curid][8] = u8;
          UCTX_LOC[curid][9] = u9;
          UCTX_LOC[curid][10] = u10;
          UCTX_LOC[curid][11] = u11;
          UCTX_LOC[curid][12] = u12;
          UCTX_LOC[curid][13] = u13;
          UCTX_LOC[curid][14] = u14;
          UCTX_LOC[curid][15] = u15;
          UCTX_LOC[curid][16] = u16;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tu0: ident := 1.
Let tu1: ident := 2.
Let tu2: ident := 3.
Let tu3: ident := 4.
Let tu4: ident := 5.
Let tu5: ident := 6.
Let tu6: ident := 7.
Let tu7: ident := 8.
Let tu8: ident := 9.
Let tu9: ident := 10.
Let tu10: ident := 11.
Let tu11: ident := 12.
Let tu12: ident := 13.
Let tu13: ident := 14.
Let tu14: ident := 15.
Let tu15: ident := 16.
Let tu16: ident := 17.
Let tcurid: ident := 18.

Local Open Scope Z_scope.

Definition save_uctx_body : statement := 
  (Ssequence
     (Scall (Some tcurid) (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
     (Ssequence
        (Sassign (Ederef (Ebinop Oadd (Ederef
                                         (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                 (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                         (tarray tint 17)) (Econst_int (Int.repr 0) tint) (tptr tint)) tint) (Etempvar tu0 tint))
        (Ssequence
           (Sassign (Ederef (Ebinop Oadd (Ederef
                                            (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                    (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                            (tarray tint 17)) (Econst_int (Int.repr 1) tint) (tptr tint)) tint) (Etempvar tu1 tint))
           (Ssequence
              (Sassign (Ederef (Ebinop Oadd (Ederef
                                               (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                       (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                               (tarray tint 17)) (Econst_int (Int.repr 2) tint) (tptr tint)) tint) (Etempvar tu2 tint))
              (Ssequence
                 (Sassign (Ederef (Ebinop Oadd (Ederef
                                                  (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                          (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                  (tarray tint 17)) (Econst_int (Int.repr 3) tint) (tptr tint)) tint) (Etempvar tu3 tint))
                 (Ssequence
                    (Sassign (Ederef (Ebinop Oadd (Ederef
                                                     (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                             (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                     (tarray tint 17)) (Econst_int (Int.repr 4) tint) (tptr tint)) tint) (Etempvar tu4 tint))
                    (Ssequence
                       (Sassign (Ederef (Ebinop Oadd (Ederef
                                                        (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                        (tarray tint 17)) (Econst_int (Int.repr 5) tint) (tptr tint)) tint) (Etempvar tu5 tint))
                       (Ssequence
                          (Sassign (Ederef (Ebinop Oadd (Ederef
                                                           (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                   (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                           (tarray tint 17)) (Econst_int (Int.repr 6) tint) (tptr tint)) tint) (Etempvar tu6 tint))
                          (Ssequence
                             (Sassign (Ederef (Ebinop Oadd (Ederef
                                                              (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                      (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                              (tarray tint 17)) (Econst_int (Int.repr 7) tint) (tptr tint)) tint) (Etempvar tu7 tint))
                             (Ssequence
                                (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                 (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                         (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                 (tarray tint 17)) (Econst_int (Int.repr 8) tint) (tptr tint)) tint) (Etempvar tu8 tint))
                                (Ssequence
                                   (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                    (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                            (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                    (tarray tint 17)) (Econst_int (Int.repr 9) tint) (tptr tint)) tint) (Etempvar tu9 tint))
                                   (Ssequence
                                      (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                       (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                               (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                       (tarray tint 17)) (Econst_int (Int.repr 10) tint) (tptr tint)) tint) (Etempvar tu10 tint))
                                      (Ssequence
                                         (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                          (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                                  (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                          (tarray tint 17)) (Econst_int (Int.repr 11) tint) (tptr tint)) tint) (Etempvar tu11 tint))
                                         (Ssequence
                                            (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                             (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                                     (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                             (tarray tint 17)) (Econst_int (Int.repr 12) tint) (tptr tint)) tint) (Etempvar tu12 tint))
                                            (Ssequence
                                               (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                                (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                                        (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                                (tarray tint 17)) (Econst_int (Int.repr 13) tint) (tptr tint)) tint) (Etempvar tu13 tint))
                                               (Ssequence
                                                  (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                                   (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                                           (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                                   (tarray tint 17)) (Econst_int (Int.repr 14) tint) (tptr tint)) tint) (Etempvar tu14 tint))
                                                  (Ssequence
                                                     (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                                      (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                                              (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                                      (tarray tint 17)) (Econst_int (Int.repr 15) tint) (tptr tint)) tint) (Etempvar tu15 tint))
                                                     (Sassign (Ederef (Ebinop Oadd (Ederef
                                                                                      (Ebinop Oadd (Evar UCTX_LOC (tarray (tarray tint 17) 64))
                                                                                              (Etempvar tcurid tint) (tptr (tarray tint 17)))
                                                                                      (tarray tint 17)) (Econst_int (Int.repr 16) tint) (tptr tint)) tint) (Etempvar tu16 tint))
  )))))))))))))))))
.

Definition f_save_uctx := {|
                           fn_return := tvoid;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tu0, tint) :: (tu1, tint) :: (tu2, tint) :: (tu3, tint) :: (tu4, tint) :: (tu5, tint) :: (tu6, tint) :: (tu7, tint) :: (tu8, tint) :: (tu9, tint) :: (tu10, tint) :: (tu11, tint) :: (tu12, tint) :: (tu13, tint) :: (tu14, tint) :: (tu15, tint) :: (tu16, tint) :: nil);
                           fn_temps := ((tcurid, tint) :: nil);
                           fn_body := save_uctx_body
                         |}.