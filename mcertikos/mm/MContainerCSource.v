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
      #define NUM_PROC 64

      extern void set_cr3 (char ** );

      extern char * PTPool_LOC[NUM_PROC][1024];

      void set_pt(unsigned int index)
      {
          set_cr3(PTPool_LOC[index]);
      }
>>
 *)

Let tsetpt_index: ident := 1 % positive.

Definition set_pt_body : statement := 
  (Scall None
  (Evar set_cr3 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
  ((Ederef
     (Ebinop Oadd (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
       (Etempvar tsetpt_index tint) (tptr (tarray (tptr tchar) 1024)))
     (tarray (tptr tchar) 1024)) :: nil))
.

Definition f_set_pt := {|
                        fn_return := Tvoid;
                        fn_callconv := cc_default;
                        fn_vars := nil;
                        fn_params := ((tsetpt_index, tint) :: nil);
                        fn_temps := nil;
                        fn_body := set_pt_body
                      |}.



(**
<<
      #define NUM_PROC 64

      extern char * PTPool_LOC[NUM_PROC][1024];

      unsigned int get_PDE(unsigned int proc_index, unsigned int pde_index)
      {
          unsigned int pde;
          pde = (unsigned int)PTPool_LOC[proc_index][pde_index] / 4096;
          return pde;
      }
>>
 *)

Let tproc_index: ident := 1 % positive.
Let tpde_index: ident := 2 % positive.
Let tpde: ident := 3 % positive.


Definition get_PDE_body : statement := 
  (Ssequence
     (Sset tpde
           (Ebinop Odiv
                   (Ecast
                      (Ederef
                         (Ebinop Oadd
                                 (Ederef
                                    (Ebinop Oadd
                                            (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
                                            (Etempvar tproc_index tint)
                                            (tptr (tarray (tptr tchar) 1024)))
                                    (tarray (tptr tchar) 1024)) (Etempvar tpde_index tint)
                                 (tptr (tptr tchar))) (tptr tchar)) tint)
                   (Econst_int (Int.repr 4096) tint) tint))
     (Sreturn (Some (Etempvar tpde tint))))
.

Definition f_get_PDE := {|
                         fn_return := tint;
                         fn_callconv := cc_default;
                         fn_params := ((tproc_index, tint) :: (tpde_index, tint) :: nil);
                         fn_vars := nil;
                         fn_temps := ((tpde, tint) :: nil);
                         fn_body := get_PDE_body
                       |}.



(** 
<<
     #define NUM_PROC 64
     #define PT_PERM_PTU 7

     extern char * PTPool_LOC[NUM_PROC][1024];
     extern unsigned int IDPMap_LOC[1024][1024];

     void set_PDE(unsigned int proc_index, unsigned int pde_index)
     {
         PTPool_LOC[proc_index][pde_index] = ((char * )(IDPMap_LOC[pde_index])) + PT_PERM_PTU;
     }
>>
 *)

Definition set_pde_body: statement :=
  (Sassign
  (Ederef
    (Ebinop Oadd
      (Ederef
        (Ebinop Oadd
          (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
          (Etempvar tproc_index tint) (tptr (tarray (tptr tchar) 1024)))
        (tarray (tptr tchar) 1024)) (Etempvar tpde_index tint)
      (tptr (tptr tchar))) (tptr tchar))
  (Ebinop Oadd
    (Ecast
      (Ederef
        (Ebinop Oadd (Evar IDPMap_LOC (tarray (tarray tint 1024) 1024))
          (Etempvar tpde_index tint) (tptr (tarray tint 1024)))
        (tarray tint 1024)) (tptr tchar)) (Econst_int (Int.repr 7) tint)
    (tptr tchar))).

Definition f_set_pde := {|
                         fn_return := Tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tpde_index, tint) :: nil);
                         fn_temps := nil;
                         fn_body := set_pde_body
                       |}.


(** 
<<
     #define NUM_PROC 64
     #define PT_PERM_UP 0

     extern char * PTPool_LOC[NUM_PROC][1024];

     void rmv_PDE(unsigned int proc_index, unsigned int pde_index)
     {
         PTPool_LOC[proc_index][pde_index] = (char * )PT_PERM_UP;
     }
>>
 *)

Definition rmv_pde_body: statement :=
  (Sassign
  (Ederef
    (Ebinop Oadd
      (Ederef
        (Ebinop Oadd
          (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
          (Etempvar tproc_index tint) (tptr (tarray (tptr tchar) 1024)))
        (tarray (tptr tchar) 1024)) (Etempvar tpde_index tint)
      (tptr (tptr tchar))) (tptr tchar))
  (Ecast (Econst_int (Int.repr 0) tint) (tptr tchar))).

Definition f_rmv_pde := {|
                         fn_return := Tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tpde_index, tint) :: nil);
                         fn_temps := nil;
                         fn_body := rmv_pde_body
                       |}.



(** 
<<
     #define NUM_PROC 64
     #define PT_PERM_PTU 7

     extern char * PTPool_LOC[NUM_PROC][1024];

     void set_PDEU(unsigned int proc_index, unsigned int pde_index, unsigned int pi)
     {
         PTPool_LOC[proc_index][pde_index] = (char * )(pi * 4096 + PT_PERM_PTU);
     }
>>
 *)

Let tpi: ident := 4 % positive.

Definition set_pdeu_body: statement :=
  (Sassign
  (Ederef
    (Ebinop Oadd
      (Ederef
        (Ebinop Oadd
          (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
          (Etempvar tproc_index tint) (tptr (tarray (tptr tchar) 1024)))
        (tarray (tptr tchar) 1024)) (Etempvar tpde_index tint)
      (tptr (tptr tchar))) (tptr tchar))
  (Ecast
    (Ebinop Oadd
      (Ebinop Omul (Etempvar tpi tint) (Econst_int (Int.repr 4096) tint)
        tint) (Econst_int (Int.repr 7) tint) tint) (tptr tchar))).

Definition f_set_pdeu := {|
                         fn_return := Tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tpde_index, tint) :: (tpi, tint) :: nil);
                         fn_temps := nil;
                         fn_body := set_pdeu_body
                       |}.



(** 
<<
     #define NUM_PROC 64
     #define PT_PERM_PTU 7

     extern char * PTPool_LOC[NUM_PROC][1024];
     extern unsigned int fload(unsigned int);

     unsigned int get_PTE(unsigned int proc_index, unsigned int pde_index, unsigned int vadr)
     {
         unsigned int pte;
         unsigned int offset;
         offset = ((unsigned int)PTPool_LOC[proc_index][pde_index] - PT_PERM_PTU) / 4096;
         pte = fload(offset * 1024 + vadr);
         return pte;
     }
>>
 *)

Let tpte: ident := 5 % positive.
Let toffset: ident := 6 % positive.
Let tvadr: ident := 7 % positive.

Definition get_pte_body: statement :=
  (Ssequence
  (Sset toffset
    (Ebinop Odiv
      (Ebinop Osub
        (Ecast
          (Ederef
            (Ebinop Oadd
              (Ederef
                (Ebinop Oadd
                  (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
                  (Etempvar tproc_index tint)
                  (tptr (tarray (tptr tchar) 1024)))
                (tarray (tptr tchar) 1024)) (Etempvar tpde_index tint)
              (tptr (tptr tchar))) (tptr tchar)) tint)
        (Econst_int (Int.repr 7) tint) tint)
      (Econst_int (Int.repr 4096) tint) tint))
  (Ssequence
    (Ssequence
      (Scall (Some 13%positive)
        (Evar fload (Tfunction (Tcons tint Tnil) tint cc_default))
        ((Ebinop Oadd
           (Ebinop Omul (Etempvar toffset tint)
             (Econst_int (Int.repr 1024) tint) tint) (Etempvar tvadr tint)
           tint) :: nil))
      (Sset tpte (Etempvar 13%positive tint)))
      (Sreturn (Some (Etempvar tpte tint))))).

Definition f_get_pte := {|
                         fn_return := tint;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tpde_index, tint) :: (tvadr, tint) :: nil);
                         fn_temps := (toffset, tint) :: (tpte, tint) :: (13%positive, tint) :: nil;
                         fn_body := get_pte_body
                       |}.



(** 
<<
     #define NUM_PROC 64
     #define PT_PERM_PTU 7

     extern char * PTPool_LOC[NUM_PROC][1024];
     extern void fstore(unsigned int, unsigned int);

     void set_PTE(unsigned int proc_index, unsigned int pde_index, unsigned int vadr, unsigned int padr, unsigned int perm)
     {
         unsigned int offset;
         offset = ((unsigned int)PTPool_LOC[proc_index][pde_index] - PT_PERM_PTU) / 4096;
         fstore(offset * 1024 + vadr, padr * 4096 + perm);
     }
>>
 *)

Let tpadr: ident := 8 % positive.
Let tperm: ident := 9 % positive.

Definition set_pte_body: statement :=
  (Ssequence
  (Sset toffset
    (Ebinop Odiv
      (Ebinop Osub
        (Ecast
          (Ederef
            (Ebinop Oadd
              (Ederef
                (Ebinop Oadd
                  (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
                  (Etempvar tproc_index tint)
                  (tptr (tarray (tptr tchar) 1024)))
                (tarray (tptr tchar) 1024)) (Etempvar tpde_index tint)
              (tptr (tptr tchar))) (tptr tchar)) tint)
        (Econst_int (Int.repr 7) tint) tint)
      (Econst_int (Int.repr 4096) tint) tint))
  (Scall None
    (Evar fstore (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
    ((Ebinop Oadd
       (Ebinop Omul (Etempvar toffset tint)
         (Econst_int (Int.repr 1024) tint) tint) (Etempvar tvadr tint)
       tint) ::
     (Ebinop Oadd
       (Ebinop Omul (Etempvar tpadr tint) (Econst_int (Int.repr 4096) tint)
         tint) (Etempvar tperm tint) tint) :: nil))).

Definition f_set_pte := {|
                         fn_return := Tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tpde_index, tint) :: (tvadr, tint) :: (tpadr, tint) :: (tperm, tint) :: nil);
                         fn_temps := (toffset, tint) :: nil;
                         fn_body := set_pte_body
                       |}.


(** 
<<
     #define NUM_PROC 64
     #define PT_PERM_PTU 7

     extern char * PTPool_LOC[NUM_PROC][1024];
     extern void fstore(unsigned int, unsigned int);

     void rmv_PTE(unsigned int proc_index, unsigned int pde_index, unsigned int vadr)
     {
         unsigned int offset;
         offset = ((unsigned int)PTPool_LOC[proc_index][pde_index] - PT_PERM_PTU) / 4096;
         fstore(offset * 1024 + vadr, 0);
     }
>>
 *)

Definition rmv_pte_body: statement :=
  (Ssequence
  (Sset toffset
    (Ebinop Odiv
      (Ebinop Osub
        (Ecast
          (Ederef
            (Ebinop Oadd
              (Ederef
                (Ebinop Oadd
                  (Evar PTPool_LOC (tarray (tarray (tptr tchar) 1024) 64))
                  (Etempvar tproc_index tint)
                  (tptr (tarray (tptr tchar) 1024)))
                (tarray (tptr tchar) 1024)) (Etempvar tpde_index tint)
              (tptr (tptr tchar))) (tptr tchar)) tint)
        (Econst_int (Int.repr 7) tint) tint)
      (Econst_int (Int.repr 4096) tint) tint))
  (Scall None
    (Evar fstore (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
    ((Ebinop Oadd
       (Ebinop Omul (Etempvar toffset tint)
         (Econst_int (Int.repr 1024) tint) tint) (Etempvar tvadr tint)
       tint) :: (Econst_int (Int.repr 0) tint) :: nil))).

Definition f_rmv_pte := {|
                         fn_return := Tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tpde_index, tint) :: (tvadr, tint) :: nil);
                         fn_temps := (toffset, tint) :: nil;
                         fn_body := rmv_pte_body
                       |}.


(** 
<<
     extern unsigned int IDPMap_LOC[1024][1024];

     void set_IDPTE(unsigned int pde_index, unsigned int vadr, unsigned int perm)
     {
         IDPMap_LOC[pde_index][vadr] = (pde_index * 1024 + vadr) * 4096 + perm;
     }
>>
 *)

Definition set_idpte_body: statement :=
  (Sassign
  (Ederef
    (Ebinop Oadd
      (Ederef
        (Ebinop Oadd (Evar IDPMap_LOC (tarray (tarray tint 1024) 1024))
          (Etempvar tpde_index tint) (tptr (tarray tint 1024)))
        (tarray tint 1024)) (Etempvar tvadr tint) (tptr tint)) tint)
  (Ebinop Oadd
    (Ebinop Omul
      (Ebinop Oadd
        (Ebinop Omul (Etempvar tpde_index tint)
          (Econst_int (Int.repr 1024) tint) tint) (Etempvar tvadr tint)
        tint) (Econst_int (Int.repr 4096) tint) tint)
    (Etempvar tperm tint) tint)).

Definition f_set_idpte := {|
                         fn_return := Tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tpde_index, tint) :: (tvadr, tint) :: (tperm, tint) :: nil);
                         fn_temps := nil;
                         fn_body := set_idpte_body
                       |}.
