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
      extern unsigned int container_alloc(unsigned int);
      extern unsigned int pt_insert(unsigned int, unsigned int, unsigned int, unsigned int);

      #define MagicNumber 1048577

      unsigned int pt_resv(unsigned int proc_index, unsigned int vaddr, unsigned int perm)
      {
          unsigned int pi;
          unsigned int result;
          pi = container_alloc(proc_index);
          if (pi == 0)
            result = MagicNumber;
          else
            result = pt_insert(proc_index, vaddr, pi, perm);
          return result;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index: ident := 1.
Let tvaddr: ident := 2.
Let tperm: ident := 3.
Let tpi: ident := 4.
Let tresult: ident := 5.

Local Open Scope Z_scope.

Definition pt_resv_body : statement := 
  (Ssequence
     (Scall (Some tpi) (Evar container_alloc (Tfunction (Tcons tint Tnil) tint cc_default)) ((Etempvar tproc_index tint) :: nil))
     (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar tpi tint)
                             (Econst_int (Int.repr 0) tint) tint)
                     (Sset tresult (Econst_int (Int.repr 1048577) tint))
                     (Scall (Some tresult)
                            (Evar pt_insert (Tfunction
                                               (Tcons tint
                                                      (Tcons tint (Tcons tint (Tcons tint Tnil))))
                                               tint cc_default))
                            ((Etempvar tproc_index tint) :: (Etempvar tvaddr tint) ::
                                                         (Etempvar tpi tint) :: (Etempvar tperm tint) :: nil)))
        (Sreturn (Some (Etempvar tresult tint)))))
   .

Definition f_pt_resv := {|
                         fn_return := tint;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: (tperm, tint) :: nil);
                         fn_temps := ((tpi, tint) :: (tresult, tint) :: nil);
                         fn_body := pt_resv_body
                       |}.



(** 
<<
      extern unsigned int container_alloc(unsigned int);
      extern unsigned int pt_insert(unsigned int, unsigned int, unsigned int, unsigned int);

      #define MagicNumber 1048577

      unsigned int pt_resv2(unsigned int proc_index, unsigned int vaddr, unsigned int perm, unsigned int proc_index2, unsigned int vaddr2, unsigned int perm2)
      {
          unsigned int pi;
          unsigned int result;
          pi = container_alloc(proc_index);
          if (pi == 0)
            result = MagicNumber;
          else
          {
            result = pt_insert(proc_index, vaddr, pi, perm);
            if (result == MagicNumber)
              result = pt_insert(proc_index2, vaddr2, pi, perm2);
          }
          return result;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index2: ident := 6.
Let tvaddr2: ident := 7.
Let tperm2: ident := 8.

Local Open Scope Z_scope.

Definition pt_resv2_body : statement := 
  (Ssequence
     (Scall (Some tpi) (Evar container_alloc (Tfunction (Tcons tint Tnil) tint cc_default)) ((Etempvar tproc_index tint) :: nil))
     (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar tpi tint)
                             (Econst_int (Int.repr 0) tint) tint)
                     (Sset tresult (Econst_int (Int.repr 1048577) tint))
                     (Ssequence
                        (Scall (Some tresult)
                               (Evar pt_insert (Tfunction
                                                  (Tcons tint
                                                         (Tcons tint
                                                                (Tcons tint (Tcons tint Tnil)))) tint cc_default))
                               ((Etempvar tproc_index tint) :: (Etempvar tvaddr tint) ::
                                                            (Etempvar tpi tint) :: (Etempvar tperm tint) :: nil))
                        (Sifthenelse (Ebinop One (Etempvar tresult tint)
                                             (Econst_int (Int.repr 1048577) tint) tint)
                                     (Scall (Some tresult)
                                            (Evar pt_insert (Tfunction
                                                               (Tcons tint
                                                                      (Tcons tint
                                                                             (Tcons tint (Tcons tint Tnil))))
                                                               tint cc_default))
                                            ((Etempvar tproc_index2 tint) :: (Etempvar tvaddr2 tint) ::
                                                                          (Etempvar tpi tint) :: (Etempvar tperm2 tint) :: nil))
                                     Sskip)))
        (Sreturn (Some (Etempvar tresult tint)))))
.

Definition f_pt_resv2 := {|
                         fn_return := tint;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: (tperm, tint) :: (tproc_index2, tint) :: (tvaddr2, tint) :: (tperm2, tint) :: nil);
                         fn_temps := ((tpi, tint) :: (tresult, tint) :: nil);
                         fn_body := pt_resv2_body
                       |}.



(** 
<<
      extern void pt_init(unsigned int);
       
      void pmap_init(unsigned int mbi_adr)
      {
          pt_init(mbi_adr);
      }
>>
 *)

(* function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tmbi_adr: ident := 6.

Local Open Scope Z_scope.

Definition pmap_init_body : statement := 
   Scall None (Evar pt_init (Tfunction (Tcons tint Tnil) Tvoid cc_default)) ((Etempvar tmbi_adr tint)::nil).

Definition f_pmap_init := {|
                           fn_return := tvoid;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tmbi_adr, tint) :: nil);
                           fn_temps := nil;
                           fn_body := pmap_init_body
                         |}.



(** 
<<
    extern unsigned int container_split(unsigned int, unsigned int);
     
    unsigned int pt_new(unsigned int id, unsigned int quota)
    {
        unsigned int child;
        child = container_split(id, quota);
        return child;
    } 
>>
 *)

(** Local temporaries used in pt_new function *)
Local Open Scope positive_scope.
Let tchild: ident := 9.
Let tid: ident := 10.
Let tquota: ident := 11.

Local Open Scope Z_scope.

Definition pt_new_body : statement := 
  Ssequence 
    (Scall (Some tchild)
       (Evar container_split (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
       (Etempvar tid tint :: Etempvar tquota tint :: nil))
    (Sreturn (Some (Etempvar tchild tint))).

Definition f_pt_new := {|
                        fn_return := tint;
                        fn_callconv := cc_default;
                        fn_vars := nil;
                        fn_params := (tid,tint) :: (tquota,tint) :: nil;
                        fn_temps := (tchild, tint) :: nil;
                        fn_body := pt_new_body
                      |}.


(*
(** 
<<
      extern void set_bit(unsigned int, unsigned int);
      extern void pt_rmv(unsigned int, unsigned int);
      
      #define PgSize 4096
      #define kern_low 262144
      #define kern_high 983040
      #define adr_low (kern_low * PgSize)
      #define adr_high (kern_high * PgSize)
      
      void pt_free(unsigned int proc_index)
      {
          unsigned int i;
          set_bit(proc_index, 0);
          i = adr_low;
          while(i < adr_high)
          {
              pt_rmv(proc_index, i);
              i = i + PgSize;
          }
      }
>>
 *)

Definition pt_free_while_condition : expr := (Ebinop Olt (Etempvar ti tint)
                                                     (Econst_int (Int.repr adr_high) tint) tint).

Definition pt_free_while_body : statement := 
  (Ssequence
     (Scall None (Evar pt_rmv (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default))
            ((Etempvar tproc_index tint) :: (Etempvar ti tint) :: nil))
     (Sset ti (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr PgSize) tint) tint))).


Definition pt_free_body : statement := 
  (Ssequence
     (Scall None (Evar set_bit (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default))
            ((Etempvar tproc_index tint) :: (Econst_int (Int.repr 0) tint) :: nil))
     (Ssequence
        (Sset ti (Econst_int (Int.repr adr_low) tint))
        (Swhile pt_free_while_condition pt_free_while_body)))
.

Definition f_pt_free := {|
                         fn_return := tvoid;
                         fn_callconv := cc_default;
                         fn_vars := nil;
                         fn_params := ((tproc_index, tint) :: nil);
                         fn_temps := ((ti, tint) :: nil);
                         fn_body := pt_free_body
                       |}.
*)