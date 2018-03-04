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
    void pfree(unsigned int pfree_index)
    {
        at_set(pfree_index, 0);
    }
>>
 *)

(** pfree function parameter *)
Let tpfree_index: ident := 1 % positive.

Definition pfree_body : statement :=
  Scall None (Evar at_set (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) 
        (Etempvar tpfree_index tint::Econst_int (Int.repr 0) tint::nil). 


Definition f_pfree := {|
                       fn_return := Tvoid;
                       fn_callconv := cc_default;
                       fn_params := ((tpfree_index, tint) :: nil);
                       fn_vars := nil;
                       fn_temps := nil;
                       fn_body := pfree_body
                     |}.


(** 
<<
    extern unsigned int get_nps(void);
    extern unsigned int is_norm(unsigned int);
    extern unsigned int at_get(unsigned int);
    extern void at_set(unsigned int, unsigned int);
    extern void at_set_c(unsigned int, unsigned int);

    unsigned int palloc()
    {
        unsigned int tnps;
        unsigned int palloc_index;
        unsigned int palloc_cur_at;
        unsigned int palloc_is_norm;
        unsigned int free_index;

        tnps = get_nps();
        palloc_index = 1;
        palloc_free_index = tnps;
        while( palloc_index < tnps && palloc_free_index == tnps )
        {
            palloc_is_norm = is_norm(palloc_index);
            if (palloc_is_norm == 1)
            {
                palloc_cur_at = at_get(palloc_index);
                if (palloc_cur_at == 0)
                    palloc_free_index = palloc_index;
            }
            palloc_index ++;
        }
        if (palloc_free_index == tnps)
            palloc_free_index = 0;
        else
        {
            at_set(palloc_free_index, 1);
            at_set_c(palloc_free_index, 0);
        }
        return palloc_free_index;
    } 
>>
 *)

(** Local temporaries used in palloc function *)
Local Open Scope positive_scope.
Let tpalloc_index: ident := 1.
Let tpalloc_cur_at: ident := 2.
Let tpalloc_is_norm: ident := 3.
Let tnps: ident := 4.
Let tpalloc_free_index: ident := 5.
Let tid: ident := 6.

Definition palloc_while_condition : expr := 
  Ebinop Oand 
         (Ebinop Olt (Etempvar tpalloc_index tint) (Etempvar tnps tint) tint)
         (Ebinop Oeq (Etempvar tpalloc_free_index tint) (Etempvar tnps tint) tint) tint.

Definition palloc_while_body : statement := 
  (Ssequence
     (Scall
        (Some tpalloc_is_norm)
        (Evar is_norm (Tfunction (Tcons tint Tnil) tint cc_default)) 
        (Etempvar tpalloc_index tint::nil)
     )
     (Ssequence
        (Sifthenelse
           (Ebinop Oeq (Etempvar tpalloc_is_norm tint)
                   (Econst_int (Int.repr 1) tint) tint)
           (Ssequence
              (Scall 
                 (Some tpalloc_cur_at) 
                 (Evar at_get (Tfunction (Tcons tint Tnil) tint cc_default)) 
                 (Etempvar tpalloc_index tint::nil)
              )
              (Sifthenelse
                 (Ebinop Oeq (Etempvar tpalloc_cur_at tint) 
                         (Econst_int (Int.repr 0) tint) tint)
                 (Sset tpalloc_free_index (Etempvar tpalloc_index tint))
                 Sskip
              )
           )
           Sskip
        )
        (Sset 
           tpalloc_index
           (Ebinop Oadd (Etempvar tpalloc_index tint) 
                   (Econst_int (Int.repr 1) tint) tint)
        )
     )
  )
.



Definition palloc_body : statement := 
  Ssequence
    (Scall (Some tnps) (Evar get_nps (Tfunction Tnil tint cc_default)) nil)
    (Ssequence
       (Sset tpalloc_index (Econst_int (Int.repr 1) tint))
       (Ssequence
          (Sset tpalloc_free_index (Etempvar tnps tint))
          (Ssequence
             (Swhile
                palloc_while_condition
                palloc_while_body
             )
             (Ssequence
                (Sifthenelse
                   (Ebinop Oeq (Etempvar tpalloc_free_index tint)
                           (Etempvar tnps tint) tint)
                   (Sset tpalloc_free_index (Econst_int (Int.repr 0) tint))
                   (Ssequence
                      (Scall None
                             (Evar at_set (Tfunction (Tcons tint (Tcons tint Tnil))
                                                     tvoid cc_default))
                             ((Etempvar tpalloc_free_index tint) ::
                                                                 (Econst_int (Int.repr 1) tint) :: nil))
                      (Scall None
                             (Evar at_set_c (Tfunction (Tcons tint (Tcons tint Tnil))
                                                       tvoid cc_default))
                             ((Etempvar tpalloc_free_index tint) ::
                                                                 (Econst_int (Int.repr 0) tint) :: nil))
                ))
                (Sreturn (Some (Etempvar tpalloc_free_index tint)))
    )))).

Definition f_palloc := {|
                        fn_return := tint;
                        fn_callconv := cc_default;
                        fn_params := nil;
                        fn_vars := nil;
                        fn_temps := ((tnps, tint) :: (tpalloc_index, tint) :: (tpalloc_cur_at, tint) :: (tpalloc_is_norm, tint) :: (tpalloc_free_index, tint) :: nil);
                        fn_body := palloc_body
                      |}.
