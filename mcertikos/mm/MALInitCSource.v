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
  extern int get_size(void);
  extern int get_mms(unsigned int);
  extern int get_mml(unsigned int);
  extern int is_usable(unsigned int);
  extern void set_norm(unsigned int, unsigned int);
  extern void set_nps(unsigned int);
  extern void container_init(unsigned int);

  void mem_init(unsigned int mbi_adr)
  {
    unsigned int i, j, s, l, isnorm, nps, maxs, size, mm, flag;
    boot_loader(mbi_adr);
    i = 0;
    size = get_size();
    nps = 0;
    while(i < size)
    {
        s = get_mms(i);
        l = get_mml(i);
        maxs = (s + l) / PgSize + 1;
        if(maxs > nps)
            nps = maxs;
        i++;
    }
    set_nps(nps);
    i = 0;
    while(i < nps)
    {
        if(i < kern_low || i >= kern_high)
            set_norm(i, 1);
        else
        {
            j = 0;
            flag = 0;
            isnorm = 0;
            while(j < size && flag == 0)
            {
                s = get_mms(j);
                l = get_mml(j);
                isnorm = is_usable(j);
                if(s <= i * PgSize && l + s >= (i + 1) * PgSize)
                    flag = 1;
                j++;
            }
            if(flag == 1 && isnorm == 1)
                set_norm(i, 2);
            else
                set_norm(i, 0);
        }
        i++;
    }
  }
>>
 *)

(** Local temporaries used *)
Local Open Scope positive_scope.
Let ti: ident := 1.
Let tj: ident := 2.
Let ts: ident := 3.
Let tl: ident := 4.
Let tisnorm: ident := 5.
Let tnps: ident := 6.
Let tmaxs: ident := 7.
Let tsize: ident := 8.
Let tmm: ident := 9.
Let tflag: ident := 10.
Let tmbi_adr: ident := 11.


Definition nps_while_condition : expr := 
  (Ebinop Olt (Etempvar ti tint) (Etempvar tsize tint) tint).

Definition nps_while_body : statement := 
  (Ssequence
     (Scall (Some ts) (Evar get_mms (Tfunction (Tcons tint Tnil) tint cc_default))
            ((Etempvar ti tint) :: nil))
     (Ssequence
        (Scall (Some tl) (Evar get_mml (Tfunction (Tcons tint Tnil) tint cc_default))
               ((Etempvar ti tint) :: nil))
        (Ssequence
           (Sset tmaxs (Ebinop Oadd
                               (Ebinop Odiv
                                       (Ebinop Oadd (Etempvar ts tint) (Etempvar tl tint) tint)
                                       (Econst_int (Int.repr PgSize) tint) tint)
                               (Econst_int (Int.repr 1) tint) tint))
           (Ssequence
              (Sifthenelse 
                 (Ebinop Ogt (Etempvar tmaxs tint) (Etempvar tnps tint) tint)
                 (Sset tnps (Etempvar tmaxs tint))
                 Sskip
              )
              (Sset ti (Ebinop Oadd (Etempvar ti tint)
                               (Econst_int (Int.repr 1) tint) tint))))))
.


Definition inner_while_condition : expr := 
  (Ebinop Oand
          (Ebinop Olt (Etempvar tj tint) (Etempvar tsize tint) tint)
          (Ebinop Oeq (Etempvar tflag tint) (Econst_int (Int.repr 0) tint) tint) tint).

Definition inner_while_body : statement := 
  (Ssequence
     (Scall (Some ts) (Evar get_mms (Tfunction (Tcons tint Tnil) tint cc_default))
            ((Etempvar tj tint) :: nil))
     (Ssequence
        (Scall (Some tl) (Evar get_mml (Tfunction (Tcons tint Tnil) tint cc_default))
               ((Etempvar tj tint) :: nil))
        (Ssequence
           (Scall (Some tisnorm) (Evar is_usable (Tfunction (Tcons tint Tnil) tint cc_default))
                  ((Etempvar tj tint) :: nil))
           (Ssequence
              (Sifthenelse
                 (Ebinop Ole (Etempvar ts tint)
                         (Ebinop Omul (Etempvar ti tint) (Econst_int (Int.repr PgSize) tint) tint) tint)
                 (Sifthenelse
                    (Ebinop Oge (Ebinop Oadd (Etempvar tl tint) (Etempvar ts tint) tint)
                            (Ebinop Omul (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint) tint)
                                    (Econst_int (Int.repr PgSize) tint) tint) tint) 
                    (Sset tflag (Econst_int (Int.repr 1) tint))
                    Sskip
                 )
                 Sskip
              )
              (Sset tj (Ebinop Oadd (Etempvar tj tint) (Econst_int (Int.repr 1) tint) tint))))))
.

Definition outter_while_condition : expr := 
  (Ebinop Olt (Etempvar ti tint) (Etempvar tnps tint) tint).

Definition outter_while_body : statement := 
  (Ssequence
     (Sifthenelse 
        (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr kern_low) tint) tint)
        (Scall None (Evar set_norm (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default))
               ((Etempvar ti tint) :: (Econst_int (Int.repr 1) tint) :: nil))
        (Sifthenelse 
           (Ebinop Oge (Etempvar ti tint) (Econst_int (Int.repr kern_high) tint) tint) 
           (Scall None (Evar set_norm (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default))
                  ((Etempvar ti tint) :: (Econst_int (Int.repr 1) tint) :: nil))
           (Ssequence
              (Sset tj (Econst_int (Int.repr 0) tint))
              (Ssequence
                 (Sset tflag (Econst_int (Int.repr 0) tint))
                 (Ssequence
                    (Sset tisnorm (Econst_int (Int.repr 0) tint))
                    (Ssequence
                       (Swhile inner_while_condition inner_while_body)
                       (Sifthenelse 
                          (Ebinop Oeq (Etempvar tflag tint) (Econst_int (Int.repr 1) tint) tint)
                          (Sifthenelse 
                             (Ebinop Oeq (Etempvar tisnorm tint) (Econst_int (Int.repr 1) tint) tint)
                             (Scall None (Evar set_norm (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default))
                                    ((Etempvar ti tint) :: (Econst_int (Int.repr 2) tint) :: nil))
                             (Scall None (Evar set_norm (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default))
                                    ((Etempvar ti tint) :: (Econst_int (Int.repr 0) tint) :: nil))
                          )
                          (Scall None (Evar set_norm (Tfunction (Tcons tint (Tcons tint Tnil)) Tvoid cc_default))
                                 ((Etempvar ti tint) :: (Econst_int (Int.repr 0) tint) :: nil))
                       )
           ))))
        )
     )
     (Sset ti (Ebinop Oadd (Etempvar ti tint)
                      (Econst_int (Int.repr 1) tint) tint))
  )
.


Definition mem_init_body : statement := 
  (Ssequence
     (Scall None (Evar boot_loader (Tfunction (Tcons tint Tnil) Tvoid cc_default)) ((Etempvar tmbi_adr tint)::nil))
     (Ssequence
        (Sset ti (Econst_int (Int.repr 0) tint))
        (Ssequence
           (Scall (Some tsize) (Evar get_size (Tfunction Tnil tint cc_default)) nil)
           (Ssequence
              (Sset tnps (Econst_int (Int.repr 0) tint))
              (Ssequence
                 (Swhile nps_while_condition nps_while_body)
                 (Ssequence
                    (Scall None (Evar set_nps (Tfunction (Tcons tint Tnil) Tvoid cc_default)) ((Etempvar tnps tint) :: nil))
                    (Ssequence
                       (Sset ti (Econst_int (Int.repr 0) tint))
                       (Swhile outter_while_condition outter_while_body)
  )))))))
.

Definition f_mem_init := {|
                          fn_return := Tvoid;
                          fn_callconv := cc_default;
                          fn_params := ((tmbi_adr, tint)::nil);
                          fn_vars := nil;
                          fn_temps := ((ti, tint) :: (tj, tint) :: (ts, tint) :: (tl, tint) :: (tisnorm, tint) :: (tnps, tint) :: (tmaxs, tint) :: (tsize, tint) :: (tmm, tint) :: (tflag, tint) :: nil);
                          fn_body := mem_init_body
                        |}.
