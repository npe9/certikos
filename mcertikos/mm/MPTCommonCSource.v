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
      extern void set_PDE(unsigned int, unsigned int);
      extern void pt_init_comm(unsigned int);

      void pt_init_kern(unsigned int mbi_adr)
      {
          unsigned int i;
          pt_init_comm(mbi_adr);
          i = 256;
          while(i < 960)
          {
              set_PDE(0, i);
              i ++;
          }
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let ti: ident := 1.
Let tmbi_adr: ident := 2.

Definition pt_init_kern_while_condition : expr := 
  (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr 960) tint) tint).

Definition pt_init_kern_while_body : statement := 
  (Ssequence
     (Scall None
            (Evar set_PDE (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
            ((Econst_int (Int.repr 0) tint) :: (Etempvar ti tint) :: nil))
     (Sset ti
           (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint)
                   tint))).


Definition pt_init_kern_body : statement := 
  (Ssequence
     (Scall None (Evar pt_init_comm (Tfunction (Tcons tint Tnil) Tvoid cc_default)) ((Etempvar tmbi_adr tint)::nil))
     (Ssequence 
        (Sset ti (Econst_int (Int.repr 256) tint))
        (Swhile pt_init_kern_while_condition pt_init_kern_while_body))).

Definition f_pt_init_kern := {|
                              fn_return := tvoid;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tmbi_adr, tint) :: nil);
                              fn_temps := ((ti, tint) :: nil);
                              fn_body := pt_init_kern_body
                            |}.



(** 
<<
      #define MagicNumber 1048577

      extern unsigned int pt_read_pde(unsigned int, unsigned int);
      extern void pt_insert_aux(unsigned int, unsigned int, unsigned int, unsigned int);
      extern unsigned int pt_alloc_pde(unsigned int, unsigned int);
      extern unsigned int at_get_c(unsigned int);
      extern void at_set_c(unsigned int, unsigned int);

      unsigned int pt_insert(unsigned int proc_index, unsigned int vadr, unsigned int padr, unsigned int perm)
      {
        unsigned int pi;
        unsigned int result;
        unsigned int count;
        pi = pt_read_pde(proc_index, vadr);
        if (pi != 0)
          result = 0;
        else
        {
          result = pt_alloc_pde(proc_index, vadr);
          if (result == 0)
            result = MagicNumber;
        }
        if (result != MagicNumber)
        {
          pt_insert_aux(proc_index, vadr, padr, perm);
          count = at_get_c(padr);
          at_set_c(padr, count + 1);
        }
        return result;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tproc_index: ident := 3.
Let tvadr: ident := 4.
Let tpadr: ident := 5.
Let tperm: ident := 6.
Let tpi: ident := 7.
Let tresult: ident := 8.
Let tcount: ident := 9.


Definition pt_insert_body : statement := 
  (Ssequence
     (Scall (Some tpi)
            (Evar pt_read_pde (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
            ((Etempvar tproc_index tint) :: (Etempvar tvadr tint) :: nil))
     (Ssequence
        (Sifthenelse (Ebinop One (Etempvar tpi tint)
                             (Econst_int (Int.repr 0) tint) tint)
                     (Sset tresult (Econst_int (Int.repr 0) tint))
                     (Ssequence
                        (Scall (Some tresult)
                               (Evar pt_alloc_pde (Tfunction (Tcons tint (Tcons tint Tnil))
                                                              tint cc_default))
                               ((Etempvar tproc_index tint) :: (Etempvar tvadr tint) :: nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar tresult tint)
                                             (Econst_int (Int.repr 0) tint) tint)
                                     (Sset tresult (Econst_int (Int.repr 1048577) tint))
                                     Sskip)))
        (Ssequence
           (Sifthenelse (Ebinop One (Etempvar tresult tint)
                                (Econst_int (Int.repr 1048577) tint) tint)
                        (Ssequence
                           (Scall None
                                  (Evar pt_insert_aux (Tfunction
                                                          (Tcons tint
                                                                 (Tcons tint
                                                                        (Tcons tint (Tcons tint Tnil))))
                                                          tvoid cc_default))
                                  ((Etempvar tproc_index tint) :: (Etempvar tvadr tint) ::
                                                                (Etempvar tpadr tint) :: (Etempvar tperm tint) :: nil))
                           (Ssequence
                              (Scall (Some tcount)
                                     (Evar at_get_c (Tfunction (Tcons tint Tnil) tint cc_default))
                                     ((Etempvar tpadr tint) :: nil))
                              (Scall None
                                     (Evar at_set_c (Tfunction (Tcons tint (Tcons tint Tnil))
                                                                tvoid cc_default))
                                     ((Etempvar tpadr tint) ::
                                                             (Ebinop Oadd (Etempvar tcount tint)
                                                                     (Econst_int (Int.repr 1) tint) tint) :: nil))))
                        Sskip)
           (Sreturn (Some (Etempvar tresult tint))))))
.

Definition f_pt_insert := {|
                              fn_return := tint;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tproc_index, tint) :: (tvadr, tint) :: (tpadr, tint) :: (tperm, tint) :: nil);
                              fn_temps := ((tpi, tint) :: (tresult, tint) :: (tcount, tint) :: nil);
                              fn_body := pt_insert_body
                            |}.



(** 
<<
      #define PAGESIZE 4096

      extern unsigned int pt_read(unsigned int, unsigned int);
      extern void pt_rmv_aux(unsigned int, unsigned int);
      extern unsigned int at_get_c(unsigned int);
      extern void at_set_c(unsigned int, unsigned int);

      unsigned int pt_rmv(unsigned int proc_index, unsigned int vadr)
      {
        unsigned int padr;
        unsigned int count;
        padr = pt_read(proc_index, vadr);
        if (padr != 0)
        {
          pt_rmv_aux(proc_index, vadr);
          count = at_get_c(padr / PAGESIZE);
          if (count > 0)
            at_set_c(padr / PAGESIZE, count - 1);
        }
        return padr / PAGESIZE;
      }
>>
 *)

Definition pt_rmv_body : statement := 
  (Ssequence
    (Scall (Some tpadr)
      (Evar pt_read (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                       cc_default))
      ((Etempvar tproc_index tuint) :: (Etempvar tvadr tuint) :: nil))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar tpadr tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall None
          (Evar pt_rmv_aux (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                              cc_default))
          ((Etempvar tproc_index tuint) :: (Etempvar tvadr tuint) :: nil))
        (Ssequence
            (Scall (Some tcount)
              (Evar at_get_c (Tfunction (Tcons tuint Tnil) tuint cc_default))
              ((Ebinop Odiv (Etempvar tpadr tuint)
                 (Econst_int (Int.repr 4096) tint) tuint) :: nil))
          (Sifthenelse (Ebinop Ogt (Etempvar tcount tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Scall None
              (Evar at_set_c (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                tvoid cc_default))
              ((Ebinop Odiv (Etempvar tpadr tuint)
                 (Econst_int (Int.repr 4096) tint) tuint) ::
               (Ebinop Osub (Etempvar tcount tuint)
                 (Econst_int (Int.repr 1) tint) tuint) :: nil))
            Sskip)))
      Sskip)
    (Sreturn (Some (Ebinop Odiv (Etempvar tpadr tuint)
                 (Econst_int (Int.repr 4096) tint) tuint)))))
.

Definition f_pt_rmv := {|
                              fn_return := tint;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tproc_index, tint) :: (tvadr, tint) :: nil);
                              fn_temps := ((tpadr, tint) :: (tcount, tint) :: nil);
                              fn_body := pt_rmv_body
                            |}.