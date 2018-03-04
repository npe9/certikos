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
      extern void rmv_PDE(unsigned int, unsigned int);
      extern void idpde_init(unsigned int);

      #define num_proc 64
      #define one_k 1024

      void pt_init_comm(unsigned int mbi_adr)
      {
          unsigned int i, j;
          idpde_init(mbi_adr);
          i = 0;
          while(i < num_proc)
          {
              j = 0;
              while(j < one_k)
              {
                  if (j < 256)
                    set_PDE(i, j);
                  else if(j >= 960)
                    set_PDE(i, j);
                  else
                    rmv_PDE(i, j);
                  j++;
              }
              i++;
          }
      }
>>
 *)


(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let ti: ident := 1.
Let tj: ident := 2.
Let tmbi_adr: ident := 3.


Definition pd_inner_while_condition : expr := (Ebinop Olt (Etempvar tj tint) (Econst_int (Int.repr 1024) tint) tint).

Definition pd_inner_while_body : statement := 
  (Ssequence
     (Sifthenelse (Ebinop Olt (Etempvar tj tint)
                          (Econst_int (Int.repr 256) tint) tint)
                  (Scall None
                         (Evar set_PDE (Tfunction (Tcons tint (Tcons tint Tnil))
                                                  tvoid cc_default))
                         ((Etempvar ti tint) :: (Etempvar tj tint) :: nil))
                  (Sifthenelse (Ebinop Oge (Etempvar tj tint)
                                       (Econst_int (Int.repr 960) tint) tint)
                               (Scall None
                                      (Evar set_PDE (Tfunction
                                                       (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                      ((Etempvar ti tint) :: (Etempvar tj tint) :: nil))
                               (Scall None
                                      (Evar rmv_PDE (Tfunction
                                                       (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                                      ((Etempvar ti tint) :: (Etempvar tj tint) :: nil))))
     (Sset tj
           (Ebinop Oadd (Etempvar tj tint)
                   (Econst_int (Int.repr 1) tint) tint))).


Definition pt_init_comm_outter_while_condition : expr := (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr num_proc) tint) tint).

Definition pt_init_comm_outter_while_body : statement := 
  (Ssequence
     (Sset tj (Econst_int (Int.repr 0) tint))
     (Ssequence
        (Swhile pd_inner_while_condition pd_inner_while_body)
        (Sset ti
              (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint)
                      tint))))
.


Definition pt_init_comm_body : statement := 
  (Ssequence
     (Scall None (Evar idpde_init (Tfunction (Tcons tint Tnil) tvoid cc_default)) ((Etempvar tmbi_adr tint) :: nil))
     (Ssequence
        (Sset ti (Econst_int (Int.repr 0) tint))
        (Swhile pt_init_comm_outter_while_condition pt_init_comm_outter_while_body))).

Definition f_pt_init_comm := {|
                              fn_return := tvoid;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tmbi_adr, tint) :: nil);
                              fn_temps := ((ti, tint) :: (tj, tint) :: nil);
                              fn_body := pt_init_comm_body
                            |}.



      (** 
<<
      extern unsigned int container_alloc(unsigned int);
      extern void pt_insert_pde(unsigned int, unsigned int, unsigned int);
      extern void rmv_PTE(unsigned int, unsigned int, unsigned int);

      unsigned int pt_alloc_pde(unsigned int proc_index, unsigned int vadr)
      {
        unsigned int i;
        unsigned int pi;
        unsigned int pde_index;
        pi = container_alloc(proc_index);
        if (pi != 0)
        {
          pt_insert_pde(proc_index, vadr, pi);
          pde_index = vadr / (4096 * 1024);
          i = 0;
          while (i < 1024)
          {
            rmv_PTE(proc_index, pde_index, i);
            i ++;
          }
        }
        return pi;
      }
>>
       *)


      Let tpi:= 4 % positive.
      Let tproc_index:= 5 % positive.
      Let tvadr:= 6 % positive.
      Let tpde_index:= 7 % positive.

      Definition pt_alloc_pde_while_condition : expr := (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr 1024) tint) tint).

      Definition pt_alloc_pde_while_body : statement := 
        (Ssequence
           (Scall None
                  (Evar rmv_PTE (Tfunction
                                    (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                    tvoid cc_default))
                  ((Etempvar tproc_index tint) :: (Etempvar tpde_index tint) ::
                                                (Etempvar ti tint) :: nil))
           (Sset ti
                 (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint)
                         tint))).

      Definition pt_alloc_pde_body : statement := 
        (Ssequence
           (Scall (Some tpi) (Evar container_alloc (Tfunction (Tcons tuint Tnil) tint cc_default)) ((Etempvar tproc_index tint) :: nil))
           (Ssequence
              (Sifthenelse (Ebinop One (Etempvar tpi tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                           (Ssequence
                              (Scall None
                                     (Evar pt_insert_pde (Tfunction
                                                             (Tcons tint
                                                                    (Tcons tint (Tcons tint Tnil))) tvoid cc_default))
                                     ((Etempvar tproc_index tint) :: (Etempvar tvadr tint) ::
                                                                   (Etempvar tpi tint) :: nil))
                              (Ssequence
                                 (Sset tpde_index
                                       (Ebinop Odiv (Etempvar tvadr tint)
                                               (Ebinop Omul (Econst_int (Int.repr 4096) tint)
                                                       (Econst_int (Int.repr 1024) tint) tint) tint))
                                 (Ssequence
                                    (Sset ti (Econst_int (Int.repr 0) tint))
                                    (Swhile pt_alloc_pde_while_condition pt_alloc_pde_while_body))))
                           Sskip)
              (Sreturn (Some (Etempvar tpi tint)))))
          .

      Definition f_pt_alloc_pde := {|
                                 fn_return := tint;
                                 fn_callconv := cc_default;
                                 fn_vars := nil;
                                 fn_params := ((tproc_index, tint) :: (tvadr, tint) :: nil);
                                 fn_temps := ((ti, tint) :: (tpi, tint) :: (tpde_index, tint) :: nil);
                                 fn_body := pt_alloc_pde_body
                               |}.




      (** 
<<
      extern unsigned int pt_read_pde(unsigned int, unsigned int);
      extern void pfree(unsigned int);
      extern void pt_rmv_pde(unsigned int, unsigned int);

      void pt_free_pde(unsigned int proc_index, unsigned int vadr)
      {
        unsigned int pi;
        pi = pt_read_pde(proc_index, vadr);
        pt_rmv_pde(proc_index, vadr);
        pfree(pi);
      }
>>
       *)

          Definition pt_free_pde_body : statement := 
            (Ssequence
               (Scall (Some tpi)
                      (Evar pt_read_pde (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
                      ((Etempvar tproc_index tint) :: (Etempvar tvadr tint) :: nil))
               (Ssequence
                  (Scall None
                         (Evar pt_rmv_pde (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                         ((Etempvar tproc_index tint) :: (Etempvar tvadr tint) :: nil))
                  (Scall None (Evar pfree (Tfunction (Tcons tint Tnil) tvoid cc_default))
                         ((Etempvar tpi tint) :: nil))))
          .

      Definition f_pt_free_pde := {|
                                 fn_return := Tvoid;
                                 fn_callconv := cc_default;
                                 fn_vars := nil;
                                 fn_params := ((tproc_index, tint) :: (tvadr, tint) :: nil);
                                 fn_temps := ((tpi, tint) :: nil);
                                 fn_body := pt_free_pde_body
                               |}.
