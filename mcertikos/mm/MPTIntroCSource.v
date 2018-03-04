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
      extern void get_PTE(unsigned int, unsigned int, unsigned int);
      
      unsigned int pt_read(unsigned int proc_index, unsigned int vaddr)
      {
          unsigned int pdx_index;
          unsigned int vaddrl;
          unsigned int paddr;
          pdx_index = vaddr / (4096 * 1024);
          vaddrl = (vaddr / 4096) % 1024;
          paddr = get_PTE(proc_index, pdx_index, vaddrl);
          return paddr;
      }
>>
       *)

      Let tproc_index:= 1 % positive.
      Let tvaddr:= 2 % positive.
      Let tpaddr:= 3 % positive.
      Let tperm:= 4 % positive.
      Let tpdx_index:= 5 % positive.
      Let tvaddrl:= 6 % positive.

      Definition pt_read_body : statement := 
        (Ssequence 
           (Sset tpdx_index (Ebinop Odiv (Etempvar tvaddr tint)
                                    (Ebinop Omul (Econst_int (Int.repr 4096) tint)
                                            (Econst_int (Int.repr 1024) tint) tint) tint))
           (Ssequence
              (Sset tvaddrl
                    (Ebinop Omod
                            (Ebinop Odiv (Etempvar tvaddr tint) (Econst_int (Int.repr 4096) tint)
                                    tint) (Econst_int (Int.repr 1024) tint) tint))
              (Ssequence
                 (Scall (Some tpaddr)
                        (Evar get_PTE (Tfunction
                                         (Tcons tint (Tcons tint (Tcons tint Tnil))) tint cc_default))
                        ((Etempvar tproc_index tint) :: (Etempvar tpdx_index tint) ::
                                                     (Etempvar tvaddrl tint) :: nil))
                 (Sreturn (Some (Etempvar tpaddr tint))))))
      .


      Definition f_pt_read := {|
                               fn_return := tint;
                               fn_callconv := cc_default;
                               fn_vars := nil;
                               fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: nil);
                               fn_temps := ((tpdx_index, tint) :: (tvaddrl, tint) :: (tpaddr, tint) :: nil);
                               fn_body := pt_read_body
                             |}.


      (** 
<<
      extern unsigned int get_PDE(unsigned int, unsigned int);

      unsigned int pt_read_pde(unsigned int proc_index, unsigned int vaddr)
      {
          unsigned int pdx_index;
          unsigned int paddr;
          pdx_index = vaddr / (4096 * 1024);
          paddr = get_PDE(proc_index, pdx_index);
          return paddr;
      }
>>
       *)

      Definition pt_read_pde_body : statement := 
        (Ssequence
           (Sset tpdx_index
                 (Ebinop Odiv (Etempvar tvaddr tint)
                         (Ebinop Omul (Econst_int (Int.repr 4096) tint)
                                 (Econst_int (Int.repr 1024) tint) tint) tint))
           (Ssequence
                 (Scall (Some tpaddr)
                        (Evar get_PDE (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
                        ((Etempvar tproc_index tint) :: (Etempvar tpdx_index tint) :: nil))
              (Sreturn (Some (Etempvar tpaddr tint)))))
      .


      Definition f_pt_read_pde := {|
                               fn_return := tint;
                               fn_callconv := cc_default;
                               fn_vars := nil;
                               fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: nil);
                               fn_temps := ((tpdx_index, tint) :: (tpaddr, tint) :: nil);
                               fn_body := pt_read_pde_body
                             |}.


      (** 
<<
      extern void rmv_PTE(unsigned int, unsigned int, unsigned int);
      
      void pt_rmv_aux(unsigned int proc_index, unsigned int vaddr)
      {
          unsigned int pdx_index;
          unsigned int vaddrl;
          pdx_index = vaddr / (4096 * 1024);
          vaddrl = (vaddr / 4096) % 1024;
          rmv_PTE(proc_index, pdx_index, vaddrl);
      }
>>
       *)

      Definition pt_rmv_aux_body : statement := 
        (Ssequence (Sset tpdx_index (Ebinop Odiv (Etempvar tvaddr tint)
                                            (Ebinop Omul (Econst_int (Int.repr PgSize) tint)
                                                    (Econst_int (Int.repr one_k) tint) tint) tint))
                   (Ssequence
                      (Sset tvaddrl (Ebinop Omod
                                            (Ebinop Odiv (Etempvar tvaddr tint) (Econst_int (Int.repr PgSize) tint)
                                                    tint) (Econst_int (Int.repr one_k) tint) tint))
                      (Scall None
                             (Evar rmv_PTE (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default))
                             ((Etempvar tproc_index tint) :: (Etempvar tpdx_index tint) ::
                                                          (Etempvar tvaddrl tint) :: nil))))
      .

      Definition f_pt_rmv_aux := {|
                              fn_return := tvoid;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: nil);
                              fn_temps := ((tpdx_index, tint) :: (tvaddrl, tint) :: nil);
                              fn_body := pt_rmv_aux_body
                            |}.



      (** 
<<
      extern void rmv_PDE(unsigned int, unsigned int);

      void pt_rmv_pde(unsigned int proc_index, unsigned int vaddr)
      {
          unsigned int pdx_index;
          pdx_index = vaddr / (4096 * 1024);
          rmv_PDE(proc_index, pdx_index);
      }
>>
       *)

      Definition pt_rmv_pde_body : statement := 
        (Ssequence
           (Sset tpdx_index
                 (Ebinop Odiv (Etempvar tvaddr tint)
                         (Ebinop Omul (Econst_int (Int.repr 4096) tint)
                                 (Econst_int (Int.repr 1024) tint) tint) tint))
           (Scall None
                  (Evar rmv_PDE (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar tproc_index tint) :: (Etempvar tpdx_index tint) :: nil)))
      .

      Definition f_pt_rmv_pde := {|
                              fn_return := tvoid;
                              fn_callconv := cc_default;
                              fn_vars := nil;
                              fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: nil);
                              fn_temps := ((tpdx_index, tint) :: nil);
                              fn_body := pt_rmv_pde_body
                            |}.



      (** 
<<
      extern void set_PTE(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);
      
      void pt_insert_aux(unsigned int proc_index, unsigned int vaddr, unsigned int paddr, unsigned int perm)
      {
          unsigned int pdx_index;
          unsigned int vaddrl;
          pdx_index = vaddr / (4096 * 1024);
          vaddrl = (vaddr / 4096) % 1024;
          set_PTE(proc_index, pdx_index, vaddrl, paddr, perm);
      }
>>
       *)


      Definition pt_insert_aux_body : statement := 
        (Ssequence (Sset tpdx_index (Ebinop Odiv (Etempvar tvaddr tint)
                                            (Ebinop Omul (Econst_int (Int.repr PgSize) tint)
                                                    (Econst_int (Int.repr one_k) tint) tint) tint))
                   (Ssequence (Sset tvaddrl (Ebinop Omod
                                                    (Ebinop Odiv (Etempvar tvaddr tint) (Econst_int (Int.repr PgSize) tint)
                                                            tint) (Econst_int (Int.repr one_k) tint) tint))
                              (Scall None (Evar set_PTE (Tfunction (Tcons tint (Tcons tint
                                                                                      (Tcons tint (Tcons tint (Tcons tint Tnil))))) Tvoid cc_default))
                                     ((Etempvar tproc_index tint) :: (Etempvar tpdx_index tint) ::
                                                                  (Etempvar tvaddrl tint) :: (Etempvar tpaddr tint) ::
                                                                  (Etempvar tperm tint) :: nil))))
      .

      Definition f_pt_insert_aux := {|
                                 fn_return := Tvoid;
                                 fn_callconv := cc_default;
                                 fn_vars := nil;
                                 fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: (tpaddr, tint) :: (tperm, tint) :: nil);
                                 fn_temps := ((tpdx_index, tint) :: (tvaddrl, tint) :: nil);
                                 fn_body := pt_insert_aux_body
                               |}.




      (** 
<<
      extern void set_PDEU(unsigned int, unsigned int, unsigned int);

      void pt_insert_pde(unsigned int proc_index, unsigned int vaddr, unsigned int pi)
      {
          unsigned int pdx_index;
          pdx_index = vaddr / (4096 * 1024);
          set_PDEU(proc_index, pdx_index, pi);
      }
>>
       *)


      Let tpi:= 7 % positive.

      Definition pt_insert_pde_body : statement := 
        (Ssequence
           (Sset tpdx_index
                 (Ebinop Odiv (Etempvar tvaddr tint)
                         (Ebinop Omul (Econst_int (Int.repr 4096) tint)
                                 (Econst_int (Int.repr 1024) tint) tint) tint))
           (Scall None
                  (Evar set_PDEU (Tfunction (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                             tvoid cc_default))
                  ((Etempvar tproc_index tint) :: (Etempvar tpdx_index tint) ::
                                                (Etempvar tpi tint) :: nil)))
      .

      Definition f_pt_insert_pde := {|
                                 fn_return := Tvoid;
                                 fn_callconv := cc_default;
                                 fn_vars := nil;
                                 fn_params := ((tproc_index, tint) :: (tvaddr, tint) :: (tpi, tint) :: nil);
                                 fn_temps := ((tpdx_index, tint) :: nil);
                                 fn_body := pt_insert_pde_body
                               |}.




      (** 
<<
      #define PT_PERM_PTKF 3
      #define PT_PERM_PTKT 259

      extern void container_init(unsigned int);
      extern void set_IDPTE(unsigned int, unsigned int, unsigned int);

      void idpde_init(unsigned int mbi_adr)
      {
        unsigned int i, j;
        unsigned int perm;
        container_init(mbi_adr);
        for(i = 0; i < 1024; i ++)
        {
          if (i < 256)
            perm = PT_PERM_PTKT;
          else if (i >= 960)
            perm = PT_PERM_PTKT;
          else
            perm = PT_PERM_PTKF;
          for(j = 0; j < 1024; j ++)
          {
            set_IDPTE(i, j, perm);
          }
        }
      }
>>
       *)

      Let ti:= 8 % positive.
      Let tj:= 9 % positive.
      Let tmbi_adr:= 10 % positive.

      Definition idpde_init_inner_while_condition : expr := 
        (Ebinop Olt (Etempvar tj tint)
                (Econst_int (Int.repr 1024) tint) tint).

      Definition idpde_init_inner_while_body : statement := 
        (Ssequence
           (Scall None
                  (Evar set_IDPTE (Tfunction
                                      (Tcons tint
                                             (Tcons tint (Tcons tint Tnil)))
                                      tvoid cc_default))
                  ((Etempvar ti tint) :: (Etempvar tj tint) ::
                                       (Etempvar tperm tint) :: nil))
           (Sset tj
                 (Ebinop Oadd (Etempvar tj tint)
                         (Econst_int (Int.repr 1) tint) tint))).

      Definition idpde_init_outter_while_condition : expr :=
        (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr 1024) tint) tint).

      Definition idpde_init_outter_while_body : statement :=
        (Ssequence
           (Sifthenelse (Ebinop Olt (Etempvar ti tint)
                                (Econst_int (Int.repr 256) tint) tint)
                        (Sset tperm (Econst_int (Int.repr 259) tint))
                        (Sifthenelse (Ebinop Oge (Etempvar ti tint)
                                             (Econst_int (Int.repr 960) tint) tint)
                                     (Sset tperm (Econst_int (Int.repr 259) tint))
                                     (Sset tperm (Econst_int (Int.repr 3) tint))))
           (Ssequence
              (Sset tj (Econst_int (Int.repr 0) tint))
              (Ssequence
                 (Swhile idpde_init_inner_while_condition idpde_init_inner_while_body)
                 (Sset ti
                       (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint)
                               tint))))).


      Definition idpde_init_body : statement := 
        (Ssequence
           (Scall None (Evar container_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
                  ((Etempvar tmbi_adr tint) :: nil))
           (Ssequence
              (Sset ti (Econst_int (Int.repr 0) tint))
              (Swhile idpde_init_outter_while_condition idpde_init_outter_while_body))).

      Definition f_idpde_init := {|
                                 fn_return := Tvoid;
                                 fn_callconv := cc_default;
                                 fn_vars := nil;
                                 fn_params := ((tmbi_adr, tint) :: nil);
                                 fn_temps := ((ti, tint) :: (tj, tint) :: (tperm, tint) :: nil);
                                 fn_body := idpde_init_body
                               |}.