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
(*                        David Costanzo                               *)
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

Definition _id : ident := 1%positive.
Definition _p : ident := 2%positive.
Definition _i : ident := 3%positive.
Definition _mbi : ident := 4%positive.
Definition _n : ident := 5%positive.
Definition t_i : ident := 6%positive.
Definition t_u : ident := 7%positive.
Definition t_q : ident := 8%positive.
Definition t_nc : ident := 9%positive.
Definition t_child : ident := 10%positive.

(*


Definition container_init_while_condition : expr :=
  (Ebinop Olt (Etempvar t_i tuint) (Econst_int (Int.repr num_id) tint) tint).

Definition container_init_while_body : statement :=
  (Ssequence
     (Sassign
        (Efield
           (Ederef
              (Ebinop Oadd
                      (Evar AC_LOC (gvar_info container_loc_type))
                      (Etempvar t_i tint) (tptr t_struct_AC))
              t_struct_AC) AC_used tint)
        (Econst_int (Int.repr 0) tint))
     (Sset t_i
           (Ebinop Oadd (Etempvar t_i tint)
                   (Econst_int (Int.repr 1) tint) tint))).

Definition container_init_body :=
(Ssequence
  (Scall None (Evar boot_loader (Tfunction (Tcons tint Tnil) tvoid cc_default))
    ((Etempvar _mbi tint) :: nil))
  (Ssequence
    (Sassign
      (Efield
        (Ederef
          (Ebinop Oadd
            (Evar AC_LOC (gvar_info container_loc_type))
            (Econst_int (Int.repr 0) tint) (tptr t_struct_AC))
          t_struct_AC) AC_quota tint)
      (Econst_int (Int.repr root_quota) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Evar AC_LOC (gvar_info container_loc_type))
              (Econst_int (Int.repr 0) tint) (tptr t_struct_AC))
            t_struct_AC) AC_usage tint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Econst_int (Int.repr 0) tint)
                (tptr t_struct_AC)) t_struct_AC)
            AC_parent tint) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar AC_LOC (gvar_info container_loc_type))
                  (Econst_int (Int.repr 0) tint)
                  (tptr t_struct_AC)) t_struct_AC)
              AC_nchildren tint) (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Evar AC_LOC (gvar_info container_loc_type))
                    (Econst_int (Int.repr 0) tint)
                    (tptr t_struct_AC)) t_struct_AC)
                AC_used tint) (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset t_i (Econst_int (Int.repr 1) tint))
              (Swhile
                container_init_while_condition
                container_init_while_body)))))))).

Definition f_container_init :=
  {|
    fn_return := tvoid;
    fn_callconv := cc_default;
    fn_params := ((_mbi, tint) :: nil);
    fn_vars := nil;
    fn_temps := ((t_i, tint) :: nil);
    fn_body := container_init_body
  |}.
*)

(**
<<
        extern void mem_init(unsigned int);
        extern unsigned int get_nps(void);
        extern unsigned int is_norm(unsigned int);
        extern unsigned int at_get(unsigned int);

        void container_init(unsigned int mbi_addr)
        {
          unsigned int nps, real_quota, i, norm, used;

          mem_init(mbi_addr);

          nps = get_nps();
          real_quota = 0;
          i = 1;
          while (i < nps) {
            norm = is_norm(i);
            used = at_get(i);
            if (norm == 1 && used == 0)
              real_quota++;
            i++;
          }

          container_LOC[0].quota = real_quota;
          container_LOC[0].usage = 0;
          container_LOC[0].parent = 0;
          container_LOC[0].nchildren = 0;
          container_LOC[0].used = 1;
        }
>>
*)

Let t_nps: ident := 11%positive.
Let t_rq: ident := 12%positive.
Let t_norm: ident := 13%positive.
Let t_used: ident := 14%positive.

Definition container_init_while_condition : expr :=
  Ebinop Olt (Etempvar t_i tint) (Etempvar t_nps tint) tint.

Definition container_init_while_body : statement := 
   Ssequence
     (Scall
        (Some t_norm)
        (Evar is_norm (Tfunction (Tcons tint Tnil) tint cc_default)) 
        (Etempvar t_i tint :: nil))
     (Ssequence
        (Scall
           (Some t_used)
           (Evar at_get (Tfunction (Tcons tint Tnil) tint cc_default)) 
           (Etempvar t_i tint :: nil))
        (Ssequence
           (Sifthenelse
              (Ebinop Oand
                 (Ebinop Oeq (Etempvar t_norm tint) (Econst_int (Int.repr 1) tint) tint)
                 (Ebinop Oeq (Etempvar t_used tint) (Econst_int (Int.repr 0) tint) tint) tint)
              (Sset t_rq
                 (Ebinop Oadd (Etempvar t_rq tint) 
                              (Econst_int (Int.repr 1) tint) tint))
              Sskip)
           (Sset t_i
              (Ebinop Oadd (Etempvar t_i tint) 
                           (Econst_int (Int.repr 1) tint) tint)))).

Definition container_init_body :=
 Ssequence
  (Scall None (Evar mem_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
    ((Etempvar _mbi tint) :: nil))
  (Ssequence
    (Scall (Some t_nps) (Evar get_nps (Tfunction Tnil tint cc_default)) nil)
    (Ssequence
       (Sset t_rq (Econst_int (Int.repr 0) tint))
       (Ssequence
          (Sset t_i (Econst_int (Int.repr 1) tint))
          (Ssequence
             (Swhile 
                container_init_while_condition
                container_init_while_body)
             (Ssequence
                (Sassign
                   (Efield
                      (Ederef
                         (Ebinop Oadd
                                 (Evar AC_LOC (gvar_info container_loc_type))
                                 (Econst_int (Int.repr 0) tint) 
                                 (tptr t_struct_AC)) t_struct_AC) 
                      AC_quota tint) (Etempvar t_rq tint))
                (Ssequence
                   (Sassign
                      (Efield
                         (Ederef
                            (Ebinop Oadd
                                    (Evar AC_LOC (gvar_info container_loc_type))
                                    (Econst_int (Int.repr 0) tint) 
                                    (tptr t_struct_AC)) t_struct_AC) 
                         AC_usage tint) (Econst_int (Int.repr 0) tint))
                   (Ssequence
                      (Sassign
                         (Efield
                            (Ederef
                               (Ebinop Oadd
                                       (Evar AC_LOC (gvar_info container_loc_type))
                                       (Econst_int (Int.repr 0) tint)
                                       (tptr t_struct_AC)) t_struct_AC)
                            AC_parent tint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                         (Sassign
                            (Efield
                               (Ederef
                                  (Ebinop Oadd
                                          (Evar AC_LOC (gvar_info container_loc_type))
                                          (Econst_int (Int.repr 0) tint)
                                          (tptr t_struct_AC)) t_struct_AC)
                               AC_nchildren tint) (Econst_int (Int.repr 0) tint))
                         (Sassign
                            (Efield
                               (Ederef
                                  (Ebinop Oadd
                                          (Evar AC_LOC (gvar_info container_loc_type))
                                          (Econst_int (Int.repr 0) tint)
                                          (tptr t_struct_AC)) t_struct_AC)
                               AC_used tint) (Econst_int (Int.repr 1) tint)))))))))).

Definition f_container_init :=
  {|
    fn_return := tvoid;
    fn_callconv := cc_default;
    fn_params := (_mbi, tint) :: nil;
    fn_vars := nil;
    fn_temps := (t_nps, tint) :: (t_rq, tint) :: (t_i, tint) :: 
                (t_norm, tint) :: (t_used, tint) ::nil;
    fn_body := container_init_body
  |}.

(** 
<<
      unsigned int container_get_parent(unsigned int id)
      {
          return container_LOC[id].parent;
      }
>>
 *)
Definition container_get_parent_body := 
  (Sreturn (Some (Efield
        (Ederef (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Etempvar _id tint) (tptr t_struct_AC))
                           t_struct_AC) AC_parent tint))).

Definition f_container_get_parent := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := ((_id, tint) :: nil);
    fn_vars := nil;
    fn_temps := nil;
    fn_body := container_get_parent_body     
  |}.

(** 
<<
      unsigned int container_get_nchildren(unsigned int id)
      {
          return container_LOC[id].nchildren;
      }
>>
 *)
Definition container_get_nchildren_body := 
  (Sreturn (Some (Efield
        (Ederef (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Etempvar _id tint) (tptr t_struct_AC))
                           t_struct_AC) AC_nchildren tint))).

Definition f_container_get_nchildren := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := ((_id, tint) :: nil);
    fn_vars := nil;
    fn_temps := nil;
    fn_body := container_get_nchildren_body     
  |}.

(** 
<<
     unsigned int container_get_quota(unsigned int id)
     {
         return container_LOC[id].quota;
     }

>>
 *)
Definition container_get_quota_body := 
  (Sreturn (Some (Efield
        (Ederef (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Etempvar _id tint) (tptr t_struct_AC))
                           t_struct_AC) AC_quota tint))).

Definition f_container_get_quota := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := ((_id, tint) :: nil);
    fn_vars := nil;
    fn_temps := nil;
    fn_body := container_get_quota_body     
  |}.

(** 
<<
      unsigned int container_get_usage(unsigned int id)
      {
          return container_LOC[id].usage;
      }
>>
 *)
Definition container_get_usage_body := 
  (Sreturn (Some (Efield
        (Ederef (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Etempvar _id tint) (tptr t_struct_AC))
                           t_struct_AC) AC_usage tint))).

Definition f_container_get_usage := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := ((_id, tint) :: nil);
    fn_vars := nil;
    fn_temps := nil;
    fn_body := container_get_usage_body     
  |}.

(** 
<<
      unsigned int container_can_consume(unsigned int id, unsigned int n)
      {
          if (container_LOC[id].usage + n > container_LOC[id].quota) return 0;
          return 1;
      }
>>
 *)

Definition container_can_consume_body :=
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _n tint)
       (Efield (Ederef (Ebinop Oadd
                  (Evar AC_LOC (gvar_info container_loc_type))
                  (Etempvar _id tint) (tptr t_struct_AC))
                             t_struct_AC) AC_quota tint) tint)
    (Sifthenelse (Ebinop Ole
       (Efield (Ederef (Ebinop Oadd
                  (Evar AC_LOC (gvar_info container_loc_type))
                  (Etempvar _id tint) (tptr t_struct_AC))
                              t_struct_AC) AC_usage tint)
       (Ebinop Osub
          (Efield (Ederef (Ebinop Oadd
                      (Evar AC_LOC (gvar_info container_loc_type))
                      (Etempvar _id tint) (tptr t_struct_AC))
                                 t_struct_AC) AC_quota tint)
          (Etempvar _n tint) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      Sskip)
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 0) tint)))).

Definition f_container_can_consume := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := ((_id, tint) :: (_n, tint) :: nil);
    fn_vars := nil;
    fn_temps := nil;
    fn_body := container_can_consume_body
  |}.

(**
<<
         #define MAX_CHILDREN 3

         unsigned int container_split(unsigned int id, unsigned int quota)
         {
           unsigned int child, nc;

           nc = container_LOC[id].numChildren;
           child = id * MAX_CHILDREN + 1 + nc;

           container_LOC[child].used = 1;
           container_LOC[child].quota = quota;
           container_LOC[child].usage = 0;
           container_LOC[child].parent = id;
           container_LOC[child].nchildren = 0;

           container_LOC[id].usage += quota;
           container_LOC[id].nchildren = nc + 1;

           return child;
         }
>>
*)

Definition container_split_body :=
  (Ssequence
    (Sset t_nc 
          (Efield
            (Ederef
              (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Etempvar _id tint) (tptr t_struct_AC))
              t_struct_AC) AC_nchildren tint))
    (Ssequence
      (Sset t_child
            (Ebinop Oadd
               (Ebinop Oadd
                  (Ebinop Omul
                     (Etempvar _id tint)
                     (Econst_int (Int.repr max_children) tint) tint)
                  (Econst_int (Int.repr 1) tint) tint)
               (Etempvar t_nc tint) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Etempvar t_child tint) (tptr t_struct_AC))
              t_struct_AC) AC_used tint)
          (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar AC_LOC (gvar_info container_loc_type))
                  (Etempvar t_child tint) (tptr t_struct_AC))
                t_struct_AC) AC_quota tint)
            (Etempvar _n tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Evar AC_LOC (gvar_info container_loc_type))
                    (Etempvar t_child tint) (tptr t_struct_AC))
                  t_struct_AC) AC_usage tint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Evar AC_LOC (gvar_info container_loc_type))
                      (Etempvar t_child tint) (tptr t_struct_AC))
                    t_struct_AC) AC_parent tint)
                (Etempvar _id tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar AC_LOC (gvar_info container_loc_type))
                        (Etempvar t_child tint)
                        (tptr t_struct_AC))
                      t_struct_AC) AC_nchildren tint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar AC_LOC (gvar_info container_loc_type))
                          (Etempvar _id tint)
                          (tptr t_struct_AC))
                        t_struct_AC) AC_usage tint)
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Evar AC_LOC (gvar_info container_loc_type))
                            (Etempvar _id tint)
                            (tptr t_struct_AC))
                          t_struct_AC) AC_usage tint)
                      (Etempvar _n tint) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Evar AC_LOC (gvar_info container_loc_type))
                            (Etempvar _id tint)
                            (tptr t_struct_AC))
                          t_struct_AC) AC_nchildren tint)
                      (Ebinop Oadd
                        (Etempvar t_nc tint)
                        (Econst_int (Int.repr 1) tint) tint))
                    (Sreturn (Some (Etempvar t_child tint)))))))))))).

Definition f_container_split := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := ((_id, tint) :: (_n, tint) :: nil);
    fn_vars := nil;
    fn_temps := (t_child, tint) :: (t_nc, tint) :: nil;
    fn_body := container_split_body
  |}.

(**
<< 
      extern unsigned int palloc(void);

      unsigned int container_alloc(unsigned int id)
      {
          unsigned int u, q, i;
          u = container_LOC[id].usage;
          q = container_LOC[id].quota;
          if (u == q) return 0;

          container_LOC[id].usage = u+1;
          i = palloc();
          return i;
      }
>>
*)

Definition container_alloc_body :=
  Ssequence
  (Sset t_u
    (Efield
      (Ederef
        (Ebinop Oadd
          (Evar AC_LOC (gvar_info container_loc_type))
          (Etempvar _id tint) (tptr t_struct_AC))
        t_struct_AC) AC_usage tint))
  (Ssequence
    (Sset t_q
      (Efield
        (Ederef
          (Ebinop Oadd
            (Evar AC_LOC (gvar_info container_loc_type))
            (Etempvar _id tint) (tptr t_struct_AC))
          t_struct_AC) AC_quota tint))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar t_u tint) (Etempvar t_q tint) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Evar AC_LOC (gvar_info container_loc_type))
                (Etempvar _id tint) (tptr t_struct_AC))
              t_struct_AC) AC_usage tint)
          (Ebinop Oadd (Etempvar t_u tint) (Econst_int (Int.repr 1) tint)
            tint))
        (Ssequence
           (Scall
              (Some t_i)
              (Evar palloc (Tfunction Tnil tint cc_default)) 
              nil)
           (Sreturn (Some (Etempvar t_i tint))))))).

Definition f_container_alloc := 
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := ((_id, tint) :: nil);
    fn_vars := nil;
    fn_temps := ((t_u, tint) :: (t_q, tint) :: (t_i, tint) :: nil);
    fn_body := container_alloc_body
  |}.