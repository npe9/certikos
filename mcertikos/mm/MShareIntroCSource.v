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
(*                                                                     *)
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

Definition tpid1 : ident := 1%positive.
Definition tpid2 : ident := 2%positive.
Definition tvadr : ident := 3%positive.

Definition shared_mem_to_pending_body : statement := 
(Ssequence
  (Scall None
    (Evar set_shared_mem_state (Tfunction
                                  (Tcons tint
                                    (Tcons tint (Tcons tint Tnil))) tvoid
                                  cc_default))
    ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
     (Econst_int (Int.repr 1) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar set_shared_mem_seen (Tfunction
                                         (Tcons tint
                                           (Tcons tint (Tcons tint Tnil)))
                                         tvoid cc_default))
      ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
       (Econst_int (Int.repr 1) tint) :: nil))
    (Scall None
        (Evar set_shared_mem_loc (Tfunction
                                         (Tcons tint
                                           (Tcons tint (Tcons tint Tnil)))
                                         tvoid cc_default))
        ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
         (Etempvar tvadr tint) :: nil)))).


Definition f_shared_mem_to_pending := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((tpid1, tint) :: (tpid2, tint) :: (tvadr, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := shared_mem_to_pending_body

|}.

Definition tdest_va : ident := 5%positive.
Definition tdest_va' : ident := 6%positive.
Definition tres : ident := 7%positive.
Definition tres' : ident := 8%positive.


(**
<<

    #define MAGIC_NUMBER 1048577

    #define READY 0

    #define SEEN 1
    #define UNSEEN 0

    int shared_mem_to_ready(int pid1, int pid2, int vadr)
    {
        int dest_va = get_shared_mem_loc(pid2, pid1);

        int res = pt_resv2(pid1, vadr, 7, pid2, dest_va, 7);

        if(res == MAGIC_NUMBER) {/* NOP */}
        else { /* res != MAGIC_NUMBER */
            set_shared_mem_state(pid1, pid2, READY);
            set_shared_mem_seen(pid1, pid2, SEEN);
            set_shared_mem_loc(pid1, pid2, 0);

            set_shared_mem_state(pid2, pid1, READY);
            set_shared_mem_seen(pid2, pid1, UNSEEN);
            set_shared_mem_loc(pid2, pid1, 0);
        }

        return res;
    }


>>
*)
Definition shared_mem_to_ready_body : statement :=
(Ssequence
  (Ssequence
    (Scall (Some tdest_va')
      (Evar get_shared_mem_loc (Tfunction
                                       (Tcons tint (Tcons tint Tnil)) tint
                                       cc_default))
      ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) :: nil))
    (Sset tdest_va (Etempvar tdest_va' tint)))
  (Ssequence
    (Ssequence
      (Scall (Some tres')
        (Evar pt_resv2 (Tfunction
                          (Tcons tint
                            (Tcons tint
                              (Tcons tint
                                (Tcons tint (Tcons tint (Tcons tint Tnil))))))
                          tint cc_default))
        ((Etempvar tpid1 tint) :: (Etempvar tvadr tint) ::
         (Econst_int (Int.repr 7) tint) :: (Etempvar tpid2 tint) ::
         (Etempvar tdest_va tint) :: (Econst_int (Int.repr 7) tint) :: nil))
      (Sset tres (Etempvar tres' tint)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar tres tint)
                     (Econst_int (Int.repr 1048577) tint) tint)
        Sskip
      (Ssequence
        (Scall None
          (Evar set_shared_mem_state (Tfunction
                                        (Tcons tint
                                          (Tcons tint (Tcons tint Tnil)))
                                        tvoid cc_default))
          ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
           (Econst_int (Int.repr 0) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar set_shared_mem_seen (Tfunction
                                               (Tcons tint
                                                 (Tcons tint
                                                   (Tcons tint Tnil)))
                                               tvoid cc_default))
            ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
             (Econst_int (Int.repr 1) tint) :: nil))
          (Ssequence 
              (Scall None
                (Evar set_shared_mem_loc (Tfunction
                                                   (Tcons tint
                                                     (Tcons tint
                                                       (Tcons tint Tnil)))
                                                   tvoid cc_default))
                ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar set_shared_mem_state (Tfunction
                                            (Tcons tint
                                              (Tcons tint
                                                (Tcons tint Tnil))) tvoid
                                            cc_default))
              ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar set_shared_mem_seen (Tfunction
                                                   (Tcons tint
                                                     (Tcons tint
                                                       (Tcons tint Tnil)))
                                                   tvoid cc_default))
                ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Scall None
                (Evar set_shared_mem_loc (Tfunction
                                                   (Tcons tint
                                                     (Tcons tint
                                                       (Tcons tint Tnil)))
                                                   tvoid cc_default))
                ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
                                       (Econst_int (Int.repr 0) tint) :: nil)))))))
      )
      (Sreturn (Some (Etempvar tres tint))))
  )).
(* 
(Ssequence
  (Ssequence
    (Scall (Some dest_va')
      (Evar get_shared_mem_loc (Tfunction
                                       (Tcons tint (Tcons tint Tnil)) tint
                                       cc_default))
      ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) :: nil))
    (Sset dest_va (Etempvar dest_va' tint)))
  (Ssequence
    (Scall None
      (Evar pt_resv2 (Tfunction
                        (Tcons tint
                          (Tcons tint
                            (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil))))))
                        tint cc_default))
      ((Etempvar tpid1 tint) :: (Etempvar tvadr tint) :: (Econst_int (Int.repr 7) tint) ::
       (Etempvar tpid2 tint) :: (Etempvar dest_va tint) :: (Econst_int (Int.repr 7) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar set_shared_mem_state (Tfunction
                                      (Tcons tint
                                        (Tcons tint (Tcons tint Tnil)))
                                      tvoid cc_default))
        ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
         (Econst_int (Int.repr 0) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar set_shared_mem_seen (Tfunction
                                             (Tcons tint
                                               (Tcons tint
                                                 (Tcons tint Tnil))) tvoid
                                             cc_default))
          ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar set_shared_mem_state (Tfunction
                                          (Tcons tint
                                            (Tcons tint (Tcons tint Tnil)))
                                          tvoid cc_default))
            ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Scall None
            (Evar set_shared_mem_seen (Tfunction
                                               (Tcons tint
                                                 (Tcons tint
                                                   (Tcons tint Tnil)))
                                               tvoid cc_default))
            ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
             (Econst_int (Int.repr 0) tint) :: nil))))))).
*)

Definition f_shared_mem_to_ready := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((tpid1, tint) :: (tpid2, tint) :: (tvadr, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((tdest_va, tint) :: (tdest_va', tint) :: (tres, tint) ::
              (tres', tint) :: nil);
  fn_body := shared_mem_to_ready_body
|}.



Definition shared_mem_to_dead_body : statement :=
(Ssequence
  (Scall None
    (Evar set_shared_mem_state (Tfunction
                                  (Tcons tint
                                    (Tcons tint (Tcons tint Tnil))) tvoid
                                  cc_default))
    ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
     (Econst_int (Int.repr 2) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar set_shared_mem_seen (Tfunction
                                         (Tcons tint
                                           (Tcons tint (Tcons tint Tnil)))
                                         tvoid cc_default))
      ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
       (Econst_int (Int.repr 1) tint) :: nil))
    (Ssequence
       (Scall None
              (Evar set_shared_mem_loc (Tfunction
                                           (Tcons tint
                                                  (Tcons tint (Tcons tint Tnil)))
                                           tvoid cc_default))
              ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) ::
                                     (Econst_int (Int.repr 0) tint) :: nil))
       (Ssequence
          (Scall None
                 (Evar set_shared_mem_state (Tfunction
                                               (Tcons tint
                                                      (Tcons tint (Tcons tint Tnil)))
                                               tvoid cc_default))
                 ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
                                        (Econst_int (Int.repr 2) tint) :: nil))
          (Ssequence
             (Scall None
                    (Evar set_shared_mem_seen (Tfunction
                                                 (Tcons tint
                                                        (Tcons tint
                                                            (Tcons tint Tnil))) tvoid
                                                 cc_default))
                    ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
                                           (Econst_int (Int.repr 0) tint) :: nil))
             (Scall None
                    (Evar set_shared_mem_loc (Tfunction
                                                 (Tcons tint
                                                        (Tcons tint
                                                            (Tcons tint Tnil))) tvoid
                                                 cc_default))
                    ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) ::
                                           (Econst_int (Int.repr 0) tint) :: nil))))))).

Definition f_shared_mem_to_dead := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((tpid1, tint) :: (tpid2, tint) :: (tvadr, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := shared_mem_to_dead_body
|}.


Definition tds_state : ident := 9%positive.

Definition get_shared_mem_status_seen_body : statement := 
  (Ssequence
     (Scall (Some tds_state)
            (Evar get_shared_mem_state (Tfunction
                                          (Tcons tint (Tcons tint Tnil)) tint
                                          cc_default))
            ((Etempvar tpid2 tint) :: (Etempvar tpid1 tint) :: nil))
  (Ssequence
     (Sifthenelse (Ebinop Oeq (Etempvar tds_state tint) (Econst_int (Int.repr 1) tint) tint)
         (Sset tres (Econst_int (Int.repr 1) tint))

         (Scall (Some tres)
                (Evar get_shared_mem_state (Tfunction
                                              (Tcons tint (Tcons tint Tnil)) tint
                                              cc_default))
                ((Etempvar tpid1 tint) :: (Etempvar tpid2 tint) :: nil))
     )

     (Sreturn (Some (Etempvar tres tint)))
  )
  ).


Definition f_get_shared_mem_status_seen := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((tpid1, tint) :: (tpid2, tint) :: nil);
  fn_vars := nil;
  fn_temps := (tds_state, tint) :: (tres, tint) :: nil;
  fn_body := get_shared_mem_status_seen_body

|}.





(**
<<

    #define num_proc 64

    extern void clear_shared_mem(unsigned int, unsigned int);
    extern void pmap_init(unsigned int);

    void shared_mem_init(unsigned int mbi_adr)
    { 
      unsigned int i, j;
      pmap_init(mbi_adr);
      i = 0;
      while (i < num_proc)
      { 
        j = 0;
        while (j < num_proc)
        {
          clear_shared_mem(i, j);
          j ++;
        } 
        i ++;
      } 
    }

>>
*)

Definition _mbi_adr := 10 % positive.
Definition _i := 11 % positive.
Definition _j := 12 % positive.

Definition shared_mem_init_inner_while_condition :=
  (Ebinop Olt (Etempvar _j tuint) (Econst_int (Int.repr 64) tint) tint).

Definition shared_mem_init_inner_while_body :=
  (Ssequence
              (Scall None
                (Evar clear_shared_mem (Tfunction
                                          (Tcons tuint (Tcons tuint Tnil))
                                          tvoid cc_default))
                ((Etempvar _i tuint) :: (Etempvar _j tuint) :: nil))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tuint)
                  (Econst_int (Int.repr 1) tint) tuint))).

Definition shared_mem_init_outter_while_condition :=
  (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 64) tint) tint).

Definition shared_mem_init_outter_while_body :=
  (Ssequence
        (Sset _j (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Swhile shared_mem_init_inner_while_condition shared_mem_init_inner_while_body)
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint)))).

Definition shared_mem_init_body :=
  (Ssequence
  (Scall None
    (Evar pmap_init (Tfunction (Tcons tuint Tnil) tvoid cc_default))
    ((Etempvar _mbi_adr tuint) :: nil))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Swhile shared_mem_init_outter_while_condition shared_mem_init_outter_while_body)
  )).


Definition f_shared_mem_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mbi_adr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_j, tuint) :: nil);
  fn_body := shared_mem_init_body
|}.
