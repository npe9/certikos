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
      #define num_chan 64
      
      extern void sched_init(unsigned int);
      extern void init_sync_chan(unsigned int);
      
      void proc_init(unsigned int mbi_adr)
      {
          unsigned int i;
          sched_init(mbi_adr);
          i = 0;
          while(i < num_chan)
          {
              init_sync_chan(i);
              i++;
          }
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let ti: ident := 6.
Let tmbi_adr: ident := 7.

Local Open Scope Z_scope.


Definition proc_init_while_condition : expr := (Ebinop Olt (Etempvar ti tint) (Econst_int (Int.repr num_chan) tint) tint).

Definition proc_init_while_body : statement := 
  (Ssequence
     (Scall None (Evar init_sync_chan (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar ti tint) :: nil))
     (Sset ti
           (Ebinop Oadd (Etempvar ti tint) (Econst_int (Int.repr 1) tint) tint))).

Definition proc_init_body : statement := 
  (Ssequence
     (Scall None (Evar sched_init (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Etempvar tmbi_adr tint) :: nil))
     (Ssequence
        (Sset ti (Econst_int (Int.repr 0) tint))
        (Swhile proc_init_while_condition proc_init_while_body))).

Definition f_proc_init := {|
                           fn_return := tvoid;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tmbi_adr, tint) :: nil);
                           fn_temps := ((ti, tint) :: nil);
                           fn_body := proc_init_body
                         |}.


(**
<<

#define MAX_BUFFSIZE 1024
#define NUM_CHAN     64

extern unsigned int get_curid(void);
extern unsigned int get_state(unsigned int pidx);

extern void set_sync_chan_paddr(unsigned int chanid, unsigned int paddr);
extern void set_sync_chan_to(unsigned int chanid, unsigned int to);
extern void set_sync_chan_count(unsigned int chanid, unsigned int count);

extern unsigned int get_sync_chan_to(unsigned int chanid);

extern unsigned int get_kernel_pa(unsigned int pid, unsigned int vaddr);

unsigned int
syncsendto_chan_pre(unsigned int pid, unsigned int vaddr, unsigned int scount)
{
  unsigned int myid = get_curid();
  unsigned int target_state = get_state(pid);

  if (target_state == 3) return MAX_BUFFSIZE+2;

  if (0 <= pid && pid < NUM_CHAN) {
    unsigned int sender_kpa = get_kernel_pa(myid, vaddr);

    if (scount < MAX_BUFFSIZE) {
      set_sync_chan_paddr(myid, sender_kpa);
      set_sync_chan_count(myid, scount);
    } else {
      set_sync_chan_paddr(myid, sender_kpa);
      set_sync_chan_count(myid, MAX_BUFFSIZE);
    }

    if (get_sync_chan_to(myid) == NUM_CHAN) {
      set_sync_chan_to(myid, pid);
    } else {
      // Should Crash
    }

    return 0;
  } else {
    return MAX_BUFFSIZE+1;
  }
}

>>
 *)

Local Open Scope positive_scope.

Definition pid                 : ident := 8.
Definition myid                : ident := 11.
Definition target_state        : ident := 12.
Definition scount              : ident := 16.
Definition sender_kpa          : ident := 17.
Definition vaddr               : ident := 18.
Definition sender_kpa'         : ident := 22.
Definition target_state'       : ident := 23.
Definition myid'               : ident := 24.
Definition syncsendto_chan_pre_tmp1 : ident := 25.
Definition syncsendto_chan_pre_tmp2 : ident := 26.

Definition syncsendto_chan_pre_body : statement :=
(Ssequence
  (Ssequence
    (Scall (Some target_state')
      (Evar get_state (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar pid tint) :: nil))
    (Sset target_state (Etempvar target_state' tint)))
  (Sifthenelse (Ebinop Oeq (Etempvar target_state tint)
                 (Econst_int (Int.repr 3) tint) tint)
    (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1024) tint)
                     (Econst_int (Int.repr 2) tint) tint)))
    (Ssequence
      (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tint)
                     (Etempvar pid tint) tint)
        (Ssequence
          (Sset syncsendto_chan_pre_tmp2
            (Ecast
              (Ebinop Olt (Etempvar pid tint)
                (Econst_int (Int.repr 64) tint) tint) tbool))
          (Sset syncsendto_chan_pre_tmp2 (Ecast (Etempvar syncsendto_chan_pre_tmp2 tbool) tint)))
        (Sset syncsendto_chan_pre_tmp2 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar syncsendto_chan_pre_tmp2 tint)
        (Ssequence
          (Ssequence
            (Scall (Some myid')
              (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
            (Sset myid (Etempvar myid' tint)))
          (Ssequence
            (Ssequence
              (Scall (Some sender_kpa')
                (Evar get_kernel_pa (Tfunction
                                       (Tcons tint (Tcons tint Tnil)) tint
                                       cc_default))
                ((Etempvar myid tint) :: (Etempvar vaddr tint) :: nil))
              (Sset sender_kpa (Etempvar sender_kpa' tint)))
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar scount tint)
                             (Econst_int (Int.repr 1024) tint) tint)
                (Ssequence
                  (Scall None
                    (Evar set_sync_chan_paddr (Tfunction
                                                 (Tcons tint
                                                   (Tcons tint Tnil)) tvoid
                                                 cc_default))
                    ((Etempvar myid tint) ::
                     (Etempvar sender_kpa tint) :: nil))
                  (Scall None
                    (Evar set_sync_chan_count (Tfunction
                                                 (Tcons tint
                                                   (Tcons tint Tnil)) tvoid
                                                 cc_default))
                    ((Etempvar myid tint) :: (Etempvar scount tint) ::
                     nil)))
                (Ssequence
                  (Scall None
                    (Evar set_sync_chan_paddr (Tfunction
                                                 (Tcons tint
                                                   (Tcons tint Tnil)) tvoid
                                                 cc_default))
                    ((Etempvar myid tint) ::
                     (Etempvar sender_kpa tint) :: nil))
                  (Scall None
                    (Evar set_sync_chan_count (Tfunction
                                                 (Tcons tint
                                                   (Tcons tint Tnil)) tvoid
                                                 cc_default))
                    ((Etempvar myid tint) ::
                     (Econst_int (Int.repr 1024) tint) :: nil))))
              (Ssequence
                (Ssequence
                  (Scall (Some syncsendto_chan_pre_tmp1)
                    (Evar get_sync_chan_to (Tfunction (Tcons tint Tnil)
                                              tint cc_default))
                    ((Etempvar myid tint) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar syncsendto_chan_pre_tmp1 tint)
                                 (Econst_int (Int.repr 64) tint) tint)
                    (Scall None
                      (Evar set_sync_chan_to (Tfunction
                                                (Tcons tint
                                                  (Tcons tint Tnil)) tvoid
                                                cc_default))
                      ((Etempvar myid tint) :: (Etempvar pid tint) ::
                       nil))
                    Sskip))
                (Sreturn (Some (Etempvar myid tint)))))))
        (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1024) tint)
                         (Econst_int (Int.repr 1) tint) tint))))))).


Definition f_syncsendto_chan_pre := {|
                                    fn_return := tint;
                                    fn_callconv := cc_default;
                                    fn_params := ((pid, tint) :: (vaddr, tint) :: (scount, tint) :: nil);
                                    fn_vars := nil;
                                    fn_temps := ((myid, tint) :: (target_state, tint) ::
                                                 (sender_kpa, tint) :: (syncsendto_chan_pre_tmp2, tint) ::
                                                 (syncsendto_chan_pre_tmp1, tint) :: (sender_kpa', tint) ::
                                                 (target_state', tint) :: (myid', tint) :: nil);
                                    fn_body := syncsendto_chan_pre_body
                                    |}.


(**
<<
#define NUM_CHAN 64
#define MAX_BUFFSIZE 1024

extern unsigned int get_curid(void);
extern unsigned int get_sync_chan_to(unsigned int chanid);
extern unsigned int get_sync_chan_count(unsigned int chanid);
extern void set_sync_chan_to(unsigned int chanid, unsigned int to);

unsigned int
syncsendto_chan_post(void)
{
  unsigned int myid = get_curid();
  unsigned int to = get_sync_chan_to(myid);

  if (to == NUM_CHAN) {
    return get_sync_chan_count(myid);
  } else {
    set_sync_chan_to(myid, NUM_CHAN);
    return MAX_BUFFSIZE+3;
  }
}
>>
 *)

Local Open Scope positive_scope.

Definition to  : ident := 27.
Definition syncsendto_chan_post_tmp := 29.

Definition syncsendto_chan_post_body : statement :=
(Ssequence
    (Scall (Some myid) (Evar get_curid (Tfunction Tnil tint cc_default))
      nil)
  (Ssequence
      (Scall (Some to)
        (Evar get_sync_chan_to (Tfunction (Tcons tint Tnil) tint
                                  cc_default))
        ((Etempvar myid tint) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar to tint)
                   (Econst_int (Int.repr 64) tint) tint)
      (Ssequence
        (Scall (Some syncsendto_chan_post_tmp)
          (Evar get_sync_chan_count (Tfunction (Tcons tint Tnil) tint
                                       cc_default))
          ((Etempvar myid tint) :: nil))
        (Sreturn (Some (Etempvar syncsendto_chan_post_tmp tint))))
      (Ssequence
        (Scall None
          (Evar set_sync_chan_to (Tfunction (Tcons tint (Tcons tint Tnil))
                                    tvoid cc_default))
          ((Etempvar myid tint) :: (Econst_int (Int.repr 64) tint) :: nil))
        (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1024) tint)
                         (Econst_int (Int.repr 3) tint) tint))))))).

Definition f_syncsendto_chan_post := {|
                                        fn_return := tint;
                                        fn_callconv := cc_default;
                                        fn_params := nil;
                                        fn_vars := nil;
                                        fn_temps := ((myid, tint) :: (to, tint) :: (syncsendto_chan_post_tmp, tint) :: nil);
                                        fn_body := syncsendto_chan_post_body
                                     |}.
 



(**
<<
#define NUM_CHAN 64
#define TCB_STATE_DEAD 3
#define MAX_BUFFSIZE 1024

extern unsigned int get_curid(void);
extern unsigned int get_state(unsigned int pid);

extern unsigned int get_sync_chan_to(unsigned int chanid);
extern unsigned int get_sync_chan_count(unsigned int chanid);
extern unsigned int get_sync_chan_paddr(unsigned int chanid);

extern unsigned int get_kernel_pa(unsigned int pid, unsigned int vaddr);

extern void set_sync_chan_to(unsigned int chanid, unsigned int to);
extern void set_sync_chan_count(unsigned int chanid, unsigned int count);
extern void set_sync_chan_paddr(unsigned int chanid, unsigned int paddr);

extern void flatmem_copy(unsigned int len, unsigned int to, unsigned int from);
extern void thread_wakeup(unsigned int pid);

unsigned int
syncreceive_chan(unsigned int pid, unsigned int vaddr, unsigned int rcount)
{
  unsigned int myid = get_curid();
  unsigned int sender_state = get_state(pid);

  if (sender_state == TCB_STATE_DEAD) {

    return MAX_BUFFSIZE+2;

  } else {

    unsigned int sender_to = get_sync_chan_to(pid);

    if (sender_to == myid) {
      unsigned int sender_count = get_sync_chan_count(pid);
      unsigned int sbuffpa = get_sync_chan_paddr(pid);

      unsigned int arecvcount = (sender_count < rcount) ? sender_count : rcount;

      unsigned int rbuffva = vaddr;

      unsigned int rbuffpa = get_kernel_pa(myid, rbuffva);

      flatmem_copy(arecvcount, rbuffpa, sbuffpa);

      set_sync_chan_to(pid, NUM_CHAN);
      set_sync_chan_paddr(pid, 0);
      set_sync_chan_count(pid, arecvcount);

      thread_wakeup(pid);

      return arecvcount;

    } else {
      return MAX_BUFFSIZE+3;
    }
  }
}
>>
 *)

Local Open Scope positive_scope.

Definition rcount        : ident := 33.
Definition rbuffva       : ident := 34.
Definition sender_count  : ident := 35.
Definition sender_state  : ident := 37.
Definition arecvcount    : ident := 39.
Definition rbuffpa       : ident := 40.
Definition sbuffpa       : ident := 41.
Definition sender_to     : ident := 42.
Definition sbuffpa'      : ident := 43.
Definition arecvcount'   : ident := 44.
Definition sender_count' : ident := 45.
Definition sender_to'    : ident := 46.
Definition rbuffpa'      : ident := 47.
Definition sender_state' : ident := 48.

Definition syncreceive_chan_body : statement := 
(Ssequence
  (Ssequence
    (Scall (Some myid') (Evar get_curid (Tfunction Tnil tint cc_default))
      nil)
    (Sset myid (Etempvar myid' tint)))
  (Ssequence
    (Ssequence
      (Scall (Some sender_state')
        (Evar get_state (Tfunction (Tcons tint Tnil) tint cc_default))
        ((Etempvar pid tint) :: nil))
      (Sset sender_state (Etempvar sender_state' tint)))
    (Sifthenelse (Ebinop Oeq (Etempvar sender_state tint)
                   (Econst_int (Int.repr 3) tint) tint)
      (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1024) tint)
                       (Econst_int (Int.repr 2) tint) tint)))
      (Ssequence
        (Ssequence
          (Scall (Some sender_to')
            (Evar get_sync_chan_to (Tfunction (Tcons tint Tnil) tint
                                      cc_default))
            ((Etempvar pid tint) :: nil))
          (Sset sender_to (Etempvar sender_to' tint)))
        (Sifthenelse (Ebinop Oeq (Etempvar sender_to tint)
                       (Etempvar myid tint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some sender_count')
                (Evar get_sync_chan_count (Tfunction (Tcons tint Tnil)
                                             tint cc_default))
                ((Etempvar pid tint) :: nil))
              (Sset sender_count (Etempvar sender_count' tint)))
            (Ssequence
              (Ssequence
                (Scall (Some sbuffpa')
                  (Evar get_sync_chan_paddr (Tfunction (Tcons tint Tnil)
                                               tint cc_default))
                  ((Etempvar pid tint) :: nil))
                (Sset sbuffpa (Etempvar sbuffpa' tint)))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar sender_count tint)
                                 (Etempvar rcount tint) tint)
                    (Sset arecvcount'
                      (Ecast (Etempvar sender_count tint) tint))
                    (Sset arecvcount'
                      (Ecast (Etempvar rcount tint) tint)))
                  (Sset arecvcount (Etempvar arecvcount' tint)))
                  (Ssequence
                    (Sset rbuffva (Etempvar vaddr tint))
                    (Ssequence
                      (Ssequence
                        (Scall (Some rbuffpa')
                          (Evar get_kernel_pa (Tfunction
                                                 (Tcons tint
                                                   (Tcons tint Tnil)) tint
                                                 cc_default))
                          ((Etempvar myid tint) ::
                           (Etempvar rbuffva tint) :: nil))
                        (Sset rbuffpa (Etempvar rbuffpa' tint)))
                      (Ssequence
                        (Scall None
                          (Evar flatmem_copy (Tfunction
                                                (Tcons tint
                                                (Tcons tint
                                                  (Tcons tint
                                                    Tnil)))
                                                tvoid cc_default))
                          ((Etempvar arecvcount tint) :: ((Etempvar sbuffpa tint) ::
                           ((Etempvar rbuffpa tint) ::
                           nil))))
                        (Ssequence
                          (Scall None
                            (Evar set_sync_chan_to (Tfunction
                                                      (Tcons tint
                                                        (Tcons tint Tnil))
                                                      tvoid cc_default))
                            ((Etempvar pid tint) ::
                             (Econst_int (Int.repr 64) tint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar set_sync_chan_paddr (Tfunction
                                                           (Tcons tint
                                                             (Tcons tint
                                                               Tnil)) tvoid
                                                           cc_default))
                              ((Etempvar pid tint) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar set_sync_chan_count (Tfunction
                                                             (Tcons tint
                                                               (Tcons tint
                                                                 Tnil)) tvoid
                                                             cc_default))
                                ((Etempvar pid tint) ::
                                 (Etempvar arecvcount tint) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar thread_wakeup (Tfunction
                                                         (Tcons tint Tnil)
                                                         tvoid cc_default))
                                  ((Etempvar pid tint) :: nil))
                                (Sreturn (Some (Etempvar arecvcount tint)))))))))))))
          (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1024) tint)
                           (Econst_int (Int.repr 3) tint) tint)))))))).


Definition f_syncreceive_chan :={|
                                  fn_return := tint;
                                  fn_callconv := cc_default;
                                  fn_params := ((pid, tint) :: (vaddr, tint) :: (rcount, tint) :: nil);
                                  fn_vars := nil;
                                  fn_temps := ((myid, tint) :: (sender_to, tint) ::
                                               (sender_state, tint) :: (sender_count, tint) ::
                                               (sbuffpa, tint) :: (arecvcount, tint) ::
                                               (rbuffva, tint) ::
                                               (rbuffpa, tint) :: (rbuffpa', tint) ::
                                               (arecvcount', tint) :: (sbuffpa', tint) ::
                                               (sender_count', tint) :: (sender_state', tint) ::
                                               (sender_to', tint) :: (myid', tint) :: nil);
                                  fn_body := syncreceive_chan_body
                                |}.
 
