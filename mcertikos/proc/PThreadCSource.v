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
      
      struct ChanStruct {
          unsigned int isbusy;
          unsigned int content;
      };
      
      extern struct ChanStruct CHPOOL_LOC[num_chan];
      
      unsigned int get_chan_info(unsigned int chan_index)
      {
          return CHPOOL_LOC[chan_index].isbusy;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tchan_index: ident := 1.

Local Open Scope Z_scope.

Definition get_chan_info_body : statement := 
  (Sreturn (Some (Efield
                    (Ederef
                       (Ebinop Oadd
                               (Evar CHPOOL_LOC (tarray t_struct_Chan num_chan))
                               (Etempvar tchan_index tint) (tptr t_struct_Chan))
                       t_struct_Chan) isbusy tint))).

Definition f_get_chan_info := {|
                               fn_return := tint;
                               fn_callconv := cc_default;
                               fn_vars := nil;
                               fn_params := ((tchan_index, tint) :: nil);
                               fn_temps := nil;
                               fn_body := get_chan_info_body
                             |}.



(** 
<<
      #define num_chan 64
      
      struct ChanStruct {
          unsigned int isbusy;
          unsigned int content;
      };
      
      extern struct ChanStruct CHPOOL_LOC[num_chan];
      
      void set_chan_info(unsigned int chan_index, unsigned int info)
      {
          CHPOOL_LOC[chan_index].isbusy = info;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tinfo: ident := 2.

Local Open Scope Z_scope.

Definition set_chan_info_body : statement := 
  (Sassign
     (Efield
        (Ederef
           (Ebinop Oadd (Evar CHPOOL_LOC (tarray t_struct_Chan num_chan))
                   (Etempvar tchan_index tint) (tptr t_struct_Chan))
           t_struct_Chan) isbusy tint) (Etempvar tinfo tint)).

Definition f_set_chan_info := {|
                               fn_return := tvoid;
                               fn_callconv := cc_default;
                               fn_vars := nil;
                               fn_params := ((tchan_index, tint) :: (tinfo, tint) :: nil);
                               fn_temps := nil;
                               fn_body := set_chan_info_body
                             |}.



(** 
<<
      #define num_chan 64
      
      struct ChanStruct {
          unsigned int isbusy;
          unsigned int content;
      };
      
      extern struct ChanStruct CHPOOL_LOC[num_chan];
      
      unsigned int get_chan_content(unsigned int chan_index)
      {
          return CHPOOL_LOC[chan_index].content;
      }
>>
 *)

Definition get_chan_content_body : statement := 
  (Sreturn (Some (Efield
                    (Ederef
                       (Ebinop Oadd
                               (Evar CHPOOL_LOC (tarray t_struct_Chan num_chan))
                               (Etempvar tchan_index tint) (tptr t_struct_Chan))
                       t_struct_Chan) content tint))).

Definition f_get_chan_content := {|
                                  fn_return := tint;
                                  fn_callconv := cc_default;
                                  fn_vars := nil;
                                  fn_params := ((tchan_index, tint) :: nil);
                                  fn_temps := nil;
                                  fn_body := get_chan_content_body
                                |}.



(** 
<<
      #define num_chan 64
      
      struct ChanStruct {
          unsigned int isbusy;
          unsigned int content;
      };
      
      extern struct ChanStruct CHPOOL_LOC[num_chan];
      
      void set_chan_content(unsigned int chan_index, unsigned int content)
      {
          CHPOOL_LOC[chan_index].content = content;
      }
>>
 *)

(** Function parameters and local temporaries used in the function *)
Local Open Scope positive_scope.
Let tcontent: ident := 3.

Local Open Scope Z_scope.

Definition set_chan_content_body : statement := 
  (Sassign
     (Efield
        (Ederef
           (Ebinop Oadd (Evar CHPOOL_LOC (tarray t_struct_Chan num_chan))
                   (Etempvar tchan_index tint) (tptr t_struct_Chan))
           t_struct_Chan) content tint) (Etempvar tcontent tint)).

Definition f_set_chan_content := {|
                                  fn_return := tvoid;
                                  fn_callconv := cc_default;
                                  fn_vars := nil;
                                  fn_params := ((tchan_index, tint) :: (tcontent, tint) :: nil);
                                  fn_temps := nil;
                                  fn_body := set_chan_content_body
                                |}.



(** 
<<
      #define num_chan 64
      
      struct ChanStruct {
          unsigned int isbusy;
          unsigned int content;
      };
      
      extern struct ChanStruct CHPOOL_LOC[num_chan];
      
      void init_chan(unsigned int chan_index, unsigned int info, unsigned int content)
      {
          CHPOOL_LOC[chan_index].isbusy = info;
          CHPOOL_LOC[chan_index].content = content;
      }
>>
 *)

Definition init_chan_body : statement := 
  (Ssequence
     (Sassign
        (Efield
           (Ederef
              (Ebinop Oadd (Evar CHPOOL_LOC (tarray t_struct_Chan num_chan))
                      (Etempvar tchan_index tint) (tptr t_struct_Chan))
              t_struct_Chan) isbusy tint) (Etempvar tinfo tint))
     (Sassign
        (Efield
           (Ederef
              (Ebinop Oadd (Evar CHPOOL_LOC (tarray t_struct_Chan num_chan))
                      (Etempvar tchan_index tint) (tptr t_struct_Chan))
              t_struct_Chan) content tint) (Etempvar tcontent tint))).

Definition f_init_chan := {|
                           fn_return := tvoid;
                           fn_callconv := cc_default;
                           fn_vars := nil;
                           fn_params := ((tchan_index, tint) :: (tinfo, tint) :: (tcontent, tint) :: nil);
                           fn_temps := nil;
                           fn_body := init_chan_body
                         |}.

(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

void init_sync_chan(unsigned int cid)
{
  SYNCCHPOOL_LOC[cid].to = num_proc;
  SYNCCHPOOL_LOC[cid].vaddr = 0;
  SYNCCHPOOL_LOC[cid].count = 0;
}
>>
  *)

Let tchanid := 4%positive.

Definition init_sync_chan_body : statement := 
  (Ssequence
    (Sassign
      (Efield
        (Ederef
          (Ebinop Oadd (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
            (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
          t_struct_SyncIPCChan) to tint) (Econst_int (Int.repr num_chan) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
              (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
            t_struct_SyncIPCChan) paddr tint) (Econst_int (Int.repr 0) tint))
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
              (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
            t_struct_SyncIPCChan) count tint) (Econst_int (Int.repr 0) tint)))).

Definition f_init_sync_chan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := init_sync_chan_body
|}.


(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

void set_sync_chan_to(unsigned int tchanid, unsigned int toval)
{
  SYNCCHPOOL_LOC[tchanid].to = toval;
}
>>
 *)

Let toval := 5%positive.

Definition set_sync_chan_to_body : statement :=
  (Sassign
    (Efield
      (Ederef
        (Ebinop Oadd (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
          (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
        t_struct_SyncIPCChan) to tint) (Etempvar toval tint)).


Definition f_set_sync_chan_to := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: (toval, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := set_sync_chan_to_body
|}.


(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

unsigned int get_sync_chan_to(unsigned int tchanid)
{
  return SYNCCHPOOL_LOC[tchanid].to;
}
>>
 *)
Definition get_sync_chan_to_body : statement :=
  (Sreturn (Some (Efield
                   (Ederef
                     (Ebinop Oadd
                       (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
                       (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
                     t_struct_SyncIPCChan) to tint))).

Definition f_get_sync_chan_to := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := get_sync_chan_to_body
|}.

(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int paddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

void set_sync_chan_paddr(unsigned int tchanid, unsigned int paddrval)
{
  SYNCCHPOOL_LOC[tchanid].paddr = paddrval;
}
>>
 *)

Let paddrval := 6%positive.

Definition set_sync_chan_paddr_body : statement :=
  (Sassign
    (Efield
      (Ederef
        (Ebinop Oadd (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
          (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
        t_struct_SyncIPCChan) paddr tint) (Etempvar paddrval tint)).

Definition f_set_sync_chan_paddr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: (paddrval, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := set_sync_chan_paddr_body
|}.



(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int paddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

unsigned int get_sync_chan_paddr(unsigned int tchanid)
{
  return SYNCCHPOOL_LOC[tchanid].paddr;
}
>>
 *)

Definition get_sync_chan_paddr_body : statement := 
  (Sreturn (Some (Efield
                   (Ederef
                     (Ebinop Oadd
                       (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
                       (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
                     t_struct_SyncIPCChan) paddr tint))).

Definition f_get_sync_chan_paddr := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := get_sync_chan_paddr_body
|}.



(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

unsigned int is_pid_sending_to(unsigned int tchanid, unsigned int to)
{
  return SYNCCHPOOL_LOC[tchanid].to == to;
}
>>
 *)

Definition is_pid_sending_to_body : statement := 
  (Sreturn (Some (Ebinop Oeq
                   (Efield
                     (Ederef
                       (Ebinop Oadd
                         (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
                         (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
                       t_struct_SyncIPCChan) to tint) (Etempvar to tint)
                   tint))).

Definition f_is_pid_sending_to := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: (to, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := is_pid_sending_to_body
|}.


(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

unsigned int get_sync_chan_count(unsigned int tchanid)
{
  return SYNCCHPOOL_LOC[tchanid].count;
}
>>
 *)

Definition get_sync_chan_count_body := 
  (Sreturn (Some (Efield
                   (Ederef
                     (Ebinop Oadd
                       (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
                       (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
                     t_struct_SyncIPCChan) count tint))).

Definition f_get_sync_chan_count := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := get_sync_chan_count_body
|}.


(**
<<
#define num_proc 64

struct SyncIPCChan {
  unsigned int to;
  unsigned int vaddr; // Sender's virtual address of the send buffer
  unsigned int count;
};

extern struct SyncIPCChan SYNCCHPOOL_LOC[num_proc];

void set_sync_chan_count(unsigned int tchanid, unsigned int countval)
{
  SYNCCHPOOL_LOC[tchanid].count = countval;
}
>>
 *)

Let countval := 7%positive.

Definition set_sync_chan_count_body : statement := 
  (Sassign
    (Efield
      (Ederef
        (Ebinop Oadd (Evar SYNCCHPOOL_LOC (tarray t_struct_SyncIPCChan num_chan))
          (Etempvar tchanid tint) (tptr t_struct_SyncIPCChan))
        t_struct_SyncIPCChan) count tint) (Etempvar countval tint)).

Definition f_set_sync_chan_count := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((tchanid, tint) :: (countval, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := set_sync_chan_count_body
|}.



(**
<<
#define PAGESIZE 4096

extern unsigned int pt_read(unsigned int pid, unsigned int vaddr);

unsigned int get_kernel_pa(unsigned int pid, unsigned int va)
{
  unsigned int kpa = pt_read(pid, va);
  kpa = kpa / PAGESIZE * PAGESIZE + va % PAGESIZE;
  return kpa;
}

>>
*)

Local Open Scope positive_scope.

Definition _pid  : ident := 8.
Definition _kpa  : ident := 30.
Definition _va   : ident := 31.

Definition get_kernel_pa_body : statement :=
(Ssequence
    (Scall (Some _kpa)
      (Evar pt_read (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                       cc_default))
      ((Etempvar _pid tuint) :: (Etempvar _va tuint) :: nil))
  (Ssequence
    (Sset _kpa
      (Ebinop Oadd
        (Ebinop Omul
          (Ebinop Odiv (Etempvar _kpa tuint)
            (Econst_int (Int.repr 4096) tint) tuint)
          (Econst_int (Int.repr 4096) tint) tuint)
        (Ebinop Omod (Etempvar _va tuint) (Econst_int (Int.repr 4096) tint)
          tuint) tuint))
    (Sreturn (Some (Etempvar _kpa tuint)))))
.

Definition f_get_kernel_pa := {|
                                 fn_return := tint;
                                 fn_callconv := cc_default;
                                 fn_params := ((_pid, tint) :: (_va, tint) :: nil);
                                 fn_vars := nil;
                                 fn_temps := ((_kpa, tint) :: nil);
                                 fn_body := get_kernel_pa_body
                               |}.
