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
    extern unsigned int uctx_arg1(void);
    extern unsigned int uctx_arg2(void);
    extern unsigned int uctx_arg3(void);
    extern unsigned int uctx_arg4(void);
    extern unsigned int uctx_arg5(void);
    extern void uctx_set_errno(unsigned int);
    extern void uctx_set_retval1(unsigned int);
    extern unsigned int syncsendto_chan_pre(unsigned int, unsigned int, unsigned int);

    unsigned int trap_sendtochan_pre()
    {
        unsigned int chid;
        unsigned int vaddr;
        unsigned int scount;
        unsigned int val;
        chid = uctx_arg2();
        vaddr = uctx_arg3();
        scount = uctx_arg4();
        val = syncsendto_chan_pre(chid, vaddr, scount);
        return val;
    }
>>
 *)


Definition _chid := 100 % positive.
Definition _vaddr := 101 % positive.
Definition _scount := 102 % positive.
Definition _val := 103 % positive.

Definition trap_sendtochan_pre_body :=
  (Ssequence
    (Scall (Some _chid) (Evar uctx_arg2 (Tfunction Tnil tuint cc_default))
      nil)
  (Ssequence
      (Scall (Some _vaddr)
        (Evar uctx_arg3 (Tfunction Tnil tuint cc_default)) nil)
    (Ssequence
        (Scall (Some _scount)
          (Evar uctx_arg4 (Tfunction Tnil tuint cc_default)) nil)
      (Ssequence
          (Scall (Some _val)
            (Evar syncsendto_chan_pre (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint (Tcons tuint Tnil)))
                                         tuint cc_default))
            ((Etempvar _chid tuint) :: (Etempvar _vaddr tuint) ::
             (Etempvar _scount tuint) :: nil))
        (Sreturn (Some (Etempvar _val tuint))))))).


Definition f_trap_sendtochan_pre := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_chid, tuint) :: (_vaddr, tuint) :: (_scount, tuint) :: (_val, tuint) :: nil);
  fn_body := trap_sendtochan_pre_body
|}.



(**
<<
    extern void uctx_set_errno(unsigned int);
    extern void uctx_set_retval1(unsigned int);
    extern unsigned int syncsendto_chan_post(void);

    void trap_sendtochan_post()
    {
        unsigned int val;
        val = syncsendto_chan_post();
        uctx_set_retval1(val);
        uctx_set_errno(0);
    }
>>
 *)


Definition trap_sendtochan_post_body :=
  (Ssequence
    (Scall (Some _val)
      (Evar syncsendto_chan_post (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
    (Scall None
      (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _val tuint) :: nil))
    (Scall None
      (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil)))).

Definition f_trap_sendtochan_post := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_val, tuint) :: nil);
  fn_body := trap_sendtochan_post_body
|}.




(**
<<
      #define SYS_puts 0
      #define SYS_ring0_spawn 1
      #define SYS_spawn 2
      #define SYS_yield 3
      #define SYS_sleep 4
      #define SYS_disk_op 5
      #define SYS_disk_cap 6
      #define SYS_is_chan_ready 7
      #define SYS_send 8
      #define SYS_recv 9
      #define SYS_get_tsc_per_ms 10
      #define SYS_hvm_run_vm 11
      #define SYS_hvm_get_exitinfo 12
      #define SYS_hvm_mmap 13
      #define SYS_hvm_set_seg 14
      #define SYS_hvm_set_reg 15
      #define SYS_hvm_get_reg 16
      #define SYS_hvm_get_next_eip 17
      #define SYS_hvm_inject_event 18
      #define SYS_hvm_check_int_shadow 19
      #define SYS_hvm_check_pending_event 20
      #define SYS_hvm_intercept_int_window 21
      #define SYS_hvm_get_tsc_offset 22
      #define SYS_hvm_set_tsc_offset 23
      #define SYS_hvm_handle_rdmsr 24
      #define SYS_hvm_handle_wrmsr 25
      #define SYS_get_quota 26
      #define MAX_SYSCALL_NR 27

      #define E_INVAL_CALLNR 3

      extern void sys_proc_create(void);
      extern void sys_get_quota(void);
      extern void uctx_set_errno(unsigned int);
      extern unsigned int uctx_arg1(void);

      void syscall_dispatch_c()
      {
        unsigned int arg1;
        arg1 = uctx_arg1();
        if (arg1 == SYS_spawn)
          sys_proc_create();
        else if(arg1 == SYS_get_quota)
          sys_get_quota();
        else
          uctx_set_errno(E_INVAL_CALLNR);
      }

>>
 *)

Definition _arg1 := 1 % positive.

Definition syscall_dispatch_c_body :=
  (Ssequence
     (Scall (Some _arg1) (Evar uctx_arg1 (Tfunction Tnil tuint cc_default))
            nil)
     (Sifthenelse (Ebinop Oeq (Etempvar _arg1 tuint)
                          (Econst_int (Int.repr 2) tint) tint)
                  (Scall None (Evar sys_proc_create (Tfunction Tnil tvoid cc_default))
                         nil)
                  (Sifthenelse (Ebinop Oeq (Etempvar _arg1 tuint)
                                       (Econst_int (Int.repr 26) tint) tint)
                               (Scall None (Evar sys_get_quota (Tfunction Tnil tvoid cc_default))
                                      nil)
                               (Sifthenelse (Ebinop Oeq (Etempvar _arg1 tuint)
                                                    (Econst_int (Int.repr 27) tint) tint)
                                            (Scall None (Evar sys_offer_shared_mem (Tfunction Tnil tvoid cc_default))
                                                   nil)
                                            (Sifthenelse (Ebinop Oeq (Etempvar _arg1 tuint)
                                                                 (Econst_int (Int.repr 28) tint) tint)
                                                         (Scall None (Evar print (Tfunction Tnil tvoid cc_default))
                                                                nil)
                                                         (Scall None
                                                                (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                                                                                cc_default))
                                                                ((Econst_int (Int.repr 3) tint) :: nil))))))).

Definition f_syscall_dispatch_c := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_arg1, tuint) :: nil);
  fn_body := syscall_dispatch_c_body
|}.
