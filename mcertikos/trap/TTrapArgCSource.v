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
(*                       Hao Chen (hao.chen@yale.edu)                  *)
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

Notation tbool := (Tint IBool Unsigned noattr).

(**
<<
extern unsigned int get_curid(void);
extern unsigned int container_get_quota(unsigned int);
extern unsigned int container_get_usage(unsigned int);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);

void sys_get_quota()
{
    unsigned int curid;
    unsigned int quota;
    unsigned int usage;
    curid = get_curid();
    quota = container_get_quota(curid);
    usage = container_get_usage(curid);
    uctx_set_retval1(quota - usage);
    uctx_set_errno(0);
}
>>
*)

Notation _curid := 1 % positive.
Notation _quota := 2 % positive.
Notation _usage := 3 % positive.

Definition sys_get_quota_body :=
(Ssequence
    (Scall (Some _curid)
      (Evar get_curid (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
      (Scall (Some _quota)
        (Evar container_get_quota (Tfunction (Tcons tuint Tnil) tuint cc_default))
	((Etempvar _curid tuint) :: nil))
    (Ssequence
        (Scall (Some _usage)
          (Evar container_get_usage (Tfunction (Tcons tuint Tnil) tuint cc_default))
	  ((Etempvar _curid tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
            ((Ebinop Osub (Etempvar _quota tuint)
                          (Etempvar _usage tuint) tuint) :: nil))
          (Scall None
            (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))))))
      .

Definition f_sys_get_quota := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_curid, tuint) :: (_quota, tuint) ::  (_usage, tuint) :: nil);
  fn_body := sys_get_quota_body
|}.

(**
<<
extern unsigned int get_curid(void);
extern unsigned int uctx_arg2(void);
extern unsigned int offer_shared_mem(unsigned int, unsigned int, unsigned int);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);

void sys_offer_shared_mem()
{
    unsigned int curid;
    unsigned int vadr;
    unsigned int res;
    curid = get_curid();
    if (curid == 1) {
       vadr = uctx_arg2();
       res = offer_shared_mem (1, 2, vadr);
       uctx_set_retval1(res);
       uctx_set_errno(0);       
    } {
       uctx_set_errno(0);             
    }
}
>>
*)
Notation _curid_share := 201 %positive.
Notation _vadr_share := 202 % positive.
Notation _res_share := 203 % positive.

Definition sys_offer_shared_mem_body :=
  (Ssequence
     (Scall (Some _curid_share)
            (Evar get_curid (Tfunction Tnil tuint cc_default)) nil)
     (Sifthenelse (Ebinop Oeq (Etempvar _curid_share tuint)
                          (Econst_int (Int.repr 1) tint) tint)
                  (Ssequence
                     (Scall (Some _vadr_share)
                            (Evar uctx_arg2 (Tfunction Tnil tuint cc_default)) nil)
                     (Ssequence
                        (Scall (Some _res_share)
                               (Evar offer_shared_mem (Tfunction
                                                         (Tcons tuint
                                                                (Tcons tuint (Tcons tuint Tnil)))
                                                         tuint cc_default))
                               ((Econst_int Int.one tuint) :: (Econst_int (Int.repr 2) tuint) ::
                                                           (Etempvar _vadr_share tuint) :: nil))
                        (Ssequence
                           (Scall None
                                  (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
                                  ((Etempvar _res_share tuint) :: nil))
                           (Scall None
                                  (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
                                  ((Econst_int (Int.repr 0) tint) :: nil)))))
                  (Scall None
                         (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
                         ((Econst_int (Int.repr 0) tint) :: nil)))).

Definition f_sys_offer_shared_mem := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_curid_share, tuint) :: (_vadr_share, tuint) ::  (_res_share, tuint) :: nil);
  fn_body := sys_offer_shared_mem_body
|}.

(*

extern unsigned int get_curid(void);
extern unsigned int uctx_arg2(void);
extern unsigned int device_output(unsigned int, unsigned int, unsigned int);
extern void uctx_set_errno(unsigned int);

      void print () {
          unsigned int curid;
          curid = get_curid();
          out = uctx_arg2();
          device_output (curid, curid, out);          
          uctx_set_errno(0); 

      }

*)

Notation tout := 301 %positive.
Notation tcurid := 302 %positive.

Definition print_body :=
  (Ssequence
     (Scall (Some tcurid)
            (Evar get_curid (Tfunction Tnil tuint cc_default)) nil)
     (Ssequence
        (Scall (Some tout)
               (Evar uctx_arg2 (Tfunction Tnil tuint cc_default)) nil)
        (Ssequence
           (Scall None
                  (Evar device_output (Tfunction
                                         (Tcons tuint
                                                (Tcons tuint (Tcons tuint Tnil)))
                                         tvoid cc_default))
                  ((Etempvar tcurid tuint) :: (Etempvar tcurid tuint) ::
                                           (Etempvar tout tuint) :: nil))
           (Scall None
                  (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
                  ((Econst_int (Int.repr 0) tint) :: nil))
        )
     )
  ).

Definition f_print := 
  {|
    fn_return := tvoid;
    fn_callconv := cc_default;
    fn_params := nil;
    fn_vars := nil;
    fn_temps := (tcurid, tuint) :: (tout, tuint) :: nil;
    fn_body := print_body
  |}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int syncreceive_chan(unsigned int, unsigned int, unsigned int);

void sys_receive_chan()
{
    unsigned int fromid;
    unsigned int vaddr;
    unsigned int rcount;
    unsigned int val;
    fromid = uctx_arg2();
    vaddr = uctx_arg3();
    rcount = uctx_arg4();
    val = syncreceive_chan(fromid, vaddr, rcount);
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
>>
*)

Definition _val := 100 % positive.
Definition _fromid := 101 % positive.
Definition _vaddr := 102 % positive.
Definition _rcount := 103 % positive.

Definition sys_receive_chan_body :=
(Ssequence
    (Scall (Some _fromid)
      (Evar uctx_arg2 (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
      (Scall (Some _vaddr)
        (Evar uctx_arg3 (Tfunction Tnil tuint cc_default)) nil)
    (Ssequence
        (Scall (Some _rcount)
          (Evar uctx_arg4 (Tfunction Tnil tuint cc_default)) nil)
      (Ssequence
          (Scall (Some _val)
            (Evar syncreceive_chan (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil)))
                                      tuint cc_default))
            ((Etempvar _fromid tuint) :: (Etempvar _vaddr tuint) ::
             (Etempvar _rcount tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid
                                      cc_default))
            ((Etempvar _val tuint) :: nil))
          (Scall None
            (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                    cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil)))))))
.

Definition f_sys_receive_chan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_fromid, tuint) :: (_vaddr, tuint) :: (_rcount, tuint) :: (_val, tuint) :: nil);
  fn_body := sys_receive_chan_body
|}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_inject_event(unsigned int, unsigned int, unsigned int, unsigned int);

void sys_inject_event()
{
    unsigned int type;
    unsigned int vector;
    unsigned int errcode;
    unsigned int ev;
    type = uctx_arg2();
    vector = uctx_arg3();
    errcode = uctx_arg4();
    ev = uctx_arg5();
    vmx_inject_event(type, vector, errcode, ev);
    uctx_set_errno(0);
}
>>
*)

Notation _type   := 4 % positive.
Notation _vector := 5 % positive.
Notation _errcode:= 6 % positive.
Notation _ev     := 7 % positive.

Definition sys_inject_event_body :=
(Ssequence
    (Scall (Some _type) (Evar uctx_arg2 (Tfunction Tnil tuint cc_default))
      nil)
  (Ssequence
      (Scall (Some _vector)
        (Evar uctx_arg3 (Tfunction Tnil tuint cc_default)) nil)
    (Ssequence
        (Scall (Some _errcode)
          (Evar uctx_arg4 (Tfunction Tnil tuint cc_default)) nil)
      (Ssequence
          (Scall (Some _ev)
            (Evar uctx_arg5 (Tfunction Tnil tuint cc_default)) nil)
        (Ssequence
          (Scall None
            (Evar vmx_inject_event (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tuint Tnil))))
                                      tvoid cc_default))
            ((Etempvar _type tuint) :: (Etempvar _vector tuint) ::
             (Etempvar _errcode tuint) :: (Etempvar _ev tuint) :: nil))
          (Scall None
            (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                    cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil)))))))
.

Definition f_sys_inject_event := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_type, tuint) :: (_vector, tuint) :: (_errcode, tuint) ::
               (_ev, tuint) :: nil);
  fn_body := sys_inject_event_body
|}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int vmx_check_int_shadow(void);

void sys_check_int_shadow()
{
    unsigned int val;
    val = vmx_check_int_shadow();
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
>>
*)

Definition sys_check_int_shadow_body := 
(Ssequence
    (Scall (Some _val)
      (Evar vmx_check_int_shadow (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
    (Scall None
      (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _val tuint) :: nil))
    (Scall None
      (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil)))).

Definition f_sys_check_int_shadow := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_val, tuint) :: nil);
  fn_body := sys_check_int_shadow_body
|}.


(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int vmx_check_pending_event(void);

void sys_check_pending_event()
{
    unsigned int val;
    val = vmx_check_pending_event();
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
>>
*)

Definition sys_check_pending_event_body :=
(Ssequence
    (Scall (Some _val)
      (Evar vmx_check_pending_event (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
    (Scall None
      (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _val tuint) :: nil))
    (Scall None
      (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil))))
.

Definition f_sys_check_pending_event := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_val, tuint) :: nil);
  fn_body := sys_check_pending_event_body

|}.


(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_set_intercept_intwin(unsigned int);

void sys_set_intercept_intwin()
{
    unsigned int enable;
    enable = uctx_arg2();
    vmx_set_intercept_intwin(enable);
    uctx_set_errno(0);
}

>>
*)

Notation _enable     := 8 % positive.

Definition sys_set_intercept_intwin_body :=
(Ssequence
    (Scall (Some _enable)
      (Evar uctx_arg2 (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
    (Scall None
      (Evar vmx_set_intercept_intwin (Tfunction (Tcons tuint Tnil) tvoid
                                        cc_default))
      ((Etempvar _enable tuint) :: nil))
    (Scall None
      (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil))))
.

Definition f_sys_set_intercept_intwin := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_enable, tuint) :: nil);
  fn_body := sys_set_intercept_intwin_body
|}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int vmx_get_next_eip(void);

void sys_get_next_eip()
{
    unsigned int val;
    val = vmx_get_next_eip();
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
>>
*)

Definition sys_get_next_eip_body :=
(Ssequence
    (Scall (Some _val)
      (Evar vmx_get_next_eip (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
    (Scall None
      (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _val tuint) :: nil))
    (Scall None
      (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil)))).

Definition f_sys_get_next_eip := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_val, tuint) :: nil);
  fn_body := sys_get_next_eip_body
|}.

(**
<<
extern unsigned int uctx_arg2(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int vmx_get_reg(unsigned int);

typedef enum
{
	GUEST_EAX = 0,
	GUEST_EBX,
	GUEST_ECX,
	GUEST_EDX,
	GUEST_ESI,
	GUEST_EDI,
	GUEST_EBP,
	GUEST_ESP,
	GUEST_EIP,
	GUEST_EFLAGS,
	GUEST_CR0,
	GUEST_CR2,
	GUEST_CR3,
	GUEST_CR4,
	GUEST_MAX_REG
} guest_reg_t;

enum __error_nr
{
	E_SUCC = 0, /* no errors */
	E_MEM, /* memory failure */
	E_IPC,
	E_INVAL_CALLNR, /* invalid syscall number */
	E_INVAL_ADDR, /* invalid address */
	E_INVAL_PID, /* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID, /* general invalid id */
	E_DISK_OP, /* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR /* XXX: always put it at the end of __error_nr */
};

void
sys_get_reg ()
{
	unsigned int reg;

	reg = uctx_arg2 ();

	if (GUEST_EAX <= reg && reg < GUEST_MAX_REG)
	{
		reg = vmx_get_reg (reg);
		uctx_set_retval1 (reg);
		uctx_set_errno (E_SUCC);
	}
	else
	{
		uctx_set_errno (E_INVAL_REG);
	}
	return;
}

>>
*)

Notation _reg     := 9 % positive.

Definition sys_get_reg_body :=
(Ssequence
    (Scall (Some _reg) (Evar uctx_arg2 (Tfunction Tnil tuint cc_default))
      nil)
  (Ssequence
    (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tint)
                   (Etempvar _reg tuint) tint)
      (Ssequence
        (Sset 73%positive
          (Ecast
            (Ebinop Olt (Etempvar _reg tuint) (Econst_int (Int.repr 14) tint)
              tint) tbool))
        (Sset 73%positive (Ecast (Etempvar 73%positive tbool) tint)))
      (Sset 73%positive (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Etempvar 73%positive tint)
      (Ssequence
          (Scall (Some _reg)
            (Evar vmx_get_reg (Tfunction (Tcons tuint Tnil) tuint
                                 cc_default)) ((Etempvar _reg tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid
                                      cc_default))
            ((Etempvar _reg tuint) :: nil))
          (Scall None
            (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                    cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))))
      (Scall None
        (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 6) tint) :: nil))))).

Definition f_sys_get_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_reg, tuint) :: (73%positive, tint) :: nil);
  fn_body := sys_get_reg_body

|}.


(**
<<
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern void uctx_set_errno(unsigned int);
extern void vmx_set_reg(unsigned int, unsigned int);

typedef enum
{
	GUEST_EAX = 0,
	GUEST_EBX,
	GUEST_ECX,
	GUEST_EDX,
	GUEST_ESI,
	GUEST_EDI,
	GUEST_EBP,
	GUEST_ESP,
	GUEST_EIP,
	GUEST_EFLAGS,
	GUEST_CR0,
	GUEST_CR2,
	GUEST_CR3,
	GUEST_CR4,
	GUEST_MAX_REG
} guest_reg_t;

enum __error_nr
{
	E_SUCC = 0, /* no errors */
	E_MEM, /* memory failure */
	E_IPC,
	E_INVAL_CALLNR, /* invalid syscall number */
	E_INVAL_ADDR, /* invalid address */
	E_INVAL_PID, /* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID, /* general invalid id */
	E_DISK_OP, /* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR /* XXX: always put it at the end of __error_nr */
};

void
sys_set_reg ()
{
	unsigned int reg;
	unsigned int val;

	reg = uctx_arg2 ();
	val = uctx_arg3 ();

	if (GUEST_EAX <= reg && reg < GUEST_MAX_REG)
	{
		vmx_set_reg (reg, val);
		uctx_set_errno (E_SUCC);
	}
	else
	{
		uctx_set_errno (E_INVAL_REG);
	}

}


>>
*)

Definition sys_set_reg_body :=
(Ssequence
    (Scall (Some _reg) (Evar uctx_arg2 (Tfunction Tnil tuint cc_default))
      nil)
  (Ssequence
      (Scall (Some _val) (Evar uctx_arg3 (Tfunction Tnil tuint cc_default))
        nil)
    (Ssequence
      (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tint)
                     (Etempvar _reg tuint) tint)
        (Ssequence
          (Sset 124%positive
            (Ecast
              (Ebinop Olt (Etempvar _reg tuint)
                (Econst_int (Int.repr 14) tint) tint) tbool))
          (Sset 124%positive (Ecast (Etempvar 124%positive tbool) tint)))
        (Sset 124%positive (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar 124%positive tint)
        (Ssequence
          (Scall None
            (Evar vmx_set_reg (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                 tvoid cc_default))
            ((Etempvar _reg tuint) :: (Etempvar _val tuint) :: nil))
          (Scall None
            (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                    cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil)))
        (Scall None
          (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                  cc_default))
          ((Econst_int (Int.repr 6) tint) :: nil)))))).
        

Definition f_sys_set_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_reg, tuint) :: (_val, tuint) :: (124%positive, tint) ::  nil);
  fn_body := sys_set_reg_body
|}.


(**
<<
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern unsigned int uctx_arg6(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_set_desc(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);

typedef enum
{
	GUEST_CS = 0,
	GUEST_DS,
	GUEST_ES,
	GUEST_FS,
	GUEST_GS,
	GUEST_SS,
	GUEST_LDTR,
	GUEST_TR,
	GUEST_GDTR,
	GUEST_IDTR,
	GUEST_MAX_SEG_DESC
} guest_seg_t;

enum __error_nr
{
	E_SUCC = 0, /* no errors */
	E_MEM, /* memory failure */
	E_IPC,
	E_INVAL_CALLNR, /* invalid syscall number */
	E_INVAL_ADDR, /* invalid address */
	E_INVAL_PID, /* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID, /* general invalid id */
	E_DISK_OP, /* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR /* XXX: always put it at the end of __error_nr */
};

void
sys_set_seg ()
{
	unsigned int seg;
	unsigned int sel;
	unsigned int base;
	unsigned int lim;
	unsigned int ar;
	seg = uctx_arg2 ();
	sel = uctx_arg3 ();
	base = uctx_arg4 ();
	lim = uctx_arg5 ();
	ar = uctx_arg6 ();
	if (GUEST_CS <= seg && seg < GUEST_MAX_SEG_DESC)
	{
		vmx_set_desc (seg, sel, base, lim, ar);
		uctx_set_errno (E_SUCC);
	}
	else
	{
		uctx_set_errno (E_INVAL_SEG);
	}
}
>>
*)

Notation _seg   := 10 % positive.
Notation _sel   := 11 % positive.
Notation _base  := 12 % positive.
Notation _lim   := 13 % positive.
Notation _ar    := 14 % positive.


Definition sys_set_seg_body :=
(Ssequence
    (Scall (Some _seg) (Evar uctx_arg2 (Tfunction Tnil tuint cc_default))
      nil)
  (Ssequence
      (Scall (Some _sel) (Evar uctx_arg3 (Tfunction Tnil tuint cc_default))
        nil)
    (Ssequence
        (Scall (Some _base)
          (Evar uctx_arg4 (Tfunction Tnil tuint cc_default)) nil)
      (Ssequence
          (Scall (Some _lim)
            (Evar uctx_arg5 (Tfunction Tnil tuint cc_default)) nil)
        (Ssequence
            (Scall (Some _ar)
              (Evar uctx_arg6 (Tfunction Tnil tuint cc_default)) nil)
          (Ssequence
            (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tint)
                           (Etempvar _seg tuint) tint)
              (Ssequence
                (Sset 135%positive
                  (Ecast
                    (Ebinop Olt (Etempvar _seg tuint)
                      (Econst_int (Int.repr 10) tint) tint) tbool))
                (Sset 135%positive
                  (Ecast (Etempvar 135%positive tbool) tint)))
              (Sset 135%positive (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar 135%positive tint)
              (Ssequence
                (Scall None
                  (Evar vmx_set_desc (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint Tnil))))) tvoid
                                        cc_default))
                  ((Etempvar _seg tuint) :: (Etempvar _sel tuint) ::
                   (Etempvar _base tuint) :: (Etempvar _lim tuint) ::
                   (Etempvar _ar tuint) :: nil))
                (Scall None
                  (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                          cc_default))
                  ((Econst_int (Int.repr 0) tint) :: nil)))
              (Scall None
                (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                        cc_default))
                ((Econst_int (Int.repr 7) tint) :: nil))))))))).

Definition f_sys_set_seg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_seg, tuint) :: (_sel, tuint) :: (_base, tuint) ::
               (_lim, tuint) :: (_ar, tuint) :: (135%positive, tint) :: nil);
  fn_body := sys_set_seg_body
|}.

(**
<<
extern  void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void uctx_set_retval2(unsigned int);
extern unsigned long long vmx_get_tsc_offset(void);

#define pow2to32 (0x100000000ull)

void sys_get_tsc_offset()
{
    unsigned long long tsc;
    unsigned int hi;
    unsigned int lo;
    tsc = vmx_get_tsc_offset();
    hi = (unsigned int) (tsc / pow2to32);
    lo = (unsigned int) (tsc % pow2to32);

    uctx_set_retval1(hi);
    uctx_set_retval2(lo);
    uctx_set_errno(0);
}

>>
*)

Notation _tsc := 15 % positive.
Notation _hi  := 16 % positive.
Notation _lo  := 17 % positive.

Definition sys_get_tsc_offset_body :=
(Ssequence
    (Scall (Some _tsc)
      (Evar vmx_get_tsc_offset (Tfunction Tnil tulong cc_default)) nil)
  (Ssequence
    (Sset _hi
      (Ecast
        (Ebinop Odiv (Etempvar _tsc tulong)
          (Econst_long (Int64.repr 4294967296) tulong) tulong) tuint))
    (Ssequence
      (Sset _lo
        (Ecast
          (Ebinop Omod (Etempvar _tsc tulong)
            (Econst_long (Int64.repr 4294967296) tulong) tulong) tuint))
      (Ssequence
        (Scall None
          (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid
                                    cc_default))
          ((Etempvar _hi tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar uctx_set_retval2 (Tfunction (Tcons tuint Tnil) tvoid
                                      cc_default))
            ((Etempvar _lo tuint) :: nil))
          (Scall None
            (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                    cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))))))).
            

Definition f_sys_get_tsc_offset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_tsc, tulong) :: (_hi, tuint) :: (_lo, tuint) ::
               nil);
  fn_body := sys_get_tsc_offset_body
|}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void vmx_set_tsc_offset(unsigned long long tsc_offset);

#define pow2to32 (0x100000000ull)

void sys_set_tsc_offset()
{
    unsigned int hi;
    unsigned int lo;
    unsigned long long tsc;
    hi = uctx_arg2();
    lo = uctx_arg3();
    tsc = ((unsigned long long)hi) * pow2to32 + (unsigned long long)lo;
    vmx_set_tsc_offset(tsc);
    uctx_set_errno(0);
}


>>
*)

Definition sys_set_tsc_offset_body :=
(Ssequence
    (Scall (Some _hi) (Evar uctx_arg2 (Tfunction Tnil tuint cc_default))
      nil)
  (Ssequence
      (Scall (Some _lo) (Evar uctx_arg3 (Tfunction Tnil tuint cc_default))
        nil)
    (Ssequence
      (Sset _tsc
        (Ebinop Oadd
          (Ebinop Omul (Ecast (Etempvar _hi tuint) tulong)
            (Econst_long (Int64.repr 4294967296) tulong) tulong)
          (Ecast (Etempvar _lo tuint) tulong) tulong))
      (Ssequence
        (Scall None
          (Evar vmx_set_tsc_offset (Tfunction (Tcons tulong Tnil) tvoid
                                      cc_default))
          ((Etempvar _tsc tulong) :: nil))
        (Scall None
          (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                  cc_default))
          ((Econst_int (Int.repr 0) tint) :: nil))))))
.

Definition f_sys_set_tsc_offset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_hi, tuint) :: (_lo, tuint) :: (_tsc, tulong) :: nil);
  fn_body := sys_set_tsc_offset_body
|}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern void uctx_set_retval2(unsigned int);
extern void uctx_set_retval3(unsigned int);
extern void uctx_set_retval4(unsigned int);
extern unsigned int vmx_get_exit_reason(void);
extern unsigned int vmx_get_exit_io_port(void);
extern unsigned int vmx_get_exit_io_width(void);
extern unsigned int vmx_get_exit_io_write(void);
extern unsigned int vmx_get_exit_io_rep(void);
extern unsigned int vmx_get_exit_io_str(void);
extern unsigned int vmx_get_exit_fault_addr(void);

#define EXIT_REASON_INOUT		30
#define EXIT_REASON_EPT_FAULT		48

void
sys_get_exitinfo ()
{
	unsigned int reason = 0;
	unsigned int port = 0;
	unsigned int width = 0;
	unsigned int write = 0;
	unsigned int rep = 0;
	unsigned int str = 0;
	unsigned int fault_addr = 0;
	unsigned int flags;

	flags = 0;
	reason = vmx_get_exit_reason ();
	port = vmx_get_exit_io_port ();
	width = vmx_get_io_width ();
	write = vmx_get_io_write ();
	rep = vmx_get_exit_io_rep ();
	str = vmx_get_exit_io_str ();
	fault_addr = vmx_get_exit_fault_addr ();

	uctx_set_retval1 (reason);

	if (reason == EXIT_REASON_INOUT)
	{
		uctx_set_retval2 (port);
		uctx_set_retval3 (width);
		if (write)
			flags |= (1 << 0);
		if (rep)
			flags |= (1 << 1);
		if (str)
			flags |= (1 << 2);
		uctx_set_retval4 (flags);
	}
	else if (reason == EXIT_REASON_EPT_FAULT)
	{
		uctx_set_retval2 (fault_addr);
	}

	uctx_set_errno (0);
}
>>
*)


Notation _reason    := 18 % positive.
Notation _port      := 19 % positive.
Notation _width     := 20 % positive.
Notation _write     := 21 % positive.
Notation _rep       := 22 % positive.
Notation _str       := 23 % positive.
Notation _fault_addr:= 24 % positive.
Notation _flags     := 25 % positive.


Definition sys_get_exitinfo_body :=
(Ssequence
  (Sset _reason (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _port (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _width (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _write (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sset _rep (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sset _str (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sset _fault_addr (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sset _flags (Econst_int (Int.repr 0) tint))
                (Ssequence
                    (Scall (Some _reason)
                      (Evar vmx_get_exit_reason (Tfunction Tnil tuint
                                                   cc_default)) nil)
                  (Ssequence
                      (Scall (Some _port)
                        (Evar vmx_get_exit_io_port (Tfunction Tnil tuint
                                                      cc_default)) nil)
                    (Ssequence
                        (Scall (Some _width)
                          (Evar vmx_get_io_width (Tfunction Tnil tuint
                                                         cc_default)) nil)
                      (Ssequence
                          (Scall (Some _write)
                            (Evar vmx_get_io_write (Tfunction Tnil
                                                           tuint cc_default))
                            nil)
                        (Ssequence
                            (Scall (Some _rep)
                              (Evar vmx_get_exit_io_rep (Tfunction Tnil
                                                           tuint cc_default))
                              nil)
                          (Ssequence
                              (Scall (Some _str)
                                (Evar vmx_get_exit_io_str (Tfunction Tnil
                                                             tuint
                                                             cc_default))
                                nil)
                            (Ssequence
                                (Scall (Some _fault_addr)
                                  (Evar vmx_get_exit_fault_addr (Tfunction
                                                                   Tnil tuint
                                                                   cc_default))
                                  nil)
                              (Ssequence
                                (Scall None
                                  (Evar uctx_set_retval1 (Tfunction
                                                            (Tcons tuint
                                                              Tnil) tvoid
                                                            cc_default))
                                  ((Etempvar _reason tuint) :: nil))
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _reason tuint)
                                                 (Econst_int (Int.repr 30) tint)
                                                 tint)
                                    (Ssequence
                                      (Scall None
                                        (Evar uctx_set_retval2 (Tfunction
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                        ((Etempvar _port tuint) :: nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar uctx_set_retval3 (Tfunction
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                          ((Etempvar _width tuint) :: nil))
                                        (Ssequence
                                          (Sifthenelse (Etempvar _write tuint)
                                            (Sset _flags
                                              (Ebinop Oor
                                                (Etempvar _flags tuint)
                                                (Ebinop Oshl
                                                  (Econst_int (Int.repr 1) tint)
                                                  (Econst_int (Int.repr 0) tint)
                                                  tint) tuint))
                                            Sskip)
                                          (Ssequence
                                            (Sifthenelse (Etempvar _rep tuint)
                                              (Sset _flags
                                                (Ebinop Oor
                                                  (Etempvar _flags tuint)
                                                  (Ebinop Oshl
                                                    (Econst_int (Int.repr 1) tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) tuint))
                                              Sskip)
                                            (Ssequence
                                              (Sifthenelse (Etempvar _str tuint)
                                                (Sset _flags
                                                  (Ebinop Oor
                                                    (Etempvar _flags tuint)
                                                    (Ebinop Oshl
                                                      (Econst_int (Int.repr 1) tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint) tuint))
                                                Sskip)
                                              (Scall None
                                                (Evar uctx_set_retval4 
                                                (Tfunction (Tcons tuint Tnil)
                                                  tvoid cc_default))
                                                ((Etempvar _flags tuint) ::
                                                 nil)))))))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _reason tuint)
                                                   (Econst_int (Int.repr 48) tint)
                                                   tint)
                                      (Scall None
                                        (Evar uctx_set_retval2 (Tfunction
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                        ((Etempvar _fault_addr tuint) :: nil))
                                      Sskip))
                                  (Scall None
                                    (Evar uctx_set_errno (Tfunction
                                                            (Tcons tuint
                                                              Tnil) tvoid
                                                            cc_default))
                                    ((Econst_int (Int.repr 0) tint) :: nil)))))))))))))))))))
                                    .

Definition f_sys_get_exitinfo := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_reason, tuint) :: (_port, tuint) :: (_width, tuint) ::
               (_write, tuint) :: (_rep, tuint) :: (_str, tuint) ::
               (_fault_addr, tuint) :: (_flags, tuint) :: nil);
  fn_body := sys_get_exitinfo_body

|}.


(**
<<
typedef unsigned int	uint32_t;
typedef unsigned long long	uint64_t;

enum
{
	GUEST_EAX = 0,
	GUEST_EBX,
	GUEST_ECX,
	GUEST_EDX,
	GUEST_ESI,
	GUEST_EDI,
	GUEST_EBP,
	GUEST_ESP,
	GUEST_EIP,
	GUEST_EFLAGS,
	GUEST_CR0,
	GUEST_CR2,
	GUEST_CR3,
	GUEST_CR4,
	GUEST_MAX_REG
} guest_reg_t;

extern void uctx_set_errno(unsigned int);

extern unsigned int vmx_get_reg(unsigned int reg);
extern void vmx_set_reg(unsigned int, unsigned int);
extern unsigned int vmx_get_next_eip(void);
extern uint64_t rdmsr(uint32_t msr);

#define pow2to32 (0x100000000ull)

void sys_handle_rdmsr()
{
    uint32_t msr, next_eip;
    uint64_t val;

    msr = vmx_get_reg(GUEST_EAX);

    val = rdmsr(msr);

    vmx_set_reg(GUEST_EAX, (unsigned int)(val % pow2to32));
    vmx_set_reg(GUEST_EDX, (unsigned int)(val / pow2to32));

    next_eip = vmx_get_next_eip();
    vmx_set_reg(GUEST_EIP, next_eip);
    uctx_set_errno(0);
}
>>
*)

Notation _msr      := 26 % positive.
Notation _next_eip := 27 % positive.

Definition sys_handle_rdmsr_body :=
(Ssequence
    (Scall (Some _msr)
      (Evar vmx_get_reg (Tfunction (Tcons tuint Tnil) tuint cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil))
  (Ssequence
      (Scall (Some _val)
        (Evar rdmsr (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Etempvar _msr tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar vmx_set_reg (Tfunction (Tcons tuint (Tcons tuint Tnil)) tvoid
                             cc_default))
        ((Econst_int (Int.repr 0) tint) ::
         (Ecast
           (Ebinop Omod (Etempvar _val tulong)
             (Econst_long (Int64.repr 4294967296) tulong) tulong) tuint) ::
         nil))
      (Ssequence
        (Scall None
          (Evar vmx_set_reg (Tfunction (Tcons tuint (Tcons tuint Tnil))
                               tvoid cc_default))
          ((Econst_int (Int.repr 3) tint) ::
           (Ecast
             (Ebinop Odiv (Etempvar _val tulong)
               (Econst_long (Int64.repr 4294967296) tulong) tulong) tuint) ::
           nil))
        (Ssequence
            (Scall (Some _next_eip)
              (Evar vmx_get_next_eip (Tfunction Tnil tuint cc_default)) nil)
          (Ssequence
            (Scall None
              (Evar vmx_set_reg (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                   tvoid cc_default))
              ((Econst_int (Int.repr 8) tint) ::
               (Etempvar _next_eip tuint) :: nil))
            (Scall None
              (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                      cc_default))
              ((Econst_int (Int.repr 0) tint) :: nil)))))))).

Definition f_sys_handle_rdmsr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_msr, tuint) :: (_next_eip, tuint) :: (_val, tulong) :: nil);
  fn_body := sys_handle_rdmsr_body
|}.

(**
<<
typedef unsigned int	uint32_t;
typedef unsigned long long	uint64_t;

typedef enum
{
	GUEST_EAX = 0,
	GUEST_EBX,
	GUEST_ECX,
	GUEST_EDX,
	GUEST_ESI,
	GUEST_EDI,
	GUEST_EBP,
	GUEST_ESP,
	GUEST_EIP,
	GUEST_EFLAGS,
	GUEST_CR0,
	GUEST_CR2,
	GUEST_CR3,
	GUEST_CR4,
	GUEST_MAX_REG
} guest_reg_t;

extern void uctx_set_errno(unsigned int);

extern unsigned int vmx_get_reg(unsigned int reg);
extern void vmx_set_reg(unsigned int, unsigned int);
extern unsigned int vmx_get_next_eip(void);
extern int wrmsr(uint32_t msr, uint64_t val);

#define pow2to32 (0x100000000ull)

void sys_handle_wrmsr()
{
	uint32_t msr, next_eip, eax, edx;
	uint64_t val;

	msr = vmx_get_reg(GUEST_ECX);
	eax = vmx_get_reg(GUEST_EAX);
	edx = vmx_get_reg(GUEST_EDX);
	val = (((uint64_t) edx) * pow2to32) + (uint64_t) eax;
	wrmsr(msr, val);

	next_eip = vmx_get_next_eip();
    vmx_set_reg(GUEST_EIP, next_eip);

    uctx_set_errno(0);
}
>>
*)

Notation _eax       := 30 % positive.
Notation _edx       := 31 % positive.

Definition sys_handle_wrmsr_body :=
(Ssequence
    (Scall (Some _msr)
      (Evar vmx_get_reg (Tfunction (Tcons tuint Tnil) tuint cc_default))
      ((Econst_int (Int.repr 2) tint) :: nil))
  (Ssequence
      (Scall (Some _eax)
        (Evar vmx_get_reg (Tfunction (Tcons tuint Tnil) tuint cc_default))
        ((Econst_int (Int.repr 0) tint) :: nil))
    (Ssequence
        (Scall (Some _edx)
          (Evar vmx_get_reg (Tfunction (Tcons tuint Tnil) tuint cc_default))
          ((Econst_int (Int.repr 3) tint) :: nil))
      (Ssequence
        (Sset _val
          (Ebinop Oadd
            (Ebinop Omul (Ecast (Etempvar _edx tuint) tulong)
              (Econst_long (Int64.repr 4294967296) tulong) tulong)
            (Ecast (Etempvar _eax tuint) tulong) tulong))
        (Ssequence
          (Scall None
            (Evar wrmsr (Tfunction (Tcons tuint (Tcons tulong Tnil)) tint
                           cc_default))
            ((Etempvar _msr tuint) :: (Etempvar _val tulong) :: nil))
          (Ssequence
              (Scall (Some _next_eip)
                (Evar vmx_get_next_eip (Tfunction Tnil tuint cc_default))
                nil)
            (Ssequence
              (Scall None
                (Evar vmx_set_reg (Tfunction
                                     (Tcons tuint (Tcons tuint Tnil)) tvoid
                                     cc_default))
                ((Econst_int (Int.repr 8) tint) ::
                 (Etempvar _next_eip tuint) :: nil))
              (Scall None
                (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                        cc_default))
                ((Econst_int (Int.repr 0) tint) :: nil))))))))).
                
Definition f_sys_handle_wrmsr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_msr, tuint) :: (_next_eip, tuint) :: (_eax, tuint) ::
               (_edx, tuint) :: (_val, tulong) :: nil);
  fn_body := sys_handle_wrmsr_body
|}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);

extern unsigned int get_curid(void);

extern unsigned int pt_read(unsigned int proc_index, unsigned int vaddr);
extern unsigned int pt_resv(unsigned int proc_index, unsigned int vaddr, unsigned int perm);
extern unsigned int vmx_set_mmap(unsigned int gpa, unsigned int hpa, unsigned int mem_type);

#define PAGESIZE			4096u
#define VM_USERHI			0xf0000000u
#define VM_USERLO			0x40000000u

#define PTE_P				0x001u	/* Present */
#define PTE_W				0x002u	/* Writeable */
#define PTE_U				0x004u	/* User-accessible */

enum __error_nr
{
	E_SUCC = 0, /* no errors */
	E_MEM, /* memory failure */
	E_IPC,
	E_INVAL_CALLNR, /* invalid syscall number */
	E_INVAL_ADDR, /* invalid address */
	E_INVAL_PID, /* invalid process ID */
	E_INVAL_REG,
	E_INVAL_SEG,
	E_INVAL_EVENT,
	E_INVAL_PORT,
	E_INVAL_HVM,
	E_INVAL_CHID,
	E_INVAL_ID, /* general invalid id */
	E_DISK_OP, /* disk operation failure */
	E_HVM_VMRUN,
	E_HVM_MMAP,
	E_HVM_REG,
	E_HVM_SEG,
	E_HVM_NEIP,
	E_HVM_INJECT,
	E_HVM_IOPORT,
	E_HVM_MSR,
	E_HVM_INTRWIN,
	MAX_ERROR_NR /* XXX: always put it at the end of __error_nr */
};

void
sys_mmap ()
{
	unsigned int cur_pid;
	unsigned int gpa;
	unsigned int hva;
	unsigned int hpa;
	unsigned int mem_type;

	cur_pid = get_curid ();
	gpa = uctx_arg2 ();
	hva = uctx_arg3 ();
	mem_type = uctx_arg4 ();

	if (hva % PAGESIZE != 0 || gpa % PAGESIZE != 0
			|| !(VM_USERLO <= hva && hva <= VM_USERHI - PAGESIZE))
	{
		uctx_set_errno (E_INVAL_ADDR);
	}

	hpa = pt_read (cur_pid, hva);

	if ((hpa & PTE_P) == 0)
	{
		pt_resv (cur_pid, hva, PTE_P | PTE_U | PTE_W);
		hpa = pt_read (cur_pid, hva);
	}

	hpa = (hpa & 0xfffff000u) + (hva % PAGESIZE);

	vmx_set_mmap (gpa, hpa, mem_type);

	uctx_set_errno (E_SUCC);
}

>>
*)

Notation _cur_pid    := 33 % positive.
Notation _gpa        := 34 % positive.
Notation _gpa'       := 46 % positive.
Notation _hva        := 35 % positive.
Notation _hpa        := 36 % positive.
Notation _mem_type   := 37 % positive.
Notation _hpa'1      := 38 % positive.
Notation _hpa'       := 39 % positive.
Notation _mem_type'  := 40 % positive.
Notation _hva'       := 41 % positive.
Notation _cur_pid'   := 43 % positive.

Definition sys_mmap_body :=
(Ssequence
  (Ssequence
    (Scall (Some _cur_pid')
      (Evar get_curid (Tfunction Tnil tuint cc_default)) nil)
    (Sset _cur_pid (Etempvar _cur_pid' tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _gpa') (Evar uctx_arg2 (Tfunction Tnil tuint cc_default))
        nil)
      (Sset _gpa (Etempvar _gpa' tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _hva')
          (Evar uctx_arg3 (Tfunction Tnil tuint cc_default)) nil)
        (Sset _hva (Etempvar _hva' tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _mem_type')
            (Evar uctx_arg4 (Tfunction Tnil tuint cc_default)) nil)
          (Sset _mem_type (Etempvar _mem_type' tuint)))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop One
                             (Ebinop Omod (Etempvar _hva tuint)
                               (Econst_int (Int.repr 4096) tuint) tuint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset 113%positive (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Sset 113%positive
                    (Ecast
                      (Ebinop One
                        (Ebinop Omod (Etempvar _gpa tuint)
                          (Econst_int (Int.repr 4096) tuint) tuint)
                        (Econst_int (Int.repr 0) tint) tint) tbool))
                  (Sset 113%positive
                    (Ecast (Etempvar 113%positive tbool) tint))))
              (Sifthenelse (Etempvar 113%positive tint)
                (Sset 114%positive (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop Ole
                                   (Econst_int (Int.repr 1073741824) tuint)
                                   (Etempvar _hva tuint) tint)
                      (Ssequence
                        (Sset 115%positive
                          (Ecast
                            (Ebinop Ole
                              (Etempvar _hva tuint)
                              (Econst_int (Int.repr (4026527744)) tuint)
                              tint) tbool))
                        (Sset 115%positive
                          (Ecast (Etempvar 115%positive tbool) tint)))
                      (Sset 115%positive (Econst_int (Int.repr 0) tint)))
                    (Sset 114%positive
                      (Ecast
                        (Eunop Onotbool (Etempvar 115%positive tint) tint)
                        tbool)))
                  (Sset 114%positive
                    (Ecast (Etempvar 114%positive tbool) tint)))))
            (Sifthenelse (Etempvar 114%positive tint)
              (Scall None
                  (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                          cc_default))
                  ((Econst_int (Int.repr 4) tint) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _hpa')
                (Evar pt_read (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                 tuint cc_default))
                ((Etempvar _cur_pid tuint) :: (Etempvar _hva tuint) :: nil))
              (Sset _hpa (Etempvar _hpa' tuint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Ebinop Oand (Etempvar _hpa tuint)
                               (Econst_int (Int.repr 1) tuint) tuint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Scall None
                    (Evar pt_resv (Tfunction
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil)))
                                     tuint cc_default))
                    ((Etempvar _cur_pid tuint) :: (Etempvar _hva tuint) ::
                     (Ebinop Oor
                       (Ebinop Oor (Econst_int (Int.repr 1) tuint)
                         (Econst_int (Int.repr 4) tuint) tuint)
                       (Econst_int (Int.repr 2) tuint) tuint) :: nil))
                  (Ssequence
                    (Scall (Some _hpa'1)
                      (Evar pt_read (Tfunction
                                       (Tcons tuint (Tcons tuint Tnil)) tuint
                                       cc_default))
                      ((Etempvar _cur_pid tuint) :: (Etempvar _hva tuint) ::
                       nil))
                    (Sset _hpa (Etempvar _hpa'1 tuint))))
                Sskip)
              (Ssequence
                (Sset _hpa
                  (Ebinop Oadd
                    (Ebinop Oand (Etempvar _hpa tuint)
                      (Econst_int (Int.repr (-4096)) tuint) tuint)
                    (Ebinop Omod (Etempvar _hva tuint)
                      (Econst_int (Int.repr 4096) tuint) tuint) tuint))
                (Ssequence
                  (Scall None
                    (Evar vmx_set_mmap (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint (Tcons tuint Tnil)))
                                          tuint cc_default))
                    ((Etempvar _gpa tuint) :: (Etempvar _hpa tuint) ::
                     (Etempvar _mem_type tuint) :: nil))
                  (Scall None
                    (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                            cc_default))
                    ((Econst_int (Int.repr 0) tint) :: nil)))))))))))).

Definition f_sys_mmap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_cur_pid, tuint) :: (_gpa, tuint) :: (_hva, tuint) ::
               (_hpa, tuint) :: (_mem_type, tuint) :: (_hpa'1, tuint) ::
               (_hpa', tuint) :: (115%positive, tint) ::
               (114%positive, tint) :: (113%positive, tint) ::
               (_mem_type', tuint) :: (_hva', tuint) :: (_gpa', tuint) ::
               (_cur_pid', tuint) :: nil);
  fn_body := sys_mmap_body

|}.

(**
<<
#define PT_PERM_PTU 7
#define addr_low 1073741824
#define addr_high 4026531840

extern unsigned int get_curid(void);
extern void pt_resv(unsigned int, unsigned int, unsigned int);

void ptfault_resv(unsigned int vaddr)
{
    unsigned int curid; 
    curid = get_curid();
    if (addr_low <= vaddr < addr_high)
      pt_resv(curid, vaddr, PT_PERM_PTU);
}

>>
*)
  

Locate Olt.

Definition ptfault_resv_body :=
  (Ssequence
     (Scall (Some _curid) (Evar get_curid (Tfunction Tnil tuint cc_default))
            nil)
     (Sifthenelse (Ebinop Oand
                          (Ebinop Ole (Econst_int (Int.repr 1073741824) tint)
                                  (Etempvar _vaddr tuint) tint)
                          (Ebinop Olt (Etempvar _vaddr tuint)
                                  (Econst_int (Int.repr 4026531840) tint)
                                   tint) tint)
                  (Scall None
                         (Evar pt_resv (Tfunction
                                          (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tuint
                                          cc_default))
                         ((Etempvar _curid tuint) :: (Etempvar _vaddr tuint) ::
                                                  (Econst_int (Int.repr 7) tint) :: nil))
                  Sskip)).

Definition f_ptfault_resv := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vaddr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_curid, tuint) :: nil);
  fn_body := ptfault_resv_body
|}.

(**
<<
#define NUM_ID 64
#define MAX_CHILDREN 3

extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int get_curid(void);
extern unsigned int container_get_nchildren(unsigned int);
extern unsigned int container_can_consume(unsigned int, unsigned int);
extern unsigned int proc_create(void *, void * ); 

extern void * ELF_ENTRY_LOC[NUM_ID];
extern void * ELF_LOC;

void sys_proc_create()
{
    unsigned int elf_id;
    unsigned int proc_index;
    unsigned int quota, qok;
    unsigned int nc;

    curid = get_curid();
    quota = uctx_arg3();    
    qok = container_can_consume(curid, quota);
    nc = container_get_nchildren(curid);
    if (qok == 0 || NUM_ID < curid * MAX_CHILDREN + 1 + MAX_CHILDREN
                 || nc == MAX_CHILDREN) uctx_set_errno(1);
    else {    
      elf_id = uctx_arg2();
      proc_index = proc_create(ELF_LOC, ELF_ENTRY_LOC[elf_id], quota);
      uctx_set_retval1(proc_index);
      uctx_set_errno(0);
    }
}
>>
*)

Notation _elf_id      := 44 % positive.
Notation _proc_index  := 45 % positive.
Notation _qok := 46 % positive.
Notation _nc := 47 % positive.

Definition sys_proc_create_body :=
(Ssequence
  (Scall (Some _curid)
    (Evar get_curid (Tfunction Tnil tint cc_default)) nil)
  (Ssequence 
    (Scall (Some _quota)
      (Evar uctx_arg3 (Tfunction Tnil tint cc_default)) nil)
    (Ssequence
      (Scall (Some _qok)
        (Evar container_can_consume (Tfunction (Tcons tint (Tcons tint Tnil)) tint cc_default))
        (Etempvar _curid tint :: Etempvar _quota tint :: nil))
      (Ssequence 
        (Scall (Some _nc)
          (Evar container_get_nchildren (Tfunction (Tcons tint Tnil) tint cc_default))
          (Etempvar _curid tint :: nil))
        (Sifthenelse
          (Ebinop Oor 
            (Ebinop Oeq (Etempvar _qok tint) (Econst_int (Int.repr 0) tint) tint)
            (Ebinop Oor
              (Ebinop Olt (Econst_int (Int.repr num_id) tint)
                          (Ebinop Oadd
                            (Ebinop Oadd
                              (Ebinop Omul (Etempvar _curid tint) (Econst_int (Int.repr max_children) tint) tint)
                              (Econst_int (Int.repr 1) tint) tint)
                            (Econst_int (Int.repr max_children) tint) tint) tint)
              (Ebinop Oeq (Etempvar _nc tint) (Econst_int (Int.repr max_children) tint) tint) tint) tint)
          (Scall None
             (Evar uctx_set_errno (Tfunction (Tcons tint Tnil) tvoid cc_default))
             (Econst_int (Int.repr 1) tint :: nil))
          (Ssequence
            (Scall (Some _elf_id)
                   (Evar uctx_arg2 (Tfunction Tnil tuint cc_default)) nil)
            (Ssequence
               (Scall (Some _proc_index)
                  (Evar proc_create (Tfunction
                                       (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tint Tnil)))
                                       tint cc_default))
                      ((Eaddrof (Evar ELF_LOC (tptr tvoid)) (tptr tvoid)) ::
                       (Ederef (Ebinop Oadd (Evar ELF_ENTRY_LOC (tarray (tptr tvoid) 64))
                               (Etempvar _elf_id tuint) (tptr (tptr tvoid))) (tptr tvoid)) :: 
                       (Etempvar _quota tint) :: nil))
               (Ssequence
                  (Scall None
                         (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
                         ((Etempvar _proc_index tuint) :: nil))
                  (Scall None
                         (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
                         ((Econst_int (Int.repr 0) tint) :: nil)))))))))).

Definition f_sys_proc_create := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_elf_id, tint) :: (_proc_index, tint) :: (_curid, tint) ::
               (_quota, tint) :: (_qok, tint) :: (_nc, tint) :: nil);
  fn_body := sys_proc_create_body
|}.
 

(*
(** 
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int is_chan_ready(void);

void sys_is_chan_ready()
{
    unsigned int val;
    val = is_chan_ready();
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
>>
*)

Notation _val := 1 % positive.

Definition sys_is_chan_ready_body :=
(Ssequence
    (Scall (Some _val)
      (Evar is_chan_ready (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
    (Scall None
      (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Etempvar _val tuint) :: nil))
    (Scall None
      (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tint) :: nil))))
      .

Definition f_sys_is_chan_ready := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_val, tuint) :: nil);
  fn_body := sys_is_chan_ready_body
|}.

(**
<<
extern unsigned int uctx_arg1(void);
extern unsigned int uctx_arg2(void);
extern unsigned int uctx_arg3(void);
extern unsigned int uctx_arg4(void);
extern unsigned int uctx_arg5(void);
extern void uctx_set_errno(unsigned int);
extern void uctx_set_retval1(unsigned int);
extern unsigned int sendto_chan(unsigned int, unsigned int);

void sys_sendto_chan()
{
    unsigned int chan_index;
    unsigned int content;
    unsigned int val;
    chan_index = uctx_arg2();
    content = uctx_arg3();
    val = sendto_chan(chan_index, content);
    uctx_set_retval1(val);
    uctx_set_errno(0);
}
>>
*)

Notation _chan_index := 2 % positive.
Notation _content := 3 % positive.

Definition sys_sendto_chan_body :=
(Ssequence
    (Scall (Some _chan_index)
      (Evar uctx_arg2 (Tfunction Tnil tuint cc_default)) nil)
  (Ssequence
      (Scall (Some _content)
        (Evar uctx_arg3 (Tfunction Tnil tuint cc_default)) nil)
    (Ssequence
        (Scall (Some _val)
          (Evar sendto_chan (Tfunction (Tcons tuint (Tcons tuint Tnil))
                               tuint cc_default))
          ((Etempvar _chan_index tuint) :: (Etempvar _content tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar uctx_set_retval1 (Tfunction (Tcons tuint Tnil) tvoid
                                    cc_default))
          ((Etempvar _val tuint) :: nil))
        (Scall None
          (Evar uctx_set_errno (Tfunction (Tcons tuint Tnil) tvoid
                                  cc_default))
          ((Econst_int (Int.repr 0) tint) :: nil)))))).

Definition f_sys_sendto_chan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_chan_index, tuint) :: (_content, tuint) :: (_val, tuint) ::
               nil);
  fn_body := sys_sendto_chan_body
|}.
*)


