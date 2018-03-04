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
(*       C datatype definitions used in CertiKOS implementation        *)
(*                                                                     *)
(*                       Xiongnan (Newman) Wu                          *)
(*                                                                     *)
(*                         Yale University                             *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Events.
Require Import Globalenvs.
Require Import Locations.
Require Import LAsm.
Require Import Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Ctypes.
Require Import Cop.
Require Import ZArith.Zwf.
Require Export GlobIdent.
Require Export Constant.
Require Import AuxStateDataType.

  (** * C type notations*)

  Notation tchar := (Tint I8 Unsigned noattr).
  Notation tuchar := tchar.
  Notation tint := (Tint I32 Unsigned noattr).
  Notation tbool := (Tint IBool Unsigned noattr).
  Notation tuint := tint.
  Notation tulong := (Tlong Unsigned noattr).
  Notation tptr := (fun ty => Tpointer ty noattr).
  Notation tarray := (fun ty size => Tarray ty size noattr).
  Notation tvoid := (Tvoid).

  Definition exec_stmt `{compiler_config_ops: CompilerConfigOps} `{writable_block_ops: WritableBlockOps} ge :=
    ClightBigstep.exec_stmt ge (fun _ => function_entry2).


  (** * Properties of C types *)

  Lemma tcharsize: sizeof tchar = 1.
  Proof. trivial. Qed.

  Lemma tintsize: sizeof tint = 4.
  Proof. trivial. Qed.

  Lemma tptrsize: forall ty, sizeof (tptr ty) = 4.
  Proof. intros. trivial. Qed.
 
  (** * Kernel context variable declarations *)

  (*Notation kern_low:= 262144.
  Notation kern_high:= 983040.
  Notation PgSize:= 4096.
  Notation maxpage:= 1048576.
  Notation num_proc:= 64.
  Notation num_chan:= 64.
  Notation PTK_true := 259.
  Notation PTK_false := 3.
  Notation TSTATE_READY := 0.
  Notation TSTATE_RUN := 1.
  Notation TSTATE_SLEEP := 2.
  Notation TSTATE_DEAD := 3.
  Notation NPTEPERM := 7.
  Notation NPDEPERM := 39.
  Notation VMCB_V_SIZE := 16.
  Notation VMCB_Z_SIZE := 1008.
  Notation XVMST_SIZE := 6.*)
    
  Notation PDXPERM := 7.
  Notation S := Datatypes.S.
  Notation STACK_TOP:= (Int.repr (kern_high * PgSize)).


  (** * Properties of the kernel context variables *)

  Lemma adr_high_val: adr_high = 4026531840.
  Proof. reflexivity. Qed.

  Lemma adr_low_val: adr_low = 1073741824.
  Proof. reflexivity. Qed.

  Lemma adr_max_val: adr_max = 4294967296.
  Proof. reflexivity. Qed.

  Lemma one_k_val: one_k = 1024.
  Proof. compute. trivial. Qed.

  Lemma one_k_minus1: PDX Int.max_unsigned = one_k - 1.
  Proof. compute; trivial. Qed.

  Lemma one_k_plus1: PDX Int.max_unsigned + 2 = one_k + 1.
  Proof. compute; trivial. Qed.

  Lemma one_k_minus1': PTX Int.max_unsigned = one_k - 1.
  Proof. compute. trivial. Qed.

  Lemma valid_addr: 0 < kern_low < kern_high /\ kern_low < maxpage.
  Proof. omega. Qed.

  Lemma valid_n_proc: num_proc > 0.
  Proof. omega. Qed.
  
  Lemma valid_pgs: PgSize > 260.
  Proof. omega. Qed.

  Lemma div_pgs: (4 | PgSize).
  Proof.
    unfold Z.divide.
    exists 1024.
    compute.
    trivial.
  Qed.

  Lemma HPS: PgSize > 0.
  Proof. omega. Qed. 

  Lemma Hmax: maxpage * 8 + 4 < Int.max_unsigned.
  Proof.
    vm_compute; reflexivity.
  Qed.

  Lemma HPS4: PgSize >= 4.
  Proof. omega. Qed.

  Lemma Hnpc: num_proc > 0.
  Proof. omega. Qed.

  Lemma Hlow: (PgSize * one_k | kern_low * PgSize).
  Proof.
    unfold Z.divide.
    exists (kern_low / one_k).
    compute.
    trivial.
  Qed.

  Lemma Hhigh: (PgSize * one_k | kern_high * PgSize).
  Proof.
    unfold Z.divide.
    exists (kern_high / one_k).
    compute.
    trivial.
  Qed. 

  Lemma Hnchan: num_chan > 0.
  Proof. omega. Qed.



  (** * C type Declarations *)
  Local Open Scope positive.

  Definition flatmem_loc_type : globvar type :=
    {|
      gvar_info := (tarray tchar adr_max);
      gvar_init := ((Init_space adr_max)::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Notation AC := 500.
  Notation AC_quota := 510.
  Notation AC_usage := 520.
  Notation AC_parent := 530.
  Notation AC_nchildren := 540.
  Notation AC_used := 550.
  Notation t_struct_AC :=
    (Tstruct AC
      (Fcons AC_quota tint
        (Fcons AC_usage tint
          (Fcons AC_parent tint
            (Fcons AC_nchildren tint (Fcons AC_used tint Fnil))))) noattr).
  Fact sizeof_AC : sizeof t_struct_AC = 20%Z.
  Proof. auto. Qed.

  Definition container_loc_type : globvar type := 
    {|
      gvar_info := (tarray t_struct_AC num_id);
      gvar_init := (Init_space (num_id*20) :: nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Definition nps_loc_type : globvar type :=
    {|
      gvar_info := tint;
      gvar_init := (Init_int32 Int.zero :: nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Notation A := 1000. (**r struct type identifier *)
  Notation A_isnorm_ident := 1100. (**r struct field identifier *)
  Notation A_allocated_ident := 1200. (**r struct field identifier *)
  Notation A_c_ident := 1250.
  Notation t_struct_A := (Tstruct A (Fcons A_isnorm_ident tint (Fcons A_allocated_ident tint (Fcons A_c_ident tint Fnil))) noattr).
  Definition at_loc_type : globvar type :=
    {|
      gvar_info := (tarray t_struct_A maxpage);
      gvar_init := ((Init_space (maxpage*12))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Definition ptp_loc_type : globvar type :=
    {|
      gvar_info := (tarray tint num_proc);
      gvar_init := ((Init_space (num_proc*4))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Definition ptpool_loc_type : globvar type :=
    {|
      gvar_info := (tarray (tarray (tptr tchar) 1024%Z) 64%Z);
      gvar_init := ((Init_space (num_proc*PgSize))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Definition idpmap_loc_type : globvar type :=
    {|
      gvar_info := (tarray (tarray tint 1024%Z) 1024%Z);
      gvar_init := ((Init_space (1024%Z*PgSize))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Notation KCtxtStruct := 1600.
  Notation ESP := 1700.
  Notation EDI := 1800.
  Notation ESI := 1900.
  Notation EBX := 2000.
  Notation EBP := 2100.
  Notation RA := 2200.
  Notation t_struct_KCtxt := (Tstruct KCtxtStruct
     (Fcons ESP (tptr tvoid)
     (Fcons EDI (tptr tvoid)
     (Fcons ESI (tptr tvoid)
     (Fcons EBX (tptr tvoid)
     (Fcons EBP (tptr tvoid) 
     (Fcons RA (tptr tvoid) Fnil)))))) noattr).
  Definition kctxtpool_loc_type : globvar type :=
    {|
      gvar_info := (tarray t_struct_KCtxt num_proc);
      gvar_init := ((Init_space (num_proc*24))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Notation TCB := 2300.
  Notation state := 2400.
  Notation prev := 2500.
  Notation next := 2600.
  Notation t_struct_TCB := (Tstruct TCB 
     (Fcons state tint (Fcons prev tint (Fcons next tint Fnil))) noattr).
  Definition tcbpool_loc_type : globvar type :=
    {|
      gvar_info := (tarray t_struct_TCB num_chan);
      gvar_init := ((Init_space (num_proc*12))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Notation TDQ := 2700.
  Notation head := 2800.
  Notation tail := 2900.
  Notation t_struct_TDQ := (Tstruct TDQ 
     (Fcons head tint (Fcons tail tint Fnil)) noattr).
  Definition tdqpool_loc_type : globvar type :=
    {|
      gvar_info := (tarray t_struct_TDQ (num_chan + 1)%Z);
      gvar_init := ((Init_space ((num_chan+1)*8))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Definition curid_loc_type : globvar type :=
    {|
      gvar_info := tint;
      gvar_init := (Init_int32 (Int.repr 0) :: nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

(*
  Notation NPTStruct := 1020. (**r struct type identifier *)
  Notation t_struct_NPT := (Tstruct NPTStruct (Fcons pdir_ident (tarray (tptr tchar) one_k)
                            (Fcons pt_ident (tarray (tarray tint one_k) one_k) Fnil)) noattr).
  Definition npt_loc_type : globvar type :=
    {|
      gvar_info := (tarray t_struct_NPT num_proc);
      gvar_init := nil;
      gvar_readonly := false;
      gvar_volatile := false
    |}.
*)

  Notation ChanStruct := 3100.
  Notation isbusy := 3200.
  Notation content := 3300.
  Notation t_struct_Chan := (Tstruct ChanStruct
     (Fcons isbusy tint (Fcons content tint Fnil)) noattr).
  Definition chpool_loc_type : globvar type :=
    {|
      gvar_info := (tarray t_struct_Chan num_proc);
      gvar_init := ((Init_space (num_chan*8))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  Notation count := 3400.
  Notation paddr := 3500.
  Notation to := 3600.
  Notation SyncChanStruct := 3700.
    
  Notation t_struct_SyncIPCChan :=
     (Tstruct SyncChanStruct
       (Fcons to tint (Fcons paddr tint (Fcons count tint Fnil))) noattr).

  Definition syncchpool_loc_type : globvar type := {|
    gvar_info := (tarray t_struct_SyncIPCChan num_proc);
    gvar_init := (Init_space (num_proc*12) :: nil);
    gvar_readonly := false;
    gvar_volatile := false
  |}.

  Definition uctx_loc_type : globvar type :=
    {|
      gvar_info := (tarray (tarray tint UCTXT_SIZE) num_proc);
      gvar_init := ((Init_space (num_proc*UCTXT_SIZE*4))::nil);
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  (** * Properties of C types declared *)

  Open Local Scope Z.

  Lemma t_struct_KCtxt_size: sizeof t_struct_KCtxt = 24.
  Proof. reflexivity. Qed.

  Lemma ptr_size: forall t, sizeof (tptr t) = 4.
  Proof. intro. reflexivity. Qed.

  Lemma tvoid_size: sizeof tvoid = 1.
  Proof. reflexivity. Qed.

  Lemma t_struct_TCB_size: sizeof t_struct_TCB = 12.
  Proof. reflexivity. Qed.

  Lemma t_struct_TDQ_size: sizeof t_struct_TDQ = 8.
  Proof. reflexivity. Qed.

(*
  Lemma t_struct_NPT_size: sizeof t_struct_NPT = 1025 * PgSize.
  Proof.
    simpl.
    unfold align; simpl.
    trivial.
  Qed.
*)

  Lemma t_struct_Chan_size: sizeof t_struct_Chan = 8.
  Proof. reflexivity. Qed.

  Lemma t_struct_SyncChan_size: sizeof t_struct_SyncIPCChan = 12.
  Proof. reflexivity. Qed.


  (** * Additional definitions to compcert *)
  Fixpoint bind_parameter_temps' (formals: list (ident * type)) (args: list val)
                              (le: temp_env) : temp_env :=
    match bind_parameter_temps formals args le with
    | None => le
    | Some le' => le'
    end.
