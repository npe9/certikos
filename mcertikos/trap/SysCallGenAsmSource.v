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
(*           Layers of PM: Assembly Verification for Thread            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Integers.
Require Import Constant.
Require Import GlobIdent.
Require Import AST.

Require Import liblayers.compat.CompatLayers.
Require Import LAsm.

Section ASM_CODE.

  Definition AddrMake (ofs:int) :=
    Addrmode (Some ESP) None (inl ofs).

  Definition proc_exit_user_sig :=
    mksignature (Tint::Tint::Tint::Tint::Tint::Tint::
                     Tint::Tint::Tint::Tint::Tint::
                     Tint::Tint::Tint::Tint::Tint::
                     Tint::nil) None cc_default.

  Definition syscall_c_dispatch_sig := null_signature.

  (*mksignature nil None cc_default.*)
  Definition trap_get_sig := null_signature.
  (*mksignature nil (Some Tint) cc_default.*)
  Definition proc_start_user_sig := null_signature.

  (*Definition sys_is_chan_ready_sig := null_signature.
  (*mksignature nil None cc_default.*)
  Definition sys_sendto_chan_sig := null_signature.
  (*mksignature nil None cc_default.*)
  Definition sys_receive_chan_sig := null_signature.
  (*mksignature nil None cc_default.*)
  Definition sys_proc_create_sig := null_signature.
  (*mksignature nil None cc_default.*)*)

  Definition thread_yield_sig := null_signature.
  (*mksignature nil None cc_default.*)
  Definition ptfault_resv_sig := mksignature (Tint::nil) None cc_default.
  Definition thread_sleep_sig :=
    mksignature (Tint::nil) None cc_default.

  Definition trap_sendtochan_pre_sig :=
    mksignature nil (Some Tint) cc_default.

  Section SysDispatch.

    (*	
	.globl sys_dispatch
sys_dispatch:

        call    proc_exit_user   
        call    sys_c_dispatch
        call    proc_start_user
     *)

    Definition Im_sys_dispatch : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pcall_s syscall_dispatch_C syscall_c_dispatch_sig) ::
                      asm_instruction (Pcall_s proc_start_user proc_start_user_sig) ::
                      nil.

    Definition sys_dispatch_function: function := mkfunction null_signature Im_sys_dispatch.

  End SysDispatch.

  (*Section SysReady.

    (*	
	.globl sys_ready
sys_is_chan_ready:

        call    proc_exit_user   
        call    sys_is_chan_ready
        call    proc_start_user
     *)

    Definition Im_sys_ready : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pcall_s sys_is_chan_ready sys_is_chan_ready_sig) ::
                      asm_instruction (Pcall_s proc_start_user proc_start_user_sig) ::
                      nil.

    Definition sys_ready_function: function := mkfunction null_signature Im_sys_ready.

  End SysReady.


  Section SysSend.

    (*	
	.globl sys_send
sys_send:

        call    proc_exit_user   
        call    sys_sendto_chan
        call    proc_start_user
     *)

    Definition Im_sys_send : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pcall_s sys_sendto_chan sys_sendto_chan_sig) ::
                      asm_instruction (Pcall_s proc_start_user proc_start_user_sig) ::
                      nil.

    Definition sys_send_function: function := mkfunction null_signature Im_sys_send.

  End SysSend.


  Section SysRecv.

    (*	
	.globl sys_recv
sys_recv:

        call    proc_exit_user   
        call    sys_receive_chan
        call    proc_start_user
     *)

    Definition Im_sys_recv : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pcall_s sys_receive_chan sys_receive_chan_sig) ::
                      asm_instruction (Pcall_s proc_start_user proc_start_user_sig) ::
                      nil.

    Definition sys_recv_function: function := mkfunction null_signature Im_sys_recv.

  End SysRecv.*)


  Section SysYield.

    (*	
	.globl sys_yield
sys_yield:

        call    proc_exit_user   
        movl    proc_start_user, RA

        call    thread_yield
     *)

    Definition Im_sys_yield : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      Pmov_ra_RA proc_start_user ::
                      asm_instruction (Pjmp_s thread_yield thread_yield_sig) ::
                      nil.

    Definition sys_yield_function: function := mkfunction null_signature Im_sys_yield.

  End SysYield.


  (*Section SysSpawn.

    (*	
	.globl sys_spawn
sys_proc_create:

        call    proc_exit_user   
        call    sys_proc_create
        call    proc_start_user
     *)

    Definition Im_sys_spawn : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pcall_s sys_proc_create sys_proc_create_sig) ::
                      asm_instruction (Pcall_s proc_start_user proc_start_user_sig) ::
                      nil.

    Definition sys_spawn_function: function := mkfunction null_signature Im_sys_spawn.

  End SysSpawn.*)


  Section PgfHandler.

    (*	
	.globl pgf_handler
pgf_handler:

        call    proc_exit_user   
        allocframe   
        call    trap_get
        movl    %eax, 0(%esp)   
        call    ptfault_resv
        freeframe   
        call    proc_start_user
     *)

    Definition Im_pgf_handler : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pallocframe 12 (Int.repr 8) (Int.repr 4)) ::
                      asm_instruction (Pcall_s trap_get trap_get_sig) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.zero)) EAX) ::
                      asm_instruction (Pcall_s ptfault_resv ptfault_resv_sig) ::
                      asm_instruction (Pfreeframe 12 (Int.repr 8) (Int.repr 4)) ::
                      asm_instruction (Pcall_s proc_start_user proc_start_user_sig) ::
                      nil.

    Definition pgf_handler_function: function := mkfunction null_signature Im_pgf_handler.

  End PgfHandler.


  Section SysSendPre.

    (*	
	.globl sys_sendtochan_pre
sys_sendtochan_pre:

        call    proc_exit_user   
        call    trap_sendtochan_pre
        movl    sys_sendtochan_post, RA
        movl    %eax, 0(%esp)   
        jmp    thread_sleep
     *)

    Definition Im_sys_sendtochan_pre : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pcall_s trap_sendtochan_pre trap_sendtochan_pre_sig) ::
                      Pmov_ra_RA sys_sendtochan_post ::
                      asm_instruction (Plea ESP (AddrMake (Int.repr 28))) ::
                      asm_instruction (Pjmp_s thread_sleep thread_sleep_sig) ::
                      nil.

    Definition sys_sendtochan_pre_function: function := mkfunction null_signature Im_sys_sendtochan_pre.

  End SysSendPre.


  Section SysSendPost.

    (*	
	.globl sys_sendtochan_post
sys_sendtochan_post:

        call    sys_sendto_chan_post
        call    proc_start_user
     *)

    Definition Im_sys_sendtochan_post : list instruction := 
      asm_instruction (Pcall_s trap_sendtochan_post null_signature) ::
                      asm_instruction (Pcall_s proc_start_user proc_start_user_sig) ::
                      nil.

    Definition sys_sendtochan_post_function: function := mkfunction null_signature Im_sys_sendtochan_post.

  End SysSendPost.

  Section SysRunVM.

    (*	
	.globl sys_run_vm
sys_run_vm:

        call    proc_exit_user   
        jmp    vmx_run_vm
     *)

    Definition Im_sys_run_vm : list instruction := 
      asm_instruction (Pcall_s proc_exit_user proc_exit_user_sig) ::
                      asm_instruction (Pjmp_s vmx_run_vm null_signature) ::
                      nil.

    Definition sys_run_vm_function: function := mkfunction null_signature Im_sys_run_vm.

  End SysRunVM.

End ASM_CODE.