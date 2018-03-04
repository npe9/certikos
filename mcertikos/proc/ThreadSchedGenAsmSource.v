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
(*           Layers of PM: Assembly Verification for ThreadSched       *)
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

    (*	
	.globl thread_sched
thread_sched:

        movr    num_chan, %eax
        movl    %eax, (%esp) // arguments for dequeue (num_chan)
        call    dequeue

        movl    %eax, 0(%esp) // return vaule :last l, also the arguments
        movr    1, %eax
        movl    %eax, 4(%esp) // arguements for set_state (last l, 1)
        call    set_state

        call    get_curid   
        movl    %eax, 4(%esp) // save cid

        call    set_curid // argument is already there, set_curid (last l)

        call    clear_cr2 // clear part of the trapinfo for security reasons
        
        movl    0(%esp), %edx
        movl    4(%esp), %eax
        jmp kctxt_switch

     *)

  Definition dequeue_sig:= mksignature (Tint::nil) (Some Tint) cc_default.
  Definition set_state_sig := mksignature (Tint::Tint::nil) None cc_default.
  Definition get_curid_sig := mksignature nil (Some Tint) cc_default.
  Definition set_curid_sig := mksignature (Tint::nil) None cc_default.
  Definition clear_cr2_sig := mksignature nil None cc_default.

  Definition AddrMake (ofs:int) :=
    Addrmode (Some ESP) None (inl ofs).

  Definition Im_thread_sched : list instruction := 
    asm_instruction (Pallocframe 16 (Int.repr 12) (Int.repr 8)) ::
                    asm_instruction (Pmov_ri EAX (Int.repr num_chan)) ::
                    asm_instruction (Pmov_mr (AddrMake Int.zero) EAX) ::
                    asm_instruction (Pcall_s dequeue dequeue_sig) ::

                    asm_instruction (Pmov_mr (AddrMake (Int.zero)) EAX) ::
                    asm_instruction (Pmov_ri EAX Int.one) ::
                    asm_instruction (Pmov_mr (AddrMake (Int.repr 4)) EAX) ::
                    asm_instruction (Pcall_s set_state set_state_sig) ::

                    asm_instruction (Pcall_s get_curid get_curid_sig) ::
                    asm_instruction (Pmov_mr (AddrMake (Int.repr 4)) EAX) ::

                    asm_instruction (Pcall_s set_curid set_curid_sig) ::

                    asm_instruction (Pcall_s clear_cr2 clear_cr2_sig) ::

                    asm_instruction (Pmov_rm EDX (AddrMake (Int.repr 0))) ::
                    asm_instruction (Pmov_rm EAX (AddrMake (Int.repr 4))) ::

                    asm_instruction (Pfreeframe 16 (Int.repr 12) (Int.repr 8)) ::
                    asm_instruction (Pjmp_s kctxt_switch null_signature) ::
                    nil.

  Definition threadsched_function: function := mkfunction null_signature Im_thread_sched.

End ASM_CODE.

