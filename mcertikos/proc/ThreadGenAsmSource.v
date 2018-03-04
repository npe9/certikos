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

  Definition enqueue_sig:= mksignature (Tint::Tint::nil) None cc_default.
  Definition set_state_sig := mksignature (Tint::Tint::nil) None cc_default.
  Definition get_curid_sig := mksignature nil (Some Tint) cc_default.

  Definition AddrMake (ofs:int) :=
    Addrmode (Some ESP) None (inl ofs).

  Definition AddrMake' (r: ireg) (ofs:int) :=
    Addrmode (Some r) None (inl ofs).

  Section ThreadYield.

    (*	
	.globl thread_yield
thread_yield:

        call    get_curid   
        movr    %eax, %edx
        movl    %edx, 0(%esp) // save cid

        movr    0, %eax
        movl    %eax, 4(%esp) // arguements for set_state (cid, 1)
        call    set_state

        movr    num_chan, %eax
        movl    %eax, (%esp) 
        movl    %edx, 4(%esp) // arguments for enqueue (num_chan, cid)
        call    enqueue

        jmp     thread_sched
     *)

    Definition Im_thread_yield : list instruction := 
      asm_instruction (Pallocframe 16 (Int.repr 12) (Int.repr 8)) ::
                      asm_instruction (Pcall_s get_curid get_curid_sig) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 0)) EAX) ::
                      
                      asm_instruction (Pmov_ri EAX (Int.repr 0)) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 4)) EAX) ::
                      asm_instruction (Pcall_s set_state set_state_sig) ::
                      
                      asm_instruction (Pmov_rm EAX (AddrMake (Int.repr 0))) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 4)) EAX) ::
                      asm_instruction (Pmov_ri EAX (Int.repr num_chan)) ::
                      asm_instruction (Pmov_mr (AddrMake Int.zero) EAX) ::
                      asm_instruction (Pcall_s enqueue enqueue_sig) ::
                      asm_instruction (Pfreeframe 16 (Int.repr 12) (Int.repr 8)) ::
                      asm_instruction (Pjmp_s thread_sched null_signature) ::
                      nil.

    Definition threadyield_function: function := mkfunction null_signature Im_thread_yield.

  End ThreadYield.

  Section ThreadSleep.

    (*	
	.globl thread_sleep
thread_sleep:
       

        alloc_stack_frame
        movl    0(%esp), %eax // get parameter chan_id
        movl    %eax, 8(%esp) // save parameter chan_id
       
        call    get_curid   
        movl    %eax, 0(%esp) // save cid

        movr    2, %eax
        movl    %eax, 4(%esp) // arguements for set_state (cid, 2)
        call    set_state

        movl    0(%esp), %eax // get parameter cid
        movl    %eax, 4(%esp)
        movl    8(%esp), %eax // get parameter cid
        movl    %eax, 0(%esp) // arguements for set_state (cid, 2)

        call    enqueue       // arguments for enqueue (chan_id, cid)

        jmp     thread_sched
     *)

    Definition Im_thread_sleep : list instruction := 
      asm_instruction (Pallocframe 20 (Int.repr 16) (Int.repr 12)) ::
                      asm_instruction (Pmov_rm EAX (AddrMake' EDX  (Int.repr 0))) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 8)) EAX) ::

                      asm_instruction (Pcall_s get_curid get_curid_sig) ::

                      asm_instruction (Pmov_mr (AddrMake (Int.repr 0)) EAX) ::
                      asm_instruction (Pmov_ri EAX (Int.repr 2)) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 4)) EAX) ::
                      asm_instruction (Pcall_s set_state set_state_sig) ::

                      asm_instruction (Pmov_rm EAX (AddrMake (Int.repr 0))) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 4)) EAX) ::
                      asm_instruction (Pmov_rm EAX (AddrMake (Int.repr 8))) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 0)) EAX) ::
                      
                      asm_instruction (Pcall_s enqueue enqueue_sig) ::
                      
                      asm_instruction (Pfreeframe 20 (Int.repr 16) (Int.repr 12)) ::
                      asm_instruction (Pjmp_s thread_sched null_signature) ::
                      nil.

    Definition thread_sleep_sig := mksignature (Tint::nil) None cc_default.

    Definition threadsleep_function: function := mkfunction thread_sleep_sig Im_thread_sleep.

  End ThreadSleep.

End ASM_CODE.