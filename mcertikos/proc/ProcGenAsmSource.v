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

  Definition get_curid_sig := mksignature nil (Some Tint) cc_default.
  Definition set_pt_sig := mksignature (Tint::nil) None cc_default.
  Definition restore_uctx_sig := mksignature (Tint::nil) None cc_default.

  Definition exit_sig := 
    mksignature (Tint::Tint::Tint::Tint::Tint::Tint::
                     Tint::Tint::Tint::Tint::Tint::
                     Tint::Tint::Tint::Tint::Tint::
                     Tint::nil) None cc_default.

  Section StartUser.

    (*	
	.globl proc_start_user
proc_start_user:

        alloc_stack_frame
        call    tss_switch   
        call    get_curid   
        movl    %eax, 0(%esp) // save cid

        call    pt_out

        call    set_pt        // arguements for set_pt (cid) 
        
        jmp     restore_uctx
     *)

    Definition Im_proc_start_user : list instruction := 
      asm_instruction (Pallocframe 12 (Int.repr 8) (Int.repr 4)) ::
                      asm_instruction (Pcall_s get_curid get_curid_sig) ::
                      asm_instruction (Pmov_mr (AddrMake (Int.repr 0)) EAX) ::

                      Ptss_switch ::
                      asm_instruction (Pcall_s pt_out null_signature) ::

                      asm_instruction (Pcall_s set_pt set_pt_sig) ::

                      asm_instruction (Pjmp_s restore_uctx restore_uctx_sig) ::

                      nil.

    Definition proc_start_user_function: function := mkfunction null_signature Im_proc_start_user.

  End StartUser.

  Section ExitUser.

    (*	
	.globl proc_exit_user
proc_exit_user:

        movl    RA, %ebx      // save RA

        call    trap_in   
        call    save_uctx
        
        movl    %ebx, RA      // restore RA

        allocframe
        movr    0, %eax
        movl    %eax, 0(%esp) // set argument
        call    set_pt        // arguements for set_pt (0)
        call    pt_in
        freeframe

        ret
     *)

    Definition Im_proc_exit_user : list instruction := 
      Ppopl_RA EBX ::
               asm_instruction (Pcall_s trap_in null_signature) ::
               asm_instruction (Pcall_s save_uctx exit_sig) ::
               Ppushl_RA EBX ::
               
               asm_instruction (Pallocframe 12 (Int.repr 8) (Int.repr 4)) ::
               asm_instruction (Pmov_ri EAX Int.zero) ::
               asm_instruction (Pmov_mr (AddrMake (Int.repr 0)) EAX) ::
               asm_instruction (Pcall_s set_pt set_pt_sig) ::
               asm_instruction (Pcall_s pt_in null_signature) ::

               asm_instruction (Pfreeframe 12 (Int.repr 8) (Int.repr 4)) ::

               asm_instruction (Pret) ::
               
               nil.

    Definition proc_exit_user_function: function := mkfunction exit_sig Im_proc_exit_user.

  End ExitUser.

End ASM_CODE.
