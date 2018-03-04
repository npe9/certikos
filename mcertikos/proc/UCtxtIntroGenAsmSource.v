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
    Addrmode (Some EAX) None (inl ofs).

  Section RestoreUCtxt.

    (*	
	.globl restore_uctx
restore_uctx:
	movl	0(%esp), %eax	/* %eax <- n */

	sall	$2, %eax
	movl	%eax, %edx
	sall	$4, %eax
	leal	UCTX_LOC(%edx, %eax, 1), %eax
	leal	32(%eax), %esp	/* prepare the stack of trap_out() */
	/* load the user context */
	movl	(%eax), %edi
	movl	4(%eax), %esi
	movl	8(%eax), %ebp
	movl	16(%eax), %ebx
	movl	20(%eax), %edx
	movl	24(%eax), %ecx

        movl    U_ESP(%eax), %esp
        movl    U_EIP(%eax), %eip

	movl	28(%eax), %eax
        jmp     trap_out
     *)

    Definition Im_restore_uctx : list instruction := 
      (* get n *)
      asm_instruction (Pmov_rm EAX (Addrmode (Some Asm.ESP) None (inl Int.zero))) ::

                      asm_instruction (Psal_ri EAX (Int.repr 2)) ::
                      asm_instruction (Pmov_rr EDX EAX) ::
                      asm_instruction (Psal_ri EAX (Int.repr 4)) ::
                      asm_instruction (Plea EAX (Addrmode (Some EDX) (Some (EAX, Int.one)) (inr (UCTX_LOC, Int.zero)))) ::

                      asm_instruction (Plea Asm.ESP (AddrMake (Int.repr (U_ES * 4)))) ::

                      (*load the new kernel context*)
                      asm_instruction (Pmov_rm Asm.EDI (AddrMake (Int.repr (U_EDI * 4)))) ::
                      asm_instruction (Pmov_rm Asm.ESI (AddrMake (Int.repr (U_ESI * 4)))) ::
                      asm_instruction (Pmov_rm Asm.EBP (AddrMake (Int.repr (U_EBP * 4)))) ::
                      asm_instruction (Pmov_rm Asm.EBX (AddrMake (Int.repr (U_EBX * 4)))) ::
                      asm_instruction (Pmov_rm EDX (AddrMake (Int.repr (U_EDX * 4)))) ::
                      asm_instruction (Pmov_rm ECX (AddrMake (Int.repr (U_ECX * 4)))) ::
                      
                      Pmov_rm_nop Asm.ESP (AddrMake (Int.repr (U_ESP * 4))) ::
                      Pmov_rm_nop_RA (AddrMake (Int.repr (U_EIP * 4))) ::
                      
                      asm_instruction (Pmov_rm Asm.EAX (AddrMake (Int.repr (U_EAX * 4)))) ::
                      asm_instruction (Pjmp_s trap_out null_signature) ::
                      nil.

    Definition restoreuctx_function: function := mkfunction (mksignature (AST.Tint::nil) None cc_default) Im_restore_uctx.

  End RestoreUCtxt.

  Section ELFLoad.

    (*	
	.globl elf_load
elf_load:
        ELF_LOAD
     *)

    Definition Im_elf_load : list instruction := 
      (* load elf *)
      PELFLOAD ::
               nil.

    Definition elf_load_sig := mksignature (Tint::Tint::nil) None cc_default.

    Definition elfload_function: function := mkfunction elf_load_sig Im_elf_load.

  End ELFLoad.

End ASM_CODE.

Notation MCode_Asm :=
  (restore_uctx ↦ restoreuctx_function
                ⊕ elf_load ↦ elfload_function).
