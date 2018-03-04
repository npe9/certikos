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
(*           Layers of PM: Assembly Verification for PKContext         *)
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

Require Import liblayers.compat.CompatLayers.
Require Import LAsm.

Section ASM_CODE.

  Definition AddrMake1 (r: ireg) :=
    Addrmode (Some r) (Some (r, Int.repr 2)) (inl Int.zero).

  Definition AddrMake2 (r: ireg) :=
    Addrmode None (Some (r, Int.repr 8)) (inr (KCtxtPool_LOC, Int.zero)).

  Definition AddrMake3 (r: ireg) (ofs:int) :=
    Addrmode (Some r) None (inl ofs).

  (*	
	.globl cswitch
cswitch:
	/* save the old kernel context */
	leal	(%eax,%eax,2), %eax
	leal	KCtxtPool_LOC(,%eax,8), %eax
	movl	%esp, (%eax)
	movl	%edi, 4(%eax)
	movl	%esi, 8(%eax)
	movl	%ebx, 12(%eax)
	movl	%ebp, 16(%eax)

	popl	%ecx
	movl	%ecx, 20(%eax)

	/* load the new kernel context */
	leal	(%edx,%edx,2), %edx
	leal	KCtxtPool_LOC(,%edx,8), %edx
	movl	(%edx), %esp
	movl	4(%edx), %edi
	movl	8(%edx), %esi
	movl	12(%edx), %ebx
	movl	16(%edx), %ebp
	movl	20(%edx), %ecx
	pushl	%ecx
	xorl	%eax, %eax
	ret

   *)

  Definition Im_cswitch : list instruction := 
    (*save the old kernel context*)
    asm_instruction (Plea EAX (AddrMake1 EAX)) ::  (* EAX = EAX * 3 *)
                    asm_instruction (Plea EAX (AddrMake2 EAX)) ::  (* EAX = KCtxtPool_LOC (EAX * 8) *)
                    asm_instruction (Pmov_mr (AddrMake3 EAX Int.zero) Asm.ESP) ::
                    asm_instruction (Pmov_mr (AddrMake3 EAX (Int.repr 4)) Asm.EDI) ::
                    asm_instruction (Pmov_mr (AddrMake3 EAX (Int.repr 8)) Asm.ESI) ::
                    asm_instruction (Pmov_mr (AddrMake3 EAX (Int.repr 12)) Asm.EBX) ::
                    asm_instruction (Pmov_mr (AddrMake3 EAX (Int.repr 16)) Asm.EBP) ::
                    Ppopl_RA ECX ::
                    asm_instruction (Pmov_mr (AddrMake3 EAX (Int.repr 20)) ECX) ::
                    
                    (*load the new kernel context*)
                    asm_instruction (Plea EDX (AddrMake1 EDX)) ::  (* EAX = EAX * 3 *)
                    asm_instruction (Plea EDX (AddrMake2 EDX)) ::  (* EAX = KCtxtPool_LOC (EAX * 8) *)
                    
                    asm_instruction (Pmov_rm Asm.ESP (AddrMake3 EDX Int.zero)) ::
                    asm_instruction (Pmov_rm Asm.EDI (AddrMake3 EDX (Int.repr 4))) ::
                    asm_instruction (Pmov_rm Asm.ESI (AddrMake3 EDX (Int.repr 8))) ::
                    asm_instruction (Pmov_rm Asm.EBX (AddrMake3 EDX (Int.repr 12))) ::
                    asm_instruction (Pmov_rm Asm.EBP (AddrMake3 EDX (Int.repr 16))) ::
                    asm_instruction (Pmov_rm Asm.ECX (AddrMake3 EDX (Int.repr 20))) ::
                    Ppushl_RA ECX ::
                    asm_instruction (Pxor_r EAX) ::
                    asm_instruction (Pret) ::
                    nil.

  Definition cswitch_function: function := mkfunction null_signature Im_cswitch.
  
End ASM_CODE.

