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
(*              Constant used in Certikos                              *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Integers.
Require Import Values.

(** This file provide some [constant] that will be used in the layer definitions and refinement proofs*)

(** Machine Configuration *)
Notation kern_low:= 262144.
Notation kern_high:= 983040.
Notation PgSize:= 4096.
Notation maxpage:= 1048576.
Notation num_proc:= 64.
Notation num_chan:= 64.
Notation one_k := 1024.
Notation adr_max := 4294967296.
Notation adr_low := 1073741824.
Notation adr_high := 4026531840.
Notation MagicNumber := (maxpage + 1).

Notation num_id:= 64.
Notation max_children := 3.

(** Page Table Permission*)
Notation PT_PERM_UP := 0.
Notation PT_PERM_P := 1. (**r kern: >1G, PTE_P *)
Notation PT_PERM_PTKF := 3. (**r kern: >1G, PTE_P|_W *)
Notation PT_PERM_PTKT := 259. (**r kern: <1G, PTE_P|_W|_G *)
Notation PT_PERM_PTU := 7. (**r usr: >1G, PTE_P|_W|_U *)
(* redundant *)
(*
Notation PDXPERM := 7.
Notation PTK_true := 259.
Notation PTK_false := 3.
 *)

Notation TSTATE_READY := 0.
Notation TSTATE_RUN := 1.
Notation TSTATE_SLEEP := 2.
Notation TSTATE_DEAD := 3.
Notation NPTEPERM := 7.
Notation NPDEPERM := 39.
Notation EPTEPERM := 7.
Notation EPDTEPERM := 39.
Notation VMCB_V_SIZE := 16.
Notation VMCB_Z_SIZE := 1008.
Notation XVMST_SIZE := 6.

Notation U_EDI := 0.
Notation U_ESI := 1.
Notation U_EBP := 2.
Notation U_OESP := 3.
Notation U_EBX := 4.
Notation U_EDX := 5.
Notation U_ECX := 6.
Notation U_EAX := 7.
Notation U_ES := 8.
Notation U_DS := 9.
Notation U_TRAPNO := 10.
Notation U_ERR := 11.
Notation U_EIP := 12.
Notation U_CS := 13.
Notation U_EFLAGS := 14.
Notation U_ESP := 15.
Notation U_SS := 16.

Notation UCTXT_SIZE := 17.
Notation STACK_TOP:= (Int.repr (kern_high * PgSize)).
Notation CPU_GDT_UDATA := (Vint (Int.repr 35)).
Notation CPU_GDT_UCODE := (Vint (Int.repr 27)).
Notation FL_IF := (Vint (Int.repr 512)).


(* Offset within VMCB_Z *)
Notation VMCB_Z_INTCEPT_LO_OFFSET     := 3.
Notation VMCB_Z_INTCEPT_HI_OFFSET     := 4.
Notation VMCB_Z_GASID_OFFSET          := 22.
Notation VMCB_Z_INT_CTL_OFFSET        := 24.
Notation VMCB_Z_INT_STATE_OFFSET      := 26.
Notation VMCB_Z_EXITCODE_LO_OFFSET    := 28.
Notation VMCB_Z_EXITINFO1_LO_OFFSET   := 30.
Notation VMCB_Z_EXITINFO2_LO_OFFSET   := 32.
Notation VMCB_Z_EXITINTINFO_LO_OFFSET := 34.
Notation VMCB_Z_EXITINTINFO_HI_OFFSET := 35.
Notation VMCB_Z_NESTED_CTL_OFFSET     := 36.
Notation VMCB_Z_EVENTINJ_LO_OFFSET    := 42.
Notation VMCB_Z_EVENTINJ_HI_OFFSET    := 43.
Notation VMCB_Z_NEXT_RIP_LO_OFFSET    := 50.

Notation VMCB_Z_ES_OFFSET             := 256.
Notation VMCB_Z_CS_OFFSET             := 260.
Notation VMCB_Z_SS_OFFSET             := 264.
Notation VMCB_Z_DS_OFFSET             := 268.
Notation VMCB_Z_FS_OFFSET             := 272.
Notation VMCB_Z_GS_OFFSET             := 276.
Notation VMCB_Z_GDTR_OFFSET           := 280.
Notation VMCB_Z_LDTR_OFFSET           := 284.
Notation VMCB_Z_IDTR_OFFSET           := 288.
Notation VMCB_Z_TR_OFFSET             := 292.

Notation VMCB_Z_EFER_LO_OFFSET        := 308.
Notation VMCB_Z_DR7_LO_OFFSET         := 344.
Notation VMCB_Z_DR6_LO_OFFSET         := 346.
Notation VMCB_Z_GPAT_LO_OFFSET        := 410.
Notation VMCB_Z_GPAT_HI_OFFSET        := 411.

(* Offsets within VMCB_Val *)
Notation VMCB_V_CR4_LO_OFFSET         := 338.
Notation VMCB_V_CR3_LO_OFFSET         := 340.
Notation VMCB_V_CR0_LO_OFFSET         := 342.
Notation VMCB_V_RFLAGS_LO_OFFSET      := 348.
Notation VMCB_V_RIP_LO_OFFSET         := 350.
Notation VMCB_V_RSP_LO_OFFSET         := 374.
Notation VMCB_V_RAX_LO_OFFSET         := 382.
Notation VMCB_V_CR2_LO_OFFSET         := 400.

(* SVM VMEXIT cpde *)
Notation VMEXIT_VINTR := 96.
Notation VMEXIT_IOIO  := 123.
Notation VMEXIT_NPF   := 1024.

(* Other constants *)
Notation VMCB_INTCEPT_VINT_SHIFT    := 4.

Notation VMCB_INT_CTL_VIRQ_SHIFT    := 8.
Notation VMCB_INT_CTL_IGN_TPR_SHIFT := 20.

Notation VMCB_EVENTINJ_VALID_SHIFT  := 31.
Notation VMCB_EVENTINJ_EV_SHIFT     := 11.
Notation VMCB_EVENTINJ_TYPE_SHIFT   := 8.
Notation VMCB_EVENTINJ_TYPE_INTR    := 0.
Notation VMCB_EVENTINJ_TYPE_EXCPT   := 3.

Notation VMCB_SEG_ATTR_SHIFT        := 2.
Notation VMCB_SEG_LIM_SHIFT         := 4.
Notation VMCB_SEG_BASE_SHIFT        := 8.

Notation EXIT_INTINFO_VALID_SHIFT   := 31.
Notation EXIT_INTINFO_TYPE_SHIFT    := 8.
Notation EXIT_INTINFO_TYPE_MASK     := (Z.shiftl 7 EXIT_INTINFO_TYPE_SHIFT).
Notation EXIT_INTINFO_TYPE_INTR     := 0.
Notation EXIT_INTINFO_VECTOR_MASK   := 255.

(* Offsets within XVMState *)
Notation XVMST_EBX_OFFSET := 0.
Notation XVMST_ECX_OFFSET := 1.
Notation XVMST_EDX_OFFSET := 2.
Notation XVMST_ESI_OFFSET := 3.
Notation XVMST_EDI_OFFSET := 4.
Notation XVMST_EBP_OFFSET := 5.

(* segment registers *)
Notation G_CS    := 0.
Notation G_DS    := 1.
Notation G_ES    := 2.
Notation G_FS    := 3.
Notation G_GS    := 4.
Notation G_SS    := 5.
Notation G_LDTR  := 6.
Notation G_TR    := 7.
Notation G_GDTR  := 8.
Notation G_IDTR  := 9.
Notation MAX_SEG := 10.
(* registers *)

Notation G_EAX    := 0.
Notation G_EBX    := 1.
Notation G_ECX    := 2.
Notation G_EDX    := 3.
Notation G_ESI    := 4.
Notation G_EDI    := 5.
Notation G_EBP    := 6.
Notation G_ESP    := 7.
Notation G_EIP    := 8.
Notation G_EFLAGS := 9.
Notation G_CR0    := 10.
Notation G_CR2    := 11.
Notation G_CR3    := 12.
Notation G_CR4    := 13.

Definition sz32_mask := Z.shiftl 1 6.
Definition sz16_mask := Z.shiftl 1 5.
Definition sz8_mask  := Z.shiftl 1 4.
Definition rep_mask  := Z.shiftl 1 3.
Definition str_mask  := Z.shiftl 1 2.

Notation in_mask := 1.
Notation SZ8  := 0.
Notation SZ16 := 1.
Notation SZ32 := 2.



Notation SHARED_MEM_READY := 0.
Notation SHARED_MEM_PEND := 1.
Notation SHARED_MEM_DEAD := 2.


(* Intel Virtualization *)

Notation five_one_two := 512.
(* VMCS Encoding *)
Notation C_VMCS_VPID := 0	(* 0x00000000 *).
Notation C_VMCS_GUEST_ES_SELECTOR := 2048	(* 0x00000800 *).
Notation C_VMCS_GUEST_CS_SELECTOR := 2050	(* 0x00000802 *).
Notation C_VMCS_GUEST_SS_SELECTOR := 2052	(* 0x00000804 *).
Notation C_VMCS_GUEST_DS_SELECTOR := 2054	(* 0x00000806 *).
Notation C_VMCS_GUEST_FS_SELECTOR := 2056	(* 0x00000808 *).
Notation C_VMCS_GUEST_GS_SELECTOR := 2058	(* 0x0000080A *).
Notation C_VMCS_GUEST_LDTR_SELECTOR := 2060	(* 0x0000080C *).
Notation C_VMCS_GUEST_TR_SELECTOR := 2062	(* 0x0000080E *).
Notation C_VMCS_HOST_ES_SELECTOR := 3072	(* 0x00000C00 *).
Notation C_VMCS_HOST_CS_SELECTOR := 3074	(* 0x00000C02 *).
Notation C_VMCS_HOST_SS_SELECTOR := 3076	(* 0x00000C04 *).
Notation C_VMCS_HOST_DS_SELECTOR := 3078	(* 0x00000C06 *).
Notation C_VMCS_HOST_FS_SELECTOR := 3080	(* 0x00000C08 *).
Notation C_VMCS_HOST_GS_SELECTOR := 3082	(* 0x00000C0A *).
Notation C_VMCS_HOST_TR_SELECTOR := 3084	(* 0x00000C0C *).
Notation C_VMCS_IO_BITMAP_A := 8192	(* 0x00002000 *).
Notation C_VMCS_IO_BITMAP_A_HI := 8193	(* 0x00002001 *).
Notation C_VMCS_IO_BITMAP_B := 8194	(* 0x00002002 *).
Notation C_VMCS_IO_BITMAP_B_HI := 8195	(* 0x00002003 *).
Notation C_VMCS_MSR_BITMAP := 8196	(* 0x00002004 *).
Notation C_VMCS_MSR_BITMAP_HI := 8197	(* 0x00002005 *).
Notation C_VMCS_EXIT_MSR_STORE := 8198	(* 0x00002006 *).
Notation C_VMCS_EXIT_MSR_LOAD := 8200	(* 0x00002008 *).
Notation C_VMCS_ENTRY_MSR_LOAD := 8202	(* 0x0000200A *).
Notation C_VMCS_EXECUTIVE_VMCS := 8204	(* 0x0000200C *).
Notation C_VMCS_TSC_OFFSET := 8208	(* 0x00002010 *).
Notation C_VMCS_VIRTUAL_APIC := 8210	(* 0x00002012 *).
Notation C_VMCS_APIC_ACCESS := 8212	(* 0x00002014 *).
Notation C_VMCS_EPTP := 8218	(* 0x0000201A *).
Notation C_VMCS_EPTP_HI := 8219	(* 0x0000201B *).
Notation C_VMCS_GUEST_PHYSICAL_ADDRESS := 9216	(* 0x00002400 *).
Notation C_VMCS_LINK_POINTER := 10240	(* 0x00002800 *).
Notation C_VMCS_GUEST_IA32_DEBUGCTL := 10242	(* 0x00002802 *).
Notation C_VMCS_GUEST_IA32_PAT := 10244	(* 0x00002804 *).
Notation C_VMCS_GUEST_IA32_EFER := 10246	(* 0x00002806 *).
Notation C_VMCS_GUEST_IA32_PERF_GLOBAL_CTRL  := 10248	(* 0x00002808 *).
Notation C_VMCS_GUEST_PDPTE0 := 10250	(* 0x0000280A *).
Notation C_VMCS_GUEST_PDPTE1 := 10252	(* 0x0000280C *).
Notation C_VMCS_GUEST_PDPTE2 := 10254	(* 0x0000280E *).
Notation C_VMCS_GUEST_PDPTE3 := 10256	(* 0x00002810 *).
Notation C_VMCS_HOST_IA32_PAT := 11264	(* 0x00002C00 *).
Notation C_VMCS_HOST_IA32_EFER := 11266	(* 0x00002C02 *).
Notation C_VMCS_HOST_IA32_PERF_GLOBAL_CTRL := 11268	(* 0x00002C04 *).
Notation C_VMCS_PIN_BASED_CTLS := 16384	(* 0x00004000 *).
Notation C_VMCS_PRI_PROC_BASED_CTLS := 16386	(* 0x00004002 *).
Notation C_VMCS_EXCEPTION_BITMAP := 16388	(* 0x00004004 *).
Notation C_VMCS_PF_ERROR_MASK := 16390	(* 0x00004006 *).
Notation C_VMCS_PF_ERROR_MATCH := 16392	(* 0x00004008 *).
Notation C_VMCS_CR3_TARGET_COUNT := 16394	(* 0x0000400A *).
Notation C_VMCS_EXIT_CTLS := 16396	(* 0x0000400C *).
Notation C_VMCS_EXIT_MSR_STORE_COUNT := 16398	(* 0x0000400E *).
Notation C_VMCS_EXIT_MSR_LOAD_COUNT := 16400	(* 0x00004010 *).
Notation C_VMCS_ENTRY_CTLS := 16402	(* 0x00004012 *).
Notation C_VMCS_ENTRY_MSR_LOAD_COUNT := 16404	(* 0x00004014 *).
Notation C_VMCS_ENTRY_INTR_INFO := 16406	(* 0x00004016 *).
Notation C_VMCS_ENTRY_EXCEPTION_ERROR := 16408	(* 0x00004018 *).
Notation C_VMCS_ENTRY_INST_LENGTH := 16410	(* 0x0000401A *).
Notation C_VMCS_TPR_THRESHOLD := 16412	(* 0x0000401C *).
Notation C_VMCS_SEC_PROC_BASED_CTLS := 16414	(* 0x0000401E *).
Notation C_VMCS_PLE_GAP := 16416	(* 0x00004020 *).
Notation C_VMCS_PLE_WINDOW := 16418	(* 0x00004022 *).
Notation C_VMCS_INSTRUCTION_ERROR := 17408	(* 0x00004400 *).
Notation C_VMCS_EXIT_REASON := 17410	(* 0x00004402 *).
Notation C_VMCS_EXIT_INTERRUPTION_INFO := 17412	(* 0x00004404 *).
Notation C_VMCS_EXIT_INTERRUPTION_ERROR := 17414	(* 0x00004406 *).
Notation C_VMCS_IDT_VECTORING_INFO := 17416	(* 0x00004408 *).
Notation C_VMCS_IDT_VECTORING_ERROR := 17418	(* 0x0000440A *).
Notation C_VMCS_EXIT_INSTRUCTION_LENGTH := 17420	(* 0x0000440C *).
Notation C_VMCS_EXIT_INSTRUCTION_INFO := 17422	(* 0x0000440E *).
Notation C_VMCS_GUEST_ES_LIMIT := 18432	(* 0x00004800 *).
Notation C_VMCS_GUEST_CS_LIMIT := 18434	(* 0x00004802 *).
Notation C_VMCS_GUEST_SS_LIMIT := 18436	(* 0x00004804 *).
Notation C_VMCS_GUEST_DS_LIMIT := 18438	(* 0x00004806 *).
Notation C_VMCS_GUEST_FS_LIMIT := 18440	(* 0x00004808 *).
Notation C_VMCS_GUEST_GS_LIMIT := 18442	(* 0x0000480A *).
Notation C_VMCS_GUEST_LDTR_LIMIT := 18444	(* 0x0000480C *).
Notation C_VMCS_GUEST_TR_LIMIT := 18446	(* 0x0000480E *).
Notation C_VMCS_GUEST_GDTR_LIMIT := 18448	(* 0x00004810 *).
Notation C_VMCS_GUEST_IDTR_LIMIT := 18450	(* 0x00004812 *).
Notation C_VMCS_GUEST_ES_ACCESS_RIGHTS := 18452	(* 0x00004814 *).
Notation C_VMCS_GUEST_CS_ACCESS_RIGHTS := 18454	(* 0x00004816 *).
Notation C_VMCS_GUEST_SS_ACCESS_RIGHTS := 18456	(* 0x00004818 *).
Notation C_VMCS_GUEST_DS_ACCESS_RIGHTS := 18458	(* 0x0000481A *).
Notation C_VMCS_GUEST_FS_ACCESS_RIGHTS := 18460	(* 0x0000481C *).
Notation C_VMCS_GUEST_GS_ACCESS_RIGHTS := 18462	(* 0x0000481E *).
Notation C_VMCS_GUEST_LDTR_ACCESS_RIGHTS := 18464	(* 0x00004820 *).
Notation C_VMCS_GUEST_TR_ACCESS_RIGHTS := 18466	(* 0x00004822 *).
Notation C_VMCS_GUEST_INTERRUPTIBILITY := 18468	(* 0x00004824 *).
Notation C_VMCS_GUEST_ACTIVITY := 18470	(* 0x00004826 *).
Notation C_VMCS_GUEST_SMBASE := 18472	(* 0x00004828 *).
Notation C_VMCS_GUEST_IA32_SYSENTER_CS := 18474	(* 0x0000482A *).
Notation C_VMCS_PREEMPTION_TIMER_VALUE := 18478	(* 0x0000482E *).
Notation C_VMCS_HOST_IA32_SYSENTER_CS := 19456	(* 0x00004C00 *).
Notation C_VMCS_CR0_MASK := 24576	(* 0x00006000 *).
Notation C_VMCS_CR4_MASK := 24578	(* 0x00006002 *).
Notation C_VMCS_CR0_SHADOW := 24580	(* 0x00006004 *).
Notation C_VMCS_CR4_SHADOW := 24582	(* 0x00006006 *).
Notation C_VMCS_CR3_TARGET0 := 24584	(* 0x00006008 *).
Notation C_VMCS_CR3_TARGET1 := 24586	(* 0x0000600A *).
Notation C_VMCS_CR3_TARGET2 := 24588	(* 0x0000600C *).
Notation C_VMCS_CR3_TARGET3 := 24590	(* 0x0000600E *).
Notation C_VMCS_EXIT_QUALIFICATION := 25600	(* 0x00006400 *).
Notation C_VMCS_IO_RCX := 25602	(* 0x00006402 *).
Notation C_VMCS_IO_RSI := 25604	(* 0x00006404 *).
Notation C_VMCS_IO_RDI := 25606	(* 0x00006406 *).
Notation C_VMCS_IO_RIP := 25608	(* 0x00006408 *).
Notation C_VMCS_GUEST_LINEAR_ADDRESS := 25610	(* 0x0000640A *).
Notation C_VMCS_GUEST_CR0 := 26624	(* 0x00006800 *).
Notation C_VMCS_GUEST_CR3 := 26626	(* 0x00006802 *).
Notation C_VMCS_GUEST_CR4 := 26628	(* 0x00006804 *).
Notation C_VMCS_GUEST_ES_BASE := 26630	(* 0x00006806 *).
Notation C_VMCS_GUEST_CS_BASE := 26632	(* 0x00006808 *).
Notation C_VMCS_GUEST_SS_BASE := 26634	(* 0x0000680A *).
Notation C_VMCS_GUEST_DS_BASE := 26636	(* 0x0000680C *).
Notation C_VMCS_GUEST_FS_BASE := 26638	(* 0x0000680E *).
Notation C_VMCS_GUEST_GS_BASE := 26640	(* 0x00006810 *).
Notation C_VMCS_GUEST_LDTR_BASE := 26642	(* 0x00006812 *).
Notation C_VMCS_GUEST_TR_BASE := 26644	(* 0x00006814 *).
Notation C_VMCS_GUEST_GDTR_BASE := 26646	(* 0x00006816 *).
Notation C_VMCS_GUEST_IDTR_BASE := 26648	(* 0x00006818 *).
Notation C_VMCS_GUEST_DR7 := 26650	(* 0x0000681A *).
Notation C_VMCS_GUEST_RSP := 26652	(* 0x0000681C *).
Notation C_VMCS_GUEST_RIP := 26654	(* 0x0000681E *).
Notation C_VMCS_GUEST_RFLAGS := 26656	(* 0x00006820 *).
Notation C_VMCS_GUEST_PENDING_DBG_EXCEPTIONS := 26658	(*  0x00006822 *).
Notation C_VMCS_GUEST_IA32_SYSENTER_ESP := 26660	(* 0x00006824 *).
Notation C_VMCS_GUEST_IA32_SYSENTER_EIP := 26662	(* 0x00006826 *).
Notation C_VMCS_HOST_CR0 := 27648	(* 0x00006C00 *).
Notation C_VMCS_HOST_CR3 := 27650	(* 0x00006C02 *).
Notation C_VMCS_HOST_CR4 := 27652	(* 0x00006C04 *).
Notation C_VMCS_HOST_FS_BASE := 27654	(* 0x00006C06 *).
Notation C_VMCS_HOST_GS_BASE := 27656	(* 0x00006C08 *).
Notation C_VMCS_HOST_TR_BASE := 27658	(* 0x00006C0A *).
Notation C_VMCS_HOST_GDTR_BASE := 27660	(* 0x00006C0C *).
Notation C_VMCS_HOST_IDTR_BASE := 27662	(* 0x00006C0E *).
Notation C_VMCS_HOST_IA32_SYSENTER_ESP := 27664	(* 0x00006C10 *).
Notation C_VMCS_HOST_IA32_SYSENTER_EIP := 27666	(* 0x00006C12 *).
Notation C_VMCS_HOST_RSP := 27668	(* 0x00006C14 *).
Notation C_VMCS_HOST_RIP := 27670	(* 0x00006c16 *).    
Notation MAX_INT_16 := 65535.
Notation MAX_INT_32 := 4294967296.
Notation MAX_INT_64 := 18446744073709551616.


(* structure of vmx
struct vmx {
	/*
	 * VMCS does not store following registers for guest, so we have
	 * to do that by ourself.
	 */
	uint64_t	g_rax, g_rbx, g_rcx, g_rdx, g_rsi, g_rdi, g_rbp, g_rip;
	uint32_t	g_cr2;
	uint32_t	g_dr0, g_dr1, g_dr2, g_dr3, g_dr6;
	uint32_t	enter_tsc[2], exit_tsc[2];


	uint32_t	vpid;

	uint32_t	exit_reason;
	uint64_t	exit_qualification;
	int32_t		pending_intr;

	int		launched;
	int		failed;
        uint32_t        h_rdi, h_rbp;
};*)

Notation VMX_G_RAX := 0.
Notation VMX_G_RBX := 8.
Notation VMX_G_RCX := 16.
Notation VMX_G_RDX := 24.
Notation VMX_G_RSI := 32.
Notation VMX_G_RDI := 40.
Notation VMX_G_RBP := 48.
Notation VMX_G_RIP := 56.
Notation VMX_G_CR2 := 64.
Notation VMX_G_DR0 := 68.
Notation VMX_G_DR1 := 72.
Notation VMX_G_DR2 := 76.
Notation VMX_G_DR3 := 80.
Notation VMX_G_DR6 := 84.
Notation VMX_ENTER_TSC0 := 88.
Notation VMX_ENTER_TSC1 := 92.
Notation VMX_EXIT_TSC0 := 96.
Notation VMX_EXIT_TSC1 := 100.
Notation VMX_VPID := 104.
Notation VMX_EXIT_REASON := 108.
Notation VMX_EXIT_QUALIFICATION := 112.
Notation VMX_PENDING_INTR := 120.
Notation VMX_LAUNCHED := 124.
Notation VMX_FAILED := 128.
Notation VMX_HOST_EBP := 132.
Notation VMX_HOST_EDI := 136.
Notation VMX_HOST_EIP := 140.
Notation VMX_Size := 144.

Notation VMX_G_RAX' := 0.
Notation VMX_G_RBX' := 2.
Notation VMX_G_RCX' := 4.
Notation VMX_G_RDX' := 6.
Notation VMX_G_RSI' := 8.
Notation VMX_G_RDI' := 10.
Notation VMX_G_RBP' := 12.
Notation VMX_G_RIP' := 14.
Notation VMX_G_CR2' := 16.
Notation VMX_G_DR0' := 17.
Notation VMX_G_DR1' := 18.
Notation VMX_G_DR2' := 19.
Notation VMX_G_DR3' := 20.
Notation VMX_G_DR6' := 21.
Notation VMX_ENTER_TSC0' := 22.
Notation VMX_ENTER_TSC1' := 23.
Notation VMX_EXIT_TSC0' := 24.
Notation VMX_EXIT_TSC1' := 25.
Notation VMX_VPID' := 26.
Notation VMX_EXIT_REASON' := 27.
Notation VMX_EXIT_QUALIFICATION' := 28.
Notation VMX_PENDING_INTR' := 30.
Notation VMX_LAUNCHED' := 31.
Notation VMX_FAILED' := 32.
Notation VMX_HOST_EBP' := 33.
Notation VMX_HOST_EDI' := 34.
Notation VMX_HOST_EIP' := 35.
Notation VMX_Size' := 36.

Notation C_GUEST_EAX := 0.
Notation C_GUEST_EBX := 1.
Notation C_GUEST_ECX := 2.
Notation C_GUEST_EDX := 3.
Notation C_GUEST_ESI := 4.
Notation C_GUEST_EDI := 5.
Notation C_GUEST_EBP := 6.
Notation C_GUEST_ESP := 7.
Notation C_GUEST_EIP := 8.
Notation C_GUEST_EFLAGS := 9.
Notation C_GUEST_CR0 := 10.
Notation C_GUEST_CR2 := 11.
Notation C_GUEST_CR3 := 12.
Notation C_GUEST_CR4 := 13.
Notation C_GUEST_MAX_REG := 14.

Notation C_GUEST_CS := 0.
Notation C_GUEST_DS := 1.
Notation C_GUEST_ES := 2.
Notation C_GUEST_FS := 3.
Notation C_GUEST_GS := 4.
Notation C_GUEST_SS := 5.
Notation C_GUEST_LDTR := 6.
Notation C_GUEST_TR := 7.
Notation C_GUEST_GDTR := 8.
Notation C_GUEST_IDTR := 9.
Notation C_GUEST_MAX_SEG_DESC := 10.

Notation MSR_VMX_BASIC := 1152. (* 0x480 *)

Notation EXIT_QUAL_IO_ONE_BYTE := 0.
Notation EXIT_QUAL_IO_TWO_BYTE := 1.
Notation EXIT_QUAL_IO_FOUR_BYTE := 4.
Notation EXIT_QUAL_IO_SIZE := 7.

Notation EXIT_QUAL_IO_OUT := 0.
Notation EXIT_QUAL_IO_IN := 1.
Notation EXIT_QUAL_IO_DIR := 3.

Notation EXIT_REASON_MASK := 65535. (*0x0000ffff*)

Notation PROCBASED_INT_WINDOW_EXITING := 4.

Notation VMCS_INTERRUPTION_INFO_VALID := 2147483648. (* 1U << 31 *)
Notation VMCS_INTERRUPTION_INFO_EV := 2048. (* 11 *)

Notation VMCS_INTERRUPTIBILITY_STI_BLOCKING := 1.
Notation VMCS_INTERRUPTIBILITY_MOVSS_BLOCKING := 2.
Notation VMCS_INTERRUPTIBILITY_STI_or_MOVSS_BLOCKING := 3.


Notation CPU_GDT_KDATA := 16. (*0x10*)
Notation CPU_GDT_KCODE := 8. (*0x08*)
Notation CPU_GDT_TSS := 40. (*0x28*)

Notation MSR_IA32_SYSENTER_CS := 372.  (*0x174*)
Notation MSR_IA32_SYSENTER_ESP := 373.  (*0x175*)
Notation MSR_IA32_SYSENTER_EIP := 374.  (*0x176*)
Notation MSR_PAT := 631.  (*0x277*)
Notation MSR_IA32_PERF_GLOBAL_CTRL := 911.  (*0x38f*)
Notation MSR_EFER := 3221225600. (*0xc0000080*)

Notation CR0_PE := 1.  (*0x00000001*)
Notation CR0_MP := 2.  (*0x00000002*)
Notation CR0_EM := 4.  (*0x00000004*)
Notation CR0_TS := 8.  (*0x00000008*)
Notation CR0_NE := 32.  (*0x00000020*)
Notation CR0_WP := 65536.  (*0x00010000*)
Notation CR0_AM := 262144.  (*0x00040000*)
Notation CR0_PG := 2147483648.  (*0x80000000*)

Notation v0x60000010 := 1610612752. (*0x60000010*)
Notation CR4_VMXE := 8192. (*1 << 13*)
Notation v0x00000400 := 1024. (*0x00000400*)
Notation v0x7040600070406 := 1974748653749254. (*0x7040600070406ULL*)
Notation v0xffffffffffffffff := 18446744073709551615.

Notation EXIT_QUAL_IO_REP := 5.
Notation EXIT_QUAL_IO_STR := 4.
Notation EXIT_REASON_ENTRY_FAIL := 2147483648. (*1 << 31*)
Notation C_EXIT_QUAL_IO_PORT := 65536.
Notation v0xffffffff := 4294967295.
Notation v0xfff0 := 65520.
Notation v0xffff0ff0 := 4294905840.



(*EPT *)

Notation EPT_NO_PERM:= 4294967288. (*~(uint32_t) 0x7)*)
Notation EPT_ADDR_OFFSET_MASK := 4095.

Notation EPT_PG_IGNORE_PAT_or_PERM:= 71.
Notation EPT_ADDR_MASK := 4294963200. (*0xfffff000*)
Notation EPT_PG_MEMORY_TYPE := 3.

Notation EPTP_pml4 := 30.
Notation T_MCHK_SHIFT := 262144.


(* VMX_INFO *)
Notation VMX_INFO_VMX_ENABLED := 1.
Notation VMX_INFO_PINBASED_CTLS := 2.
Notation VMX_INFO_PROCBASED_CTLS := 3.
Notation VMX_INFO_PROCBASED_CTLS2 := 4.
Notation VMX_INFO_EXIT_CTLS := 5.
Notation VMX_INFO_ENTRY_CTLS := 6.
Notation VMX_INFO_CR0_ONES_MASK := 7.
Notation VMX_INFO_CR0_ZEROS_MASK := 9.
Notation VMX_INFO_CR4_ONES_MASK := 11.
Notation VMX_INFO_CR4_ZEROS_MASK := 13.
Notation VMX_INFO_VMX_REGION := 14.


Notation E_SUCC := 0. (*no errors *)
Notation E_MEM := 1. (* memory failure *)
Notation E_IPC := 2.
Notation E_INVAL_CALLNR := 3. (* invalid syscall number *)
Notation E_INVAL_ADDR := 4. (* invalid address *)
Notation E_INVAL_PID := 5. (* invalid process ID *)
Notation E_INVAL_REG := 6.
Notation E_INVAL_SEG := 7.
Notation E_INVAL_EVENT := 8.
Notation E_INVAL_PORT := 9.
Notation E_INVAL_HVM := 10.
Notation E_INVAL_CHID := 11.
Notation E_DISK_OP := 12. (* disk operation failure *)
Notation E_HVM_VMRUN := 13.
Notation E_HVM_MMAP := 14.
Notation E_HVM_REG := 15.
Notation E_HVM_SEG := 16.
Notation E_HVM_NEIP := 17.
Notation E_HVM_INJECT := 18.
Notation E_HVM_IOPORT := 19.
Notation E_HVM_MSR := 20.
Notation E_HVM_INTRWIN := 21.
Notation MAX_ERROR_NR := 22.

Notation v0xfffff000 := 4294963200.

Notation EXIT_REASON_INOUT:= 30.
Notation EXIT_REASON_EPT_FAULT:= 48.

Notation SYS_puts := 0.	(* output a string to the screen *)
Notation SYS_ring0_spawn := 1. (* create a new ring0 process *)
Notation SYS_spawn := 2. (* create a new process *)
Notation SYS_yield := 3. (* yield to another process *)
Notation SYS_sleep := 4.
Notation SYS_disk_op := 5. (* perform a disk operation *)
Notation SYS_disk_cap := 6. (* get the capacity of a disk in bytes *)
Notation SYS_is_chan_ready := 7.
Notation SYS_send := 8.
Notation SYS_recv := 9.
Notation SYS_get_tsc_per_ms := 10.
Notation SYS_hvm_run_vm := 11.
Notation SYS_hvm_get_exitinfo := 12.
Notation SYS_hvm_mmap := 13.
Notation SYS_hvm_set_seg := 14.
Notation SYS_hvm_set_reg := 15.
Notation SYS_hvm_get_reg := 16.
Notation SYS_hvm_get_next_eip := 17.
Notation SYS_hvm_inject_event := 18.
Notation SYS_hvm_check_int_shadow := 19.
Notation SYS_hvm_check_pending_event := 20.
Notation SYS_hvm_intercept_int_window := 21.
Notation SYS_hvm_get_tsc_offset := 22.
Notation SYS_hvm_set_tsc_offset := 23.
Notation SYS_hvm_handle_rdmsr := 24.
Notation SYS_hvm_handle_wrmsr := 25.
Notation SYS_get_quota := 26.
Notation MAX_SYSCALL_NR := 27. (* XXX: always put it at the end of __syscall_nr *)
