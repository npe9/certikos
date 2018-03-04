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
(** Dependencies for extraction *)
Require Import Coqlib.
Require Wfsimpl.
Require AST.
Require Iteration.
Require Floats.
Require SelectLong.
Require RTLgen.
Require Inlining.
Require ValueDomain.
Require Tailcall.
Require Allocation.
Require Ctypes.
Require Csyntax.
Require Int31.
(** [CompCertX:test-compcert-param-memory] instantiations of extractees with concrete memory model *)
Require InitializersImpl.
Require Import mcertikos.driver.CertiKOSImpl.

Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.logic.Modules.
Require Import liblayers.logic.Layers.
Require Import String.

Require Import mcertikos.clib.CDataTypes.
(*Require Import mcertikos.mm.BootGenLinkSource.*)
Require Import mcertikos.mm.ALInitGenLinkSource.
Require Import mcertikos.mm.ALOpGenLinkSource.
Require Import mcertikos.mm.ALGenLinkSource.
Require Import mcertikos.mm.ContainerGenLinkSource.
Require Import mcertikos.mm.PTIntroGenLinkSource.
Require Import mcertikos.mm.PTOpGenLinkSource.
Require Import mcertikos.mm.PTCommGenLinkSource.
Require Import mcertikos.mm.PTKernGenLinkSource.
Require Import mcertikos.mm.PTInitGenLinkSource.
Require Import mcertikos.mm.PTNewGenLinkSource.
Require Import mcertikos.mm.ShareIntroGenLinkSource.
Require Import mcertikos.mm.ShareOpGenLinkSource.
Require Import mcertikos.mm.ShareGenLinkSource.
Require Import mcertikos.proc.KContextGenLinkSource.
Require Import mcertikos.proc.KContextNewGenLinkSource.
Require Import mcertikos.proc.ThreadIntroGenLinkSource.
Require Import mcertikos.proc.ThreadInitGenLinkSource.
Require Import mcertikos.proc.QueueIntroGenLinkSource.
Require Import mcertikos.proc.QueueInitGenLinkSource.
Require Import mcertikos.proc.CurIDGenLinkSource.
Require Import mcertikos.proc.ThreadSchedGenLinkSource.
Require Import mcertikos.proc.ThreadGenLinkSource.
Require Import mcertikos.proc.IPCIntroGenLinkSource.
Require Import mcertikos.proc.IPCGenLinkSource.
Require Import mcertikos.proc.UCtxtIntroGenLinkSource.
Require Import mcertikos.proc.ProcGenLinkSource.
Require Import mcertikos.trap.TrapArgGenLinkSource.
Require Import mcertikos.trap.TrapGenLinkSource.
Require Import mcertikos.trap.DispatchGenLinkSource.
Require Import mcertikos.trap.SysCallGenLinkSource.
(*Require Import mcertikos.virt.intel.EPTIntroGenLinkSource.
Require Import mcertikos.virt.intel.EPTOpGenLinkSource.
Require Import mcertikos.virt.intel.EPTInitGenLinkSource.
Require Import mcertikos.virt.intel.VMCSIntroGenLinkSource.
Require Import mcertikos.virt.intel.VMCSInitGenLinkSource.
Require Import mcertikos.virt.intel.VMXIntroGenLinkSource.
Require Import mcertikos.virt.intel.VMXInitGenLinkSource.*)

Require Import CompCertiKOSproofImpl.
Require Import RealParamsImpl.

Section WITHCOMPCERTIKOS.

  (*Definition add_loc {A} s (r: res A): res A :=
    match r with
      | OK a => OK a
      | Error e => Error (MSG (append s ": ") :: e)
    end.*)
  Definition add_loc {A} (s: string) (r: res A) := r.

  Local Notation "M ⊗ Mrest" := (Mrest ⊕ M)
    (right associativity, at level 35, only parsing).

  Definition certikos_plus_ctxt CTXT: res LAsm.module :=
    (*M0000 <- add_loc "MBoot" MBoot_impl;*)
    M0010 <- add_loc "MALInit" MALInit_impl;
    M0020 <- add_loc "MALOp" MALOp_impl;
    M0030 <- add_loc "MALT" MALT_impl;
    M0040 <- add_loc "MContainer" MContainer_impl;
    M0050 <- add_loc "MPTIntro" MPTIntro_impl;
    M0060 <- add_loc "MPTOp" MPTOp_impl;
    M0070 <- add_loc "MPTCommon" MPTCommon_impl;
    M0080 <- add_loc "MPTKern" MPTKern_impl;
    M0090 <- add_loc "MPTInit" MPTInit_impl;
    M0110 <- add_loc "MPTNew" MPTNew_impl;
    M0120 <- add_loc "MShareIntro" MShareIntro_impl;
    M0130 <- add_loc "MShareOp" MShareOp_impl;
    M0140 <- add_loc "MShare" MShare_impl;

    M1000 <- add_loc "PKContext" PKContext_impl;
    M1010 <- add_loc "PKContextNew" PKContextNew_impl;
    M1020 <- add_loc "PThreadIntro" PThreadIntro_impl;
    M1030 <- add_loc "PThreadInit" PThreadInit_impl;
    M1040 <- add_loc "PQueueIntro" PQueueIntro_impl;
    M1050 <- add_loc "PQueueInit" PQueueInit_impl;
    (* ∅ for PAbQueue here. *)
    M1060 <- add_loc "PCurID" PCurID_impl;
    M1070 <- add_loc "PThreadSched" PThreadSched_impl;
    M1080 <- add_loc "PThread" PThread_impl;
    M1090 <- add_loc "PIPCIntro" PIPCIntro_impl;
    M1100 <- add_loc "PIPC" PIPC_impl;
    M1110 <- add_loc "PUCtxtIntro" PUCtxtIntro_impl;
    M1120 <- add_loc "PProc" PProc_impl;

    (*M2000 <- add_loc "VEPTIntro" VEPTIntro_impl;
    M2010 <- add_loc "VEPTOp" VEPTOp_impl;
    M2020 <- add_loc "VEPTInit" VEPTInit_impl;
    M2030 <- add_loc "VVMCSIntro" VVMCSIntro_impl;
    M2040 <- add_loc "VVMCSInit" VVMCSInit_impl;
    M2050 <- add_loc "VVMXIntro" VVMXIntro_impl;
    M2060 <- add_loc "VVMXInit" VVMXInit_impl;*)

    M3000 <- add_loc "TTrapArg" TTrapArg_impl;
    M3010 <- add_loc "TTrap" TTrap_impl;
    M3020 <- add_loc "TDispatch" TDispatch_impl;
    M3030 <- add_loc "TSysCall" TSysCall_impl;

    ret ((*M0000 ⊗ *)M0010 ⊗ M0020 ⊗ M0030 ⊗ M0040 ⊗ M0050 ⊗ M0060 ⊗ M0070 ⊗
         M0080 ⊗ M0090 ⊗ M0110 ⊗ M0120 ⊗ M0130 ⊗ M0140 ⊗ 

         M1000 ⊗ M1010 ⊗ M1020 ⊗ M1030 ⊗ M1040 ⊗ M1050 ⊗ ∅ ⊗ M1060 ⊗ M1070 ⊗
         M1080 ⊗ M1090 ⊗ M1100 ⊗ M1110 ⊗ M1120 ⊗

         (*M2000 ⊗ M2010 ⊗ M2020 ⊗ M2030 ⊗ M2040 ⊗ M2050 ⊗ M2060 ⊗*)

         M3000 ⊗ M3010 ⊗ M3020 ⊗ M3030 ⊗

         CTXT).

  Definition certikos := certikos_plus_ctxt ∅.

End WITHCOMPCERTIKOS.
