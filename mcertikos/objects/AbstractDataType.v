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
(*              The Type of Abstract State                             *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the raw abstract data and the primitives for the MBoot layer, 
which is also the bottom layer of memory management*)
Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import FlatMemory.
Require Import Values.
Require Import Memory.
Require Import AuxLemma.
Require Import Constant.
Require Export MMDataType.
Require Import liblayers.compat.CompatLayers.
Require Import Observation.

Section ABDATA.

  Local Open Scope Z_scope.

  (*Context `{real_params: RealParams}.*)

  (** * Raw Abstract Data*)
  Record RData :=
    mkRData {

        MM: MMTable; (**r table of the physical memory's information*)
        MMSize: Z; (**r size of MMTable*)
        vmxinfo: VMXInfo; (**r information of vmx*)
        devout: DeviceOutput; (**r device output*)

        CR3: globalpointer; (**r abstract of CR3, stores the pointer to page table*)
        ti: trapinfo; (**r abstract of CR2, stores the address where page fault happens*)

        pg: bool; (**r abstract of CR0, indicates whether the paging is enabled or not*)
        ikern: bool; (**r pure logic flag, shows whether it's in kernel mode or not*)
        ihost: bool; (**r logic flag, shows whether it's in the host mode or not*)         

        HP: flatmem; (**r we model the memory from 1G to 3G as heap*)

        AC : ContainerPool; (**r container tree for all agents *)

        AT: ATable; (**r allocation table*)
        nps: Z; (**r number of the pages*)
        init: bool; (**r pure logic flag, show whether the initialization at this layer has been called or not*)
        pperm: PPermT; (**r physical page permission table *)

        PT: Z; (**r the current page table index*)
        ptpool: PMapPool; (**r page table pool*)
        idpde: IDPDE; (**r shared identity maps *)
        ipt: bool; (**r pure logic flag, shows whether the current page map is the kernel's page map*)
        LAT: LATable; (**r allocation table*)
        smspool: SharedMemSTPool; (**r the shared-memory pool for IPC*)

        kctxt: KContextPool; (**r kernel context pool*)
        tcb: TCBPool; (*r thread control blocks pool*)                 
        tdq: TDQueuePool; (**r thread queue pool*)
        abtcb: AbTCBPool; (**r thread control blocks pool*)
        abq: AbQueuePool; (**r thread queue pool*)
        cid: Z; (**r current thread id*) 
        syncchpool : SyncChanPool; (**r the channel pool for synchronous IPC*)

        uctxt : UContextPool; (**r user context pool*)

        ept: EPT; (**r nested page table for guest mode*)
        vmcs: VMCS; (**r virtual machine control structure for current VM *)

        vmx: VMX (**r VMX structure to store the extra registers of host *)
      }.

  (** functions to update each field of the record *)
  Section UPDATE_FUNCTION. 

    Definition update_MM (a : RData) b := 
      mkRData b (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_MMSize (a : RData) b := 
      mkRData (MM a) b (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_vmxinfo (a : RData) b := 
      mkRData (MM a) (MMSize a) b (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_devout (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) b (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_CR3 (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) b (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_ti (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) b (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_pg (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) b (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_ikern (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) b (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_ihost (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) b (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_HP (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) b
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_AC (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              b (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_AT (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) b (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_nps (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) b (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_init (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) b (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_pperm (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) b (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_PT (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) b (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_ptpool (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) b (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_idpde (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) b (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_ipt (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) b
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_LAT (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              b (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_smspool (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) b (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_kctxt (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) b (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_tcb (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) b (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_tdq (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) b (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_abtcb (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) b (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_abq (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) b (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_cid (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) b (syncchpool a)
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_syncchpool (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) b
              (uctxt a) (ept a) (vmcs a) (vmx a).

    Definition update_uctxt (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              b (ept a) (vmcs a) (vmx a).

    Definition update_ept (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) b (vmcs a) (vmx a).

    Definition update_vmcs (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) b (vmx a).

    Definition update_vmx (a : RData) b := 
      mkRData (MM a) (MMSize a) (vmxinfo a) (devout a) (CR3 a) (ti a) (pg a) (ikern a) (ihost a) (HP a)
              (AC a) (AT a) (nps a) (init a) (pperm a) (PT a) (ptpool a) (idpde a) (ipt a)
              (LAT a) (smspool a) (kctxt a) (tcb a) (tdq a) (abtcb a) (abq a) (cid a) (syncchpool a)
              (uctxt a) (ept a) (vmcs a) b.

  End UPDATE_FUNCTION.  

  Definition init_adt := 
    mkRData (ZMap.init MMUndef) 0 (ZMap.init 0) (ZMap.init nil)
            GLOBUndef init_trap_info false true true FlatMem.empty_flatmem
            (ZMap.init Container_unused)
            (ZMap.init ATUndef) 0 false (ZMap.init PGUndef) (-1) (ZMap.init (ZMap.init PDEUndef))
            (ZMap.init (ZMap.init IDPTEUndef)) true (ZMap.init LATUndef) 
            (ZMap.init (ZMap.init SHRDUndef)) (ZMap.init (Pregmap.init Vundef)) 
            (ZMap.init TCBUndef) (ZMap.init TDQUndef) (ZMap.init AbTCBUndef) (ZMap.init AbQUndef)
            0 (*(ZMap.init ChanUndef)*)
            (ZMap.init SyncChanUndef)
            (ZMap.init (ZMap.init Vundef)) (ZMap.init EPML4EUndef)
            (VMCSValid Vzero Vzero (ZMap.init Vundef)) (ZMap.init Vundef).

End ABDATA.

(** the notation to update each field of the record *)
Notation "a {MM : b }" := (update_MM a b) (at level 1).
Notation "a {MMSize : b }" := (update_MMSize a b) (at level 1).
Notation "a {vmxinfo : b }" := (update_vmxinfo a b) (at level 1).
Notation "a {devout : b }" := (update_devout a b) (at level 1).
Notation "a {CR3 : b }" := (update_CR3 a b) (at level 1).
Notation "a {ti : b }" := (update_ti a b) (at level 1).
Notation "a {pg : b }" := (update_pg a b) (at level 1).
Notation "a {ikern : b }" := (update_ikern a b) (at level 1).
Notation "a {ihost : b }" := (update_ihost a b) (at level 1).
Notation "a {HP : b }" := (update_HP a b) (at level 1).
Notation "a {AC : b }" := (update_AC a b) (at level 1).
Notation "a {AT : b }" := (update_AT a b) (at level 1).
Notation "a {nps : b }" := (update_nps a b) (at level 1).
Notation "a {init : b }" := (update_init a b) (at level 1).
Notation "a {pperm : b }" := (update_pperm a b) (at level 1).
Notation "a {PT : b }" := (update_PT a b) (at level 1).
Notation "a {ptpool : b }" := (update_ptpool a b) (at level 1).
Notation "a {idpde : b }" := (update_idpde a b) (at level 1).
Notation "a {ipt : b }" := (update_ipt a b) (at level 1).
Notation "a {LAT : b }" := (update_LAT a b) (at level 1).
Notation "a {smspool : b }" := (update_smspool a b) (at level 1).
Notation "a {kctxt : b }" := (update_kctxt a b) (at level 1).
Notation "a {tcb : b }" := (update_tcb a b) (at level 1).
Notation "a {tdq : b }" := (update_tdq a b) (at level 1).
Notation "a {abtcb : b }" := (update_abtcb a b) (at level 1).
Notation "a {abq : b }" := (update_abq a b) (at level 1).
Notation "a {cid : b }" := (update_cid a b) (at level 1).
Notation "a {syncchpool : b }" := (update_syncchpool a b) (at level 1).
Notation "a {uctxt : b }" := (update_uctxt a b) (at level 1).
Notation "a {ept : b }" := (update_ept a b) (at level 1).
Notation "a {vmcs : b }" := (update_vmcs a b) (at level 1).
Notation "a {vmx : b }" := (update_vmx a b) (at level 1).

Section LOW_INV.

  Record low_level_invariant (n: block) (adt: RData) := 
    mkLowInv {
        CR2_INJECT: val_inject (Mem.flat_inj n) (snd (ti adt)) (snd (ti adt));
        CR2_Type: Val.has_type (snd (ti adt)) AST.Tint;
        kctxt_INJECT: kctxt_inject_neutral (kctxt adt) n;
        uctxt_INJECT: uctxt_inject_neutral (uctxt adt) n;
        VMCS_INJECT: VMCS_inject_neutral (vmcs adt) n;
        VMX_INJECT: VMX_inject_neutral (vmx adt) n
      }.

  Lemma low_level_invariant_incr:
    forall (n n': positive) a,
      (n <= n')%positive ->
      low_level_invariant n a ->
      low_level_invariant n' a.
  Proof.
    inversion 2; subst.
    intros; constructor; trivial.
    - eapply val_inject_incr; [|eauto].
      apply flat_inj_inject_incr; trivial.
    - intros until 2. exploit kctxt_INJECT0; eauto.
      intros [? ?]. split; try assumption.
      eapply val_inject_incr; try eassumption.
      apply flat_inj_inject_incr; trivial.
    - intros until 2. exploit uctxt_INJECT0; eauto.
      intros [? ?]. split; try assumption.
      eapply val_inject_incr; try eassumption.
      apply flat_inj_inject_incr; trivial.
    - inv VMCS_INJECT0. constructor; intros.
      destruct (H2 ofs) as (? & ?).
      split; try assumption.
      eapply val_inject_incr; try eassumption.
      apply flat_inj_inject_incr; trivial.
    - inv VMX_INJECT0. constructor; intros.
      destruct (H1 ofs) as (? & ?).
      split; try assumption.
      eapply val_inject_incr; try eassumption.
      apply flat_inj_inject_incr; trivial.
  Qed.

  Lemma empty_data_low_level_invariant:
    forall n, low_level_invariant n init_adt.
  Proof.
    constructor; simpl; auto.
    - intros until 2. rewrite ZMap.gi. rewrite Pregmap.gi.
      split; constructor.
    - intros until 2. repeat rewrite ZMap.gi.
      split; constructor.
    - constructor. intros. subst v. repeat rewrite ZMap.gi.
      split; constructor.
    - constructor. intros. subst v. repeat rewrite ZMap.gi.
      split; constructor.
  Qed.

End LOW_INV.

Section InstanceT.

  Context `{Hobs: Observation}.

  Context `{data : CompatData(Obs:=Obs) RData}.
  Context `{data0 : CompatData(Obs:=Obs) RData}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  Notation LDATAOps := (cdata (cdata_ops := data_ops0) RData).

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.

  Context `{rel_prf: CompatRel _ (Obs:= Obs) (memory_model_ops:= memory_model_ops) _ 
                               (stencil_ops:= stencil_ops) HDATAOps LDATAOps}.

  Section CLASS_IFLAGS.

    Record impl_iflags d1 d2 :=
      {
        ikern_eq : ikern d1 = ikern d2;

        ihost_eq: ihost d1 = ihost d2;

        pg_eq : pg d1 = pg d2
      }.

    Class relate_impl_iflags :=
      {
        relate_impl_iflags_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          impl_iflags d1 d2;

        (* should be lifted as a property of relate_AbData *)
        relate_impl_ikern_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {ikern: b} d2 {ikern: b};

        relate_impl_ihost_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {ihost: b} d2 {ihost: b};

        relate_impl_pg_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {pg: b} d2 {pg: b}

      }.

    Class match_impl_iflags :=
      {
        match_impl_ikern_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {ikern: b} m f;

        match_impl_ihost_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {ihost: b} m f;

        match_impl_pg_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {pg: b} m f

      }.

  End CLASS_IFLAGS.

  Section CLASS_MM.

    Class relate_impl_MM :=
      {
        (* should be lifted as a property of relate_AbData *)
        relate_impl_MM_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {MM: b} d2 {MM: b};

        relate_impl_MMSize_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {MMSize: b} d2 {MMSize: b}

      }.

    Class relate_impl_MM' :=
      {
        relate_impl_MM_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (MM d1) = (MM d2);

        relate_impl_MMSize_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (MMSize d1) = (MMSize d2)
      }.

    Class match_impl_MM :=
      {
        match_impl_MM_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {MM: b} m f;

        match_impl_MMSize_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {MMSize: b} m f

      }.

  End CLASS_MM.

  Section CLASS_vmxinfo.

    Class relate_impl_vmxinfo :=
      {
        relate_impl_vmxinfo_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          vmxinfo d1 = vmxinfo d2;

        relate_impl_vmxinfo_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b, relate_AbData s ι d1 {vmxinfo: b} d2 {vmxinfo: b}
      }.

    Class match_impl_vmxinfo :=
      {
        match_impl_vmxinfo_update ι d m f:
          match_AbData ι d m f ->
          forall b, match_AbData ι d {vmxinfo: b} m f
      }.

  End CLASS_vmxinfo.

  Section CLASS_TI.

    Record impl_trapinfo f d1 d2 :=
      {
        ti_fst_eq : fst (ti d1) = fst (ti d2);

        ti_snd_eq: val_inject f (snd (ti d1)) (snd (ti d2))
      }.

    Class relate_impl_trapinfo :=
      {
        relate_impl_trapinfo_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          impl_trapinfo ι d1 d2;

        relate_impl_trapinfo_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall v r1 r2,
            val_inject ι r1 r2 ->
            relate_AbData s ι d1 {ti: (v,r1)} d2 {ti: (v,r2)}
      }.

    Class match_impl_trapinfo :=
      {
        match_impl_trapinfo_update s d m f:
          match_AbData s d m f ->
          forall b,
            match_AbData s d {ti: b} m f
      }.

  End CLASS_TI.

  Section CLASS_HP.

    Class relate_impl_HP :=
      {
        relate_impl_HP_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          FlatMem.flatmem_inj (HP d1) (HP d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_HP_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b b',
            FlatMem.flatmem_inj b b' ->
            relate_AbData s ι d1 {HP: b} d2 {HP: b'}
      }.

    Class match_impl_HP :=
      {
        match_impl_HP_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {HP: b} m f
      }.

  End CLASS_HP.

  Section CLASS_HP'.

    Class relate_impl_HP' :=
      {
        relate_impl_HP'_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          FlatMem.flatmem_inj (HP d1) (HP d2)
      }.

  End CLASS_HP'.

  Section CLASS_NPS.

    Class relate_impl_nps :=
      {
        relate_impl_nps_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (nps d1) = (nps d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_nps_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {nps: b} d2 {nps: b}
      }.

    Class match_impl_nps :=
      {
        match_impl_nps_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {nps: b} m f
      }.

  End CLASS_NPS.

  Section CLASS_INIT.

    Class relate_impl_init :=
      {
        relate_impl_init_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (init d1) = (init d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_init_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {init: b} d2 {init: b}
      }.

    Class match_impl_init :=
      {
        match_impl_init_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {init: b} m f
      }.

  End CLASS_INIT.

  Section CLASS_AC.

    Class relate_impl_AC :=
      {
        relate_impl_AC_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          AC d1 = AC d2;

        relate_impl_AC_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b, relate_AbData s ι d1 {AC: b} d2 {AC: b}
      }.

    Class match_impl_AC :=
      {
        match_impl_AC_update ι d m f:
          match_AbData ι d m f ->
          forall b, match_AbData ι d {AC: b} m f
      }.

  End CLASS_AC.

  Section CLASS_AT.

    Class relate_impl_AT :=
      {
        relate_impl_AT_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (AT d1) = (AT d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_AT_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {AT: b} d2 {AT: b}
      }.

    Class match_impl_AT :=
      {
        match_impl_AT_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {AT: b} m f
      }.

  End CLASS_AT.

  Section CLASS_CR3.

    Class relate_impl_CR3 :=
      {
        relate_impl_CR3_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (CR3 d1) = (CR3 d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_CR3_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {CR3: b} d2 {CR3: b}

      }.

    Class match_impl_CR3 :=
      {
        match_impl_CR3_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {CR3: b} m f
      }.

  End CLASS_CR3.

  Section CLASS_PPERM.

    Class relate_impl_pperm :=
      {
        relate_impl_pperm_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          pperm d1 = pperm d2;

        (* should be lifted as a property of relate_AbData *)
        relate_impl_pperm_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {pperm: b} d2 {pperm: b}

      }.

    Class match_impl_pperm :=
      {
        match_impl_pperm_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {pperm: b} m f
      }.

  End CLASS_PPERM.

  Section CLASS_IPT.

    Class relate_impl_ipt :=
      {
        relate_impl_ipt_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          ipt d1 = ipt d2;

        (* should be lifted as a property of relate_AbData *)
        relate_impl_ipt_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {ipt: b} d2 {ipt: b}

      }.

    Class match_impl_ipt :=
      {
        match_impl_ipt_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {ipt: b} m f
      }.

  End CLASS_IPT.

  Section CLASS_syncchpool.

    Class relate_impl_syncchpool :=
      {
        relate_impl_syncchpool_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (syncchpool d1) = (syncchpool d2);

        relate_impl_syncchpool_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι  d1 {syncchpool: b} d2 {syncchpool: b}
      }.

    Class match_impl_syncchpool :=
      {
        match_impl_syncchpool_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {syncchpool: b} m f
      }.
  End CLASS_syncchpool.

  Section CLASS_PTPOOL.

    Class relate_impl_ptpool :=
      {
        relate_impl_ptpool_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          ptpool d1 = ptpool d2;

        (* should be lifted as a property of relate_AbData *)
        relate_impl_ptpool_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {ptpool: b} d2 {ptpool: b}
      }.

    Class match_impl_ptpool :=
      {
        match_impl_ptpool_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {ptpool: b} m f
      }.

  End CLASS_PTPOOL.
    
  Section CLASS_PT.

    Class relate_impl_PT :=
      {
        relate_impl_PT_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          PT d1 = PT d2;

        (* should be lifted as a property of relate_AbData *)
        relate_impl_PT_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {PT: b} d2 {PT: b}

      }.

    Class match_impl_PT :=
      {
        match_impl_PT_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {PT: b} m f
      }.

  End CLASS_PT.

  Section CLASS_idpde.

    Class relate_impl_idpde :=
      {
        relate_impl_idpde_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          idpde d1 = idpde d2;

        (* should be lifted as a property of relate_AbData *)
        relate_impl_idpde_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {idpde: b} d2 {idpde: b}

      }.

    Class match_impl_idpde :=
      {
        match_impl_idpde_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {idpde: b} m f
      }.

  End CLASS_idpde.

  Section CLASS_LAT.

    Class relate_impl_LAT :=
      {
        relate_impl_LAT_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (LAT d1) = (LAT d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_LAT_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {LAT: b} d2 {LAT: b}
      }.

    Class match_impl_LAT :=
      {
        match_impl_LAT_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {LAT: b} m f
      }.

  End CLASS_LAT.

  Section CLASS_smspool.

    Class relate_impl_smspool :=
      {
        relate_impl_smspool_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (smspool d1) = (smspool d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_smspool_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {smspool: b} d2 {smspool: b}
      }.

    Class match_impl_smspool :=
      {
        match_impl_smspool_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {smspool: b} m f
      }.

  End CLASS_smspool.

  Section CLASS_kctxt.

    Class relate_impl_kctxt :=
      {
        relate_impl_kctxt_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          kctxt_inj ι num_proc (kctxt d1) (kctxt d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_kctxt_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b1 b2,
            kctxt_inj ι num_proc b1 b2 ->
            relate_AbData s ι d1 {kctxt: b1} d2 {kctxt: b2}
      }.

    Class match_impl_kctxt :=
      {
        match_impl_kctxt_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {kctxt: b} m f
      }.

  End CLASS_kctxt.

  Section CLASS_tcb.

    Class relate_impl_tcb :=
      {
        relate_impl_tcb_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (tcb d1) = (tcb d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_tcb_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {tcb: b} d2 {tcb: b}
      }.

    Class match_impl_tcb :=
      {
        match_impl_tcb_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {tcb: b} m f
      }.

  End CLASS_tcb.

  Section CLASS_tdq.

    Class relate_impl_tdq :=
      {
        relate_impl_tdq_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (tdq d1) = (tdq d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_tdq_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {tdq: b} d2 {tdq: b}
      }.

    Class match_impl_tdq :=
      {
        match_impl_tdq_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {tdq: b} m f
      }.

  End CLASS_tdq.

  Section CLASS_abtcb.

    Class relate_impl_abtcb :=
      {
        relate_impl_abtcb_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (abtcb d1) = (abtcb d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_abtcb_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {abtcb: b} d2 {abtcb: b}
      }.

    Class match_impl_abtcb :=
      {
        match_impl_abtcb_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {abtcb: b} m f
      }.

  End CLASS_abtcb.

  Section CLASS_abq.

    Class relate_impl_abq :=
      {
        relate_impl_abq_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (abq d1) = (abq d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_abq_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {abq: b} d2 {abq: b}
      }.

    Class match_impl_abq :=
      {
        match_impl_abq_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {abq: b} m f
      }.

  End CLASS_abq.

  Section CLASS_cid.

    Class relate_impl_cid :=
      {
        relate_impl_cid_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (cid d1) = (cid d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_cid_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {cid: b} d2 {cid: b}
      }.

    Class match_impl_cid :=
      {
        match_impl_cid_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {cid: b} m f
      }.

  End CLASS_cid.

  (*Section CLASS_chpool.

    Class relate_impl_chpool :=
      {
        relate_impl_chpool_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (chpool d1) = (chpool d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_chpool_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {chpool: b} d2 {chpool: b}
      }.

    Class match_impl_chpool :=
      {
        match_impl_chpool_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {chpool: b} m f
      }.

  End CLASS_chpool.*)

  Section CLASS_uctxt.

    Class relate_impl_uctxt :=
      {
        relate_impl_uctxt_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          uctxt_inj ι (uctxt d1) (uctxt d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_uctxt_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b1 b2,
          uctxt_inj ι b1 b2 ->
            relate_AbData s ι d1 {uctxt: b1} d2 {uctxt: b2}
      }.

    Class match_impl_uctxt :=
      {
        match_impl_uctxt_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {uctxt: b} m f
      }.

  End CLASS_uctxt.

  Section CLASS_ept.

    Class relate_impl_ept :=
      {
        relate_impl_ept_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          (ept d1) = (ept d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_ept_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b,
            relate_AbData s ι d1 {ept: b} d2 {ept: b}
      }.

    Class match_impl_ept :=
      {
        match_impl_ept_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {ept: b} m f
      }.

  End CLASS_ept.

  Section CLASS_vmcs.

    Class relate_impl_vmcs :=
      {
        relate_impl_vmcs_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          VMCS_inj ι (vmcs d1) (vmcs d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_vmcs_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b b',
            VMCS_inj ι b b' ->
            relate_AbData s ι d1 {vmcs: b} d2 {vmcs: b'}
      }.

    Class match_impl_vmcs :=
      {
        match_impl_vmcs_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {vmcs: b} m f
      }.

  End CLASS_vmcs.

  Section CLASS_vmx.

    Class relate_impl_vmx :=
      {
        relate_impl_vmx_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          VMX_inj ι (vmx d1) (vmx d2);

        (* should be lifted as a property of relate_AbData *)
        relate_impl_vmx_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b b',
            VMX_inj ι b b' ->
            relate_AbData s ι d1 {vmx: b} d2 {vmx: b'}
      }.

    Class match_impl_vmx :=
      {
        match_impl_vmx_update ι d m f:
          match_AbData ι d m f ->
          forall b,
            match_AbData ι d {vmx: b} m f
      }.

  End CLASS_vmx.

  Section CLASS_devout.

    Class relate_impl_devout :=
      {
        relate_impl_devout_eq s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          devout d1 = devout d2;

        relate_impl_devout_update s ι d1 d2:
          relate_AbData s ι d1 d2 ->
          forall b, relate_AbData s ι d1 {devout: b} d2 {devout: b}
      }.

    Class match_impl_devout :=
      {
        match_impl_devout_update ι d m f:
          match_AbData ι d m f ->
          forall b, match_AbData ι d {devout: b} m f
      }.

  End CLASS_devout.

  Class low_level_invariant_impl :=
    {
      low_level_invariant_impl_eq n d:
        CompatData.low_level_invariant n d ->
        low_level_invariant n d
    }.

  Class high_level_invariant_impl_AbQCorrect_range :=
    {
      high_level_invariant_impl_AbQCorrect_range_eq d:
        CompatData.high_level_invariant d ->
        pg d = true -> AbQCorrect_range (abq d)
    }.

End InstanceT.

Ltac relate_match_instance_tac:=
  split; inversion 1; eauto 2; try econstructor; eauto 2.

Hint Extern 1 relate_impl_iflags =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_iflags =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_MM =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_MM' =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_MM =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_trapinfo =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 match_impl_trapinfo =>
(relate_match_instance_tac): typeclass_instances.              

Hint Extern 1 relate_impl_HP =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_HP' =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_HP =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_nps =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_nps =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_vmxinfo =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_vmxinfo =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_init =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_init =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_AC =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_AC =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_AT =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_AT =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_CR3 =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_CR3 =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_pperm =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_pperm =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_ipt =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_ipt =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_ptpool =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_ptpool =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_PT =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_PT =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_idpde =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_idpde =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_LAT =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_LAT =>
(relate_match_instance_tac): typeclass_instances.        

Hint Extern 1 relate_impl_smspool =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_smspool =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_kctxt =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_kctxt =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_tcb =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_tcb =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_tdq =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_tdq =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_abtcb =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_abtcb =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_abq =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_abq =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_cid =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_cid =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_syncchpool =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 match_impl_syncchpool =>
(relate_match_instance_tac): typeclass_instances.

(*Hint Extern 1 relate_impl_chpool =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_chpool =>
(relate_match_instance_tac): typeclass_instances.            
 *)

Hint Extern 1 relate_impl_uctxt =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_uctxt =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_uctxt =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_ept =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_ept =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_vmcs =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_vmcs =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_vmx =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_vmx =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 relate_impl_devout =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 match_impl_devout =>
(relate_match_instance_tac): typeclass_instances.            

Hint Extern 1 low_level_invariant_impl =>
(relate_match_instance_tac): typeclass_instances.

Hint Extern 1 high_level_invariant_impl_AbQCorrect_range =>
(relate_match_instance_tac): typeclass_instances.
