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
(*          Low Level Specification                                    *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)
(** This file provide the contextual refinement proof between MBoot layer and MALInit layer*)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Asm.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import AuxLemma.
Require Import FlatMemory.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import RealParams.
Require Import AsmImplLemma.
Require Import GenSem.
Require Import PrimSemantics.
Require Import Conventions.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.
Require Import AbstractDataType.

Require Import MShare.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive kctxt_ra_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    kctxt_ra_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n bf ofs:
      find_symbol s KCtxtPool_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 24 + 5 * 4) (Vptr bf ofs) = Some m0 ->
      0 <= (Int.unsigned n) < num_proc ->
      (exists fun_id, find_symbol s fun_id = Some bf) ->
      kernel_mode (snd m'0) ->
      kctxt_ra_spec_low_step s WB (Vint n :: Vptr bf ofs :: nil) m'0 Vundef m0.

  Inductive kctxt_sp_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    kctxt_sp_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n bf ofs:
      find_symbol s KCtxtPool_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 24) (Vptr bf ofs) = Some m0 ->
      0 <= (Int.unsigned n) < num_proc ->
      Int.unsigned ofs = (Int.unsigned n + 1) * PgSize - 4 ->
      (exists fun_id, find_symbol s fun_id = Some bf) ->
      kernel_mode (snd m'0) ->
      kctxt_sp_spec_low_step s WB (Vint n :: Vptr bf ofs :: nil) m'0 Vundef m0.

  Inductive kctxt_switch_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sprimcall_sem (mem := mwd LDATAOps):=
    kctxt_switch_spec_low_intro s v0 v1 v2 v3 v4 v5
                                (m'0 m0 m1 m2 m3 m4 m5: mwd LDATAOps) b0 n n' (rs: regset) b:
      find_symbol s kctxt_switch = Some b ->
      rs PC = Vptr b Int.zero ->
      find_symbol s KCtxtPool_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * 24) (rs ESP) = Some m0 ->
      Mem.store Mint32 m0 b0 (Int.unsigned n * 24 + 4) (rs EDI) = Some m1 ->
      Mem.store Mint32 m1 b0 (Int.unsigned n * 24 + 8) (rs ESI) = Some m2 ->
      Mem.store Mint32 m2 b0 (Int.unsigned n * 24 + 12) (rs EBX) = Some m3 ->
      Mem.store Mint32 m3 b0 (Int.unsigned n * 24 + 16) (rs EBP) = Some m4 ->
      Mem.store Mint32 m4 b0 (Int.unsigned n * 24 + 20) (rs RA) = Some m5 ->
      Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 0) = Some v0 ->
      Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 4) = Some v1 ->
      Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 8) = Some v2 ->
      Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 12) = Some v3 ->
      Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 16) = Some v4 ->
      Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 20) = Some v5 ->
      kernel_mode (snd m'0) ->
      asm_invariant (mem := mwd LDATAOps) s rs m'0 ->
      rs Asm.EAX = Vint n ->
      rs Asm.EDX = Vint n' ->
      0 <= (Int.unsigned n) < num_proc ->
      0 <= (Int.unsigned n') < num_proc ->
      let rs' := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                 :: IR EDX :: IR ECX :: IR EAX :: RA :: nil) rs) in
      kctxt_switch_spec_low_step s rs m'0 
                                 (rs'#ESP<- v0 #EDI <- v1 #ESI <- v2 #EBX <- v3 
                                     #EBP <- v4#PC <- v5) m5.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition kctxt_ra_spec_low: compatsem LDATAOps :=
      csem kctxt_ra_spec_low_step (type_of_list_type (Tint32::Tpointer Tvoid noattr::nil)) Tvoid.

    Definition kctxt_sp_spec_low: compatsem LDATAOps :=
      csem kctxt_sp_spec_low_step (type_of_list_type (Tint32::Tpointer Tvoid noattr::nil)) Tvoid.

    Definition kctxt_switch_spec_low: compatsem LDATAOps :=
      asmsem kctxt_switch kctxt_switch_spec_low_step.
    
    (*Definition MSpec : compatlayer LDATAOps :=
           set_RA ↦ kctxt_ra_spec_low
           ⊕ set_SP ↦ kctxt_sp_spec_low
           ⊕ kctxt_switch ↦ kctxt_switch_spec_low.
    
    Definition MVar : compatlayer LDATAOps :=
      KCtxtPool_LOC ↦ mkglobvar (Tarray Tint32 (num_proc * 24) (mk_attr false None))
              (Init_space (num_proc * 24) :: nil) false false.*)

  End WITHMEM.

End Refinement.