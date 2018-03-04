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

Require Import PIPC.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.

  Notation LDATAOps := (cdata LDATA).

  Inductive elf_load_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sprimcall_sem (mem := mwd LDATAOps):=
  | elf_load_spec_low_intro s (m'0: mwd LDATAOps) n be ofse sig rs b:
      find_symbol s elf_load = Some b ->
      rs PC = Vptr b Int.zero ->
      (exists elf_id, find_symbol s elf_id = Some be) ->
      sig = mksignature (AST.Tint::AST.Tint::nil) None cc_default ->
      extcall_arguments rs m'0 sig (Vptr be ofse :: Vint n :: nil)  ->
      asm_invariant (mem := mwd LDATAOps) s rs m'0 ->
      elf_load_spec_low_step s rs m'0 (rs#RA<- Vundef#PC <- (rs#RA)) m'0.

  Inductive uctx_get_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    uctx_get_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n ofs v:
      find_symbol s UCTX_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 ((Int.unsigned n) * UCTXT_SIZE * 4 + Int.unsigned ofs * 4) = Some (Vint v) ->
      0 <= (Int.unsigned n) < num_proc ->
      is_UCTXT_ptr (Int.unsigned ofs) = false ->
      kernel_mode (snd m'0) ->
      uctx_get_spec_low_step s WB (Vint n :: Vint ofs :: nil) m'0 (Vint v) m'0.

  Inductive uctx_set_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    uctx_set_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n ofs v:
      find_symbol s UCTX_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + Int.unsigned ofs * 4) (Vint v) = Some m0 ->
      0 <= (Int.unsigned n) < num_proc ->
      is_UCTXT_ptr (Int.unsigned ofs) = false ->
      kernel_mode (snd m'0) ->
      uctx_set_spec_low_step s WB (Vint n :: Vint ofs :: Vint v :: nil) m'0 Vundef m0.

  Inductive uctx_set_eip_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    uctx_set_eip_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n bf ofs:
      find_symbol s UCTX_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EIP * 4) (Vptr bf ofs) = Some m0 ->
      0 <= (Int.unsigned n) < num_proc ->
      (exists fun_id, find_symbol s fun_id = Some bf) ->
      kernel_mode (snd m'0) ->
      uctx_set_eip_spec_low_step s WB (Vint n :: Vptr bf ofs :: nil) m'0 Vundef m0.

  Inductive save_uctx_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    save_uctx_spec_low_intro s (WB: _ -> Prop) 
                             (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 
                                 m15 m16 m17: mwd LDATAOps) 
                             u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 b1 n:
      find_symbol s UCTX_LOC = Some b1 ->
      Mem.store Mint32 m0 b1 (UCTXT_SIZE * 4 * n + 4 * U_EDI) (Vint u0) = Some m1 ->
      Mem.store Mint32 m1 b1 (UCTXT_SIZE * 4 * n + 4 * U_ESI) (Vint u1) = Some m2 ->
      Mem.store Mint32 m2 b1 (UCTXT_SIZE * 4 * n + 4 * U_EBP) (Vint u2) = Some m3 ->
      Mem.store Mint32 m3 b1 (UCTXT_SIZE * 4 * n + 4 * U_OESP) (Vint u3) = Some m4 ->
      Mem.store Mint32 m4 b1 (UCTXT_SIZE * 4 * n + 4 * U_EBX) (Vint u4) = Some m5 ->
      Mem.store Mint32 m5 b1 (UCTXT_SIZE * 4 * n + 4 * U_EDX) (Vint u5) = Some m6 ->
      Mem.store Mint32 m6 b1 (UCTXT_SIZE * 4 * n + 4 * U_ECX) (Vint u6) = Some m7 ->
      Mem.store Mint32 m7 b1 (UCTXT_SIZE * 4 * n + 4 * U_EAX) (Vint u7) = Some m8 ->
      Mem.store Mint32 m8 b1 (UCTXT_SIZE * 4 * n + 4 * U_ES) (Vint u8) = Some m9 ->
      Mem.store Mint32 m9 b1 (UCTXT_SIZE * 4 * n + 4 * U_DS) (Vint u9) = Some m10 ->
      Mem.store Mint32 m10 b1 (UCTXT_SIZE * 4 * n + 4 * U_TRAPNO) (Vint u10) = Some m11 -> 
      Mem.store Mint32 m11 b1 (UCTXT_SIZE * 4 * n + 4 * U_ERR) (Vint u11) = Some m12 ->
      Mem.store Mint32 m12 b1 (UCTXT_SIZE * 4 * n + 4 * U_EIP) (Vint u12) = Some m13 ->
      Mem.store Mint32 m13 b1 (UCTXT_SIZE * 4 * n + 4 * U_CS) (Vint u13) = Some m14 ->
      Mem.store Mint32 m14 b1 (UCTXT_SIZE * 4 * n + 4 * U_EFLAGS) (Vint u14) = Some m15 -> 
      Mem.store Mint32 m15 b1 (UCTXT_SIZE * 4 * n + 4 * U_ESP) (Vint u15) = Some m16 ->
      Mem.store Mint32 m16 b1 (UCTXT_SIZE * 4 * n + 4 * U_SS) (Vint u16) = Some m17 ->
      cid (snd m0) = n ->
      kernel_mode (snd m0) ->
      pg (snd m0) = true ->
      save_uctx_spec_low_step s WB (Vint u0::Vint u1::Vint u2::Vint u3::Vint u4::Vint u5::Vint u6::
                                         Vint u7::Vint u8::Vint u9::Vint u10::Vint u11::Vint u12::Vint u13
                                         ::Vint u14::Vint u15::Vint u16::nil) m0 Vundef m17.

  Inductive restore_uctx_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sprimcall_sem (mem := mwd LDATAOps):=
    restore_uctx_spec_low_intro s v0 v1 v2 v4 v5 v6 v7 v8 v9
                                (m'0: mem) b0 n rs rs' labd labd' sig b:
      find_symbol s restore_uctx = Some b ->
      rs PC = Vptr b Int.zero ->
      find_symbol s UCTX_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EDI) = Some v0 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ESI * 4) = Some v1 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EBP * 4) = Some v2 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EBX * 4) = Some v4 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EDX * 4) = Some v5 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ECX * 4) = Some v6 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EAX * 4) = Some v7 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ESP * 4) = Some v8 ->
      Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EIP * 4) = Some v9 ->
      rs' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                            :: IR ECX :: IR EAX :: RA :: nil) 
                        (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
      trapout_spec labd = Some labd' ->
      cid labd = Int.unsigned n ->
      kernel_mode labd ->
      asm_invariant (mem := mwd LDATAOps) s rs (m'0, labd) ->
      high_level_invariant labd ->
      sig = mksignature (AST.Tint::nil) None cc_default ->
      extcall_arguments rs m'0 sig (Vint n ::nil) ->
      restore_uctx_spec_low_step s rs (m'0, labd)
                                 (rs'#Asm.EDI <- v0 #Asm.ESI <- v1 #Asm.EBP <- v2 #Asm.ESP<- v8#Asm.EBX <- v4
                                     #EDX<- v5 #ECX<-v6 #EAX <- v7# PC <- v9) (m'0, labd').

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition uctx_get_spec_low: compatsem LDATAOps :=
      csem uctx_get_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition uctx_set_spec_low: compatsem LDATAOps :=
      csem uctx_set_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tvoid.

    Definition uctx_set_eip_spec_low: compatsem LDATAOps :=
      csem uctx_set_eip_spec_low_step (type_of_list_type (Tint32::Tpointer Tvoid noattr::nil)) Tvoid.

    Definition elf_load_spec_low: compatsem LDATAOps :=
      asmsem_withsig elf_load elf_load_spec_low_step (mksignature (AST.Tint::AST.Tint::nil) None cc_default).

    Definition save_uctx_spec_low: compatsem LDATAOps :=
      csem save_uctx_spec_low_step (type_of_list_type 
                                      (Tint32::Tint32::Tint32::Tint32::
                                             Tint32::Tint32::Tint32::Tint32::
                                             Tint32::Tint32::Tint32::Tint32::
                                             Tint32::Tint32::Tint32::Tint32::
                                             Tint32::nil)) Tvoid.

    Definition restore_uctx_spec_low: compatsem LDATAOps :=
      asmsem_withsig restore_uctx restore_uctx_spec_low_step (mksignature (AST.Tint::nil) None cc_default).
    
    (*Definition MSpec : compatlayer LDATAOps :=
           uctx_get ↦ uctx_get_spec_low
           ⊕ uctx_set ↦ uctx_set_spec_low
           ⊕ uctx_set_eip ↦ uctx_set_eip_spec_low
           ⊕ restore_uctx ↦ restore_uctx_spec_low
           ⊕ save_uctx ↦ save_uctx_spec_low
           ⊕ elf_load ↦ elf_load_spec_low.
    
    Definition MVar : compatlayer LDATAOps :=
      UCTX_LOC ↦ mkglobvar (Tarray Tint32 (num_proc * UCTXT_SIZE * 4) (mk_attr false None))
              (Init_space (num_proc * UCTXT_SIZE * 4) :: nil) false false.*)

  End WITHMEM.

End Refinement.
