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
Require Import CommonTactic.
Require Import AuxLemma.
Require Import FlatMemory.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import RealParams.
Require Import LoadStoreSem1.
Require Import AsmImplLemma.
Require Import LAsm.
Require Import RefinementTactic.
Require Import PrimSemantics.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.ClightModules.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatClightSem.

Require Import MContainer.

Require Import AbstractDataType.

(** * Definition of the low level specification*)
Section SPECIFICATION.  

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATAOps := (cdata RData).

  Inductive setPT_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setPT_spec_low_intro s (WB: _ -> Prop) m'0 labd labd' n ofs:
      setCR30_spec labd (GLOBP PTPool_LOC ofs) = Some labd' ->
      ofs = (Int.repr (Int.unsigned n * PgSize)) ->
      0 <= Int.unsigned n < num_proc ->
      kernel_mode labd ->
      setPT_spec_low_step s WB (Vint n :: nil) (m'0, labd) Vundef (m'0, labd').

  Inductive getPDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    getPDE_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n i pi pi':
      find_symbol s PTPool_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0
               (Int.unsigned n * PgSize + Int.unsigned i * 4) = Some (Vint pi) ->
      Int.unsigned pi' = Int.unsigned pi / PgSize ->
      0 <= Int.unsigned n < num_proc ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      kernel_mode (snd m'0) ->
      getPDE_spec_low_step s WB (Vint n :: Vint i :: nil) m'0 (Vint pi') m'0.

  Inductive setPDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setPDE_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 b1 n i:
      find_symbol s PTPool_LOC = Some b0 ->
      find_symbol s IDPMap_LOC = Some b1 ->
      Mem.store Mint32 m'0 b0
                (Int.unsigned n * PgSize + Int.unsigned i * 4)
                (Vptr b1 (Int.repr (Int.unsigned i * PgSize + PT_PERM_PTU))) = Some m0 ->
      0 <= Int.unsigned n < num_proc ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      kernel_mode (snd m'0) ->
      setPDE_spec_low_step s WB (Vint n :: Vint i :: nil) m'0 Vundef m0.

  Inductive rmvPDE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    rmvPDE_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n i:
      find_symbol s PTPool_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0
                (Int.unsigned n * PgSize + Int.unsigned i * 4)
                (Vint (Int.repr PT_PERM_UP)) = Some m0 ->
      0 <= Int.unsigned n < num_proc ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      kernel_mode (snd m'0) ->
      rmvPDE_spec_low_step s WB (Vint n :: Vint i :: nil) m'0 Vundef m0.

  Inductive setPDEU_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setPDEU_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 n i pi:
      find_symbol s PTPool_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0
                (Int.unsigned n * PgSize + Int.unsigned i * 4)
                (Vint (Int.repr (Int.unsigned pi * PgSize + PT_PERM_PTU))) = Some m0 ->
      0 <= Int.unsigned n < num_proc ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      0 < Int.unsigned pi < nps (snd m'0) ->
      init (snd m'0) = true ->
      kernel_mode (snd m'0) ->
      setPDEU_spec_low_step s WB (Vint n :: Vint i :: Vint pi :: nil) m'0 Vundef m0.

  Inductive getPTE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    getPTE_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n i vadr padr  pi pi':
      find_symbol s PTPool_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0
               (Int.unsigned n * PgSize + Int.unsigned i * 4) = Some (Vint pi) ->
      Int.unsigned pi = pi' * PgSize + PT_PERM_PTU ->
      fload'_spec (pi' * one_k + Int.unsigned vadr) (snd m'0) = Some (Int.unsigned padr) ->
      0 <= Int.unsigned n < num_proc ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
      kernel_mode (snd m'0) ->
      getPTE_spec_low_step s WB (Vint n :: Vint i :: Vint vadr :: nil) m'0 (Vint padr) m'0.

  Inductive setPTE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setPTE_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n i vadr padr p p0 pi pi' d:
      find_symbol s PTPool_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0
               (Int.unsigned n * PgSize + Int.unsigned i * 4) = Some (Vint pi) ->
      Int.unsigned pi = pi' * PgSize + PT_PERM_PTU ->
      fstore0_spec (pi' * one_k + Int.unsigned vadr)  
                  (Int.unsigned padr * PgSize + Int.unsigned p)
                  (snd m'0)= Some d ->
      0 <= Int.unsigned n < num_proc ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
      0 < Int.unsigned padr < nps (snd m'0) ->
      ZtoPerm (Int.unsigned p) = Some p0 ->
      init (snd m'0) = true ->
      kernel_mode (snd m'0) ->
      setPTE_spec_low_step s WB (Vint n :: Vint i :: Vint vadr :: Vint padr :: Vint p :: nil) m'0 Vundef (fst m'0, d).

  Inductive rmvPTE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    rmvPTE_spec_low_intro s (WB: _ -> Prop) (m'0: mwd LDATAOps) b0 n i vadr pi pi' d:
      find_symbol s PTPool_LOC = Some b0 ->
      Mem.load Mint32 m'0 b0
               (Int.unsigned n * PgSize + Int.unsigned i * 4) = Some (Vint pi) ->
      Int.unsigned pi = pi' * PgSize + PT_PERM_PTU ->
      fstore0_spec (pi' * one_k + Int.unsigned vadr) 0 (snd m'0) = Some d ->
      0 <= Int.unsigned n < num_proc ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
      kernel_mode (snd m'0) ->
      rmvPTE_spec_low_step s WB (Vint n :: Vint i :: Vint vadr :: nil) m'0 Vundef (fst m'0, d).

  Inductive setIDPTE_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}:
    sextcall_sem (mem := mwd LDATAOps) :=
    setIDPTE_spec_low_intro s (WB: _ -> Prop) (m'0 m0: mwd LDATAOps) b0 i vadr p p0:
      find_symbol s IDPMap_LOC = Some b0 ->
      Mem.store Mint32 m'0 b0
                (Int.unsigned i * PgSize + Int.unsigned vadr * 4)
                (Vint (Int.repr ((Int.unsigned i * one_k + Int.unsigned vadr) * PgSize + Int.unsigned p)))  = Some m0 ->
      0 <= Int.unsigned i <= PDX Int.max_unsigned ->
      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
      ZtoPerm (Int.unsigned p) = Some p0 ->
      kernel_mode (snd m'0) ->
      setIDPTE_spec_low_step s WB (Vint i :: Vint vadr :: Vint p :: nil) m'0 Vundef m0.

  Inductive pt_in_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | pt_in_spec_low_intro s m0 rs b:
      find_symbol s pt_in = Some b ->
      rs PC = Vptr b Int.zero ->
      kernel_mode (snd m0) ->
      asm_invariant (mem := mwd LDATAOps) s rs m0 ->
      pt_in_spec_low_step s rs m0 
                          (rs # RA <- Vundef # PC <- (rs RA)) m0.

  Inductive pt_out_spec_low_step `{StencilOps} `{Mem.MemoryModelOps} `{UseMemWithData mem}: 
    sprimcall_sem (mem := mwd LDATAOps):=
  | pt_out_spec_low_intro s m0 rs b:
      find_symbol s pt_out = Some b ->
      rs PC = Vptr b Int.zero ->
      kernel_mode (snd m0) ->
      asm_invariant (mem := mwd LDATAOps) s rs m0 ->
      pt_out_spec_low_step s rs m0 
                           (rs # RA <- Vundef # PC <- (rs RA)) m0.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Definition pt_in_spec_low: compatsem LDATAOps :=
      asmsem pt_in pt_in_spec_low_step.

    Definition pt_out_spec_low: compatsem LDATAOps :=
      asmsem pt_out pt_out_spec_low_step.

    (** * The low level specifications to the module implemented at this layer*)
    Definition rmvPTE_spec_low: compatsem LDATAOps :=
      csem rmvPTE_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Ctypes.Tvoid.

    Definition setPTE_spec_low: compatsem LDATAOps :=
      csem setPTE_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::Tint32::Tint32::nil)) Ctypes.Tvoid.

    Definition setPDE_spec_low: compatsem LDATAOps :=
      csem setPDE_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Ctypes.Tvoid.

    Definition rmvPDE_spec_low: compatsem LDATAOps :=
      csem rmvPDE_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Ctypes.Tvoid.

    Definition setPDEU_spec_low: compatsem LDATAOps :=
      csem setPDEU_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Ctypes.Tvoid.

    Definition setPT_spec_low: compatsem LDATAOps :=
      csem setPT_spec_low_step (type_of_list_type (Tint32::nil)) Ctypes.Tvoid.

    Definition getPTE_spec_low: compatsem LDATAOps :=
      csem getPTE_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Tint32.

    Definition getPDE_spec_low: compatsem LDATAOps :=
      csem getPDE_spec_low_step (type_of_list_type (Tint32::Tint32::nil)) Tint32.

    Definition setIDPTE_spec_low: compatsem LDATAOps :=
      csem setIDPTE_spec_low_step (type_of_list_type (Tint32::Tint32::Tint32::nil)) Ctypes.Tvoid.

    (*Definition MVar : compatlayer LDATAOps :=
      PTPool_LOC ↦ mkglobvar (Tarray Tint32 (num_proc * (PDX(Int.max_unsigned) + 2) * PgSize) (mk_attr false None))
                 (Init_space (num_proc * (PDX(Int.max_unsigned) + 2) * PgSize) :: nil) false false.*)

  End WITHMEM.

End SPECIFICATION.  
