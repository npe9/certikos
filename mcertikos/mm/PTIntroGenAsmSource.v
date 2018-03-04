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
(*           Layers of PM: Assembly Verification for MPTIntro          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
Require Import Coqlib.
Require Import Integers.
Require Import Constant.
Require Import GlobIdent.

Require Import liblayers.compat.CompatLayers.
Require Import LAsm.

Section ASM_CODE.

  Definition Im_ptin : list instruction := 
    asm_instruction (Pret) ::
                    nil.

  Definition Im_ptout : list instruction := 
    asm_instruction (Pret) ::
                    nil.

  Definition ptin_function: function := mkfunction null_signature Im_ptin.

  Definition ptout_function: function := mkfunction null_signature Im_ptout.

End ASM_CODE.
