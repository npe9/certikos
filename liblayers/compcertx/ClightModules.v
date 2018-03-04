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
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.PTreeModules.
Require Export compcert.common.AST.
Require Export compcert.cfrontend.Clight.
Require Export compcert.cfrontend.Ctypes.

Definition cmodule := ptree_module Clight.function (globvar Ctypes.type).

Global Instance cmodule_ops : ModuleOps ident function (globvar type) cmodule :=
  ptree_module_ops.

Global Instance cmodule_prf : Modules ident function (globvar type) cmodule :=
  ptree_module_prf.
