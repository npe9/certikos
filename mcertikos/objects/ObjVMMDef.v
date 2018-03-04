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
(*              Object Primitives                                      *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import FlatMemory.
Require Import AbstractDataType.
Require Import Integers.
Require Import Values.
Require Import Constant.

Section OBJ_VMM.

  (** primitve: set the value of n-th page table's i-th first level entry*)
  (** Since the page table is statically allocated, the contents of the first level page table can be calculated by their index*)
  (** primitve: returns the contents of the n-th page table with the fisrt level index i and second level index vadr *)    
  Definition PDE_Arg (n i: Z) : bool :=
    if zle_lt 0 n num_proc then
      if zle_le 0 i (PDX Int.max_unsigned) then
        true
      else false
    else false.

  Function setPDEU_spec (n i pi: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt, init adt, ipt adt, PDE_Arg n i) with
      | (true, true, true, true, true) =>
        if zeq n (PT adt) then None
        else
          if zlt_lt 0 pi (nps adt) then
            match ZMap.get pi (pperm adt) with
              | PGAlloc  =>
                let pt':= ZMap.set i (PDEValid pi (ZMap.init PTEUndef)) (ZMap.get n (ptpool adt)) in
                Some adt {HP: FlatMem.free_page pi (HP adt)}
                     {pperm: ZMap.set pi (PGHide (PGPMap n i)) (pperm adt)}
                     {ptpool: ZMap.set n pt' (ptpool adt)}
              | _ => None
            end
          else None
      |_ => None
    end.

  Function rmvPDE_spec (n i: Z) (adt: RData): option RData :=
    match (ikern adt, ihost adt, init adt, ipt adt, PDE_Arg n i) with
      | (true, true, true, true, true) =>
        let pt':= ZMap.set i PDEUnPresent (ZMap.get n (ptpool adt)) in
        if (if (zeq n (PT adt)) then
              if (pg adt) then true
              else false
            else false) then None
        else
          match ZMap.get i (ZMap.get n (ptpool adt)) with
            | PDEValid pi _ =>
              match ZMap.get pi (pperm adt) with
                | PGHide (PGPMap _ _)  =>
                  Some adt {pperm: ZMap.set pi PGAlloc (pperm adt)}
                       {ptpool: ZMap.set n pt' (ptpool adt)}
                | _ => None
              end
            | _ => Some adt {ptpool: ZMap.set n pt' (ptpool adt)}
          end
      |_ => None
    end.

  Definition PTE_Arg (n i vadr: Z): bool :=
    if PDE_Arg n i then
      if zle_le 0 vadr (PTX Int.max_unsigned) then
        true
      else false
    else false.

  Function getPTE_spec (n i vadr: Z) (adt: RData) : option Z :=
    match (ikern adt, ihost adt, init adt, ipt adt, PTE_Arg n i vadr) with
      | (true, true, true, true, true) =>
        let pt:= ZMap.get n (ptpool adt) in
        match ZMap.get i pt with
          | PDEValid _ pdt =>
            match ZMap.get vadr pdt with
              | PTEValid padr p => 
                Some (padr * PgSize + PermtoZ p)
              | PTEUnPresent => Some 0
              | _ => None
            end
          | _ => None
        end
      | _ => None
    end.

  Function setPTE_spec (n i vadr padr perm: Z) (adt: RData) : option RData :=
    match (ikern adt, ihost adt, init adt, ipt adt, PTE_Arg n i vadr, ZtoPerm perm) with
      | (true, true, true, true, true, Some p) =>
        if zeq n (PT adt) then None
        else
          if zlt_lt 0 padr (nps adt) then
            let pt:= ZMap.get n (ptpool adt) in
            match ZMap.get i pt with
              | PDEValid pi pdt =>
                let pdt':= ZMap.set vadr (PTEValid padr p) pdt in
                let pt' := ZMap.set i (PDEValid pi pdt') pt in
                Some adt {ptpool: ZMap.set n pt' (ptpool adt)}
              | _ => None
            end
          else None
      | _ => None
    end.

End OBJ_VMM.