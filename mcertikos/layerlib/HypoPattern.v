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
(*          Hypothesis patterns for refinement proof                   *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MALOp layer and MAL layer*)

Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import MemoryExtra.
Require Import EventsExtra.
Require Import GlobalenvsExtra.
Require Import AST.
Require Import AsmExtra.
Require Import LayerDefinition.
Require Import Implementation.
Require Import Smallstep.

Section SPEC_PATTERN1.

  Context {Hmem} {HprimOp} {HDATA} `{layer_defh: LayerDefinition HDATA HprimOp Hmem}.
  Context {Lmem} {LprimOp} {LDATA} `{layer_defl: LayerDefinition LDATA LprimOp Lmem}.
  Context `{Hlmi: !LayerMemoryInjections HDATA LDATA _ _}.

  Notation Hprogram := (program(external_function:= HprimOp)).
  Notation Lprogram := (program(external_function:= LprimOp)).

  Variable prog: Hprogram.
  Variable tprog: Lprogram.

  Notation ge := (Genv.globalenv prog).
  Notation tge := (Genv.globalenv tprog).

  Definition spec_pattern1 Lstep high_level_invariant Im sg args prim result r' b m'0 adt :=
    r' PC = Vptr b Int.zero
    -> Genv.find_funct_ptr tge b = Some Im
    -> Genv.find_funct_ptr ge b = Some (External prim)
    -> extcall_arguments r' m'0 sg args
    -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
    -> r' ESP <> Vundef
    -> r' RA  <> Vundef
    -> asm_invariant tge (State r' m'0)
    -> high_level_invariant (Mem.get_abstract_data m'0)
    -> exists f' m0' r_, 
         inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
         /\ Memtype.Mem.inject f' m'0 m0'
         /\ Mem.nextblock m'0 <= Mem.nextblock m0'
         /\ plus Lstep tge (State r' m'0) E0 (State r_ (Mem.put_abstract_data m0' adt))
         /\ result r_
         /\ r_ PC = r' RA
         /\ r_ # ESP = r' # ESP
         /\ (forall l,
               ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
               -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).

  Definition spec_pattern1' Lstep high_level_invariant Im sg args prim result r' b m'0:=
    r' PC = Vptr b Int.zero
    -> Genv.find_funct_ptr tge b = Some Im
    -> Genv.find_funct_ptr ge b = Some (External prim)
    -> extcall_arguments r' m'0 sg args
    -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
    -> r' ESP <> Vundef
    -> r' RA  <> Vundef
    -> asm_invariant tge (State r' m'0)
    -> high_level_invariant (Mem.get_abstract_data m'0)
    -> exists f' m0' r_, 
         inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
         /\ Memtype.Mem.inject f' m'0 m0'
         /\ Mem.nextblock m'0 <= Mem.nextblock m0'
         /\ plus Lstep tge (State r' m'0) E0 (State r_ m0')
         /\ result r_
         /\ r_ PC = r' RA
         /\ r_ # ESP = r' # ESP
         /\ (forall l,
               ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
               -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).

  Definition spec_pattern2 Lstep kernel_mode Im LOC sg args prim result r' b b0 m'0 m0 :=
    r' PC = Vptr b Int.zero
    -> Genv.find_funct_ptr tge b = Some Im
    -> Genv.find_funct_ptr ge b = Some (External prim)
    -> Genv.find_symbol tge LOC = Some b0
    -> Mem.tget m'0 b0 = Some Tag_global
    -> kernel_mode (Mem.get_abstract_data m'0)
    -> extcall_arguments r' m'0 sg args
    -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
    -> r' ESP <> Vundef
    -> r' RA  <> Vundef
    -> asm_invariant tge (State r' m'0)
    -> exists f' m0' r_, 
         inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
         /\ Memtype.Mem.inject f' m0 m0'
         /\ Mem.nextblock m0 <= Mem.nextblock m0'
         /\ plus Lstep tge (State r' m'0) E0 (State r_ m0')
         /\ result r_
         /\ r_ PC = r' RA
         /\ r_ # ESP = r' # ESP
         /\ (forall l,
               ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
               -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).

  Definition spec_pattern_kctxt Lstep kernel_mode Im LOC sg args prim result r' b b0 m'0 m0 :=
    r' PC = Vptr b Int.zero
    -> Genv.find_funct_ptr tge b = Some Im
    -> Genv.find_funct_ptr ge b = Some (External prim)
    -> Genv.find_symbol tge LOC = Some b0
    -> Mem.tget m'0 b0 = Some Tag_global
    -> kernel_mode (Mem.get_abstract_data m'0)
    -> extcall_arguments r' m'0 sg args
    -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
    -> r' ESP <> Vundef
    -> r' RA  <> Vundef
    -> asm_invariant tge (State r' m'0)
    -> exists f' m0' r_, 
         (inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' 
          /\ inject_incr (Mem.flat_inj (Genv.genv_next tge)) f')
         /\ Memtype.Mem.inject f' m0 m0'
         /\ Mem.nextblock m0 <= Mem.nextblock m0'
         /\ plus Lstep tge (State r' m'0) E0 (State r_ m0')
         /\ result r_
         /\ r_ PC = r' RA
         /\ r_ # ESP = r' # ESP
         /\ (forall l,
               ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
               -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).


  Definition spec_pattern2' Lstep kernel_mode Im LOC sg args prim result r' b b0 m'0 adt :=
    r' PC = Vptr b Int.zero
    -> Genv.find_funct_ptr tge b = Some Im
    -> Genv.find_funct_ptr ge b = Some (External prim)
    -> Genv.find_symbol tge LOC = Some b0
    -> Mem.tget m'0 b0 = Some Tag_global
    -> kernel_mode (Mem.get_abstract_data m'0)
    -> extcall_arguments r' m'0 sg args
    -> (forall b o, r' ESP = Vptr b o -> Mem.tget m'0 b = Some Tag_stack)
    -> r' ESP <> Vundef
    -> r' RA  <> Vundef
    -> asm_invariant tge (State r' m'0)
    -> exists f' m0' r_, 
         inject_incr (Mem.flat_inj (Mem.nextblock m'0)) f' 
         /\ Memtype.Mem.inject f' m'0 m0'
         /\ Mem.nextblock m'0 <= Mem.nextblock m0'
         /\ plus Lstep tge (State r' m'0) E0 (State r_ (Mem.put_abstract_data m0' adt))
         /\ result r_
         /\ r_ PC = r' RA
         /\ r_ # ESP = r' # ESP
         /\ (forall l,
               ~In (Locations.R l) Conventions1.temporaries -> ~In (Locations.R l) Conventions1.destroyed_at_call 
               -> Val.lessdef (r' (preg_of l)) (r_ (preg_of l))).

End SPEC_PATTERN1.
