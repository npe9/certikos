(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for ARM *)

Require Import ZArith.
Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.

Definition big_endian := false.

Notation align_int64 := 8%Z (only parsing).
Notation align_float64 := 8%Z (only parsing).

Program Definition default_pl : bool * nan_pl 53 := (false, nat_iter 51 xO xH).

Definition choose_binop_pl (s1: bool) (pl1: nan_pl 53) (s2: bool) (pl2: nan_pl 53) :=
  (** Choose second NaN if pl2 is sNaN but pl1 is qNan.
      In all other cases, choose first NaN *)
  (Pos.testbit (proj1_sig pl1) 51 &&
   negb (Pos.testbit (proj1_sig pl2) 51))%bool.

Global Opaque big_endian default_pl choose_binop_pl.
