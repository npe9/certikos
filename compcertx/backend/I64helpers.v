Require compcert.backend.SelectLong.

Import Coqlib.
Import Errors.
Import AST.
Import Globalenvs.
Import SelectLong.

(** We moved away all proofs to [I64helpersproof]. *)

(** Finally, we move here (from SelectionproofX) the following
    implementation of how identifiers of helpers and builtins are
    computed. The following implementation actually mimicks in Coq
    what compcert/extraction/extraction.v entirely implements in
    OCaml, using compcert.AST.ident_of_string, which is actually
    implemented in OCaml. *)

(** For the purpose of CertiKOS, we are using fixed identifiers instead.
    These identifiers will range from 512 onwards. *)

Open Scope string_scope.

Definition reserved_strings: list String.string :=
  "__i64_dtos"
    :: "__i64_dtou"
    :: "__i64_stod"
    :: "__i64_utod"
    :: "__i64_stof"
    :: "__i64_utof"
    :: "__i64_sdiv"
    :: "__i64_udiv"
    :: "__i64_smod"
    :: "__i64_umod"
    :: "__i64_shl"
    :: "__i64_shr"
    :: "__i64_sar"
    :: "__builtin_negl"
    :: "__builtin_addl"
    :: "__builtin_subl"
    :: "__builtin_mull"
    :: nil.

Fixpoint reserved_id_aux (n: ident) (l: list String.string) (s: String.string): res ident :=
  match l with
    | nil => Error (MSG "reserved_id_aux: string not found: " :: MSG s :: nil)
    | s' :: l' =>
      if String.string_dec s s'
      then OK n
      else reserved_id_aux (Psucc n) l' s
  end.

Definition reserved_id := reserved_id_aux 512%positive reserved_strings.

Global Instance i64helpers : I64helpers := 
  {
    get_helper F V ge s sg := reserved_id s;
    get_builtin s sg := reserved_id s
  }.

Lemma get_helpers_some:
  {hf |
   forall F V (ge: Genv.t (AST.fundef F) V),
     get_helpers ge = OK hf}.
Proof.
  unfold get_helpers; simpl. esplit. split.
Defined.

Definition hf := 
  let (hf, _) := get_helpers_some in hf.
