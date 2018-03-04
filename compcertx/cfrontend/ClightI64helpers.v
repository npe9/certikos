Require SelectLongproofX.
Require compcert.cfrontend.Clight.

Import Coqlib.
Import AST.
Import Globalenvs.
Import SelectLong.

(** This file is an adaptation of [I64helpers] for Clight.

In this file, we formalize the syntactic requirement on the Clight
program being compiled: it must contain helper external functions for
64-bit integer operations.
*)

Definition genv_contains_helpers
           (h: helper_functions)
           (ge: Clight.genv)
: Prop :=
  forall i sg, In (i, sg) (SelectLongproofX.helper_idents_sigs h) ->
               exists b,
                 exists targs,
                   exists tres,
                     exists cc,
                       Genv.find_symbol ge i = Some b /\
                       Genv.find_funct_ptr ge b = Some (Clight.External (EF_external i sg)
                                                                        targs tres cc) /\
                       sg = Ctypes.signature_of_type targs tres cc.
