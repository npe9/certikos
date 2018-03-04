Require Initializers.
Require Memimpl.

(* [CompCertX:test-compcert-param-memory] This file is required for those symbols of [Initializers] that will be
   used by OCaml mode. They have to be instantiated with the concrete
   memory model [Memimpl]. *)

Definition transl_init := Initializers.transl_init (mem := Memimpl.mem).
Definition constval := Initializers.constval (mem := Memimpl.mem).
