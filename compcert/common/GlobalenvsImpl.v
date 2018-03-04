Require Globalenvs.
Require Memimpl.

(* [CompCertX:test-compcert-param-memory] This file is required for those symbols of [Globalenvs] that will be
   used by OCaml mode. They have to be instantiated with the concrete
   memory model [Memimpl]. *)

Definition init_mem (F V: Type) := Globalenvs.Genv.init_mem (mem := Memimpl.mem) (F := F) (V := V).
