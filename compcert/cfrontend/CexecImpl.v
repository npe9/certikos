Require Cexec.
Require EventsImpl.

(* [CompCertX:test-compcert-param-memory] This file is required for those symbols of [Cexec] that will be
   used by OCaml mode. They have to be instantiated with the concrete
   memory model [Memimpl]. *)

Definition do_initial_state := Cexec.do_initial_state (mem := Memimpl.mem).
Definition do_step := Cexec.do_step (mem := Memimpl.mem).
Definition step_expr := Cexec.step_expr (mem := Memimpl.mem).
Definition at_final_state := Cexec.at_final_state (mem := Memimpl.mem).
