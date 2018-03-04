Require compcert.backend.LTL.
Require EventsX.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import Smallstep.
Import Locations.
Import Conventions.
Export LTL.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

(** Execution of LTL functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state (lm: locset) (p: LTL.program) (i: ident) (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (Hsig: sg = funsig f)
    (Hargs: args = map lm (loc_arguments sg))
  :
      initial_state lm p i sg args m (Callstate nil f lm m)
.

Inductive final_state (lm: locset) (sg: signature): state -> (list val * mem) -> Prop :=
| final_state_intro
    rs
    v
    (Hv: v = List.map rs (map R (loc_result sg)))
    (** Callee-save registers *)
    (CALLEE_SAVE: forall r,
       ~ In r destroyed_at_call ->
       rs (R r) = lm (R r))
    m :
    final_state lm sg (Returnstate nil rs m) (v, m)
.

Definition semantics
           (lm: locset)
           (p: LTL.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
  Semantics (
      let _ := writable_block_with_init_mem_writable_block_ops m in
      LTL.step lm
    ) (initial_state lm p i sg args m) (final_state lm sg) (Genv.globalenv p).

End WITHCONFIG.
