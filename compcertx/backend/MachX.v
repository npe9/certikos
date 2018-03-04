Require compcert.backend.Mach.

Import Coqlib.
Import Integers.
Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import Events.
Import Smallstep.
Import Locations.
Import Conventions.
Export Mach.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

(** Execution of Mach functions with Asm-style arguments (long long 64-bit integers NOT allowed) *)

Inductive initial_state (lm: regset) (init_sp: val) (p: Mach.program) (i: ident) (sg: signature) (args: list val) (m: mem): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    (Hargs: extcall_arguments lm m init_sp sg args)    
  :
      initial_state lm init_sp p i sg args m (Callstate nil b lm m)
.

Inductive final_state (lm: regset) (sg: signature): state -> (list val * mem) -> Prop :=
| final_state_intro
    rs
    v
    (Hv: v = List.map rs (loc_result sg))
    (** Callee-save registers.
        We use Val.lessdef instead of eq because the Stacking pass does not exactly preserve their values. *)
    (CALLEE_SAVE: forall r,
       ~ In r destroyed_at_call ->
       Val.lessdef (lm r) (rs r))
    m :
    final_state lm sg (Returnstate nil rs m) (v, m)
.

Definition semantics
           (return_address_offset: function -> code -> int -> Prop)
           (lm: regset) (init_sp init_ra: val)
           (p: Mach.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
  Semantics (Mach.step return_address_offset init_sp init_ra) (initial_state lm init_sp p i sg args m) (final_state lm sg) (Genv.globalenv p).

End WITHCONFIG.
