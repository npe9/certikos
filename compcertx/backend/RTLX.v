Require compcert.backend.RTL.
Require SmallstepX.
Require EventsX.

Import AST.
Import Values.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Export RTL.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

(** Execution of RTL functions with C-style arguments (long long 64-bit integers allowed) *)

Inductive initial_state (p: RTL.program) (i: ident) (m: mem) (sg: signature) (args: list val): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (** We need to keep the signature because it is required for lower-level languages *)
    (Hsig: sg = funsig f)
  :
      initial_state p i m sg args (Callstate nil f args m)
.

Inductive final_state (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    v
    m :
    final_state sg (Returnstate nil v m) (v, m)
.

(** We define the per-module semantics of RTL as adaptable to both C-style and Asm-style;
    by default it is C-style. *)

Definition csemantics
           (p: RTL.program) (i: ident) (m: mem) :=
  CSemantics (
      let _ := writable_block_with_init_mem_writable_block_ops m in
      RTL.step
    ) (initial_state p i m) (final_state) (Genv.globalenv p).

End WITHCONFIG.
