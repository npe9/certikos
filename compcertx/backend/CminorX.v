Require compcert.backend.Cminor.
Require SmallstepX.
Require EventsX.

Import AST.
Import Values.
Import Memory.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Export Cminor.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

(** Execution of Cminor functions with C-style arguments (long long 64-bit integers allowed) *)

Inductive initial_state (p: Cminor.program) (i: ident) (m: mem) (sg: signature) (args: list val): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (** We need to keep the signature because it is required for lower-level languages *)
    (Hsig: sg = funsig f)
  :
      initial_state p i m sg args (Callstate f args Kstop m)
.

Inductive final_state (sg: signature): state -> (val * mem) -> Prop :=
| final_state_intro
    v
    m :
    final_state sg (Returnstate v Kstop m) (v, m)
.

(** We define the per-module semantics of RTL as adaptable to both C-style and Asm-style;
    by default it is C-style. *)

Definition csemantics
           (p: Cminor.program) (i: ident) (m: mem) :=
  CSemantics (
      let _ := writable_block_with_init_mem_writable_block_ops m in
      Cminor.step
    ) (initial_state p i m) (final_state) (Genv.globalenv p).

End WITHCONFIG.
