Require compcert.cfrontend.Clight.
Require SmallstepX.
Require EventsX.

Import AST.
Import Values.
Import Globalenvs.
Import EventsX.
Import SmallstepX.
Import Ctypes.
Export Clight.

(** Execution of Clight functions with C-style arguments (long long 64-bit integers allowed)
    BUT with Asm signature (not C signature).
 *)

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Inductive initial_state (p: Clight.program) (i: ident) (m: mem) (sg: signature) (args: list val): state -> Prop :=
| initial_state_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    f
    (Hf: Genv.find_funct_ptr (Genv.globalenv p) b = Some f)
    (** We need to keep the signature because it is required for lower-level languages *)
    targs tres tcc
    (Hty: type_of_fundef f = Tfunction targs tres tcc)
    (Hsig: sg = signature_of_type targs tres tcc)
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
    by default it is C-style (except for signature, which must be Asm-style). *)

Definition csemantics
           (p: Clight.program) (i: ident) (m: mem) :=
  CSemantics (
      let _ := writable_block_with_init_mem_writable_block_ops m in
      Clight.step2
    ) (initial_state p i m) (final_state) (Genv.globalenv p).

End WITHCONFIG.
