Require Import Events.
Require Import Memimpl.

(** [CompCertX:test-compcert-param-extcall] This file reproduces the
   fact of assuming the semantics of external functions and their
   properties as axioms,as in the original CompCert 2.3. It is
   required by [ComplementsImpl].

   Even though we axiomatize over the semantics of external functions
   for CompCert 2.3 whole-program, the new [CompilerConfiguration]
   class does not need to be wholly axiomatised over, as the memory
   model is correctly implemented in [Memimpl]. That is why, in this
   file, given those axioms about external functions, we construct an
   instance of [CompilerConfiguration].  *)

(** [CompCertX:test-compcert-param-extcall] We need to individually
axiomatize each field of the type class (which are in Prop), instead
of axiomatizing on the class itself (which is in Type), because we
need an instance of ExternalCallsOps since introducing
CompilerConfigOps, the latter being used by extracted OCaml code. *)

Parameter external_functions_sem : AST.ident -> AST.signature -> extcall_sem.
Parameter builtin_functions_sem : AST.ident -> AST.signature -> extcall_sem.
Parameter inline_assembly_sem : AST.ident -> extcall_sem.

Global Instance external_calls_ops: ExternalCallsOps mem.
Proof.
  constructor.
  exact external_functions_sem.
  exact builtin_functions_sem.
  exact inline_assembly_sem.
Defined.

Axiom external_calls: ExternalCalls mem.

(** [CompCertX:test-compcert-disable-extcall-as-builtin] We may need
to disallow the use of external function calls (EF_external) as
builtins. This is already the case in assembly generation
(PrintAsm.ml), but not in the semantics of languages, which we propose
to fix through providing a switch in the compiler configuration, hence
the following CompilerConfigOps class: *)

Global Instance compiler_config_ops: CompilerConfigOps mem :=
{
(** Even though assembly generation will refuse to produce code with
external calls as builtins, the original CompCert semantics does not
prevent it, so we keep this feature here. *)
  cc_enable_external_as_builtin := true
}.

Global Instance compiler_config: CompilerConfiguration mem.
Proof.
  constructor; typeclasses eauto.
Qed.
