Require compcert.cfrontend.ClightBigstep.
Require EventsX.

Import AST.
Import Globalenvs.
Import EventsX.
Import Ctypes.
Import Clight.
Export ClightBigstep.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Inductive bigstep_function_terminates' function_entry p i sg vargs (m: mem) t vres m' : Prop :=
  | bigstep_function_terminates_intro b f targs tres cc:
      let ge := Genv.globalenv p in
      let wb := Events.writable_block_with_init_mem_writable_block_ops m in
      Genv.find_symbol ge i = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction targs tres cc ->
      sg = signature_of_type targs tres cc ->
      eval_funcall ge function_entry m f vargs t m' vres ->
      bigstep_function_terminates' function_entry p i sg vargs m t vres m'.

Definition bigstep_function_terminates2 := bigstep_function_terminates' (fun _ => function_entry2)  .

End WITHCONFIG.
