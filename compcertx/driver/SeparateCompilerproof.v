
(** We do NOT import compcert.driver.Compiler, because we do NOT want
to depend on passes that are unsupported (e.g. CompCert C) *)

(** I can list the passes of CompCert backwards by heart! *)

Require SeparateCompiler.
Require AsmgenproofX.
Require StackingproofX.
Require CleanupLabelsproofX.
Require LinearizeproofX.
Require TunnelingproofX.
Require AllocproofX.
Require DeadcodeproofX.
Require ConstpropproofX.
Require CSEproofX.
Require RenumberproofX.
Require InliningproofX.
Require TailcallproofX.
Require RTLgenproofX.
Require SelectionproofX.
Require CminorgenproofX.
Require CshmgenproofX.
Require RTLtypingX.
Require ClightI64helpers.

Import Coqlib.
Import String.
Import Errors.
Import AST.
Import Values.
Import MemoryX.
Import Globalenvs.
Import ComposePasses.
Import Events.
Import SmallstepX.
Import Conventions1.
Import Asm.
Import SeparateCompiler.

Open Local Scope string_scope.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)

Section WITHCONFIG.
Context `{compiler_config: Events.CompilerConfiguration}
        `{memory_model_x: !Mem.MemoryModelX mem}.

(** Semantic requirement on external functions and builtins related to 64-bit integers *)
Context `{genv_valid_prf: SelectLongproofX.GenvValid}.
Context `{external_calls_i64_helpers: !SelectLongproofX.ExternalCallI64Helpers external_functions_sem I64helpers.hf}
        `{external_calls_i64_builtins: !SelectLongproofX.ExternalCallI64Builtins builtin_functions_sem I64helpers.hf}.       

(** Requirements of value analysis (CSE, constant propagation, dead code elimination *)
Context `{mmatch_ops: !ValueDomain.MMatchOps mem}.
Context `{mmatch_constructions_prf: !ValueAnalysis.MMatchConstructions mem}.

(** Requirements of dead code elimination *)
Context `{magree_ops: !Deadcodeproof.MAgreeOps mem} `{magree_prf: !Deadcodeproof.MAgree mem}.

Theorem transf_clight_program_correct:
  forall p p2
         (TRANSL_TO_RTL: transf_clight_program_to_rtl p = OK p2)

  (** For Inlining, we need a parameter which contains functions to inline. We do not care here
      how it is computed, as long as it is sound with the intermediate representation p2.
      It can be very well instantiated with [PTree.empty _] to disable function inlining. *)
         fenv
         (FENV_COMPAT: Inliningspec.fenv_compat (Genv.globalenv p2) fenv)

         tp
         (TRANSL_TO_ASM: transf_rtl_program fenv p2 = OK tp)
  ,

  (** Syntactic requirement on the Clight program: it has to contain declarations
      to external i64 helpers. *)
  forall (ge_contains_helpers:
            ClightI64helpers.genv_contains_helpers I64helpers.hf (Genv.globalenv p)),
  forall (ge_valid:
            SelectLongproofX.genv_valid (Genv.globalenv p)),

  forall m init_asm_rs
         (ASM_INVARIANT: AsmX.asm_invariant (Genv.globalenv tp) init_asm_rs m)

         (** Arguments and so on, given by the local condition on Asm external call *)
         args sg
         (EXTCALL_ARGS: Asm.extcall_arguments init_asm_rs m sg args)
         (INIT_SP_NOT_GLOBAL: 
            forall (b : Values.block) (o : Integers.Int.int),
              init_asm_rs ESP = Values.Vptr b o ->
              Ple (Genv.genv_next (Genv.globalenv tp)) b)
         i
         b
         (Hsymb:  Genv.find_symbol (Genv.globalenv tp) i = Some b)
         (PC_VAL: init_asm_rs PC = Values.Vptr b Integers.Int.zero)
         (SP_NOT_VUNDEF: init_asm_rs ESP <> Vundef)
         (RA_NOT_VUNDEF: init_asm_rs RA <> Vundef)
  ,
  forward_simulation
    (semantics_as_asm (ClightX.csemantics p i m) sg args)
    (semantics_with_inject (AsmX.semantics init_asm_rs tp i sg args m) m).
Proof.
  intros.
  revert TRANSL_TO_RTL; unfold transf_clight_program_to_rtl; simpl.
  caseEq (Cshmgen.transl_program p); simpl; try congruence; intros p01 EQ01.
  caseEq (Cminorgen.transl_program p01); simpl; try congruence; intros p02 EQ02.
  set (p1 := SelectionX.sel_program p02) in *.
  caseEq (RTLgen.transl_program p1); simpl; try congruence; intros p11 EQ11.
  intro.
  inv TRANSL_TO_RTL.
  set (p2 := Tailcall.transf_program p11) in *.
  revert TRANSL_TO_ASM; unfold transf_rtl_program; simpl.
  caseEq (InliningX.transf_program fenv p2); simpl; try congruence; intros p3 EQ3.
  set (p31 := Renumber.transf_program p3) in *.
  set (p32 := ConstpropX.transf_program p31) in *.
  set (p33 := Renumber.transf_program p32) in *.
  caseEq (CSEX.transf_program p33); simpl; try congruence; intros p34 EQ34.
  caseEq (DeadcodeX.transf_program p34); simpl; try congruence; intros p35 EQ35.
  caseEq (Allocation.transf_program p35); simpl; try congruence; intros p4 EQ4.
  set (p5 := Tunneling.tunnel_program p4) in *.
  caseEq (Linearize.transf_program p5); simpl; try congruence; intros p6 EQ6.
  set (p7 := CleanupLabels.transf_program p6) in *.
  caseEq (Stacking.transf_program p7); simpl; try congruence; intros p8 EQ8.
  intro EQTP.

  inv ASM_INVARIANT.
  inv inv_inject_neutral.

  eapply compose_forward_simulation.
  {
    apply semantics_injects_c_to_asm.
    eapply compose_forward_simulation.
    {
      apply CshmgenproofX.transl_program_correct. eassumption.
    }
    eapply compose_forward_simulation.
    {
      apply CminorgenproofX.transl_program_correct. eassumption.
      assumption. 
      {
        erewrite <- Cminorgenproof.genv_next_preserved; eauto.
        erewrite <- SelectionproofX.genv_next_preserved; eauto.
        erewrite <- RTLgenproof.genv_next_preserved; eauto.
        erewrite <- Tailcallproof.genv_next_preserved; eauto.
        erewrite <- Inliningproof.genv_next_preserved; eauto.
        rewrite <- Renumberproof.genv_next_preserved. fold p31.
        rewrite <- ConstpropproofX.genv_next_preserved. fold p32.
        rewrite <- Renumberproof.genv_next_preserved. fold p33.
        erewrite <- CSEproofX.genv_next_preserved; eauto.
        erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
        erewrite <- Allocproof.genv_next_preserved; eauto.
        rewrite <- Tunnelingproof.genv_next_preserved. fold p5.
        erewrite <- Linearizeproof.genv_next_preserved; eauto.
        rewrite <- CleanupLabelsproof.genv_next_preserved. fold p7.
        erewrite <- StackingproofX.genv_next_preserved; eauto.
        erewrite <- AsmgenproofX.genv_next_preserved; eauto.
      }
      apply decode_longs_inject. eapply AsmX.extcall_args_inject_neutral; eauto.      
    }
    eapply compose_forward_simulation.
    {
      apply forward_simulation_extends_right_inject.
      apply SelectionproofX.transf_program_correct.
      eapply CminorgenproofX.genv_contains_helpers_correct; eauto.
      eapply CshmgenproofX.genv_contains_helpers_correct; eauto.
      eapply SelectLongproofX.genv_valid_preserved.
      { eapply Cminorgenproof.symbols_preserved; eauto. }
      { eapply Cminorgenproof.genv_next_preserved; eauto. }
      { unfold block_is_volatile. intro. erewrite Cminorgenproof.varinfo_preserved; eauto. }
      eapply SelectLongproofX.genv_valid_preserved.
      { eapply Cshmgenproof.symbols_preserved; eauto. }
      { eapply Cshmgenproof.genv_next_preserved; eauto. }
      { eapply Cshmgenproof.block_is_volatile_preserved; eauto. }
      assumption.
    }
    eapply compose_forward_simulation.
    {
      apply forward_simulation_extends_right_inject.
      apply RTLgenproofX.transf_program_correct. eassumption.
    }
    eapply compose_forward_simulation.
    {
      eapply forward_simulation_extends_right_inject.
      apply TailcallproofX.transf_program_correct.
    }
    eapply compose_forward_simulation.
    {
      eapply forward_simulation_inject_right.
      eapply InliningproofX.transf_program_correct; eauto.
      {
        erewrite <- Inliningproof.genv_next_preserved; eauto.
        rewrite <- Renumberproof.genv_next_preserved. fold p31.
        rewrite <- ConstpropproofX.genv_next_preserved. fold p32.
        rewrite <- Renumberproof.genv_next_preserved. fold p33.
        erewrite <- CSEproofX.genv_next_preserved; eauto.
        erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
        erewrite <- Allocproof.genv_next_preserved; eauto.
        rewrite <- Tunnelingproof.genv_next_preserved. fold p5.
        erewrite <- Linearizeproof.genv_next_preserved; eauto.
        rewrite <- CleanupLabelsproof.genv_next_preserved. fold p7.
        erewrite <- StackingproofX.genv_next_preserved; eauto.
        erewrite <- AsmgenproofX.genv_next_preserved; eauto.      
      }
      eapply decode_longs_inject.
      eapply AsmX.extcall_args_inject_neutral; eauto.
    }
    eapply forward_simulation_extends_right_inject.
    eapply compose_forward_simulation.
    {
      eapply RenumberproofX.transf_program_correct.
    }
    eapply compose_forward_simulation.
    {
      eapply ConstpropproofX.transf_program_correct; eauto.
      {
        fold p31.
        rewrite <- ConstpropproofX.genv_next_preserved. fold p32.
        rewrite <- Renumberproof.genv_next_preserved. fold p33.
        erewrite <- CSEproofX.genv_next_preserved; eauto.
        erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
        erewrite <- Allocproof.genv_next_preserved; eauto.
        rewrite <- Tunnelingproof.genv_next_preserved. fold p5.
        erewrite <- Linearizeproof.genv_next_preserved; eauto.
        rewrite <- CleanupLabelsproof.genv_next_preserved. fold p7.
        erewrite <- StackingproofX.genv_next_preserved; eauto.
        erewrite <- AsmgenproofX.genv_next_preserved; eauto.
      }
      eapply decode_longs_inject.
      eapply AsmX.extcall_args_inject_neutral; eauto.
    }
    eapply forward_simulation_extends_right.
    eapply compose_forward_simulation.
    {
      eapply RenumberproofX.transf_program_correct.
    }
    eapply compose_forward_simulation.
    {
      eapply CSEproofX.transf_program_correct; eauto.
      {
        fold p31. fold p32. fold p33.
        erewrite <- CSEproofX.genv_next_preserved; eauto.
        erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
        erewrite <- Allocproof.genv_next_preserved; eauto.
        rewrite <- Tunnelingproof.genv_next_preserved. fold p5.
        erewrite <- Linearizeproof.genv_next_preserved; eauto.
        rewrite <- CleanupLabelsproof.genv_next_preserved. fold p7.
        erewrite <- StackingproofX.genv_next_preserved; eauto.
        erewrite <- AsmgenproofX.genv_next_preserved; eauto.
      }
      eapply decode_longs_inject.
      eapply AsmX.extcall_args_inject_neutral; eauto.
    }
    eapply forward_simulation_extends_right.
    eapply DeadcodeproofX.transf_program_correct; eauto.
    {
      erewrite <- DeadcodeproofX.genv_next_preserved; eauto.
      erewrite <- Allocproof.genv_next_preserved; eauto.
      rewrite <- Tunnelingproof.genv_next_preserved. fold p5.
      erewrite <- Linearizeproof.genv_next_preserved; eauto.
      rewrite <- CleanupLabelsproof.genv_next_preserved. fold p7.
      erewrite <- StackingproofX.genv_next_preserved; eauto.
      erewrite <- AsmgenproofX.genv_next_preserved; eauto.
    }
    eapply decode_longs_inject.
    eapply AsmX.extcall_args_inject_neutral; eauto.    
  }
  eapply forward_simulation_inject_right.
  eapply compose_forward_simulation.
  {
    apply AllocproofX.transf_program_correct. eassumption.
    eapply StackingproofX.extcall_args_eq. eapply AsmgenproofX.extcall_args_match_inv. eassumption.
    apply RTLtypingX.has_type_list_normalize. eapply AsmX.extcall_args_type_decode_longs. eassumption.
  }
  eapply compose_forward_simulation.
  {
    apply forward_simulation_extends.
    apply TunnelingproofX.transf_program_correct.
  }
  eapply compose_forward_simulation.
  {
    apply forward_simulation_extends.
    apply LinearizeproofX.transf_program_correct. eassumption.
  }
  eapply compose_forward_simulation.
  {
    apply forward_simulation_extends.
    apply CleanupLabelsproofX.transf_program_correct.
  }
  eapply compose_forward_simulation.
  {
    apply forward_simulation_extends_left_inject.
    apply StackingproofX.transf_program_correct. eassumption.
    apply AsmgenproofX.extcall_args_match_inv. assumption.
    assumption.    
    erewrite <- AsmgenproofX.genv_next_preserved; eauto.
    intros; eapply inv_reg_inject_neutral.
    eapply AsmgenproofX.machregs_type; eauto.
    apply Asmgenproof.return_address_exists.
    {
      fold p7.
      erewrite <- StackingproofX.genv_next_preserved; eauto.
      erewrite <- AsmgenproofX.genv_next_preserved; eauto.
    }
    {
      intros ? ? VAL.
      generalize (inv_reg_inject_neutral ESP).
      rewrite VAL.
      inversion 1.
      clear H5.
      subst.
      unfold Mem.flat_inj in *.
      unfold Mem.valid_block.
      destruct (plt b0 (Mem.nextblock m)); congruence.
    }
    apply inv_reg_wt.
    instantiate (1 := init_asm_rs RA). apply inv_reg_wt.
  }
  apply forward_simulation_extends_right_inject.
  eapply AsmgenproofX.transf_program_correct. assumption.  
  eassumption.
  assumption.
  assumption.
  assumption.
Qed.

End WITHCONFIG.
