(* *********************************************************************)
(*                                                                     *)
(*            The CertiKOS Certified Kit Operating System              *)
(*                                                                     *)
(*                   The FLINT Group, Yale University                  *)
(*                                                                     *)
(*  Copyright The FLINT Group, Yale University.  All rights reserved.  *)
(*  This file is distributed under the terms of the Yale University    *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import SmallstepX.
Require SeparateCompilerproof.
Require Import Decision.
Require Import MemWithData.
Require Import liblayers.compat.CompatData.
Require Import Stencil.
Require Import MakeProgram.
Require Import Observation.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import liblayers.compat.I64Layer.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compat.CompatClightSem.
Require LAsmgenproof.
Require Import LAsmModuleSem.
Require Import CompCertiKOS.
Require Import LiftValueAnalysis.
Require Import LiftDeadcodeproof.

Lemma lasm_sig_preserved f tf:
  LAsmgen.transf_fundef f = Internal tf ->
  exists fi,
    f = Internal fi /\
    LAsm.fn_sig tf = Asm.fn_sig fi.
Proof.
  destruct f; try discriminate.
  simpl.
  unfold LAsmgen.transf_function.
  inversion 1; subst; simpl; eauto.
Qed.

Lemma asm_sig_preserved f tf:
  Asmgen.transf_fundef f = OK (Internal tf) ->
  Asm.fn_sig tf = Mach.funsig f.
Proof.
  destruct f; try discriminate.
  simpl.
  unfold Errors.bind.
  destruct (Asmgen.transf_function f) eqn:F; try discriminate.
  inversion 1; subst.
  revert F.
  unfold Asmgen.transf_function.
  unfold Errors.bind.
  destruct (Asmgen.transl_function f) eqn:F; try discriminate.
  destruct (zlt Int.max_unsigned (list_length_z (fn_code f0))); try discriminate.
  inversion 1; subst.
  revert F.
  unfold Asmgen.transl_function.
  unfold Errors.bind.
  destruct (Asmgen.transl_code' f (Mach.fn_code f) true); try discriminate.
  inversion 1; subst.
  reflexivity.
Qed.

Theorem transf_clight_function'_sig_translated fenv f tf:
  transf_clight_function' fenv f = OK tf ->  
  LAsm.fn_sig tf = Ctypes.signature_of_type (Ctypes.type_of_params (Clight.fn_params f)) (Clight.fn_return f) (Clight.fn_callconv f).
Proof.
  intro FUN.
  apply transf_clight_fundef_internal in FUN.
  revert FUN.
  unfold transf_clight_fundef',
  SeparateCompiler.transf_clight_fundef',
  SeparateCompiler.transf_clight_fundef_to_rtl,
  SeparateCompiler.transf_rtl_fundef.
  unfold ComposePasses.compose_partial, ComposePasses.compose_total_right, ComposePasses.apply_total, ComposePasses.apply_partial.
  destruct (Cshmgen.transl_fundef (Clight.Internal f)) eqn:?; try discriminate.
  exploit (Cshmgenproof.transl_fundef_sig2 (Clight.Internal f)); eauto.
  { reflexivity. }
  intro SIG.
  destruct (Cminorgen.transl_fundef f0) eqn:?; try discriminate.
  erewrite <- Cminorgenproof.sig_preserved in SIG; eauto.
  unfold SelectionX.sel_fundef.
  erewrite <- (Selectionproof.sig_function_translated I64helpers.hf (fun _ => None)) in SIG; eauto.
  fold SelectionX.sel_fundef in *.
  destruct (RTLgen.transl_fundef (SelectionX.sel_fundef f1)) eqn:?; try discriminate.
  erewrite <- RTLgenproof.sig_transl_function in SIG; eauto.
  erewrite <- Tailcallproof.sig_preserved in SIG.
  destruct (Inlining.transf_fundef fenv (Tailcall.transf_fundef f2)) eqn:?; try discriminate.
  erewrite <- Inliningproof.sig_function_translated in SIG; eauto.
  rewrite <- Renumberproof.sig_preserved in SIG.  
  unfold ConstpropX.transf_fundef.
  rewrite <- (Constpropproof.sig_function_translated ValueDomainX.rmtop) in SIG.
  fold ConstpropX.transf_fundef in *.
  rewrite <- Renumberproof.sig_preserved in SIG.
  unfold CSEX.transf_fundef.
  destruct (CSE.transf_fundef ValueDomainX.rmtop (Renumber.transf_fundef (ConstpropX.transf_fundef (Renumber.transf_fundef f3)))) eqn:?; try discriminate.
  erewrite <- CSEproof.sig_preserved in SIG; eauto.
  unfold DeadcodeX.transf_fundef.
  destruct (Deadcode.transf_fundef ValueDomainX.rmtop f4) eqn:?; try discriminate.
  erewrite <- Deadcodeproof.sig_function_translated in SIG; eauto.
  destruct (Allocation.transf_fundef f5) eqn:?; try discriminate.
  erewrite <- Allocproof.sig_function_translated in SIG; eauto.
  erewrite <- Tunnelingproof.sig_preserved in SIG.
  destruct (Linearize.transf_fundef (Tunneling.tunnel_fundef f6)) eqn:?; try discriminate.
  erewrite <- Linearizeproof.sig_preserved in SIG; eauto.
  rewrite <- CleanupLabelsproof.sig_function_translated in SIG.
  destruct (Stacking.transf_fundef (CleanupLabels.transf_fundef f7)) eqn:?; try discriminate.
  erewrite <- Stackingproof.sig_preserved in SIG; eauto.
  destruct (Asmgen.transf_fundef f8) eqn:?; try discriminate.
  inversion 1; subst.
  exploit lasm_sig_preserved; eauto.
  destruct 1 as (? & ? & SIG'); subst.
  exploit asm_sig_preserved; eauto.
  intro.
  congruence.
Qed.

Section WITHKERNELMODE.

  Context `{kernel_mode_prf: LAsmgenproof.KernelMode}.

  (** We have to disable externals as builtins in the source [Asm] code. *)

  Let cc_ops : CompilerConfigOps (mwd D) := 
    {|
      cc_enable_external_as_builtin := false
    |}.
  Local Existing Instance cc_ops.

    (** Remember that we are compiling Asm code, so the external
  functions must be compilable. *)
  Context `{ec_prf: !CompilerConfiguration (mwd D)}.

  (** Requirement on the memory model to compose CompCertX *)
  Context `{memory_model_x: !Mem.MemoryModelX mem}.
  
  (** Semantic requirement on external functions and builtins related to 64-bit integers *)
  Context `{genv_valid: SelectLongproofX.GenvValid}.
  Context `{external_calls_i64_helpers: !SelectLongproofX.ExternalCallI64Helpers external_functions_sem I64helpers.hf}
          `{external_calls_i64_builtins: !SelectLongproofX.ExternalCallI64Builtins builtin_functions_sem I64helpers.hf}.      

  (** Requirements of value analysis (CSE, constant propagation, dead
      code elimination).  Those can be stated on the [mem] base memory
      model, then [ValueDomainWithData] will "lift" them to [mwd D].
   *)
  Context `{mmatch_ops: !ValueDomain.MMatchOps mem}.
  Context `{mmatch_constructions_prf: !ValueAnalysis.MMatchConstructions mem}.

  (** Requirements of dead code elimination.
      Those can be stated on the [mem] base memory model, then [LiftDeadcodeproof] will
      lift them to [mwd D]. *)

  Context `{magree_ops: !Deadcodeproof.MAgreeOps mem}
          `{magree_prf: !Deadcodeproof.MAgree mem}.

  (** These are necessary for Coq to find instances of !Deadcodeproof.MAgree *)
  (** and also of !ValueAnalysis.MMatchConstructions *)
  Local Existing Instance mwd_liftmem_ops.
  Local Existing Instance mwd_liftmem_prf.

  Theorem transf_clight_program_correct:
    forall p p2
           (TRANSL_TO_RTL: SeparateCompiler.transf_clight_program_to_rtl p = OK p2)

  (** For Inlining, we need a parameter which contains functions to inline. We do not care here
      how it is computed, as long as it is sound with the intermediate representation p2.
      It can be very well instantiated with [PTree.empty _] to disable function inlining. *)
  fenv
  (FENV_COMPAT: Inliningspec.fenv_compat (Genv.globalenv p2) fenv)
  
  tp
  (TRANSL_TO_LASM: transf_rtl_program fenv p2 = OK tp)
  ,

  (** Syntactic requirement on the Clight program: it has to contain declarations
      to external i64 helpers. *)
  forall (ge_contains_helpers:
            ClightI64helpers.genv_contains_helpers I64helpers.hf (Genv.globalenv p)),
  forall (ge_valid: SelectLongproofX.genv_valid (Genv.globalenv p)),

  forall (m: mwd D) (init_asm_rs: Asm.regset)
         (ASM_INVARIANT: AsmX.asm_invariant (Genv.globalenv tp) init_asm_rs m)

         (** requirement by LAsm *)
         (kernel_mode: LAsmgenproof.kernel_mode (π_data m))

         (** Arguments and so on, given by the local condition on Asm external call *)
         args sg
         (EXTCALL_ARGS: Asm.extcall_arguments init_asm_rs m sg args)
         (INIT_SP_NOT_GLOBAL: 
            forall (b : Values.block) (o : Integers.Int.int),
              init_asm_rs (Asm.IR Asm.ESP) = Values.Vptr b o ->
              Ple (Genv.genv_next (Genv.globalenv tp)) b)
         i
         b
         (Hsymb:  Genv.find_symbol (Genv.globalenv tp) i = Some b)
         (PC_VAL: init_asm_rs Asm.PC = Values.Vptr b Integers.Int.zero)
         (SP_NOT_VUNDEF: init_asm_rs (Asm.IR Asm.ESP) <> Vundef)
         (RA_NOT_VUNDEF: init_asm_rs Asm.RA <> Vundef)
  ,
  forward_simulation
    (semantics_as_asm (ClightX.csemantics p i m) sg args)
    (semantics_with_inject (LAsmgenproof.PFLAsm.semantics init_asm_rs tp i sg args m) m).

Proof.

  intros.

  unfold transf_rtl_program in TRANSL_TO_LASM.
  simpl in TRANSL_TO_LASM.
  destruct (SeparateCompiler.transf_rtl_program fenv p2) eqn:TRANSL_TO_ASM;
    try discriminate.
  simpl in TRANSL_TO_LASM.
  inv TRANSL_TO_LASM.

  eapply compose_forward_simulation.
  {
    eapply SeparateCompilerproof.transf_clight_program_correct; eauto.
    {
      inversion ASM_INVARIANT; subst.
      constructor; eauto.
      inversion inv_inject_neutral; subst.
      rewrite LAsmgenproof.genv_next_preserved in inv_mem_valid.
      constructor; eauto.
    }
    {
      erewrite <- LAsmgenproof.genv_next_preserved; eauto.
    }
    {
      erewrite <- LAsmgenproof.symbols_preserved; eauto.
    }
  }
  apply forward_simulation_extends_inject.
  apply forward_simulation_extends.
  apply LAsmgenproof.transf_program_correct; eauto.
Qed.

End WITHKERNELMODE.

(** How to convert CompCertiKOS' correctness statement into the new framework. *)

(** How to instantiate kernel mode. *)

Section WITHLAYER.

Context `{Hobs: Observation}.
Context `{Hstencil: Stencil.Stencil}.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.

Context {D: compatdata}.

Variable (L: compatlayer D).

Instance KMOPS: LAsmgenproof.KernelModeOps D.
Proof.
  constructor.
Defined.

Context `{extcall_invariants_defined: !ExtcallInvariantsDefined L}.

Context `{acc_def_prf: !LAsm.AccessorsDefined L}.

Instance KM: LAsmgenproof.KernelMode D
                        (ec_ops_x := compatlayer_extcall_ops_x L)
                        (lc_ops   := LAsmModuleSemDef.LC L).
Proof.
  constructor.
  * (* exec_load *)
    intros. simpl.
    unfold LAsm.acc_exec_load.    
    destruct (LAsm.acc_exec_load_strong L).
    destruct x; simpl; eapply exec_load_kernel_mode; eauto.
  * (* exec_store *)
    intros. simpl.
    unfold LAsm.acc_exec_store.
    destruct (LAsm.acc_exec_store_strong L).
    destruct x; simpl; eapply exec_store_kernel_mode; eauto.
  * (* external functions *)
    intros until m'.
    intros (σ & Hget & s & σf & Hmatch & Hsem & ? & ? & ?).
    subst.
    generalize (extcall_invariants_defined i).
    rewrite Hget.
    simpl.
    destruct (sextcall_invs _ σf); try discriminate.
    intros _.
    destruct m. destruct m'.
    eapply external_call_kernel_mode; eauto.
  * (* externals require kernel mode *)
    tauto.
Qed.

End WITHLAYER.

(** Now we define compiler correctness in the new framework. We start
by defining a relationship between a C-style primitive (sextcall) and
an Asm-style primitive (sprimcall) *)

Section SIMULATION.

Context `{Hobs: Observation}.
Context `{Hstencil: Stencil.Stencil}.
Context `{Hmemx: Mem.MemoryModelX}.
Context `{Hmwd: UseMemWithData mem}.

Inductive compiler_primsim {D: compatdata}: compatsem D -> compatsem D -> Prop :=
| compiler_primsim_intro
    (sem1: sextcall_primsem D)
    (sem2: sprimcall_primsem D)
    (i: ident)
    (NAME: sprimcall_name D sem2 = Some i)
    (VALID: forall s,
              sprimcall_valid sem2 s = true ->
              sextcall_valid sem1 s = true)
    (SIG: sprimcall_sig sem2 = sextcall_sig sem1)
    (INV: isError (sprimcall_invs D sem2))
    (COMPILER_PRIMSIM: forall (m: mwd D) (rs: Asm.regset) (args: list val)
                 (res: val) (m'_clight: mwd D)
                 (s: stencil) (b: block) (WB: block -> Prop)
                 (ARGS: extcall_arguments rs m (sextcall_sig sem1) args)
                 (SYMB: find_symbol s i = Some b)
                 (PC: rs PC = Vptr b Int.zero)
                 (KERNEL_MODE: kernel_mode (π_data m))
                 (ASM_INVARIANT: asm_invariant s rs m)
                 (SP_NOT_VUNDEF: rs (Asm.IR Asm.ESP) <> Vundef)
                 (RA_NOT_VUNDEF: rs Asm.RA <> Vundef)
                 (INIT_SP_NOT_GLOBAL: 
                    forall (b : Values.block) (o : Integers.Int.int),
                      rs (Asm.IR Asm.ESP) = Values.Vptr b o ->
                      Ple (genv_next s) b)
                 (SEM1: sem1 s WB (decode_longs (sig_args (sextcall_sig sem1)) args) m res m'_clight)
                 (VALID: sprimcall_valid sem2 s = true)
                 (** The following condition is needed to compose with [CompatClightSem.primitive_le] *)
                 (HIGH: high_level_invariant (π_data m))
          ,
            exists j rs' m'_lasm,
              sprimcall_step sem2 s rs m rs' m'_lasm /\
              Mem.inject j m'_clight m'_lasm /\
              inject_incr (Mem.flat_inj (Mem.nextblock m)) j /\
              inject_separated (Mem.flat_inj (Mem.nextblock m)) j m m /\
              val_list_inject j (encode_long (sig_res (sextcall_sig sem1)) res) (map rs' (loc_external_result (sextcall_sig sem1))) /\
              (forall r,
                 ~ In r Conventions1.destroyed_at_call ->
                 Val.lessdef (rs (preg_of r)) (rs' (preg_of r))) /\
              Val.lessdef (rs RA) (rs' Asm.PC) /\
              Val.lessdef (rs ESP) (rs' ESP)

    )
  :
    compiler_primsim (inl sem1) (inr sem2).

Remark ple_prop_intro:
  forall n1 n2,
    (forall n, Plt n n1 -> Plt n n2) ->
    Ple n1 n2.
Proof.
  intros.
  destruct (peq n1 xH).
   xomega.
  generalize (Psucc_pred n1).
  destruct 1; try contradiction.
  refine (_ (H (Pos.pred n1) _)).
  intro.
  rewrite <- H0. xomega.
  xomega.
Qed.

Remark inject_incr_le:
  forall n1 n2,
    Ple n1 n2 ->
    inject_incr (Mem.flat_inj n1) (Mem.flat_inj n2).
Proof.
  unfold inject_incr, Mem.flat_inj.
  intros.
  destruct (plt b n1); try discriminate.
  destruct (plt b n2); try congruence.
  xomega.
Qed.

Theorem compatsim_compiler_primsim_compose:
  forall {D0 D: compatdata}
         (R: compatrel D0 D)
         (sem0: compatsem D0)
         (sem1 sem2: compatsem D)
         (SIM01: compatsim (freerg_inj _ _ _ R) sem0 sem1)
         (NEXTBLOCK:
            match sem1 with
              | inl s1 =>
                forall s WB args m res m', 
                  sextcall_step s1 s WB args m res m' -> Mem.nextblock m' = Mem.nextblock m
              | _ => True
            end)
         (KERNEL_MODE:
            match sem1 with
              | inl s1 =>
                forall s WB args m res m', 
                  sextcall_step s1 s WB args m res m' -> kernel_mode (π_data m)
              | _ => True
            end)
         (SIM12: compiler_primsim sem1 sem2)
  ,
    compatsim (freerg_inj _ _ _ R) sem0 sem2.
Proof.
  inversion 4; subst.
  inversion SIM01; subst.
  inversion H1; subst.
  rename sextcall_sim_valid into VALID'.
  constructor.
  constructor; eauto.
  esplit; eauto.
  split; eauto.

  * intros.
    exploit sextcall_sim_step; eauto.
    + instantiate (1 := fun _ => True).
      tauto.
    + eapply decode_longs_inject.
      eassumption.
    + destruct 1 as (f' & vres2 & m2' & d2' & SEM3 & VRESINJ & MATCHEXTCALL' & INCR).
      assert (SIG_EQ: sextcall_sig sem1 = sextcall_sig sem3) by
        (unfold sextcall_sig; congruence).
      exploit COMPILER_PRIMSIM; eauto.
      - rewrite <- SIG_EQ; eauto.
(* kernel_mode: solved by eauto.
      - assumption.
*)
      - rewrite <- SIG_EQ; eauto.
      - destruct 1 as (j & rs' & m'_lasm & SEM4 & INJ_J & INJ_INCR & INJ_SEP
                         & VRES2INJ & CALLEE_SAVE & PC_LESS & ESP_LESS).

  assert (NB: Mem.nextblock m2' = Mem.nextblock m2).
  {
    generalize (NEXTBLOCK _ _ _ _ _ _ SEM3). clear. lift_unfold. congruence.
  }
  assert (COMPOSE: compose_meminj f' j = f').
  {
    apply FunctionalExtensionality.functional_extensionality.
    unfold compose_meminj.
    intro x.
    destruct (f' x) as [ [y delta] | ] eqn:Heqx; try congruence.
    exploit Mem.valid_block_inject_2; eauto using match_inject.
    unfold Mem.valid_block.
    rewrite NB.
    intro.
    replace (j y) with (Some (y, 0%Z)).
    f_equal. f_equal. omega.
    symmetry. apply INJ_INCR. unfold Mem.flat_inj. destruct (plt y (Mem.nextblock (m2, d2))) eqn:Hlt.
     simpl in *. rewrite Hlt. reflexivity.
    exfalso. clear Hlt. revert H n. clear. lift_unfold. contradiction.
  }
  destruct m'_lasm as [m'_lasm d'_lasm].
  assert (INJ_J': Mem.inject j m2' m'_lasm /\ d2' = d'_lasm).
   revert INJ_J. clear. lift_unfold. tauto.
  destruct INJ_J' as [INJ_J' ?]; subst d2'.
  exists f'. exists rs'. exists m'_lasm. exists d'_lasm.
  split. assumption.
  split.
  {
    inversion MATCHEXTCALL'; constructor; eauto.
    rewrite <- COMPOSE. eapply Mem.inject_compose; eauto.
    {
      rewrite <- COMPOSE. eapply match_compose; eauto.
      eapply inject_incr_trans.
      2: eassumption.
      apply inject_incr_le. 
      clear COMPOSE.
      inversion ASM_INV.
      inversion inv_inject_neutral.
      assumption.
    }
    apply ple_prop_intro. intros.
    assert (Plt n (Mem.nextblock m2')) by xomega.
    generalize Hmemx Hmwd H0 INJ_J' INJ_INCR NB. clear.
    intros.
    lift_unfold.
    intros.
    rewrite <- NB in INJ_INCR.
    assert (j n = Some (n, 0%Z)).
     eapply INJ_INCR. unfold Mem.flat_inj. destruct (plt n (Mem.nextblock m2')); congruence.
    eapply Mem.valid_block_inject_2; eauto.
  }
  split. assumption.
  split.
  rewrite <- COMPOSE.
  refine (SmallstepX.val_inject_compose _ _ _ _ _ _ _).
   eapply val_list_inject_incr. instantiate (1 := f). assumption.
   eapply encode_long_inject. eassumption.
   rewrite SIG_EQ. assumption.
   split.
   assumption.
   split; assumption.

  * unfold sextcall_sig in *.
    congruence.

  * destruct INV as [err Hinvs].
    rewrite Hinvs.
    constructor.
Qed.

(** We finally define compiler simulation at the level of layers. *)
 
Inductive compiler_defsim {D}:
  res (option (compatsem D)) -> res (option (compatsem D)) -> Prop :=
| compiler_defsim_some
    sem1 sem2
    (Hsem: compiler_primsim sem1 sem2)
  : compiler_defsim (OK (Some sem1)) (OK (Some sem2))
| compiler_defsim_none p
  : compiler_defsim (OK None) p
.

Lemma res_option_sim_compatsim_compiler_defsim_compose
      D0 D (R: compatrel D0 D) sem0 sem1 sem2:
 res_le (option_le (compatsim (freerg_inj _ _ _ R))) sem0 sem1 ->
 compiler_defsim sem1 sem2 ->
 match sem1 with
   | OK (Some (inl s1)) =>
     forall s WB args m res m', 
       sextcall_step s1 s WB args m res m' -> Mem.nextblock m' = Mem.nextblock m
   | _ => True
 end ->
 forall (KERNEL_MODE:
            match sem1 with
              | OK (Some (inl s1)) =>
                forall s WB args m res m', 
                  sextcall_step s1 s WB args m res m' -> kernel_mode (π_data m)
              | _ => True
            end),
 res_le (option_le (compatsim (freerg_inj _ _ _ R))) sem0 sem2.
Proof.
  inversion 2; subst; inversion H; subst.
  * inversion H3; subst; intros;
    solve_monotonic.
    eapply compatsim_compiler_primsim_compose; eauto.
  * inversion H3; subst.
    intros. destruct sem2; solve_monotonic.
Qed.

Record compiler_layersim {D} (L1 L2: compatlayer D): Prop :=
  {
    compiler_layersim_primitives:
      forall i,
        compiler_defsim (get_layer_primitive i L1) (get_layer_primitive i L2)
    ;
    compiler_layersim_globalvars:
      forall i,
        res_le (option_le eq) (get_layer_globalvar i L1) (get_layer_globalvar i L2)
    ;
    compiler_layersim_load:
      res_le (option_le eq) (cl_exec_load L1) (cl_exec_load L2)
    ;
    compiler_layersim_store:
      res_le (option_le eq) (cl_exec_store L1) (cl_exec_store L2)
  }.
   
Theorem cl_sim_compiler_layersim_compose:
  forall {D0 D: compatdata}
         (R: compatrel D0 D)
         (L0: compatlayer D0)
         (L1 L2: compatlayer D)
         (SIM01: cl_sim _ _ (freerg_inj _ _ _ R) L0 L1)
         (NEXTBLOCK:
            forall i s1,
              get_layer_primitive i L1 = OK (Some (compatsem_inl s1)) ->
              forall s WB args m res m', 
                sextcall_step s1 s WB args m res m' -> Mem.nextblock m' = Mem.nextblock m
         )
         (KERNEL_MODE:
            forall i s1,
              get_layer_primitive i L1 = OK (Some (compatsem_inl s1)) ->
              forall s WB args m res m', 
                sextcall_step s1 s WB args m res m' -> kernel_mode (π_data m)
         )
         (SIM12: compiler_layersim L1 L2)
  ,
    cl_sim _ _ (freerg_inj _ _ _ R) L0 L2.
Proof.
  inversion 1.
  apply cl_sim_layer_pointwise in cl_sim_layer.
  destruct cl_sim_layer as [cl_sim_layer_prim cl_sim_layer_var].
  econstructor.
  * apply cl_sim_layer_pointwise.
    split.
    + intro. eapply res_option_sim_compatsim_compiler_defsim_compose; eauto.
      eapply compiler_layersim_primitives; eauto.
      destruct (get_layer_primitive i L1) as [ [ [ | ] | ] | ] eqn:?; eauto.
      destruct (get_layer_primitive i L1) as [ [ [ | ] | ] | ] eqn:?; eauto.
    + (* variables *)
      intros. etransitivity; eauto using compiler_layersim_globalvars.
  * (* exec_load *)
    inversion SIM12.
    inversion compiler_layersim_load0; subst.
    {
      rewrite <- H in cl_sim_load.
      inversion cl_sim_load; subst.
      solve_monotonic.
      inv H4.
      + constructor.
      + inv H1. constructor. assumption.
    }
    solve_monotonic.
  * (* exec_store *)
    inversion SIM12.
    inversion compiler_layersim_store0; subst.
    {
      rewrite <- H in cl_sim_store.
      inversion cl_sim_store; subst.
      solve_monotonic.
      inv H4.
      + constructor.
      + inv H1. constructor. assumption.
    }
    solve_monotonic.
Qed.

(** We now prove that [compiler_primsim] can "absorb"
[CompatClightSem.primitive_le] on its left. *)

Theorem compiler_defsim_primitive_le_compose {D}:
  forall sem1 sem2,
    res_le (option_le primitive_le) sem1 sem2 ->
    forall sem3,
      compiler_defsim (D := D) sem2 sem3 ->
      compiler_defsim sem1 sem3.
Proof.
  intros σ1 σ2 Hσ12 σ3 Hσ23.
  destruct Hσ12 as [_ _ [σ2 | σ1 σ2 Hσ12] | msg σ1];
  inversion Hσ23 as [σ2' σ3' Hσ23' | σ2']; subst; clear Hσ23;
  try constructor.
  destruct Hσ12 as [σ1 σ2 Hvalid12 Hsig12 Hsem12].
  inversion Hσ23' as [σ2' σ3 Hσ23 Hname23 Hvalid23 Hstep23]; subst.
  econstructor; eauto;
  rewrite <- Hsig12;
  eauto.
Qed.

Theorem compiler_layersim_spec_le_compose {D}:
  forall L1 L2,
    spec_le L1 L2 ->
    forall L3,
      compiler_layersim (D := D) L2 L3 ->
      compiler_layersim L1 L3.
Proof.
  inversion 1.
  intros.
  inversion H0.
  econstructor; eauto using compiler_defsim_primitive_le_compose;
  intros; etransitivity; eauto.
Qed.

End SIMULATION.


(** Missing lemma from Smallstep *)

Lemma star_plus:
  forall {genv state: Type}
         {step: genv -> state -> trace -> state -> Prop}
         ge s t s',
    star step ge s t s' ->
    s <> s' ->
    plus step ge s t s'.
Proof.
  inversion 1; subst.
   destruct 1; reflexivity.
  intros. econstructor; eauto.
Qed.

(** Compiler correctness in terms of layers *)

(** We bundle all operations needed for compiler correctness, and the
specifications whose proofs depend on the implementation of
[MakeProgram]. *)

(* Could make Observation more abstract here, but it's a lot of work. *)
Require ObservationImpl.

Class CompCertiKOSOps: Type :=
  {
    stencil: Type;
    stencil_ops :> StencilOps stencil;
    mem: Type;
    memory_model_ops :> Mem.MemoryModelOps mem;
    mwd_ops :> UseMemWithData mem;

    clight_make_program_ops :> MakeProgramOps Clight.function Ctypes.type Clight.fundef Ctypes.type;
    lasm_make_program_ops :> MakeProgramOps LAsm.function Ctypes.type LAsm.fundef unit;

    mmatch_ops :> ValueDomain.MMatchOps mem;
    magree_ops :> Deadcodeproof.MAgreeOps mem
  }.

Class CompCertiKOS `{compcertikos_ops: CompCertiKOSOps}: Prop :=
  {
    stencil_prf :> Stencil stencil;
    memory_model_x_prf :> Mem.MemoryModelX mem;

    clight_make_program_prf :> MakeProgram Clight.function Ctypes.type Clight.fundef Ctypes.type;
    lasm_make_program_prf :> MakeProgram LAsm.function Ctypes.type LAsm.fundef unit;

    mmatch_constructions_prf :> ValueAnalysis.MMatchConstructions mem;
    magree_prf :> Deadcodeproof.MAgree mem;

    builtin_idents_norepet_prf :> CompCertBuiltins.BuiltinIdentsNorepet
    ;

    (** Additional properties needed by [make_program] *)
    make_program_transf_module_recip:
      forall M1 M2,
        transf_module M1 = OK M2 ->
        forall s D L,
          isOK (make_program (D := D) s M2 L) ->
          isOK (make_program s M1 L)
    ;

    make_program_transf_module:
      forall M1 M2,
        transf_module M1 = OK M2 ->
        forall s D L x,
          make_program (D := D) s M1 L = ret x ->
          exists x_rtl,
            SeparateCompiler.transf_clight_program_to_rtl x = OK x_rtl /\
            exists fenv,
              Inliningspec.fenv_compat (Genv.globalenv x_rtl) fenv /\
              exists x_lasm,
                CompCertiKOS.transf_rtl_program fenv x_rtl = OK x_lasm /\
                make_program s M2 L = ret x_lasm
  }.

Remark res_le_ge:
  forall {F V} (ge: Genv.t F V) oge1,
    res_le (≤) oge1 (ret ge) ->
    exists ge1,  oge1 = ret ge1 /\ ge1 ≤ ge.
Proof.
  inversion 1; subst; eauto.
Qed.

Lemma make_program_l64 `{compcertikos_prf: CompCertiKOS}:
      forall (M: ClightModules.cmodule) s D L x,
        make_program s (D := D) M L = ret x ->
        L64 ≤ L ->
        ClightI64helpers.genv_contains_helpers I64helpers.hf (Genv.globalenv x)
.
Proof.

  Ltac t Heq := 
    let Hle := fresh "Hle" in
    destruct Heq as [ Heq | Hle ] ;
      [ inv Heq; simpl in *; now eauto 7 | ];
      try contradiction;
      t Hle.

  unfold L64.
  Opaque I64helpers.hf.
  intros.
  unfold ClightI64helpers.genv_contains_helpers.
  generalize (make_program_make_globalenv _ _ _ _ H).
  clear H.
  generalize (Genv.globalenv x). clear x.
  intros ge Hge.
  assert (HM: M ≤ M) by reflexivity.
  pose proof (make_globalenv_monotonic s _ _ HM _ _ H0) as Hge1.
  clear H0.
  rewrite Hge in Hge1.
  clear Hge.
  generalize (res_le_ge _ _ Hge1). clear Hge1.
  destruct 1 as (ge1 & Hge1 & Hge1le).
  generalize (make_globalenv_split_module_layer _ _ _ _ Hge1). clear Hge1.
  destruct 1 as (_ & geL & _ & (HgeL & HgeLle')).
  assert (HgeLle: geL ≤ ge) by (etransitivity; eassumption).
  clear M HM ge1 Hge1le HgeLle'.
  inv_make_globalenv_split_layer inv_make_globalenv_leaftac HgeL HgeLle.
  intros until sg. intro Hle.
  t Hle.
Qed. (* Finished transaction in 70. secs (69.914u,0.s) *)

(** XXX: Not sure whether the following bundle is convenient *)

Class LayerCompilable
      `{compcertikos_ops: CompCertiKOSOps}
      {D: compatdata}
      (L: compatlayer D)
: Prop :=
  {
    extcall_invariants_defined_prf :> ExtcallInvariantsDefined L;
    acc_def_prf :> LAsm.AccessorsDefined L;
    layer_ok_prf :> LayerOK L;
    external_calls_x_defined :> ExternalCallsXDefined L
  }.

Global Instance layer_compilable_dec
      `{compcertikos_ops: CompCertiKOSOps}
      {D: compatdata}
      (L: compatlayer D)
: Decision (LayerCompilable L).
Proof.
  destruct (extcall_invariants_defined_dec L).
  * destruct (LAsm.accessors_defined L) eqn:Hacc.
    + destruct (decide (LayerOK L)).
      - destruct (external_calls_x_defined_dec L).
        { left; constructor; auto. constructor; auto. }
        right. intro ABS. inversion ABS; contradiction.
      - right. intro ABS. inversion ABS; contradiction.
    + right. intro ABS. inversion ABS. inversion acc_def_prf0. congruence.
  * right. intro ABS. inversion ABS; contradiction.
Defined.

Section CORRECTNESS.

Context `{layer_compilable_prf: LayerCompilable}.
Context `{compcertikos_prf: !CompCertiKOS}.

(** The following two are needed to use [compat_semantics_spec_some]
and [compat_semantics_spec_none] *)

  Local Existing Instance clight_ptree_sem_ops.
  Local Existing Instance lasm_ptree_sem_ops.

(** First, establish that [M2] is disjoint as well. *)
Lemma compiler_module_layer_disjoint M1 M2:
  CompCertiKOS.transf_module M1 = OK M2 ->
  module_layer_disjoint M1 L ->
  module_layer_disjoint M2 L.
Proof.
  intros HM HM1.
  unfold module_layer_disjoint in *.
  intros i; specialize (HM1 i).
  unfold isOKNone in *.
  pose proof (get_module_function_transf_some M1 M2 HM i) as Hfs.
  pose proof (get_module_function_transf_none M1 M2 HM i) as Hfn.
  pose proof (get_module_function_transf_error M1 M2 HM i) as Hfe.
  pose proof (get_module_variable_transf M1 M2 HM i) as Hv.
  destruct HM1 as [[HMf HMv] | HL].
  * left.
    split; eauto.
    etransitivity; eauto.
  * right.
    assumption.
Qed.

Theorem compiler_correct:
  forall l64_le: L64 ≤ L,
  forall M1: ClightModules.cmodule,
  forall M2: LAsm.module,
  forall M1disj: module_layer_disjoint M1 L,
  forall TRANSF: CompCertiKOS.transf_module M1 = OK M2,
  forall MOK: ModuleOK M1,
    compiler_layersim ( 〚 M1 〛 L )  ( 〚 M2 〛 L ) .
Proof.
  intros.
  assert (M2disj: module_layer_disjoint M2 L). {
    eapply compiler_module_layer_disjoint;
    eassumption.
  }
  constructor.
{ (* primitives *)
  intro.
  destruct (get_module_function i M1) as [ [ f | ] | ] eqn:Hfunc.
  *
    assert (Hfunc2: exists f', get_module_function i M2 = OK (Some f')) by eauto using get_module_function_transf_some.
    destruct Hfunc2 as [f' Hfunc2].
    generalize (compat_semantics_spec_some_disj M1 L i f Hfunc).
    generalize (compat_semantics_spec_some_disj M2 L i f' Hfunc2).
    simpl in * |- *.
    intros CFUN LFUN.
    rewrite CFUN. rewrite LFUN.
    constructor.
    econstructor. 
    + reflexivity.
    + (* valid *) simpl.
      intro.
      destruct (decide (ExtcallInvariantsDefined L)); try discriminate.
      destruct (decide (PrimcallInvariantsDefined L)); try discriminate.
      destruct (decide (LayerNamesMatch D L)); try discriminate.
      destruct (decide (get_layer_prim_valid L s)); try discriminate.
      destruct (accessors_weak_defined L); try discriminate.
      destruct (make_program s M2 L) eqn:?; try discriminate.
      intros _.
      exploit (make_program_transf_module_recip _ _ TRANSF s _ L).
      { esplit; eauto. }
      destruct 1 as (? & MAKE).
      unfold ClightModules.cmodule in * |- *. rewrite MAKE.
      reflexivity.
    + (* signature *)
      simpl.
      exploit get_module_function_transf_some_strong; eauto.
      destruct 1 as (f2' & Hfunc' & ? & TRANS).
      unfold LAsm.module, LAsm.module_ops in Hfunc2.
      replace f2' with f' in * by (simpl in *; congruence).
      erewrite transf_clight_function'_sig_translated; eauto.
      reflexivity.
    + eexists.
      reflexivity.
    + Opaque Conventions1.destroyed_at_call loc_external_result. simpl. 
      intros.
      unfold clight_step in SEM1.
      destruct SEM1 as (sge & b' & Hsge & Hsymb & Hfunct & Hstar).
      generalize Hsymb.
      intro Hsymb'.
      generalize (make_globalenv_stencil_matches _ _ _ _ Hsge).
      intro STENCIL_MATCH.
      erewrite stencil_matches_symbols in Hsymb' by eauto.
      rewrite SYMB in Hsymb'.
      inversion Hsymb'; subst; clear Hsymb'.
      rename b' into b.
      generalize Hsge.
      unfold make_globalenv. intro Hsge'.
      inv_monad Hsge'. subst.
      assert (TRANSF_PROG:
          exists x_rtl,
            SeparateCompiler.transf_clight_program_to_rtl x = OK x_rtl /\
            exists fenv,
              Inliningspec.fenv_compat (Genv.globalenv x_rtl) fenv /\
              exists x_lasm,
                CompCertiKOS.transf_rtl_program fenv x_rtl = OK x_lasm /\
                make_program s M2 L = ret x_lasm
             ) by eauto using make_program_transf_module.
      destruct TRANSF_PROG as (x_rtl & TRANS_X & fenv & FENV_COMPAT & x_lasm & TRANS_RTL & MAKE2).
      
      assert (GE_VALID: SelectLongproofX.genv_valid (GenvValidOps := I64Layer.stencil_matches_genv_valid_ops L) (Genv.globalenv x)).
      {
        esplit.
        split; eauto.
        (** stencil valid for all C primitives of L: comes from VALID hypothesis on semantics of M2 *)
        destruct (decide (ExtcallInvariantsDefined L)); try discriminate.
        destruct (decide (PrimcallInvariantsDefined L)); try discriminate.
        destruct (decide (LayerNamesMatch D L)); try discriminate.
        destruct (decide (get_layer_prim_valid L s)) as [Hvalid | ]; try discriminate.
        destruct (accessors_weak_defined L); try discriminate.
        unfold stencil_valid. intros ? pr Hprim.
        generalize (Hvalid _ _ Hprim).
        unfold compatsem_valid.
        destruct pr; auto.
      }
      assert (CONTAINS_I64H:
          ClightI64helpers.genv_contains_helpers I64helpers.hf (Genv.globalenv x)
             ) by eauto using make_program_l64, l64_le with typeclass_instances.
      assert (STENCIL_MATCH2: stencil_matches s (Genv.globalenv x_lasm)).
      {
        eapply make_globalenv_stencil_matches.
        eapply make_program_make_globalenv.
        eassumption.
      }
      assert (ASM_INV: AsmX.asm_invariant (Genv.globalenv x_lasm) rs m).
      {
        inversion ASM_INVARIANT.
        constructor; auto.
        inversion inv_inject_neutral.
        constructor; auto.
        erewrite stencil_matches_genv_next; eauto.
      }
      assert (INIT_SP_NOT_GLOBAL' : forall (b : block) (o : int),
                                      rs ESP = Vptr b o -> Ple (Genv.genv_next (Genv.globalenv x_lasm)) b) by (erewrite stencil_matches_genv_next; eauto).
      assert (SYMB': Genv.find_symbol (Genv.globalenv x_lasm) i = Some b) by
          (erewrite stencil_matches_symbols; eauto).

      set (km_ops := KMOPS (D := D)).
      set (km := KM L).
      set (cc := compatlayer_compiler_config L _).
      set (liftmem_ops := mwd_liftmem_ops D).
      set (liftmem_prf := mwd_liftmem_prf D).
      set (i64helpers := L64_correct _ l64_le _).

      generalize (transf_clight_program_correct (kernel_mode_prf := km)
      _ _ TRANS_X
        _ FENV_COMPAT
        _ TRANS_RTL
        CONTAINS_I64H
        GE_VALID
        _ _ ASM_INV
        KERNEL_MODE
        _ _ ARGS
        INIT_SP_NOT_GLOBAL'
        _ _
        SYMB'
        PC
        SP_NOT_VUNDEF
        RA_NOT_VUNDEF
                 ).
      intro FORWARD.

      exploit (fsim_match_initial_states FORWARD (Clight.Callstate (Clight.Internal f) (decode_longs (Ctypes.typlist_of_typelist (Ctypes.type_of_params (Clight.fn_params f))) args) Clight.Kstop m)).
      {
        constructor. econstructor.
        eassumption.
        assumption.
        reflexivity.
        reflexivity.
      }
      destruct 1 as
          (j & s2 & INIT2 & MATCH2).
      generalize (simulation_star
                    FORWARD
                    Hstar
                    _ _ MATCH2).
      destruct 1 as (jf & sf & Hstar2 & MATCHF).
      exploit (fsim_match_final_states FORWARD
      _ _ _ (encode_long (Ctypes.opttyp_of_type (Clight.fn_return f)) res, m'_clight)
      MATCHF).
      {
        econstructor; eauto.
        econstructor.
      }
      intro FINAL2.
      inversion INIT2; subst.
      replace b0 with b in * by congruence; clear b0.
      inversion FINAL2; subst.
      inversion Hfinal; subst.

      exists j0. exists rs0. exists m'.
      rewrite H2, H4.
      split; auto.
      esplit; eauto.
      eapply make_program_make_globalenv. eassumption.
      eapply star_plus; eauto.
      congruence.
      split; auto.
      split; auto.      
  
  * (* case none *)
    assert (Hfunc2: get_module_function i M2 = OK None) by eauto using get_module_function_transf_none.
    setoid_rewrite compat_get_semof_primitive.
    setoid_rewrite Hfunc.
    setoid_rewrite Hfunc2.
    constructor.

  * (* case error: MOK excludes this case *)
    exfalso.
    destruct (MOK i) as [MOK_prim _ _].
    rewrite Hfunc in MOK_prim.
    destruct MOK_prim; discriminate.
}
{ (* variables *)
  (** XXX: this is pretty ugly, we'll want to think of a way to make
    it better. The main issue is that for function definitions, the
    [semof_fundef] on each side might go Error (though in practice
    that would happen under the same circumstances, which is why we
    can prove this). To work around this we actually have to examine
    each possible concrete case. *)
  intro.
  Import PTreeModules Maps.
  Local Transparent clight_ptree_sem_ops.
  Local Transparent lasm_ptree_sem_ops.
  Local Transparent compatlayer_ops ptree_layer_ops ptree_module_ops.
  generalize (get_module_variable_transf M1 M2 TRANSF i).
  generalize (get_module_function_transf_some M1 M2 TRANSF i).
  specialize (M2disj i).
  simpl in *.
  unfold ptree_semantics_mapdef, ptree_semantics_def.
  simpl in *.
  unfold ptree_module_variable, ptree_module_function in *.
  unfold ptree_layer_globalvar, ptree_layer_primitive in *.
  simpl in *.
  intros H.
  destruct ((snd M1)!i) as [[|]|] eqn:HM1i;
  destruct ((snd M2)!i) as [[|]|] eqn:HM2i;
    simpl in *; monad_norm; simpl in *;
    inversion 1; subst; reflexivity.
}
{ (* exec_load *)
  reflexivity.
}
{ (* exec_store *)
  reflexivity.
}

Qed.

End CORRECTNESS.
