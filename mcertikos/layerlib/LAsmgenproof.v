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
(* *********************************************************************)
(*                                                                     *)
(*              From CompCertX AsmX to per-function LAsm               *)
(*                                                                     *)
(*          Tahina Ramananandro <tahina.ramananandro@yale.edu>         *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provides the per-function correctness proof of the
    compiler from CompCertX [AsmX] to the [LAsm] instructions. *)

Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import MemWithData.
Require LAsmgen.
Require Import liblayers.compat.CompatData.
Require Import compcertx.driver.CompCertBuiltins.
Require Import Observation.

(** Per-function semantics of [LAsm], following [AsmX]. *)

Module PFLAsm.

Section WITHLAYERCONFOPS.
Context `{lc_ops: LAsm.LayerConfigurationOps}.

Inductive initial_state (lm: Asm.regset) (p: LAsm.program) (i: ident) (sg: signature) (args: list val) (m: mem): Asm.state -> Prop :=
| initial_state'_intro    
    b
    (Hb: Genv.find_symbol (Genv.globalenv p) i = Some b)
    (Hpc: lm Asm.PC = Vptr b Int.zero)
    (Hargs: Asm.extcall_arguments lm m sg args)    
  :
      initial_state lm p i sg args m (Asm.State lm m)
.

Definition final_state := AsmX.final_state.

Definition semantics  (lm: Asm.regset) (p: LAsm.program) (i: ident) (sg: signature) (args: list val) (m: mem) :=
  Smallstep.Semantics (LAsm.step) (initial_state lm p i sg args m) (final_state lm sg) (Genv.globalenv p).

End WITHLAYERCONFOPS.

End PFLAsm.

(** Correctness of [exec_load] and [exec_store] operations in kernel mode. *)

  Class KernelModeOps `{obs_ops: ObservationOps} `{memory_model_ops: Mem.MemoryModelOps} (D: compatdata): Type :=
    {
      kernel_mode: D -> Prop := kernel_mode
    }.

  Class KernelMode
         `{obs_ops: ObservationOps}
         `{memory_model_ops: Mem.MemoryModelOps}
         D
         `{km_ops: !KernelModeOps D}
         `{Hmwd: UseMemWithData mem}
         `{ec_ops_x: !ExternalCallsOpsX (mwd D)}
         `{lc_ops: !LAsm.LayerConfigurationOps (ec_ops := external_calls_ops_x_to_external_calls_ops (mwd D))}
  : Prop :=
    {
      exec_load_exec_loadex:
        forall {F V} (ge: _ F V) chunk m a rs rd m' rs',
        Asm.exec_load ge chunk m a rs rd = Asm.Next rs' m' ->
        kernel_mode (π_data m) ->
        LAsm.exec_load ge chunk m a rs rd = Asm.Next rs' m';

      exec_store_exec_storeex:
        forall {F V} (ge: _ F V) chunk m a rs rd rl m' rs',
        Asm.exec_store ge chunk m a rs rd rl = Asm.Next rs' m' ->
        kernel_mode (π_data m) ->
        LAsm.exec_store ge chunk m a rs rd rl = Asm.Next rs' m';

      external_functions_kernel_mode:
        forall i sg (WB: _ -> Prop) {F V} (ge: _ F V) args m t res m',
          external_functions_sem i sg WB _ _ ge args m t res m' ->
          kernel_mode (π_data m) ->
          kernel_mode (π_data m');

      kernel_mode_ok:
        forall m, LAsm.kern_mode m <-> kernel_mode (π_data m)
    }.

(** Missing lemma from Asm/AsmX *)

Section WITHMEM.
  Context `{memory_model_ops: Mem.MemoryModelOps}.

  Context  {F1 V1} (ge1: _ F1 V1)
           {F2 V2} (ge2: _ F2 V2)
           (genv_symbols_preserved: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i).

  Lemma exec_load_symbols_preserved:
    forall rs m chunk a rd,
      Asm.exec_load ge2 chunk m a rs rd =
      Asm.exec_load ge1 chunk m a rs rd.
  Proof.
    unfold Asm.exec_load. intros.
    erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
  Qed.

  Lemma exec_store_symbols_preserved:
    forall rs m chunk a rd rl,
      Asm.exec_store ge2 chunk m a rs rd rl =
      Asm.exec_store ge1 chunk m a rs rd rl.
  Proof.
    unfold Asm.exec_store. intros.
    erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
  Qed.

End WITHMEM.

Section WITHKERNELMODE.

  Context `{kernel_mode_prf: KernelMode}.

  Lemma builtin_functions_kernel_mode:
    forall i sg (WB: _ -> Prop) {F V} (ge: _ F V) args m t res m',
      builtin_functions_sem i sg WB _ _ ge args m t res m' ->
      kernel_mode (π_data m) ->
      kernel_mode (π_data m').
  Proof.
    inversion 1; subst; simpl; tauto.
  Qed.

  Lemma inline_assembly_kernel_mode:
    forall i (WB: _ -> Prop) {F V} (ge: _ F V) args m t res m',
      inline_assembly_sem i WB ge args m t res m' ->
      kernel_mode (π_data m) ->
      kernel_mode (π_data m').
  Proof.
    inversion 1.
  Qed.

  Variable (prog: Asm.program).
  Let tprog := LAsmgen.transf_program prog.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof.
    intros; unfold ge, tge, tprog, LAsmgen.transf_program. 
    apply Genv.find_symbol_transf.
  Qed.

  Lemma genv_next_preserved:
    Genv.genv_next tge = Genv.genv_next ge.
  Proof.
    apply Genv.genv_next_transf.
  Qed.

  Lemma varinfo_preserved:
    forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
  Proof.
    intros; unfold ge, tge, tprog, LAsmgen.transf_program. 
    apply Genv.find_var_info_transf.
  Qed.

  Lemma functions_translated:
    forall (v: val) (f: Asm.fundef),
      Genv.find_funct ge v = Some f ->
      Genv.find_funct tge v = Some (LAsmgen.transf_fundef f).
  Proof.  
    intros.
    exact (Genv.find_funct_transf LAsmgen.transf_fundef _ _ H).
  Qed.

  Lemma function_ptr_translated:
    forall (b: block) (f: Asm.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (LAsmgen.transf_fundef f).
  Proof.  
    intros. 
    exact (Genv.find_funct_ptr_transf LAsmgen.transf_fundef _ _ H).
  Qed.

  Definition asm_funsig (f: Asm.fundef): signature :=
    match f with
      | Internal fn => Asm.fn_sig fn
      | External ef => ef_sig ef
    end.

  Definition lasm_funsig (f: LAsm.fundef): signature :=
    match f with
      | Internal fn => LAsm.fn_sig fn
      | External ef => ef_sig ef
    end.

  Lemma sig_function_translated:
    forall f,
      lasm_funsig (LAsmgen.transf_fundef f) = asm_funsig f.
  Proof.
    intros. destruct f; reflexivity.
  Qed.

  (** First, we show that [LAsm.exec_instr] has the same semantics as
  [Asm.exec_instr] in kernel mode. *)

  Lemma label_pos_preserved:
    forall c l n,
      Asm.label_pos l n (List.map LAsm.asm_instruction c) =
      Asm.label_pos l n c.
  Proof.
    induction c; simpl.
     reflexivity.
    intros.
    destruct (Asm.is_label l a); congruence.
  Qed.

  Lemma goto_label_preserved:
    forall f l rs (m: mwd D),
      Asm.goto_label (LAsmgen.transf_function f) l rs m = Asm.goto_label f l rs m.
  Proof.
    unfold Asm.goto_label; simpl. unfold LAsmgen.transf_code. intros.
    rewrite label_pos_preserved. reflexivity.
  Qed.

  Lemma exec_instr_exec_instrex
    (f: Asm.function)
      (i: Asm.instruction)
      (rs: Asm.regset)
      (m: mwd D)
      (rs': Asm.regset)
      (m': mwd D)
    (KERNEL_MODE: kernel_mode (π_data m))
    (EXEC_INSTR: Asm.exec_instr (Hfl := Asm.FindLabels_instance_0)
                     (MemAccessors0 := Asm.mem_accessors_default)
                     ge f i rs m = Asm.Next rs' m')
    :
      LAsm.exec_instr tge
                      (LAsmgen.transf_function f)
                      (LAsm.asm_instruction i)
                      rs m = Asm.Next rs' m'.                     
  Proof.
    erewrite <- AsmX.exec_instr_symbols_preserved in EXEC_INSTR.
     2: eapply symbols_preserved.
     2: intros; eapply exec_load_symbols_preserved; apply symbols_preserved.
     2: intros; eapply exec_store_symbols_preserved; apply symbols_preserved.    
    destruct i; simpl; try tauto; eauto using exec_load_exec_loadex, exec_store_exec_storeex; simpl in *; try (rewrite goto_label_preserved; eauto).
    (* switch *)
    destruct (rs (Asm.IR r)); try discriminate.
    destruct (Coqlib.list_nth_z tbl (Int.unsigned i)); try discriminate.
    rewrite goto_label_preserved; eauto.
  Qed.

  Lemma find_instr_preserved l:
    forall n i,
      Asm.find_instr n l = Some i ->
      Asm.find_instr n (List.map LAsm.asm_instruction l) = Some (LAsm.asm_instruction i).
  Proof.
    induction l; simpl; try discriminate; intros.
    destruct (Coqlib.zeq n 0); eauto.
    congruence.
  Qed.

  (** We have to disable externals as builtins in the source [Asm] code. *)

  Let cc_ops : CompilerConfigOps (mwd D) := 
    {|
      cc_enable_external_as_builtin := false
    |}.
  Local Existing Instance cc_ops.

  (** Remember that we are compiling Asm code, so the external
  functions must be compilable. *)
  Context `{ec_prf: !CompilerConfiguration (mwd D)}.

  Lemma step_stepex:
  forall rs (m: mwd D) t s',
    kernel_mode (π_data m) ->
    Asm.step (MemAccessors0 := Asm.mem_accessors_default)
             ge (Asm.State rs m) t s' ->
    LAsm.step tge (Asm.State rs m) t s'.
  Proof.
    inversion 2; subst.
    * (* internal *)
      apply function_ptr_translated in H4.
      apply find_instr_preserved in H5.
      apply exec_instr_exec_instrex in H8; auto.
      econstructor; eauto.
      intro; rewrite kernel_mode_ok; assumption.
    * (* builtin *)
      apply function_ptr_translated in H4.
      apply find_instr_preserved in H5.
      eapply external_call_symbols_preserved' in H6; eauto using symbols_preserved, varinfo_preserved, genv_next_preserved.
      eapply LAsm.exec_step_builtin; eauto.
      rewrite kernel_mode_ok; assumption.
    * (* annot *)
      apply function_ptr_translated in H4.
      apply find_instr_preserved in H5.
      eapply external_call_symbols_preserved' in H9; eauto using symbols_preserved, varinfo_preserved, genv_next_preserved.
      eapply LAsm.exec_step_annot; eauto.
      rewrite kernel_mode_ok; assumption.
    * (* external *)
      apply function_ptr_translated in H4.
      eapply external_call_symbols_preserved' in H6; eauto using symbols_preserved, varinfo_preserved, genv_next_preserved.
      eapply LAsm.exec_step_external; eauto.
      rewrite kernel_mode_ok; assumption.
      rewrite genv_next_preserved; auto.
  Qed.

  (** To make several steps, it is necessary to prove that
  [kernel_mode] is preserved in [Asm]. *)

  (** We first prove that [Asm] internal instructions actually preserve the data. *)

  (** TODO: generalize those proofs *)

  Lemma exec_load_data_preserved:
    forall chunk (m: mwd D) a rs rd m' rs',
      Asm.exec_load ge chunk m a rs rd = Asm.Next rs' m' ->
      π_data m' = π_data m.
  Proof.
    unfold Asm.exec_load. intros.
    destruct (Mem.loadv chunk m (Asm.eval_addrmode ge a rs));
    congruence.
  Qed.
  
  Lemma exec_store_data_preserved:
    forall chunk (m: mwd D) a rs rd rl m' rs',
      Asm.exec_store ge chunk m a rs rd rl = Asm.Next rs' m' ->
      π_data m' = π_data m.
  Proof.
    unfold Asm.exec_store. intros.
    destruct (Mem.storev chunk m (Asm.eval_addrmode ge a rs) (rs rd)) eqn:Heqo; try discriminate.
    destruct (Asm.eval_addrmode ge a rs); try discriminate.
    lift_simpl. destruct Heqo. congruence.
  Qed.

  Lemma goto_label_data_preserved:
    forall (f: Asm.function) l rs (m: mwd D) rs' m',
      Asm.goto_label f l rs m = Asm.Next rs' m' ->
      π_data m' = π_data m.
  Proof.
    unfold Asm.goto_label. intros.
    destruct (Asm.label_pos l 0 (Asm.fn_code f)); try discriminate.
    destruct (rs Asm.PC); congruence.
  Qed.

  Lemma exec_instr_data_preserved
        (f: Asm.function)
        (i: Asm.instruction)
        (rs: Asm.regset)
        (m: mwd D)
        (rs': Asm.regset)
        (m': mwd D)
        (EXEC_INSTR: Asm.exec_instr (Hfl := Asm.FindLabels_instance_0)
                                    (MemAccessors0 := Asm.mem_accessors_default)
                                    ge f i rs m = Asm.Next rs' m')
  :
    π_data m' = π_data m.
  Proof.
    destruct i; try (simpl in *; eauto using exec_load_data_preserved, exec_store_data_preserved, goto_label_data_preserved; congruence; fail).
    * (* unsigned division *)
      simpl in *.
      destruct (Val.divu (rs (Asm.IR Asm.EAX)) (Asm.Pregmap.set (Asm.IR Asm.EDX) Vundef rs (Asm.IR r1))); try discriminate.
      destruct (Val.modu (rs (Asm.IR Asm.EAX))
                   (Asm.Pregmap.set (Asm.IR Asm.EDX) Vundef rs (Asm.IR r1)));
        congruence.
    * (* signed division *)
      simpl in *.
      destruct ( Val.divs (rs (Asm.IR Asm.EAX))
                   (Asm.Pregmap.set (Asm.IR Asm.EDX) Vundef rs (Asm.IR r1))); try discriminate.
      destruct ( Val.mods (rs (Asm.IR Asm.EAX))
                   (Asm.Pregmap.set (Asm.IR Asm.EDX) Vundef rs (Asm.IR r1)));
        congruence.
    * (* if *)
      simpl in *.
      destruct (Asm.eval_testcond c rs); try congruence.
      destruct b; congruence.
    * (* if *)
      simpl in *.
      destruct (Asm.eval_testcond c rs); try discriminate.
      destruct b; try congruence.
      eauto using goto_label_data_preserved.
    * (* if *)
      simpl in *.
      destruct (Asm.eval_testcond c1 rs); try discriminate.
      destruct b; destruct (Asm.eval_testcond c2 rs); try congruence.
      destruct b; try congruence.
      eauto using goto_label_data_preserved.
    * (* switch *)
      simpl in *.
      destruct (rs (Asm.IR r)); try discriminate.
      destruct (Coqlib.list_nth_z tbl (Int.unsigned i)); try discriminate.
      eauto using goto_label_data_preserved.
    * (* Pallocframe *)
      unfold Asm.exec_instr in EXEC_INSTR.
      destruct (Mem.alloc m 0 sz) eqn:Halloc; try discriminate.
      destruct (Mem.storev Mint32 m0 (Val.add (Vptr b Int.zero) (Vint ofs_link)) (rs (Asm.IR Asm.ESP))) eqn:Hstorelink; try discriminate.
      destruct (Mem.storev Mint32 m1
                   (Val.add (Vptr b Int.zero) (Vint ofs_ra)) 
                   (rs Asm.RA)) eqn:Hstorera; try discriminate.
      lift_simpl.
      destruct Halloc. destruct Hstorelink. destruct Hstorera. 
      congruence.
    * (* Pfreeframe *)
      unfold Asm.exec_instr in EXEC_INSTR.
      destruct (Mem.loadv Mint32 m (Val.add (rs (Asm.IR Asm.ESP)) (Vint ofs_ra))); try discriminate.
      destruct (Mem.loadv Mint32 m
                   (Val.add (rs (Asm.IR Asm.ESP)) (Vint ofs_link))); try discriminate.
      destruct (rs (Asm.IR Asm.ESP)); try discriminate.
      destruct (Mem.free m b 0 sz) eqn:Hfree; try discriminate.
      lift_simpl.
      destruct Hfree.
      congruence.
  Qed.

  Lemma external_call_kernel_mode:
    forall ef args (m: mwd D) t vl m',
      external_call' (fun _ : block => True) ef ge args m t vl m' ->
      kernel_mode (π_data m) ->
      kernel_mode (π_data m').
  Proof.
    inversion 1; subst.
    destruct ef; simpl in *;
    try contradiction;
    eauto using builtin_functions_kernel_mode,
    inline_assembly_kernel_mode,
    external_functions_kernel_mode.
    * (* volatile load *)
      inversion H0; congruence.
    * (* volatile store *)
      inversion H0; subst.
      inversion H2; try congruence.
      subst. lift_simpl. destruct H4. congruence.
    * (* volatile load global *)
      inversion H0; congruence.
    * (* volatile store global *)
      inversion H0; subst.
      inversion H3; try congruence.
      subst. lift_simpl. destruct H5. congruence.
    * (* malloc *)
      inversion H0; subst.
      lift_simpl.
      destruct H2. destruct H3.
      congruence.
    * (* free *)
      inversion H0; subst.
      lift_simpl.
      destruct H4.
      congruence.
    * (* memcpy *)
      inversion H0; subst.
      lift_simpl.
      destruct H9.
      congruence.
    * (* annot *)
      inversion H0; congruence.
    * (* annot val *)
      inversion H0; congruence.
  Qed.

  Lemma step_data_kernel_mode:
  forall rs (m: mwd D) t rs' m',
    Asm.step (MemAccessors0 := Asm.mem_accessors_default)
             ge (Asm.State rs m) t (Asm.State rs' m') ->
    kernel_mode (π_data m) ->
    kernel_mode (π_data m').
  Proof.
    inversion 1; subst; eauto using external_call_kernel_mode.
    (* internal *)
    apply exec_instr_data_preserved in H8.
    congruence.
  Qed.

  Theorem transf_program_correct:
    forall lm i sg args m,
      kernel_mode (π_data m) ->
      Smallstep.forward_simulation 
        (AsmX.semantics lm prog i sg args m)
        (PFLAsm.semantics lm tprog i sg args m).
  Proof.
    intros.
    eapply Smallstep.forward_simulation_step with
    (match_states := fun s1 s2 => s1 = s2 /\
                           match s1 with
                             | Asm.State _ m => kernel_mode (π_data m)
                           end).
    * (* symbols preserved *)
      apply symbols_preserved.
    * (* initial_state *)
      inversion 1; subst.
      esplit.
      split.
      + econstructor.
        - rewrite symbols_preserved. eassumption.
        - assumption.
        - assumption.
      + split; congruence.
    * (* final_state *)
      destruct 1; subst; tauto.
    * (* step *)
      simpl. destruct 2; subst.
      destruct s2.
      destruct s1'.
      eauto 6 using step_stepex, step_data_kernel_mode.
  Qed.

End WITHKERNELMODE.
