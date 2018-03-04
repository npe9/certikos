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
Require Import Maps.
Require Import Streams.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.

Require Import compcert.cfrontend.Ctypes.
Require Import Conventions.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.

Require Import CertiKOSAux.

Require Import Behavior.
Require Import AbstractDataType.
Require Import Soundness.
Require Import I64Layer.
Require Import LoadStoreSem2.
Require Import MakeProgram.

Require Import SecurityCommon.
Require Import ObsEq.
Require Import SecurityInv.
Require Import Integrity.
Require Import Confidentiality.
Require Import ConfidentialityRestore.
Require Import SecurityBigstep.
Require Import SecurityExtra.

(* This import gives us the simulation from TSysCall to MBoot.
   It takes a while to execute. *)
Require Import CertiKOSproof.

Section SECURITY.

  Local Open Scope Z_scope.

  (* Basic setup: assume that the mCertiKOS definitions produce a valid module
     "kernel", the module "CTXT" produces a valid user program "user_prog" at the
     TSysCall level, and combining CTXT with kernel produces a valid combined
     program "comb_prog" at the MBoot level. Note that stencil is something needed
     for technical reasons, that can be used to produce a global environment. *)

  Variables (sten : stencil) (CTXT kernel : module) (user_prog comb_prog : program).
  Hypothesis certikos_ok : CertiKOS.certikos = OK kernel.
  Hypothesis make_user_prog : 
    make_program sten CTXT (TSysCall.tsyscall ⊕ L64) = OK user_prog.
  Hypothesis make_comb_prog : 
    make_program sten (CTXT ⊕ kernel) (MBoot.mboot ⊕ L64) = OK comb_prog.

  Section PROCSTARTUSER.

    (* To define the necessary state invariants, we first need to find 
       the memory block where the proc_start_user primitive is implemented. *)

    Notation ge := (Genv.globalenv user_prog).

    Fact make_globalenv_ge : make_globalenv sten CTXT tsyscall_layer = OK ge.
    Proof.
      unfold make_globalenv, bind; simpl; unfold Errors.bind; simpl in *.
      unfold tsyscall_layer; rewrite make_user_prog; reflexivity.
    Qed.

    Fact stencil_matches_ge : stencil_matches sten ge.
    Proof.
      eapply make_globalenv_stencil_matches; eauto.
      eapply make_globalenv_ge.
    Qed.

    Lemma psu_block_ex : exists b, Genv.find_symbol ge proc_start_user = Some b.
    Proof.
      assert (Hge: make_globalenv sten CTXT tsyscall_layer = ret ge) by (apply make_globalenv_ge).
      unfold tsyscall_layer, TSysCall.tsyscall, TSysCall.tsyscall_passthrough in *; inv_make_globalenv Hge.
      exists b0; assumption.
    Qed.

    Lemma psu_block_con : Genv.find_symbol ge proc_start_user <> None.
    Proof.
      destruct psu_block_ex as [b Hb]; rewrite Hb; discriminate.
    Qed.

    Definition b : block.
      destruct (Genv.find_symbol ge proc_start_user) eqn:Hfs.
      apply b.
      contradiction (psu_block_con Hfs).
    Defined.

    Lemma psu_ge : Genv.find_symbol ge proc_start_user = Some b.
    Proof.
      unfold b.
      generalize (fun Hfs0 : Genv.find_symbol ge proc_start_user = None =>
                    False_rect block (psu_block_con Hfs0)); intro f.
      destruct (Genv.find_symbol ge proc_start_user) eqn:Hfs; auto.
      contradiction (psu_block_con Hfs).
    Qed.

    Lemma psu_sten : find_symbol sten proc_start_user = Some b.
    Proof.
      erewrite <- stencil_matches_symbols.
      apply psu_ge.
      apply stencil_matches_ge.
    Qed.

  End PROCSTARTUSER.

  Hint Resolve make_globalenv_ge stencil_matches_ge psu_ge psu_sten.
  Existing Instance MakeProgramImpl.make_program_ops.
  Existing Instance MakeProgramImpl.make_program_prf.

  (* state1 is the type of program state at the MBoot level, while state2 
     is the type at the TSysCall level (which is also the type at the TSysCall-local level) *)
  Notation state1 := (Asm.state (mem:= mwd (cdata (cdata_ops:= MBoot.mboot_data_ops) RData))).
  Notation state2 := (Asm.state (mem:= mwd (cdata (cdata_ops:= PProc.pproc_data_ops) RData))).
  Notation mboot := (MBoot.mboot ⊕ L64).
  Notation tsyscall := (TSysCall.tsyscall ⊕ L64).

  Local Instance : ExternalCallsOps (mwd (cdata RData)) := 
    CompatExternalCalls.compatlayer_extcall_ops mboot.
  Local Instance : LayerConfigurationOps := compatlayer_configuration_ops mboot.

  Local Instance : ExternalCallsOps (mwd (cdata RData)) := 
    CompatExternalCalls.compatlayer_extcall_ops tsyscall.
  Local Instance : LayerConfigurationOps := compatlayer_configuration_ops tsyscall.

  (* Bottom semantics: MBoot machine *)
  Definition sem1 : semantics int state1 := 
    LAsm.semantics (lcfg_ops := LC mboot) comb_prog.

  (* Middle semantics: TSysCall machine *)
  Definition sem2 : semantics int state2 := 
    LAsm.semantics (lcfg_ops := LC tsyscall) user_prog.

  Section BIGSTEPIMPL.

    (* Instantiation of SecBigstepOps and proofs of SecBigstep properties *)

    (* p is the observer principal *)
    Variable p : Z.

    (* A full LAsm state in mCertiKOS consists of the three components registers,
       CompCert memory, and abstract data. In ObsEq.v, we only defined observations
       over abstract data, so we extend the observation function here. Note that,
       by the time we make it up to the TSysCall level, all relevant program state 
       has been abstracted from CompCert memory to the abstract data. This means that
       the CompCert memory portion of state should never affect execution at this level.
       For technical reasons, we actually need to make it observable as it can have 
       minor effects, but we also prove that it can never be written to. *)

    Record ostate : Type := 
      {
        observe_rs: option regset;
        observe_d: my_obs;
        observe_m: mem
      }.

    Definition xobserve (s : state2) : ostate := 
      match s with
        | State rs (m,d) =>
          {|
            observe_rs:= if zeq p (cid d) then Some rs else None;
            observe_d:= my_observe p d;
            observe_m:= m
          |}
      end.

    Notation obs_eq s1 s2 := (xobserve s1 = xobserve s2).

    (* The following definitions and lemmas are parameters to the SecurityBigstep.v framework
       that converts them into a high-level security proof over the TSysCall-local semantics. *)

    Lemma observe_obs_eq : 
      forall s1 s2, obs_eq s1 s2 -> observe_lasm _ p s1 = observe_lasm _ p s2.
    Proof.
      unfold observe; simpl.
      intros [rs1 [m1 d1]] [rs2 [m2 d2]] Hobs_eq; simpl in *; inv Hobs_eq; auto.
    Qed.

    Lemma final_nostep :
      forall s r, final_state sem2 s r -> Nostep sem2 s.
    Proof.
      intros [rs [m d]] r Hfin t s Hstep; inv Hfin; inv Hstep; rewrites.
    Qed.

    Definition active (s : state2) : Prop :=
      match s with State _ (_,d) => p = cid d end.

    Lemma active_obs_eq :
      forall s1 s2, obs_eq s1 s2 -> (active s1 <-> active s2).
    Proof.
      intros [rs1 [m1 d1]] [rs2 [m2 d2]]; simpl.
      intro Hobs_eq; inv Hobs_eq.
      destruct (zeq p (cid d1)), (zeq p (cid d2)); inv H6; intuition.
    Qed.

    Lemma active_dec : forall s, Decidable.decidable (active s).
    Proof.
      intros [rs [m d]]; simpl.
      destruct (zeq p (cid d)); [left; auto | right; auto].
    Qed.

    Definition state_inv (s : state2) : Prop := 
      match s with State _ (_,d) => secure_inv b p d end.

    Lemma initial_state_inv :
      forall s, initial_state sem2 s -> state_inv s.
    Proof.
      simpl; intros [rs [m d]] Hinit; inv Hinit; simpl in *.
      unfold Genv.init_mem in *; simpl in *.
      rewrite (InitMem.alloc_globals_with_data _ _ Memimpl.empty (init_adt:cdata RData)) in H0.
      elim_none; inv H0; apply secure_inv_init.
    Qed.

    Lemma state_inv_preserved :
      forall s s' t, Step sem2 s t s' -> state_inv s -> state_inv s'.
    Proof.
      intros [rs [m d]] [rs' [m' d']] Hstep Hinv.
      simpl in *; eapply secure_inv_preserved; eauto.
    Qed.

    Definition init (s : state2) : Prop := 
      match s with State rs (_,d) => secure_inv' b p rs d end.

    Lemma init_preserved :
      forall s s' t, Step sem2 s t s' -> state_inv s -> init s -> init s'.
    Proof.
      intros [rs1 [m1 d1]] [rs2 [m2 d2]] t; simpl; intros.
      eapply secure_inv'_preserved; eauto.
    Qed.

    (* the next three lemmas apply the major TSysCall lemmas described in 
       Section 5 of the paper *)

    Lemma conf : 
      p > high_id ->
      forall s1 s1' s2 s2' t1 t2,
        init s1 -> state_inv s1 ->
        init s2 -> state_inv s2 ->
        active s1 -> Step sem2 s1 t1 s1' -> Step sem2 s2 t2 s2' ->
        obs_eq s1 s2 -> obs_eq s1' s2'.
    Proof.
      intros p_prop [rs1 [m1 d1]] [rs1' [m1' d1']] [rs2 [m2 d2]] [rs2' [m2' d2']]; simpl.       
      intros ? ? ? ? ? ? ? ? ? Hobs_eq.
      assert (Hobs_eq': my_obs_eq p d1 d2) by
          (apply my_obs_eq_convert; inv Hobs_eq; unfold my_observe; apply f_equal_my_obs; auto).
      destruct (zeq p (cid d1)), (zeq p (cid d2)); auto; inv Hobs_eq; try congruence.
      edestruct confidentiality; [| | | | | | | eapply H4 | eapply H5 | | |]; eauto.
      destruct H6; f_equal; auto.
      destruct H3; destruct (zeq (cid d1) (cid d1')), (zeq (cid d1) (cid d2')); auto; intuition.
      apply my_obs_eq_convert; auto.
    Qed.

    Lemma integ :
      p > high_id ->
      forall s s' t,
        init s -> state_inv s ->
        ~ active s -> ~ active s' -> 
        Step sem2 s t s' -> obs_eq s s'.
    Proof.
      intros p_prop [rs [m d]] [rs' [m' d']]; simpl.
      intros; edestruct integrity; eauto; f_equal; auto.
      destruct (zeq p (cid d)), (zeq p (cid d')); auto; contradiction.
      apply my_obs_eq_convert; auto.
    Qed.

    Lemma conf_restore :
      p > high_id ->
      forall s1 s1' s2 s2' t1 t2,
        init s1 -> state_inv s1 ->
        init s2 -> state_inv s2 ->
        ~ active s1 -> active s1' -> active s2' ->
        Step sem2 s1 t1 s1' -> Step sem2 s2 t2 s2' ->
        obs_eq s1 s2 -> obs_eq s1' s2'.
    Proof.
      intros p_prop [rs1 [m1 d1]] [rs1' [m1' d1']] [rs2 [m2 d2]] [rs2' [m2' d2']]; simpl.        
      intros ? ? ? ? ? ? ? ? ? ? ? Hobs_eq.
      assert (Hobs_eq': my_obs_eq p d1 d2) by
          (apply my_obs_eq_convert; inv Hobs_eq; unfold my_observe; apply f_equal_my_obs; auto).
      inv Hobs_eq.
      edestruct confidentiality_restore; [| | | | | | | eapply H6 | eapply H7 | idtac..]; eauto.
      destruct H8; f_equal; auto.
      destruct (zeq (cid d1') (cid d1')), (zeq (cid d1') (cid d2')); auto; try contradiction; intuition.
      apply my_obs_eq_convert; auto.
    Qed.

    Lemma integ_observe :
      forall s s' t,
        init s -> state_inv s -> 
        active s -> ~ active s' ->
        Step sem2 s t s' -> 
        observe_lasm _ p s = observe_lasm _ p s'.
    Proof.
      intros [rs [m d]] [rs' [m' d']] t Hinit Hinv Hact Hact' Hstep.
      simpl in *; unfold ObservationImpl.observe; f_equal.
      eapply new_cid_no_output; eauto; congruence.
    Qed.

  End BIGSTEPIMPL.

  Instance tsyscall_bigstep_ops : SecBigstepOps :=
    {|
      principal_ok p := p > high_id;
      xobserve := xobserve;
      active := active;
      state_inv := state_inv;
      init := init 
    |}.

  (* This is basically a safety and liveness property. See the discussion
     on the provided artifact evaluation webpage for why we need to assume
     this. In the future, we plan to upgrade mCertiKOS to provide a sandbox
     environment for user processes, and to be preemptive. These changes will
     allow us to completely get rid of this hypothesis. *)
  Hypothesis active_forever :
    forall p, 
      principal_ok p ->
      forall s, 
        init p s -> state_inv p s ->
        exists s' t, Plus sem2 s t s' /\ active p s'.

  Instance tsyscall_bigstep : SecBigstep sem2 (observe_lasm _).
  Proof.
    constructor.
    - intros; apply observe_obs_eq; auto.
    - intros; eapply final_nostep; eauto.
    - intros; apply active_obs_eq; auto.
    - apply active_dec.
    - apply active_forever.
    - intros; apply initial_state_inv; auto.
    - intros; eapply state_inv_preserved; eauto.
    - intros; eapply init_preserved; eauto.
    - apply conf.
    - apply integ.
    - apply conf_restore.
    - intros; eapply integ_observe; eauto.
  Qed.

  Section WITHPRINCIPAL.

    Require Import Observation.
    Require Import Determinism.

    Variable p : Z.
    Hypothesis p_ok : p > high_id.

    Notation observe := (observe_lasm _ p).

    (* Top semantics: TSysCall-local machine (p's local view) *)
    Definition sem3 : semantics int state2 := sec_sem sem2 p.
    
    (* Where can I get an actual instance of this? *)
    Context `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet}.

    Theorem my_simulation : inhabited (simulation sem3 sem1 observe observe).
    Proof.
      eapply compose_simulation_inhabited.
      constructor; eapply secure_sim.
      eapply CertiKOS_correct_simulation; eauto.
    Qed.

    Lemma tsyscall_sec_notrace :
      forall s t s',
        init p s -> Step sem3 s t s' -> t = E0.
    Proof.
      induction 2; destruct s as [rs [m d]], s' as [rs' [m' d']].
      eapply tsyscall_notrace; eauto.
      assert (t = E0) by (eapply tsyscall_notrace; eauto); subst.
      rewrite IHsec_step; auto.
      eapply init_preserved; eauto.
    Qed.

    Lemma state_inv_preserved_star :
      forall s s' t,
        Star sem2 s t s' -> state_inv p s -> state_inv p s'.
    Proof.
      induction 1; auto.
      intros; apply IHstar; eapply state_inv_preserved; eauto.
    Qed.

    Variable wi : world.

    (* The main theorem, which exploits high-level security of TSysCall-local and
       the simulation from TSysCall-local to MBoot, obtaining the low-level security
       property on MBoot. 

       NOTE: There is a minor difference between how we do things here versus how it's
             described in the paper. The SecurityBigstep framework actually produces
             not only the high-level security property on TSysCall-local, but also
             immediately applies Behaviorality of TSysCall to obtain a low-level
             security property of TSysCall-local. This latter property is then transferred
             to one at the MBoot level via the following proof. As hinted at in the proof
             sketch of Theorem 1 in the paper, this strategy is fundamentally equivalent
             to what is described in the paper: what we are really doing is implicitly
             defining a semantics TSysCall-local' that behaves the same as TSysCall-local
             but uses the (behavioral) observation function of MBoot. Notice that the
             lemma observe_obs_eq of the SecurityBigstep framework is precisely the
             indistinguishability-preservation property in the paper, when the 
             observation functions xobserve and observe_lasm are taken to be observation
             functions of different machines. 
     *)

    Theorem end_to_end_security :
      exists sim : simulation sem3 sem1 observe observe,
        forall Si S1 t,
          initial_state sem2 Si -> Star sem2 Si t S1 -> init p S1 ->
          forall S2 s1 s2 i1 i2,
            state_inv p S2 -> init p S2 ->
            xobserve p S1 = xobserve p S2 -> sim i1 S1 s1 -> sim i2 S2 s2 ->
            forall w1 w2,
              state_beh_eq (world_sem int sem1 wi) (world_sem int sem1 wi)
                           (world_observe observe) (world_observe observe) (s1,w1) (s2,w2).
    Proof.
      destruct my_simulation as [sim]; exists sim.
      intros Si S1 t Hinitial Hstar Hinit1 S2 s1 s2 i1 i2 Hinv2 Hinit2 Hobs_eq Hsim1 Hsim2 w1 w2.
      assert (Hinv1: state_inv p S1).
      {
        eapply state_inv_preserved_star; eauto.
        apply initial_state_inv; auto.
      }
      assert (inv_init_preserved: 
                forall s t s',
                  state_inv p s /\ init p s ->
                  Step sem3 s t s' -> state_inv p s' /\ init p s').
      {
        intros S t' S' [Hinv Hinit] Hstep; simpl; split.
        eapply (sec_state_inv_preserved _ p_ok _ _ _ Hstep); auto.
        eapply (sec_init_preserved _ p_ok _ _ _ Hstep); auto.
      }
      assert (inv_init_no_trace:
                forall s t s',
                  state_inv p s /\ init p s -> Step sem3 s t s' -> t = E0).
      {
        intros S t' S' [Hinv Hinit] Hstep; eapply tsyscall_sec_notrace; [|eauto]; auto.
      }
      assert (inv_init_safe:
                forall s, state_inv p s /\ init p s -> safe sem3 s).
      {
        intros S [Hinv Hinit] S' t' Hstar'.
        right; apply sec_safe; auto.
        eapply sec_init_preserved_star; eauto.
        eapply sec_state_inv_preserved_star; eauto.
      }

      eapply state_beh_eq_trans.
      { (* B(S1,wi) = B(s1,wi) *)
        eapply state_beh_eq_sym.
        eapply (sim_beh_eq _ _ _ _ sim) with (init:= fun S => state_inv p S /\ init p S); auto.
        - eapply soundness_determinate; eauto; decision.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply mboot_behavioral.
        - split; [eapply Hinv1 | eapply Hinit1].
        - eauto.
      }
      eapply state_beh_eq_trans.
      { (* B(S1) = B(S1,wi) *)
        eapply state_beh_eq_sym.
        eapply world_state_beh_eq with (init:= fun S => state_inv p S /\ init p S); auto.
        - apply ObservationImpl.devact_observation.
        - apply sec_final_nostep.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply world_safe with (init:= fun S => state_inv p S /\ init p S); auto.
      }
      eapply state_beh_eq_trans.
      { (* B(S1) = B(S2) *)
        eapply obs_eq_beh_eq; eauto.
        apply tsyscall_behavioral.
      }
      eapply state_beh_eq_trans.
      { (* B(S2) = B(S2,wi) *)
        eapply world_state_beh_eq with (init:= fun S => state_inv p S /\ init p S); auto.
        - apply ObservationImpl.devact_observation.
        - apply sec_final_nostep.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply world_safe with (init:= fun S => state_inv p S /\ init p S); auto.
      }
      { (* B(S2,wi) = B(s2,wi) *)
        eapply (sim_beh_eq _ _ _ _ sim) with (init:= fun S => state_inv p S /\ init p S); auto.
        - eapply soundness_determinate; eauto; decision.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply mboot_behavioral.
        - eauto.
      }
    Qed.


    (* Alternative formulation: exploit the fact that TSysCall is determinate to 
       relate behaviors of sem2 to sem1. 

       Pro: this theorem formulation never mentions TSysCall-local, which is a 
            semantics defined only for the purpose of proving security 
       Con: this theorem requires determinism of TSysCall - while it is actually
            deterministic, we may want a future version to be nondeterministic *)

    Theorem end_to_end_security' :
      exists sim : simulation sem2 sem1 observe observe,
        forall Si S1 t,
          initial_state sem2 Si -> Star sem2 Si t S1 -> init p S1 ->
          forall S2 s1 s2 i1 i2,
            state_inv p S2 -> init p S2 ->
            xobserve p S1 = xobserve p S2 -> sim i1 S1 s1 -> sim i2 S2 s2 ->
            forall w1 w2,
              state_beh_eq (world_sem int sem1 wi) (world_sem int sem1 wi)
                           (world_observe observe) (world_observe observe) (s1,w1) (s2,w2).
    Proof.
      edestruct CertiKOS_correct_simulation as [sim]; eauto; exists sim.
      intros Si S1 t Hinitial Hstar Hinit1 S2 s1 s2 i1 i2 Hinv2 Hinit2 Hobs_eq Hsim1 Hsim2 w1 w2.
      assert (Hinv1: state_inv p S1).
      {
        eapply state_inv_preserved_star; eauto.
        apply initial_state_inv; auto.
      }
      assert (inv_init_preserved: 
                forall s t s',
                  state_inv p s /\ init p s ->
                  Step sem3 s t s' -> state_inv p s' /\ init p s').
      {
        intros S t' S' [Hinv Hinit] Hstep; simpl; split.
        eapply (sec_state_inv_preserved _ p_ok _ _ _ Hstep); auto.
        eapply (sec_init_preserved _ p_ok _ _ _ Hstep); auto.
      }

      assert (inv_init_no_trace:
                forall s t s',
                  state_inv p s /\ init p s -> Step sem3 s t s' -> t = E0).
      {
        intros S t' S' [Hinv Hinit] Hstep; eapply tsyscall_sec_notrace; [|eauto]; auto.
      }
      assert (inv_init_safe:
                forall s, state_inv p s /\ init p s -> safe sem3 s).
      {
        intros S [Hinv Hinit] S' t' Hstar'.
        right; apply sec_safe; auto.
        eapply sec_init_preserved_star; eauto.
        eapply sec_state_inv_preserved_star; eauto.
      }
      assert (Hinv1': state_inv p S1).
      {
        eapply state_inv_preserved_star; eauto.
        apply initial_state_inv; auto.
      }
      assert (inv_init_preserved': 
                forall s t s',
                  state_inv p s /\ init p s ->
                  Step sem2 s t s' -> state_inv p s' /\ init p s').
      {
        intros S t' S' [Hinv Hinit] Hstep; simpl; split.
        eapply state_inv_preserved; eauto.
        eapply init_preserved; eauto.
      }
      assert (inv_init_no_trace':
                forall s t s',
                  state_inv p s /\ init p s -> Step sem2 s t s' -> t = E0).
      {
        intros [? [? ?]] t' [? [? ?]] [Hinv Hinit] Hstep; eapply tsyscall_notrace; eauto.
      }
      assert (inv_init_safe':
                forall s, state_inv p s /\ init p s -> safe sem2 s).
      {
        intros S [Hinv Hinit] S' t' Hstar'.
        destruct active_forever with (s:=S') (p:=p) as [S'' [t'' [Hplus ?]]]; auto.
        eapply (init_preserved_star (Hsec:=tsyscall_bigstep_ops)); eauto.
        eapply state_inv_preserved_star; eauto.
        inv Hplus; right; eauto.
      }

      eapply state_beh_eq_trans.
      { (* B2(S1,wi) = B(s1,wi) *)
        eapply state_beh_eq_sym.
        eapply (sim_beh_eq _ _ _ _ sim) with (init:= fun S => state_inv p S /\ init p S); auto.
        - eapply soundness_determinate; eauto; decision.
        - apply tsyscall_behavioral.
        - apply mboot_behavioral.
        - split; [eapply Hinv1 | eapply Hinit1].
        - eauto.
      }
      eapply state_beh_eq_trans.
      { (* B(S1,wi) = B2(S1,wi) *)
        eapply state_beh_eq_sym.
        eapply (sim_beh_eq _ _ _ _ (secure_sim p)) 
          with (init:= fun S => state_inv p S /\ init p S) (i:= tt); auto.
        - eapply soundness_determinate; eauto; decision.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply tsyscall_behavioral.
        - split; [eapply Hinv1 | eapply Hinit1].
        - simpl; auto.
      }
      eapply state_beh_eq_trans.
      { (* B(S1) = B(S1,wi) *)
        eapply state_beh_eq_sym.
        eapply world_state_beh_eq with (init:= fun S => state_inv p S /\ init p S); auto.
        - apply ObservationImpl.devact_observation.
        - apply sec_final_nostep.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply world_safe with (init:= fun S => state_inv p S /\ init p S); auto.
      }
      eapply state_beh_eq_trans.
      { (* B(S1) = B(S2) *)
        eapply obs_eq_beh_eq; eauto.
        apply tsyscall_behavioral.
      }
      eapply state_beh_eq_trans.
      { (* B(S2) = B(S2,wi) *)
        eapply world_state_beh_eq with (init:= fun S => state_inv p S /\ init p S); auto.
        - apply ObservationImpl.devact_observation.
        - apply sec_final_nostep.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply world_safe with (init:= fun S => state_inv p S /\ init p S); auto.
      }
      eapply state_beh_eq_trans.
      { (* B(S2,wi) = B2(S2,wi) *)
        eapply (sim_beh_eq _ _ _ _ (secure_sim p)) 
          with (init:= fun S => state_inv p S /\ init p S) (i:= tt); auto.
        - eapply soundness_determinate; eauto; decision.
        - apply secure_behavioral; auto; apply tsyscall_behavioral.
        - apply tsyscall_behavioral.
        - simpl; auto.
      }
      { (* B2(S2,wi) = B(s2,wi) *)
        eapply (sim_beh_eq _ _ _ _ sim) with (init:= fun S => state_inv p S /\ init p S); auto.
        - eapply soundness_determinate; eauto; decision.
        - apply tsyscall_behavioral.
        - apply mboot_behavioral.
        - eauto.
      }
    Qed.
      
  End WITHPRINCIPAL.

End SECURITY.

(* When we run "Check end_to_end_security" here, Coq gives us the full type of the 
   theorem, including hypotheses:

   end_to_end_security :

     (* basic setup assumptions *)
     forall (sten : stencil) (CTXT kernel : module) (user_prog comb_prog : program),
       CertiKOS.certikos = OK kernel ->
       forall make_user_prog : 
                make_program sten CTXT (TSysCall.tsyscall ⊕ L64) = OK user_prog,
       make_program sten (CTXT ⊕ kernel) (MBoot.mboot ⊕ L64) = OK comb_prog ->

       (* safety/liveness assumption *)
       (forall p : principal,
        principal_ok p ->
        forall s : Asm.state,
        init sten CTXT user_prog make_user_prog p s ->
        state_inv sten CTXT user_prog make_user_prog p s ->
        exists (s' : Asm.state) (t : trace),
          Plus (sem2 user_prog) s t s' /\ active p s') ->

       (* theorem applies to untrusted processes only *)
       forall p : Z, (p > 2)%Z ->

       (* random technical CompCert relic, CompCert doesn't give us an instance for 
          some reason; mCertiKOS never uses CompCert builtin functions, so this is irrelevant *)
       CompCertBuiltins.BuiltinIdentsNorepet ->

       (* fix a particular initial world of external events; note that mCertiKOS never
          uses events, this is only needed for interfacing with CompCert *)
       forall wi : world,

       (* simulation from TSysCall-local (sem3) to MBoot (sem1) *)
       exists
         sim : simulation (sem3 sten CTXT user_prog make_user_prog p)
                 (sem1 comb_prog)
                 (fun s : Asm.state => observe_lasm (cdata RData) p s)
                 (fun s : Asm.state => observe_lasm (cdata RData) p s),

         (* pick any high-level initialized state S1 obtained from multiple steps from the
            TSysCall initial state *)
         forall (Si S1 : Asm.state) (t : trace),
         initial_state (sem2 user_prog) Si ->
         Star (sem2 user_prog) Si t S1 ->
         init sten CTXT user_prog make_user_prog p S1 ->

         (* pick any observably equivalent state S2 for which the state invariant also holds, 
            and pick low-level states s1 and s2 related to S1 and S2 by the simulation *)
         forall (S2 s1 s2 : Asm.state)
           (i1 i2 : sim_index (sem3 sten CTXT user_prog make_user_prog p) (sem1 comb_prog)
                       (fun s : Asm.state => observe_lasm (cdata RData) p s)
                       (fun s : Asm.state => observe_lasm (cdata RData) p s) sim),
         state_inv sten CTXT user_prog make_user_prog p S2 ->
         init sten CTXT user_prog make_user_prog p S2 ->
         xobserve p S1 = xobserve p S2 ->
         sim i1 S1 s1 ->
         sim i2 S2 s2 ->

         (* pick any specific worlds for s1 and s2; since mCertiKOS ignores external
            events, this choice of worlds is completely irrelevant *)
         forall w1 w2 : world,

         (* conclusion: the whole-execution behaviors of the MBoot machine semantics (sem1)                       determinized by initial world wi on states s1 and s2 are equal *)
         state_beh_eq (world_sem int (sem1 comb_prog) wi)
                      (world_sem int (sem1 comb_prog) wi)
                      (fun s : state (world_sem int (sem1 comb_prog) wi) =>
                          world_observe (observe_lasm (cdata RData) p) s)
                      (fun s : state (world_sem int (sem1 comb_prog) wi) =>
                          world_observe (observe_lasm (cdata RData) p) s) 
                      (s1, w1) (s2, w2) 
*)

(* When we run "Print Assumptions end_to_end_security" here, Coq lists all assumptions
   being made by the theorem, which come from axioms in other files being imported.
   Pretty much all of these axioms are inherited from CompCert, and a lot of them relate
   to arithmetic over reals, which we purposely avoid reasoning about in mCertiKOS.
   Some of the more interesting ones are non-constructive logic axioms such as 
   functional extensionality, constructive indefinite description, excluded middle,
   and proof irrelevance; we do occasionally make use of these axioms in mCertiKOS,
   but only when they are truly needed.

   JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y
   Rdefinitions.R : Set
   Rdefinitions.R0 : Rdefinitions.R
   Rdefinitions.R1 : Rdefinitions.R
   Raxioms.R1_neq_R0 : Rdefinitions.R1 <> Rdefinitions.R0
   Rdefinitions.Rinv : Rdefinitions.R -> Rdefinitions.R
   Raxioms.Rinv_l : forall r : Rdefinitions.R,
                 r <> Rdefinitions.R0 ->
                 Rdefinitions.Rmult (Rdefinitions.Rinv r) r = Rdefinitions.R1
   Rdefinitions.Rlt : Rdefinitions.R -> Rdefinitions.R -> Prop
   Raxioms.Rlt_asym : forall r1 r2 : Rdefinitions.R,
                      Rdefinitions.Rlt r1 r2 -> ~ Rdefinitions.Rlt r2 r1
   Raxioms.Rlt_trans : forall r1 r2 r3 : Rdefinitions.R,
                       Rdefinitions.Rlt r1 r2 ->
                       Rdefinitions.Rlt r2 r3 -> Rdefinitions.Rlt r1 r3
   Rdefinitions.Rmult : Rdefinitions.R -> Rdefinitions.R -> Rdefinitions.R
   Raxioms.Rmult_1_l : forall r : Rdefinitions.R, Rdefinitions.Rmult 1 r = r
   Raxioms.Rmult_assoc : forall r1 r2 r3 : Rdefinitions.R,
                         Rdefinitions.Rmult (Rdefinitions.Rmult r1 r2) r3 =
                         Rdefinitions.Rmult r1 (Rdefinitions.Rmult r2 r3)
   Raxioms.Rmult_comm : forall r1 r2 : Rdefinitions.R,
                     Rdefinitions.Rmult r1 r2 = Rdefinitions.Rmult r2 r1
   Raxioms.Rmult_lt_compat_l : forall r r1 r2 : Rdefinitions.R,
                               Rdefinitions.Rlt 0 r ->
                               Rdefinitions.Rlt r1 r2 ->
                               Rdefinitions.Rlt (Rdefinitions.Rmult r r1)
                              (Rdefinitions.Rmult r r2)
   Raxioms.Rmult_plus_distr_l : forall r1 r2 r3 : Rdefinitions.R,
                                Rdefinitions.Rmult r1 (Rdefinitions.Rplus r2 r3) =
                                Rdefinitions.Rplus (Rdefinitions.Rmult r1 r2)
                               (Rdefinitions.Rmult r1 r3)
   Rdefinitions.Ropp : Rdefinitions.R -> Rdefinitions.R
   Rdefinitions.Rplus : Rdefinitions.R -> Rdefinitions.R -> Rdefinitions.R
   Raxioms.Rplus_0_l : forall r : Rdefinitions.R, Rdefinitions.Rplus 0 r = r
   Raxioms.Rplus_assoc : forall r1 r2 r3 : Rdefinitions.R,
                         Rdefinitions.Rplus (Rdefinitions.Rplus r1 r2) r3 =
                         Rdefinitions.Rplus r1 (Rdefinitions.Rplus r2 r3)
   Raxioms.Rplus_comm : forall r1 r2 : Rdefinitions.R,
                        Rdefinitions.Rplus r1 r2 = Rdefinitions.Rplus r2 r1
   Raxioms.Rplus_lt_compat_l : forall r r1 r2 : Rdefinitions.R,
                               Rdefinitions.Rlt r1 r2 ->
                               Rdefinitions.Rlt (Rdefinitions.Rplus r r1)
                              (Rdefinitions.Rplus r r2)
   Raxioms.Rplus_opp_r : forall r : Rdefinitions.R,
                         Rdefinitions.Rplus r (Rdefinitions.Ropp r) =
                         Rdefinitions.R0
   Raxioms.archimed : forall r : Rdefinitions.R,
                      Rdefinitions.Rgt (Raxioms.IZR (Rdefinitions.up r)) r /\
                      Rdefinitions.Rle
                     (Rdefinitions.Rminus (Raxioms.IZR (Rdefinitions.up r)) r) 1
   Classical_Prop.classic : forall P : Prop, P \/ ~ P
   RTLgen.compile_switch : nat -> Switch.table -> Switch.comptree
   Raxioms.completeness : forall E : Rdefinitions.R -> Prop,
                          Raxioms.bound E ->
                          (exists x : Rdefinitions.R, E x) ->
                          {m : Rdefinitions.R | Raxioms.is_lub E m}
   ClassicalEpsilon.constructive_indefinite_description : 
      forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
   Compopts.eliminate_tailcalls : unit -> bool
   Linearize.enumerate_aux : LTL.function -> PMap.t bool -> list LTL.node
   Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) 
                                (Q : U -> Type) (x : Q p) 
                                (h : p = p), x = eq_rect p Q x p h
   FunctionalExtensionality.functional_extensionality_dep : 
      forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
      (forall x : A, f x = g x) -> f = g
   Compopts.generate_float_constants : unit -> bool
   ident_of_string : String.string -> ident
   RTLgen.more_likely : CminorSel.condexpr ->
                        CminorSel.stmt -> CminorSel.stmt -> bool
   Compopts.optim_for_size : unit -> bool
   Axioms.proof_irr : ClassicalFacts.proof_irrelevance
   ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
   Compopts.propagate_float_constants : unit -> bool
   Allocation.regalloc : SelectLong.I64helpers ->
                         RTL.function -> res LTL.function
   Inlining.should_inline : ident -> RTL.function -> bool
   SelectOp.symbol_is_external : ident -> bool
   Raxioms.total_order_T : forall r1 r2 : Rdefinitions.R,
                           {Rdefinitions.Rlt r1 r2} + {r1 = r2} +
                           {Rdefinitions.Rgt r1 r2}
   Rdefinitions.up : Rdefinitions.R -> Z
   Compopts.va_strict : unit -> bool
*)