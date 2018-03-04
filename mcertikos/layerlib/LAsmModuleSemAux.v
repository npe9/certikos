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
(** This file provide the semantics for the [Asm] instructions. Since we introduce paging mechanisms, the semantics of memory load and store are different from [Compcert Asm]*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import AsmX.
Require Import Conventions.
Require Import Machregs.
Require Import AuxLemma.
Require Import CommonTactic.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import CompCertBuiltins.
Require Import LAsm.
Require Import MemoryExtra.
Require Import LAsmModuleSemDef.
Require Import Observation.

(** ** Auxilary lemmas of LAsm modules *)

Section ModuleSemantics_Aux.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

(** Summary of the properties of LAsm per-module semantics *)

Section cl_exec_inL.

  Lemma cl_exec_load_inL: 
    forall D (L: compatlayer D) i (σi: compatsem D),
      cl_exec_load (L ⊕ i ↦ σi) = cl_exec_load L.
  Proof.
    intros; simpl.
    destruct (cl_exec_load L). 
    destruct o; trivial.
    trivial.
  Qed.

  Lemma cl_exec_store_inL: 
    forall D (L: compatlayer D) i (σi: compatsem D),
      cl_exec_store (L ⊕ i ↦ σi) = cl_exec_store L.
  Proof.
    intros; simpl.
    destruct (cl_exec_store L). 
    destruct o; trivial.
    trivial.
  Qed.

End cl_exec_inL.

Section small_step.

  Lemma one_sim_star {D}
        `{ex_op1: ExternalCallsOps (mwd D)}
        `{ex_op2: ExternalCallsOps (memory_model_ops:= memory_model_ops0) (mwd D)}
        L1 L2 ge ge' rs rs' (m m': mwd D) t:
    star (step (ec_ops:= ex_op1) (lcfg_ops:= L1)) 
         ge (State rs m) t (State rs' m') ->
    (forall rs rs' (m m': mwd D) t,
       step (ec_ops:= ex_op1) (lcfg_ops:= L1) 
            ge (State rs m) t (State rs' m') -> 
       step (ec_ops:= ex_op2) (lcfg_ops:= L2)
            ge' (State rs m) t (State rs' m')) ->
    star (step (ec_ops:= ex_op2) (lcfg_ops:= L2))  
         ge' (State rs m) t (State rs' m').
  Proof.
    intros. induction H.
    constructor.
    econstructor; eauto.
    destruct s1, s2; eauto.
  Qed.

  Lemma one_sim_plus {D: compatdata}
        `{ex_op1: ExternalCallsOps (mwd D)}
        `{ex_op2: ExternalCallsOps (memory_model_ops:= memory_model_ops0) (mwd D)}
        L1 L2 ge ge' rs rs' (m m': mwd D) t:
    plus (step (ec_ops:= ex_op1) (lcfg_ops:= L1)) 
         ge (State rs m) t (State rs' m') ->
    (forall rs rs' (m m': mwd D) t,
       step (ec_ops:= ex_op1) (lcfg_ops:= L1) 
            ge (State rs m) t (State rs' m') -> 
       step (ec_ops:= ex_op2) (lcfg_ops:= L2)
            ge' (State rs m) t (State rs' m')) ->
    plus (step (ec_ops:= ex_op2) (lcfg_ops:= L2))  
         ge' (State rs m) t (State rs' m').
  Proof.
    intros. inv H.
    destruct s2.
    apply H0 in H1.
    econstructor; eauto.
    apply (one_sim_star _ _ _ _ _ _ _ _ _ H2 H0). 
  Qed.

  Lemma star_sim_plus {D}
        `{ex_op1: ExternalCallsOps (mwd D)}
        `{ex_op2: ExternalCallsOps (memory_model_ops:= memory_model_ops0) (mwd D)}
        L1 L2 ge ge' rs rs' (m m': mwd D) t:
    star (step (ec_ops:= ex_op1) (lcfg_ops:= L1)) 
         ge (State rs m) t (State rs' m') ->
    (forall rs rs' (m m': mwd D) t,
       step (ec_ops:= ex_op1) (lcfg_ops:= L1) 
            ge (State rs m) t (State rs' m') -> 
       plus (step (ec_ops:= ex_op2) (lcfg_ops:= L2))
            ge' (State rs m) t (State rs' m')) ->
    star (step (ec_ops:= ex_op2) (lcfg_ops:= L2))  
         ge' (State rs m) t (State rs' m').
  Proof.
    intros. induction H.
    intros; constructor.
    destruct s1, s2.
    apply plus_star.
    apply H0 in H.
    eapply plus_star_trans; eauto.
  Qed.

  Lemma plus_sim_plus {D}
        `{ex_op1: ExternalCallsOps (mwd D)}
        `{ex_op2: ExternalCallsOps (memory_model_ops:= memory_model_ops0) (mwd D)}
        L1 L2 ge ge' rs rs' (m m': mwd D) t:
    plus (step (ec_ops:= ex_op1) (lcfg_ops:= L1)) 
         ge (State rs m) t (State rs' m') ->
    (forall rs rs' (m m': mwd D) t,
       step (ec_ops:= ex_op1) (lcfg_ops:= L1) 
            ge (State rs m) t (State rs' m') -> 
       plus (step (ec_ops:= ex_op2) (lcfg_ops:= L2))
            ge' (State rs m) t (State rs' m')) ->
    plus (step (ec_ops:= ex_op2) (lcfg_ops:= L2))  
         ge' (State rs m) t (State rs' m').
  Proof.
    inversion 1. intros.
    destruct s2. apply H6 in H0.
    eapply plus_star_trans; eauto.
    eapply star_sim_plus in H1; eauto.
  Qed.
 
  Lemma star_step_match_plus  {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall (s: stencil) ge ge' (s1 s2: state) t, 
      star (step (lcfg_ops:= LC L1)) 
           ge s1 t s2 ->
      forall rs1 rs1' m1 m1' (d1 d1': D1) rs2 m2 (d2: D2) f,
        s1 = (State rs1 (m1, d1)) ->
        s2 = (State rs1' (m1', d1')) ->
        MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
        high_level_invariant d1 ->
        high_level_invariant d2 ->
        low_level_invariant (Mem.nextblock m2) d2 ->
        asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
        (forall f rs1 rs1' m1 m1' (d1 d1': D1) rs2 m2 (d2: D2) t,
           (step (lcfg_ops:= LC L1)) 
             ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
           MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
           high_level_invariant d1 ->
           high_level_invariant d2 ->
           low_level_invariant (Mem.nextblock m2) d2 ->
           asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
           exists f' rs2' m2' d2',
             plus (step (lcfg_ops:= LC L2)) 
                  ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
             /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'
             /\ high_level_invariant d1'
             /\ high_level_invariant d2'
             /\ low_level_invariant (Mem.nextblock m2') d2'
             /\ asm_invariant (mem:= mwd D2) s rs2' (m2', d2')) ->
        exists f' rs2' m2' d2',
          star (step (lcfg_ops:= LC L2)) 
               ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
          /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    induction 1; intros.
    inv H. inv H7.
    repeat_esplit.
    split; eauto. constructor.
    
    inv H2. destruct s2. destruct m.
    exploit H9; eauto 2.
    intros [?[?[?[?[Hplus [Hmatch [Hhigh[Hhigh'[Hlow' Hasm']]]]]]]]].
    exploit IHstar; eauto.
    intros [?[?[?[?[Hstar Hmatch']]]]].
    repeat_esplit.
    split; eauto. 
    apply plus_star.
    eapply plus_star_trans; eauto.
  Qed.
 
  Lemma plus_step_match_plus  {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} `{acc_def_prf1: !AccessorsDefined L1}
        `{acc_def_prf2: !AccessorsDefined L2}:
    forall (s: stencil) ge ge' f rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 t, 
      MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
      plus (step (lcfg_ops:= LC L1)) 
           ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
      high_level_invariant d1 ->
      high_level_invariant d2 ->
      low_level_invariant (Mem.nextblock m2) d2 ->
      asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
      (forall f rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 t,
         (step (lcfg_ops:= LC L1)) 
           ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
         MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
         high_level_invariant d1 ->
         high_level_invariant d2 ->
         low_level_invariant (Mem.nextblock m2) d2 ->
         asm_invariant (mem:= mwd D2) s rs2 (m2, d2) -> 
         exists f' rs2' m2' d2',
           plus (step (lcfg_ops:= LC L2)) 
                ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
           /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'
           /\ high_level_invariant d1'
           /\ high_level_invariant d2'
           /\ low_level_invariant (Mem.nextblock m2') d2'
           /\ asm_invariant (mem:= mwd D2) s rs2' (m2', d2')) ->
      exists f' rs2' m2' d2',
        plus (step (lcfg_ops:= LC L2)) 
             ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
        /\ MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2'.
  Proof.
    inversion 2. intros.
    destruct s2. destruct m. subst.
    exploit H11; eauto 2.
    intros [?[?[?[?[Hplus [Hmatch [Hhigh[Hhigh'[Hlow' Hasm']]]]]]]]].
    exploit (star_step_match_plus s ge ge'); eauto.
    intros [?[?[?[?[Hstar Hmatch']]]]].
    repeat_esplit.
    split; eauto.
    eapply plus_star_trans; eauto.
  Qed.

End small_step.

Lemma external_call_preserved {D}
      `{ex_op1: ExternalCallsOpsX (mwd D)}:
  forall {F1 V1 F2 V2} WB ef (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2)
         args m0 t vl m'0
         (BUILTIN_ENABLED : match ef with
                              | EF_external _ _ => False
                              | _ => True
                            end),
    (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
    (forall b, block_is_volatile ge2 b = block_is_volatile ge1 b) ->
    forall GENV_NEXT_EQ: Genv.genv_next ge2 = Genv.genv_next ge1,
      external_call' WB ef ge1 args m0 t vl m'0 ->
      external_call' WB ef ge2 args m0 t vl m'0.
Proof.
  intros; destruct ef; inv BUILTIN_ENABLED; 
  inv H1; econstructor; eauto; simpl in *; 
  try (inv H2; econstructor; eauto; fail).
  - (* builtin_functions *)
    inv H2.
    eapply builtin_sem_i64_neg; eauto.
    eapply builtin_sem_i64_add; eauto.
    eapply builtin_sem_i64_sub; eauto.
    eapply builtin_sem_i64_mul; eauto.
  - (* volatile load*)
    inv H2; econstructor; eauto.
    eapply volatile_load_preserved; eauto.
  - (* volatile store*)
    inv H2; econstructor; eauto.
    eapply volatile_store_preserved; eauto.
  - (* volatile global load*)
    inv H2; econstructor; eauto.
    erewrite H; eauto.
    eapply volatile_load_preserved; eauto.
  - (* volatile global store*)
    inv H2; econstructor; eauto.
    erewrite H; eauto.
    eapply volatile_store_preserved; eauto.
  - (* eventval_list *)
    inv H2; econstructor; eauto.
    eapply eventval_list_match_preserved; eauto.
  - (* eventval *)
    inv H2; econstructor; eauto.
     eapply eventval_match_preserved; eauto.
Qed.

  Lemma annot_arg_inject {D1: compatdata} {D2: compatdata}:
    forall d1 d2 rs1 rs2 m1 m2 args vargs f,
      annot_arg (mem:= mwd D1) rs1 (m1, d1) args vargs ->
      (forall r, val_inject f (Pregmap.get r rs1) (Pregmap.get r rs2)) ->
      Mem.inject f m1 m2 ->
      (forall (b1 b2 : block) (delta : Z),
        f b1 = Some (b2, delta) -> delta = 0%Z /\ b1 <= b2) ->
      exists vargs',
        annot_arg (mem:= mwd D2) rs2 (m2, d2) args vargs'
        /\ val_inject f vargs vargs'.
  Proof.
    induction 1; intros.
    exists (rs2 r).
    split; eauto. constructor.
    specialize (H1 ESP).
    unfold Pregmap.get in *.
    rewrite H in H1. inv H1.
    lift_unfold. exploit Mem.load_inject; eauto.
    intros [?[Hld Hval]].
    exists x.
    split; trivial.
    econstructor; eauto. 
    exploit H3; eauto.
    intros [? _]; subst.
    rewrite Int.add_zero.
    rewrite Z.add_0_r in *. trivial.
  Qed.

  Lemma annot_args_inject {D1: compatdata} {D2: compatdata}:
    forall d1 d2 rs1 rs2 m1 m2 args vargs f,
      annot_arguments (mem:= mwd D1) rs1 (m1, d1) args vargs ->
      (forall r, val_inject f (Pregmap.get r rs1) (Pregmap.get r rs2)) ->
      Mem.inject f m1 m2 ->
      (forall (b1 b2 : block) (delta : Z),
        f b1 = Some (b2, delta) -> delta = 0%Z /\ b1 <= b2) ->
      exists vargs',
        annot_arguments (mem:= mwd D2) rs2 (m2, d2) args vargs'
        /\ val_list_inject f vargs vargs'.
  Proof.
    induction 1; intros.
    exists nil. split; eauto. constructor.
    exploit IHlist_forall2; eauto.
    intros [? [Han Hval]].
    exploit (annot_arg_inject d1 d2); eauto.
    intros [?[Han' Hval']].
    refine_split';
    econstructor; eauto.
  Qed.

  Lemma extcall_arg_inject {D1: compatdata} {D2: compatdata}:
    forall d1 d2 rs1 rs2 m1 m2 args vargs f,
      extcall_arg (mem:= mwd D1) rs1 (m1, d1) args vargs ->
      (forall r, val_inject f (Pregmap.get r rs1) (Pregmap.get r rs2)) ->
      Mem.inject f m1 m2 ->
      (forall (b1 b2 : block) (delta : Z),
        f b1 = Some (b2, delta) -> delta = 0%Z /\ b1 <= b2) ->
      exists vargs',
        extcall_arg (mem:= mwd D2) rs2 (m2, d2) args vargs'
        /\ val_inject f vargs vargs'.
  Proof.
    induction 1; intros.
    exists (rs2 (preg_of r)).
    split; eauto. constructor.
    specialize (H1 ESP).
    unfold Pregmap.get in *. 
    Opaque Z.mul.    
    destruct (rs1 ESP); simpl in H0; contra_inv.
    inv H1.
    lift_unfold. exploit Mem.load_inject; eauto.
    intros [?[Hld Hval]].
    exists x.
    split; trivial.
    econstructor; eauto. 
    rewrite <- H6. simpl.
    lift_unfold.
    exploit H3; eauto.
    intros [? _]; subst.
    rewrite Int.add_zero.
    rewrite Z.add_0_r in *. trivial.
  Qed.

  Lemma extcall_args_inject {D1: compatdata} {D2: compatdata}:
    forall d1 d2 rs1 rs2 m1 m2 args vargs f,
      extcall_arguments (mem:= mwd D1) rs1 (m1, d1) args vargs ->
      (forall r, val_inject f (Pregmap.get r rs1) (Pregmap.get r rs2)) ->
      Mem.inject f m1 m2 ->
      (forall (b1 b2 : block) (delta : Z),
        f b1 = Some (b2, delta) -> delta = 0%Z /\ b1 <= b2) ->
      exists vargs',
        extcall_arguments (mem:= mwd D2) rs2 (m2, d2) args vargs'
        /\ val_list_inject f vargs vargs'.
  Proof.
    unfold extcall_arguments. intros until args. generalize (loc_arguments args). clear args.
    induction 1; intros.
    refine_split'; eauto.
    econstructor; eauto.
    exploit IHlist_forall2; eauto.
    intros [? [Han Hval]].
    exploit (extcall_arg_inject d1 d2); eauto.
    intros [?[Han' Hval']].
    refine_split';
    econstructor; eauto.
  Qed.

  Lemma extcall_arg_with_data {D: compatdata}:
    forall d1 rs1 m1 args vargs,
      extcall_arg rs1 m1 args vargs ->
      extcall_arg (mem:= mwd D) rs1 (m1, d1) args vargs.
  Proof.
    induction 1; intros. constructor.
    econstructor; eauto.
  Qed.

  Lemma extcall_args_with_data {D: compatdata}:
    forall d1 rs1 m1 args vargs,
      extcall_arguments rs1 m1 args vargs ->
      extcall_arguments (mem:= mwd D) rs1 (m1, d1) args vargs.
  Proof.
    unfold extcall_arguments. intros until args. 
    induction 1; intros. constructor.
    econstructor; eauto.
    apply extcall_arg_with_data; trivial.
  Qed.

  Lemma extcall_arg_without_data {D: compatdata}:
    forall d1 rs1 m1 args vargs,
      extcall_arg (mem:= mwd D) rs1 (m1, d1) args vargs ->
      extcall_arg rs1 m1 args vargs.
  Proof.
    induction 1; intros. constructor.
    econstructor; eauto.
  Qed.

  Lemma extcall_args_without_data {D: compatdata}:
    forall d1 rs1 m1 args vargs,
      extcall_arguments (mem:= mwd D) rs1 (m1, d1) args vargs ->
      extcall_arguments rs1 m1 args vargs.
  Proof.
    unfold extcall_arguments. intros until args. 
    induction 1; intros. constructor.
    econstructor; eauto.
    eapply extcall_arg_without_data; eauto.
  Qed.

  Lemma ge_external_valid_le:
    forall {F V} (ge ge': Genv.t (AST.fundef F) V)
           (Hge_external': 
              forall b ef, 
                Genv.find_funct_ptr ge' b = Some (External ef) ->
                exists i sg, ef = EF_external i sg),
      ge ≤ ge' ->
      forall b ef, 
        Genv.find_funct_ptr ge b = Some (External ef) ->
        exists i sg, ef = EF_external i sg.
  Proof.
    intros. inv H.
    specialize (genv_le_find_funct_ptr b).
    rewrite H0 in genv_le_find_funct_ptr.
    inv genv_le_find_funct_ptr.
    specialize (Hge_external' b).
    rewrite <- H1 in Hge_external'.
    eauto.
  Qed.

  Lemma ge_external_valid {D} s M L ge':
    make_globalenv (D := D) s M L = ret ge' ->
    forall b ef, 
      Genv.find_funct_ptr ge' b = Some (External ef) ->
      exists i sg, ef = EF_external i sg.
  Proof.
    intros.
    exploit (make_globalenv_find_funct_ptr (D := D)); eauto.
    destruct 1 as (? & ? & [ (? & ? & ?) | (? & ? & MAKE_EXTERNAL) ]);
      try discriminate.
    inv MAKE_EXTERNAL.
    eauto.
  Qed.

  Lemma get_layer_primitive_right_neq {D} `{L: compatlayer D}: 
    forall i j (σi σj: compatsem D),
      i <> j ->
      get_layer_primitive i (L ⊕ j ↦ σj) = OK (Some σi) ->
      get_layer_primitive i L = OK (Some σi).
  Proof.
    intros i j σi σj Hij.
    get_layer_normalize.
    rewrite id_right.
    tauto.
  Qed.

  Lemma get_layer_primitive_right_eq {D} `{L: compatlayer D}: 
    forall i σ σ',
      get_layer_primitive i L = OK None ->
      get_layer_primitive i (L ⊕ i ↦ σ) = OK (Some σ') ->
      σ' ≤ σ.
  Proof.
    intros i σ σ'.
    get_layer_normalize.
    intros HiL Hσ'.
    rewrite HiL in Hσ'.
    rewrite id_left in Hσ'.
    inversion Hσ'; subst.
    reflexivity.
  Qed.

End ModuleSemantics_Aux.
