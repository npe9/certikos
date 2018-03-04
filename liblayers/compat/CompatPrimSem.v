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
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.ia32.Asm.
Require Import compcertx.ia32.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Layers.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compcertx.Observation.
Open Scope positive_scope.


(** * Data-agnostic definitions *)

(** ** Step relations *)

(** NB: In [sextcall_sem], the parameter [WB] can be ignored for weak semantics. *)

Definition sextcall_sem `{st_ops: StencilOps} `{mem_ops: Mem.MemoryModelOps} :=
  forall (s: stencil) (WB: block -> Prop), list val -> mem -> val -> mem -> Prop.

Definition sprimcall_sem `{st_ops: StencilOps} `{mem_ops: Mem.MemoryModelOps} :=
  forall (s: stencil), regset -> mem -> regset -> mem -> Prop.

(** XXX: Coq bug, cannot be inside the section below *)
Inductive null_sextcall_sem `{st_ops: StencilOps} `{mem_ops: Mem.MemoryModelOps}: sextcall_sem := .
Inductive null_sprimcall_sem `{st_ops: StencilOps} `{mem_ops: Mem.MemoryModelOps}: sprimcall_sem := .

Definition null_signature :=
  {| sig_args := nil; sig_res := None; sig_cc := cc_default |}.

Section WITH_MEMORY_MODEL.
  Context `{stencil_ops: StencilOps}.
  Context `{mem_ops: Mem.MemoryModelOps}.

  (** ** Order and union of step relations *)

  (** Thanks to [pointwise_preorder] we don't have to prove
    explicitely that the following are [PreOrder]s. *)

  Definition sextcall_sem_le: relation sextcall_sem :=
    (- ==> - ==> - ==> - ==> - ==> - ==> impl)%signature.

  (*
  Definition sextcall_sem_union (sem1 sem2: sextcall_sem): sextcall_sem :=
    fun s WB vargs m vres m' =>
      sem1 s WB vargs m vres m' \/ sem2 s WB vargs m vres m'.

  Global Instance sextcall_sem_union_monotonic:
    Proper
      (sextcall_sem_le ++> sextcall_sem_le ++> sextcall_sem_le)
      sextcall_sem_union.
  Proof.
    compute; firstorder.
  Qed.

  Global Instance sextcall_sem_union_comm:
    Commutative sextcall_sem_le sextcall_sem_union.
  Proof.
    firstorder.
  Qed.

  Global Instance sextcall_sem_union_assoc:
    Associative sextcall_sem_le sextcall_sem_union.
  Proof.
    firstorder.
  Qed.

  Global Instance sextcall_sem__union_le_left:
    LeftUpperBound sextcall_sem_le sextcall_sem_union.
  Proof.
    firstorder.
  Qed.
  *)

  (** Order and union of [sprimcall_sem] step relations. *)

  Definition sprimcall_sem_le: relation sprimcall_sem :=
    (- ==> - ==> - ==> - ==> - ==> impl)%signature.

  (** ** Semantics of high-level primitives *)

  (** In addition to the step relation, those specify the primitive's
    signature (in term of C types) as well as the requirements on
    the stencil used. *)

  Record sextcall_info :=
    {
      sextcall_step :>
        stencil -> (block -> Prop) -> list val -> mem -> val -> mem -> Prop;
      sextcall_csig: csignature;
      sextcall_valid: stencil -> bool
    }.

  Global Instance: Measure sextcall_step.

  Definition null_sextcall_info :=
    {|
      sextcall_step := null_sextcall_sem;
      sextcall_csig := mkcsig Ctypes.Tnil Ctypes.Tvoid;
      sextcall_valid γ := true
    |}.

  Definition sextcall_args (sem: sextcall_info): Ctypes.typelist :=
    csig_args (sextcall_csig sem).

  Definition sextcall_res (sem: sextcall_info): Ctypes.type :=
    csig_res (sextcall_csig sem).

  Definition sextcall_cc (sem: sextcall_info): AST.calling_convention :=
    csig_cc (sextcall_csig sem).

  Definition sextcall_sig (sem: sextcall_info): signature :=
    csig_sig (sextcall_csig sem).

  (** *** Order *)

  Record sextcall_info_le (sem1 sem2: sextcall_info): Prop :=
    {
      sextcall_info_le_sem s:
        sextcall_valid sem2 s = true ->
        (- ==> - ==> - ==> - ==> - ==> impl) (sem1 s) (sem2 s);
      sextcall_info_le_sig:
        sextcall_csig sem1 = sextcall_csig sem2;
      sextcall_info_le_valid s:
        sextcall_valid sem2 s = true -> sextcall_valid sem1 s = true
    }.

  Global Instance sextcall_info_le_preorder:
    PreOrder sextcall_info_le.
  Proof.
    split.
    * intros sem.
      split; eauto; reflexivity.
    * intros sem1 sem2 sem3 [] [].
      split; eauto; etransitivity; eauto.
  Qed.

  (** ** Semantics of low-level primitives *)

  Record sprimcall_info :=
    {
      sprimcall_step :> stencil -> regset -> mem -> regset -> mem -> Prop;
      (** The following is needed for make_external *)
      sprimcall_sig: AST.signature;
      sprimcall_valid: stencil -> bool
    }.

  Record sprimcall_info_le (sem1 sem2: sprimcall_info): Prop :=
    {
      sprimcall_info_le_step s:
        sprimcall_valid sem2 s = true ->
        (- ==> - ==> - ==> - ==> impl)
          (sprimcall_step sem1 s)
          (sprimcall_step sem2 s);
      sprimcall_info_le_sig:
        sprimcall_sig sem1 =
        sprimcall_sig sem2;
      sprimcall_info_le_valid s:
        sprimcall_valid sem2 s = true ->
        sprimcall_valid sem1 s = true
    }.

  Global Instance sprimcall_info_le_preorder:
    PreOrder sprimcall_info_le.
  Proof.
    split.
    * intros sem.
      split; eauto; reflexivity.
    * intros sem1 sem2 sem3 [] [].
      split; eauto; etransitivity; eauto.
  Qed.

  (** ** Miscellaneous definitions *)

  (** Here we need to redefine the whole thing just because of
    [inv_mem_valid], which hadrly belongs there. Oh well. *)

  Record inject_neutral_invariant (s: stencil) (rs: Asm.regset) (m: mem) :=
    {
      inv_mem_valid:
        genv_next s <= Mem.nextblock m;
      inv_mem_inject_neutral:
        Mem.inject_neutral (Mem.nextblock m) m;
      inv_reg_inject_neutral r:
        val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)
    }.

  Record asm_invariant (s: stencil) (rs: Asm.regset) (m: mem): Prop :=
    {
      inv_inject_neutral : inject_neutral_invariant s rs m;
      inv_reg_wt : wt_regset rs
    }.
End WITH_MEMORY_MODEL.


Section WITH_MEMORY_MODEL_AND_DATA.
Context `{Hstencil: Stencil}.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.
Context `{Hobs: Observation}.


(** * Semantic domains for primitives *)

(** Basically we bundle the semantics of primitives as they have been
  defined above, with sets of optional properties that they may satisfy.
  Different layers need primitives which satisfy different properties,
  depending on how they're used. *)

(** ** C-level primitives *)

(** FIXME: nomenclature? m1 m2 m1' m2' *)
Class ExtcallProperties {D: compatdata} (sem: sextcall_info (mem := mwd D)) :=
  {
    external_call_well_typed s WB vargs m1 vres m2:
      sem s WB vargs m1 vres m2 ->
      Val.has_type vres (typ_of_type (sextcall_res sem));

    external_call_valid_block s WB vargs m1 vres m2 b:
      sem WB s vargs m1 vres m2 ->
      Mem.valid_block m1 b ->
      Mem.valid_block m2 b;

    external_call_max_perm s WB vargs m1 vres m2 b ofs p:
      sem s WB vargs m1 vres m2 ->
      Mem.valid_block m1 b ->
      Mem.perm m2 b ofs Max p ->
      Mem.perm m1 b ofs Max p;

    external_call_readonly s WB vargs m1 vres m2:
      sem s WB vargs m1 vres m2 ->
      Mem.unchanged_on (loc_not_writable m1) m1 m2;

    external_call_mem_extends s WB vargs m1 vres m2 m1' vargs':
      sem s WB vargs m1 vres m2 ->
      Mem.extends m1 m1' ->
      Val.lessdef_list vargs vargs' ->
      exists vres' m2',
        sem s WB vargs' m1' vres' m2' /\
        Val.lessdef vres vres' /\
        Mem.extends m2 m2' /\
        Mem.unchanged_on (loc_out_of_bounds m1) m1' m2';

    external_call_mem_inject s (WB WB': _ -> Prop) vargs m1 vres m2 f m1' vargs':
      meminj_preserves_stencil s f ->
      sem s WB vargs m1 vres m2 ->
      Mem.inject f m1 m1' ->
      val_list_inject f vargs vargs' ->
      forall WRITABLE_INJ: forall b b' o, f b = Some (b', o) -> WB b -> WB' b',
      exists f' vres' m2',
        sem s WB' vargs' m1' vres' m2' /\
        val_inject f' vres vres' /\
        Mem.inject f' m2 m2' /\
        Mem.unchanged_on (loc_unmapped f) m1 m2 /\
        Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' /\
        inject_incr f f' /\
        inject_separated f f' m1 m1';

    external_call_determ s WB vargs m vres1 m1 vres2 m2:
      sem s WB vargs m vres1 m1 ->
      sem s WB vargs m vres2 m2 ->
      vres1 = vres2 /\ m1 = m2; 

    external_call_writable_block_weak s (WB1 WB2: _ -> Prop) vargs m1 vres m2:
      (forall b, WB1 b -> WB2 b) ->
      sem s WB1 vargs m1 vres m2 ->
      sem s WB2 vargs m1 vres m2;

    external_call_not_writable s WB vargs m vres m' b chunk o:
      sem s WB vargs m vres m' ->
      Mem.valid_block m b ->
      ~ WB b ->
      Mem.load chunk m' b o = Mem.load chunk m b o

  }.

Class ExtcallInvariants {D: compatdata} (sem: sextcall_info (mem := mwd D)) :=
  {
    external_call_low_level_invariant s WB vargs m d vres m' d':
      sem s WB vargs (m, d) vres (m', d') ->
      forall VALID_GENV_NEXT: genv_next s <= Mem.nextblock m,
        low_level_invariant (Mem.nextblock m) d ->
        low_level_invariant (Mem.nextblock m') d';

    external_call_high_level_invariant (s: stencil) WB vargs m d vres m' d':
      sem s WB vargs (m, d) vres (m', d') ->
      high_level_invariant d ->
      high_level_invariant d';

    external_call_kernel_mode s WB vargs m d vres m' d':
      sem s WB vargs (m, d) vres (m', d') ->
      kernel_mode d ->
      kernel_mode d';

    external_call_inv_nextblock s WB vargs m d vres m' d':
      sem s WB vargs (m, d) vres (m', d') ->
      Mem.nextblock m <= Mem.nextblock m';

    external_call_inject_neutral s WB vargs m d vres m' d':
      sem s WB vargs (m, d) vres (m', d') ->
      (* XXXX: is [low_level_invariant (Mem.nextblock m) d] necessary here?
         If so, then this property will have to be moved to [ExtcallInvariants] *)
      val_list_inject (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
      Mem.inject_neutral (Mem.nextblock m) m ->
      forall NEXT_LE: Ple (genv_next s) (Mem.nextblock m),
      (val_inject (Mem.flat_inj (Mem.nextblock m')) vres vres /\
       Mem.inject_neutral (Mem.nextblock m') m');

    external_call_inv_well_typed s WB vargs m1 vres m2:
      sem s WB vargs m1 vres m2 ->
      Val.has_type vres (typ_of_type (sextcall_res sem))

  }.

Record sextcall_primsem (D: compatdata) :=
  {
    sextcall_primsem_step :> sextcall_info (mem := mwd D);
    sextcall_props: res (ExtcallProperties sextcall_primsem_step);
    sextcall_invs: res (ExtcallInvariants sextcall_primsem_step)
  }.

Global Instance: forall D, Measure (sextcall_primsem_step D).

Record sextcall_primsem_le {D} (σ1 σ2: sextcall_primsem D): Prop :=
  {
    sextcall_primsem_le_step:
      sextcall_info_le
        (sextcall_primsem_step D σ1)
        (sextcall_primsem_step D σ2);
    sextcall_primsem_le_invs:
      res_le ⊤%signature
        (sextcall_invs D σ1)
        (sextcall_invs D σ2)
  }.

Local Instance RelCompFun_preorder {A B} (R: relation B) (π: A -> B):
  Measure π ->
  PreOrder R ->
  PreOrder (R @@ π)%signature.
Proof.
  intros Hπ HR.
  split; typeclasses eauto.
Qed.

Global Instance sextcall_primsem_le_preorder D:
  PreOrder (sextcall_primsem_le (D:=D)).
Proof.
  split.
  * intros sem.
    split.
    + reflexivity.
    + destruct (sextcall_invs D sem); repeat constructor.
  * intros sem1 sem2 sem3 [Hstep12 Hinvs12] [Hstep23 Hinvs23].
    split.
    + etransitivity; eassumption.
    + destruct Hinvs23; repeat constructor.
      inversion Hinvs12; repeat constructor.
Qed.

(** ** Assembly-level primitives *)

Class PrimcallProperties {D: compatdata} (sem: sprimcall_sem (mem := mwd D)) :=
  {
    primitive_call_determ s r m r1 m1 r2 m2:
      sem s r m r1 m1 ->
      sem s r m r2 m2 ->
      m1 = m2 /\ r1 = r2
  }.

Class PrimcallInvariants {D: compatdata} (sem: sprimcall_sem (mem := mwd D)) :=
  {
    primitive_call_invariant s rs m rs' m':
      sem s rs m rs' m' ->
      (* XXXX: is [low_level_invariant (Mem.nextblock m) (π_data m)] necessary here? *)
      asm_invariant s rs m ->
      asm_invariant s rs' m';

    primitive_call_low_level_invariant s rs m d rs' m' d':
      sem s rs (m, d) rs' (m', d') ->
      asm_invariant s rs m ->
      low_level_invariant (Mem.nextblock m) d ->
      low_level_invariant (Mem.nextblock m') d';

    primitive_call_high_level_invariant s rs m d rs' m' d':
      sem s rs (m, d) rs' (m', d') ->
      high_level_invariant d ->
      high_level_invariant d'
  }.

Record sprimcall_primsem (D: compatdata) :=
  {
    sprimcall_primsem_step :> sprimcall_info (mem := mwd D);
    sprimcall_name: option ident;
    sprimcall_props: res (PrimcallProperties sprimcall_primsem_step);
    sprimcall_invs: res (PrimcallInvariants sprimcall_primsem_step)
  }.

Global Instance: forall D, Measure (sprimcall_primsem_step D).

Record sprimcall_primsem_le {D} (σ1 σ2: sprimcall_primsem D): Prop :=
  {
    sprimcall_primsem_le_step:
      sprimcall_info_le
        (sprimcall_primsem_step D σ1)
        (sprimcall_primsem_step D σ2);
    sprimcall_primsem_le_name:
      option_le eq
        (sprimcall_name D σ1)
        (sprimcall_name D σ2);
    sprimcall_primsem_le_invs:
      res_le ⊤%signature
        (sprimcall_invs D σ1)
        (sprimcall_invs D σ2)
  }.

Global Instance sprimcall_primsem_le_preorder D:
  PreOrder (sprimcall_primsem_le (D:=D)).
Proof.
  split.
  * intros σ.
    split.
    + reflexivity.
    + reflexivity.
    + destruct (sprimcall_invs _ _); repeat constructor.
  * intros σ1 σ2 σ3 [Hstep12 Hname12 Hinvs12] [Hstep23 Hname23 Hinvs23].
    split.
    + etransitivity; eassumption.
    + etransitivity; eassumption.
    + destruct Hinvs23; repeat constructor.
      inversion Hinvs12; repeat constructor.
Qed.

(** ** Combined primitives *)

(** We should define a conversion from C primitive semantics to
  assembly primitive semantics. For now, we want to stick to the way
  existing proofs are done (ie. duplicated), and we just define the
  sum of both kinds. *)

Definition compatsem (D: compatdata) :=
  (sextcall_primsem D + sprimcall_primsem D)%type.

Definition compatsem_sig {D} (σ: compatsem D): signature :=
  match σ with
    | inl σl => sextcall_sig σl
    | inr σr => sprimcall_sig σr
(*      match sprimcall_sig σr with
        | Some s => s
        | _ => null_signature
      end *)
  end.

(** Helps with unification. *)
Definition compatsem_inl {D}: sextcall_primsem D -> compatsem D := inl.
Definition compatsem_inr {D}: sprimcall_primsem D -> compatsem D := inr.

Inductive compatsem_le (D: compatdata): relation (compatsem D) :=
  | compatsem_le_inl:
      Proper (sextcall_primsem_le ++> compatsem_le D) compatsem_inl
  | compatsem_le_inr:
      Proper (sprimcall_primsem_le ++> compatsem_le D) compatsem_inr.

Global Existing Instance compatsem_le_inl.
Global Existing Instance compatsem_le_inr.

Hint Resolve (compatsem_le_inl: forall D σ1 σ2, _ σ1 σ2 -> _) : liblayers.
Hint Resolve (compatsem_le_inr: forall D σ1 σ2, _ σ1 σ2 -> _) : liblayers.

Global Instance compatsem_le_preorder D:
  PreOrder (compatsem_le D).
Proof.
  split.
  * intros [σl | σr]; constructor; reflexivity.
  * intros _ _ σ3 [σl1 σl2 Hl12 | σr1 σr2 Hr12] H23;
    inversion H23 as [σl2x σl3 Hl23 | σr2x σr3 Hr23]; subst; clear H23;
    constructor;
    etransitivity;
    eassumption.
Qed.

(** * Simulation diagrams *)

Class MatchExtcallStates {D1 D2} (R: compatrel D1 D2)
    s f m1 d1 m2 d2:=
  {
    match_inject:
      Mem.inject f m1 m2;
    match_related:
      relate_AbData s f d1 d2;
    match_match:
      match_AbData s d1 m2 f;
    match_inject_flat:
      inject_incr (Mem.flat_inj (genv_next s)) f;
    match_inject_forward:
      forall b1 b2 delta, f b1 = Some (b2, delta) -> delta = 0%Z /\ b1 <= b2;
    match_nextblock_forward:
      Mem.nextblock m1 <= Mem.nextblock m2;
    match_newglob_noperm i b ofs k p:
      In i new_glbl ->
      find_symbol s i = Some b ->
      ~ Mem.perm m1 b ofs k p;
    match_newglob_nextblock i b:
      In i new_glbl ->
      find_symbol s i = Some b ->
      b < Mem.nextblock m1
  }.

Class MatchPrimcallStates {D1 D2} R s f rs1 m1 d1 rs2 m2 d2 :=
  {
    match_extcall_states :>
      @MatchExtcallStates D1 D2 R s f m1 d1 m2 d2;
    match_reg reg:
      val_inject f (Pregmap.get reg rs1) (Pregmap.get reg rs2)
  }.

Record sextcall_sim {D1 D2: compatdata} (R: compatrel D1 D2)
       (sem1: sextcall_primsem D1) (sem2: sextcall_primsem D2): Prop :=
  {
    sextcall_sim_step:
      forall s (WB1 WB2: _ -> Prop) f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2,
      (forall (b1 b2 : block) (o : Z),
         f b1 = Some (b2, o) -> WB1 b1 -> WB2 b2) ->
      forall (STENCIL_VALID: sextcall_valid sem2 s = true),
      forall (LOW_LEVEL_INVARIANT: low_level_invariant (Mem.nextblock m2) d2),
      forall (L_HIGH_LEVEL_INVARIANT: high_level_invariant d2),
      forall (H_HIGH_LEVEL_INVARIANT: high_level_invariant d1),
      sem1 s WB1 vargs1 (m1, d1) vres1 (m1', d1') ->
      val_list_inject f vargs1 vargs2 ->
      MatchExtcallStates R s f m1 d1 m2 d2 ->
      exists f' vres2 m2' d2',
        sem2 s WB2 vargs2 (m2, d2) vres2 (m2', d2') /\
        val_inject f vres1 vres2 /\        MatchExtcallStates R s f' m1' d1' m2' d2' /\
        inject_incr f f';
    sextcall_sim_sig:
      sextcall_csig sem1 = sextcall_csig sem2;
    sextcall_sim_valid s:
      sextcall_valid sem2 s = true -> sextcall_valid sem1 s = true;
    sextcall_sim_invs:
      res_le ⊤%signature (sextcall_invs D1 sem1) (sextcall_invs D2 sem2)
  }.

Record sprimcall_sim {D1 D2: compatdata} (R: compatrel D1 D2)
       (sem1: sprimcall_primsem D1) (sem2: sprimcall_primsem D2): Prop :=
  {
    sprimcall_sim_step:
      forall s f rs1 m1 d1 rs1' m1' d1' rs2 m2 d2,
      forall (STENCIL_VALID: sprimcall_valid sem2 s = true),
      forall (LOW_LEVEL_INVARIANT: low_level_invariant (Mem.nextblock m2) d2),
      forall (L_HIGH_LEVEL_INVARIANT: high_level_invariant d2),
      forall (H_HIGH_LEVEL_INVARIANT: high_level_invariant d1),
      forall (ASM_INV: asm_invariant (mem:= mwd D2) s rs2 (m2, d2)),
        sprimcall_step sem1 s rs1 (m1, d1) rs1' (m1', d1') ->
        MatchPrimcallStates R s f rs1 m1 d1 rs2 m2 d2 ->
        exists f' rs2' m2' d2',
          sprimcall_step sem2 s rs2 (m2, d2) rs2' (m2', d2') /\
          MatchPrimcallStates R s f' rs1' m1' d1' rs2' m2' d2';
    sprimcall_sim_sig:
      sprimcall_sig sem2 = sprimcall_sig sem1;
    sprimcall_sim_valid s:
      sprimcall_valid sem2 s = true -> sprimcall_valid sem1 s = true;
    sprimcall_sim_name:
      option_le eq
        (sprimcall_name D1 sem1)
        (sprimcall_name D2 sem2);
    sprimcall_sim_invs:
      res_le ⊤%signature (sprimcall_invs D1 sem1) (sprimcall_invs D2 sem2)
  }.

Require Import OptionMonad.

Record sextcall_sprimcall_sim {D1 D2} (R: compatrel D1 D2)
       (sem1: sextcall_primsem D1) (sem2: sprimcall_primsem D2): Prop :=
  {
    sextcall_sprimcall_sim_step:
      exists i, sprimcall_name D2 sem2 = Some i /\
                forall s b f WB1 vargs1 vargs2 vres m1 d1 m1' d1' rs2 m2 (d2: D2),
                (** Invariants *)
                forall (STENCIL_VALID: sprimcall_valid sem2 s = true),
                forall (LOW_LEVEL_INVARIANT: low_level_invariant (Mem.nextblock m2) d2),
                forall (L_HIGH_LEVEL_INVARIANT: high_level_invariant d2),
                forall (H_HIGH_LEVEL_INVARIANT: high_level_invariant d1),
                (** Higher-layer semantics *)
                forall (SEM1: sem1 s WB1 (decode_longs (sig_args (sextcall_sig sem1)) vargs1) (m1, d1) vres (m1', d1')),
                (** Match states *)
                forall (MATCH: MatchExtcallStates R s f m1 d1 m2 d2),
                (** Calling convention *)
                forall (SYMB: find_symbol s i = Some b),
                forall (PC: rs2 Asm.PC = Vptr b Integers.Int.zero),
                forall (ARGS_INJ: val_list_inject f vargs1 vargs2),
                forall (EXTCALL_ARG: Asm.extcall_arguments rs2 (m2, d2) (sextcall_sig sem1) vargs2),
                (** Requirements of the compiler (to make "transitivity" possible) *)
                forall (ASM_INV: asm_invariant s rs2 (m2, d2)),
                (*
      forall (KERNEL_MODE: kernel_mode d2),
                 *)
                forall (SP_NOT_VUNDEF: rs2 (Asm.IR Asm.ESP) <> Vundef),
                forall (RA_NOT_VUNDEF: rs2 Asm.RA <> Vundef),
                forall (INIT_SP_NOT_GLOBAL: 
                          forall (b : Values.block) (o : Integers.Int.int),
                            rs2 (Asm.IR Asm.ESP) = Values.Vptr b o ->
                            Ple (genv_next s) b),
                exists f' rs2' m2' d2',
                  sprimcall_step sem2 s rs2 (m2, d2) rs2' (m2', d2') /\
                  MatchExtcallStates R s f' m1' d1' m2' d2' /\
                  inject_incr f f' /\
                  val_list_inject f'
                                  (encode_long (sig_res (sextcall_sig sem1)) vres)
                                  (map rs2' (loc_external_result (sextcall_sig sem1))) /\
                  (forall r,
                     ~ In r Conventions1.destroyed_at_call ->
                     Val.lessdef (rs2 (preg_of r)) (rs2' (preg_of r)))
                  /\ Val.lessdef (rs2 RA) (rs2' Asm.PC)
                  /\ Val.lessdef (rs2 ESP) (rs2' ESP);
    sextcall_sprimcall_sim_sig:
      sprimcall_sig sem2 = sextcall_sig sem1;
    sextcall_sprimcall_sim_valid s:
      sprimcall_valid sem2 s = true ->
      sextcall_valid sem1 s = true;
    sextcall_sprimcall_invs:
      (res_le ⊤%signature)
        (sextcall_invs D1 sem1)
        (sprimcall_invs D2 sem2)
  }.

Inductive compatsim_def {D1 D2: compatdata} (R: compatrel D1 D2):
  compatsem D1 -> compatsem D2 -> Prop :=
    | sextcall_sim_either_sim sem1 sem2:
        sextcall_sim R sem1 sem2 ->
        compatsim_def R (compatsem_inl sem1) (compatsem_inl sem2)
    | sprimcall_sim_either_sim sem1 sem2:
        sprimcall_sim R sem1 sem2 ->
        compatsim_def R (compatsem_inr sem1) (compatsem_inr sem2)
    | sextcall_sprimcall_sim_either_sim sem1 sem2:
        sextcall_sprimcall_sim R sem1 sem2 ->
        compatsim_def R (compatsem_inl sem1) (compatsem_inr sem2).

Definition compatsim {D1 D2}:
  freerg compatrel D1 D2 -> compatsem D1 -> compatsem D2 -> Prop :=
  freerg_rel compatsem_le (@compatsim_def) D1 D2.

Global Instance compat_sim_op: Sim (freerg compatrel) compatsem :=
  freerg_sim_op compatsem_le (@compatsim_def).

Global Instance compat_quiv_sim_prf:
  ReflexiveGraphSim compatdata (freerg compatrel) compatsem.
Proof.
  apply freerg_sim_prf.

  * (* [le] is compatible with [sim] *)
    intros v1 v2 e.
    intros σ1 σ1' H1 σ2 σ2' H2 H.
    unfold flip in *; simpl in *.
    destruct H as [sem1 sem2 Hl | sem1 sem2 Hr | sem sem2 Hlr].

    + (* extcall *)
      inversion H1 as [sem1' sem1x Hsem1 | ]; subst; clear H1.
      inversion H2 as [sem2x sem2' Hsem2 | ]; subst; clear H2.
      constructor.
      destruct sem1 as [sem1 props1 invs1].
      destruct sem2 as [sem2 props2 invs2].
      destruct sem1' as [sem1' props1' invs1'].
      destruct sem2' as [sem2' props2' invs2'].
      destruct Hsem1 as [[Hstep1 Hsig1 Hvalid1] Hinvs1].
      destruct Hsem2 as [[Hstep2 Hsig2 Hvalid2] Hinvs2].
      destruct Hl as [Hl_step Hl_csig Hl_valid Hl_invs]; subst.
      simpl in *.
      constructor; simpl; eauto; try congruence.
      - intros.
        exploit Hl_step; try rel_auto.
        intros [f' [vres2 [m2' [d2' [Hstep2' [Hinj12 Hmatch]]]]]].
        exists f', vres2, m2', d2'; rel_auto.
      - destruct Hinvs1, Hinvs2; repeat constructor.
        inversion Hl_invs.

    + (* primcall *)
      inversion H1 as [ | sem1' sem1x Hsem1]; subst; clear H1.
      inversion H2 as [ | sem2x sem2' Hsem2]; subst; clear H2.
      constructor.
      destruct sem1 as [sem1 name1 props1 invs1].
      destruct sem2 as [sem2 name2 props2 invs2].
      destruct sem1' as [sem1' name1' props1' invs1'].
      destruct sem2' as [sem2' name2' props2' invs2'].
      destruct Hsem1 as [[Hstep1 Hsig1 Hvalid1] Hname1 Hinvs1].
      destruct Hsem2 as [[Hstep2 Hsig2 Hvalid2] Hname2 Hinvs2].
      destruct Hr as [Hr_step Hr_sig Hr_valid Hr_name Hr_invs].
      simpl in *.
      constructor; simpl; eauto; try congruence.
      - intros.
        exploit Hr_step; try rel_auto; clear Hr_step.
        intros [f' [rs2' [m2' [d2' [Hstep2' Hmatch]]]]].
        exists f', rs2', m2', d2'; rel_auto.
      - transitivity name1; try eassumption.
        transitivity name2; try eassumption.
      - destruct Hinvs1, Hinvs2; repeat constructor.
        inversion Hr_invs.

    + (* heterogenous *)
      rename sem into σe2.
      rename sem2 into σp1.
      inversion H1 as [σe1 xσe2 Hσe | ]; subst; clear H1.
      inversion H2 as [ | xσp1 σp2 Hσp]; subst; clear H2.
      constructor.
      destruct σe1 as [sem1 props1 invs1].
      destruct σe2 as [sem2 props2 invs2].
      destruct σp1 as [sem1' name1' props1' invs1'].
      destruct σp2 as [sem2' name2' props2' invs2'].
      destruct Hσe as [[Hstep1 Hsig1 Hvalid1] Hinvs1].
      destruct Hσp as [[Hstep2 Hsig2 Hvalid2] Hname2 Hinvs2].
      destruct Hlr as [Hlr_step Hlr_sig Hlr_valid Hlr_invs].
      simpl in *.
      constructor; simpl; eauto.
      - intros.
        destruct Hlr_step as (i & Hname1' & Hlr_step); exists i.
        split. {
          subst.
          inversion Hname2; subst.
          reflexivity.
        }
        intros.
        edestruct Hlr_step as (f' & rs2' & m2' & d2' & Hstep' & Hmatch' & Hincr & Hargs' & Hret'); eauto.
        {
          eapply Hstep1; eauto.
          rewrite <- Hsig1.
          eassumption.
        }
        {
          unfold sextcall_sig in *.
          rewrite <- Hsig1.
          assumption.
        }
        exists f', rs2', m2', d2'.
        split. {
          apply Hstep2; eauto.
        }
        split;
          trivial.
        split;
          trivial.
        split. {
          unfold sextcall_sig.
          rewrite !Hsig1.
          assumption.
        }
        assumption.
      - unfold sextcall_sig in *.
        congruence.
      - destruct Hinvs2; repeat constructor.
        destruct Hinvs1; repeat constructor.
        inversion Hlr_invs.

  * (* [le] is a preorder *)
    typeclasses eauto.
Qed.

Global Instance compat_primsem_ops: PrimitiveOps compatsem :=
  {
    (*prim_union := compatsem_union*)
  }.

Global Instance compatsem_primsem_prf:
  Primitives compatsem.
Proof.
  split; try typeclasses eauto.
Qed.

(** Convenient shortcut for defining primitives as [p ↦ csem sem]. *)

Definition csem {D: compatdata} (sem: sextcall_sem (mem := mwd D)) targs tres :=
  compatsem_inl
    {|
      sextcall_primsem_step :=
        {|
          sextcall_step := sem;
          sextcall_csig := mkcsig targs tres;
          sextcall_valid s := true
        |};
      sextcall_props := Error (MSG "missing extcall properties"::nil);
      sextcall_invs := Error (MSG "primitive does not preserve invariants"::nil)
    |}.

Definition asmsem {D: compatdata} (name: ident) (sem: sprimcall_sem (mem := mwd D)) :=
  compatsem_inr
    {|
      sprimcall_primsem_step :=
        {|
          sprimcall_step := sem;
          sprimcall_sig := null_signature;
          sprimcall_valid s := true
        |};
      sprimcall_name := Some name;
      sprimcall_props := Error (MSG "missing primcall properties"::nil);
      sprimcall_invs := Error (MSG "primitive does not preserve invariants"::nil)
    |}.

Definition asmsem_withsig {D: compatdata} (name: ident) (sem: sprimcall_sem (mem := mwd D))  sig:=
  compatsem_inr
    {|
      sprimcall_primsem_step :=
        {|
          sprimcall_step := sem;
          sprimcall_sig := sig;
          sprimcall_valid s := true
        |};
      sprimcall_name := Some name;
      sprimcall_props := Error (MSG "missing primcall properties"::nil);
      sprimcall_invs := Error (MSG "primitive does not preserve invariants"::nil)
    |}.

End WITH_MEMORY_MODEL_AND_DATA.
