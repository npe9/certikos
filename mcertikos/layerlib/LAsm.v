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
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
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
Require Import Asm.
Require Import Conventions.
Require Import Machregs.
Require Import AuxLemma.
Require Import Observation.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import Decision.


(** * Syntax *)

(** We construct it by extending the syntax of [Asm] with new instructions. *)

Inductive instruction :=
  | asm_instruction (i: Asm.instruction)
  | Pmov_rm_RA (a: addrmode)
  | Pmov_ra_RA (id: ident)
  | Ppopl_RA (rd: ireg)
  | Ppushl_RA (rd: ireg)
  | PELFLOAD
  | Pmov_rm_nop (rd: ireg) (a: addrmode)
  | Pmov_rm_nop_RA (a: addrmode)
  | Ptss_switch


      (*vmx_load_guest
             /* save the address of vmx on the stack */
             "pushl %%ecx;"         /* placeholder */
             "pushl %%ecx;"         /* address of vmx */
             "movl %1, %%edi;"
             "vmwrite %%esp, %%edi;"
             /* save entry TSC */
             "pushl %%ecx;"
             "rdtscp;"
             "popl %%ecx;"
             "movl %%eax, %c[enter_tsc_lo](%0);"
             "movl %%edx, %c[enter_tsc_hi](%0);"
             */

             /* load guest registers */
             "movl %c[g_cr2](%0), %%edi;"   /* guest %cr2 */
             "movl %%edi, %%cr2;"
             "movl %c[g_dr0](%0), %%edi;"   /* guest %dr0 */
             "movl %%edi, %%dr0;"
             "movl %c[g_dr1](%0), %%edi;"   /* guest %dr1 */
             "movl %%edi, %%dr1;"
             "movl %c[g_dr2](%0), %%edi;"   /* guest %dr2 */
             "movl %%edi, %%dr2;"
             "movl %c[g_dr3](%0), %%edi;"   /* guest %dr3 */
             "movl %%edi, %%dr3;"
             "movl %c[g_dr6](%0), %%edi;"   /* guest %dr6 */*)
  | Pvmx_load_guest

  (* vmx_store_guest
             "movl %%cr2, %%edi;"       /* guest %cr2 */
             "movl %%edi, %c[g_cr2](%0);"
             "movl %%dr0, %%edi;"       /* guest %dr0 */
             "movl %%edi, %c[g_dr0](%0);"
             "movl %%dr1, %%edi;"       /* guest %dr1 */
             "movl %%edi, %c[g_dr1](%0);"
             "movl %%dr2, %%edi;"       /* guest %dr2 */
             "movl %%edi, %c[g_dr1](%0);"
             "movl %%dr3, %%edi;"       /* guest %dr3 */
             "movl %%edi, %c[g_dr3](%0);"
             "movl %%dr6, %%edi;"       /* guest %dr6 */
             "movl %%edi, %c[g_dr6](%0);"
/* should be removed

             /* save exit TSC */
             "pushl %%ecx;"
             "rdtscp;"
             "popl %%ecx;"
             "movl %%eax, %c[exit_tsc_lo](%0);"
             "movl %%edx, %c[exit_tsc_hi](%0);"*)

  | Pvmx_store_guest

  | Prdmsr (* print rdmsr *)
  | Pwrmsr (* print wrmsr *)
  | Prcr0 (rd: ireg) (* print movl %%cr0, %%eax *)
  | Prcr3 (rd: ireg) (* print movl %%cr3, %%eax *)
  | Prcr4 (rd: ireg) (* print movl %%cr4, %%eax *)
  | Pvmptrld (id: ident) (*print vmptrld*)

(*
static gcc_inline uint32_t
vmread(uint32_t encoding)
{
	uint32_t val;
	__asm __volatile("vmread %1, %0" : "=r" (val) : "r" (encoding) : "cc");
	return val;
}*)

  | Pvmread (id: ident) (rd rs: ireg) (* print vmread rd rs*)

(*
static gcc_inline void
vmwrite(uint32_t encoding, uint32_t val)
{
	uint8_t error;
	__asm __volatile("vmwrite %1, %2; setna %0"
			 : "=q" (error)
			 : "r" (val), "r" (encoding)
			 : "cc");
	if (unlikely(error))
		KERN_PANIC("vmwrite 0x%08x 0x%08x error %d\n",
			   val, encoding, error);
}*)
  | Pvmwrite (id: ident) (rd rs: ireg) (* print vmwrite rd rs*)


(*

/*
 * Invalidate the EPT TLB.
 */
void
ept_invalidate_mappings(uint64_t pml4ept)
{
	invept(INVEPT_TYPE_SINGLE_CONTEXT, EPTP(pml4ept));
}
 *)
  | Pinvept (rd: ireg) (a: addrmode) (* 	__asm __volatile("invept %0, %1" :: "m" (desc), "r" (type) *)
.


Coercion asm_instruction : Asm.instruction >-> instruction.

Definition code := list instruction.

Record function : Type :=
  mkfunction {
    fn_sig : signature;
    fn_code : code
  }.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
Definition genv := Genv.t fundef unit.

Definition is_label (l: label) (i: instruction): bool :=
  match i with
    | asm_instruction i => Asm.is_label l i
    | _ => false
  end.

Global Instance: FindLabels is_label fn_code.

(** ** Low-level assembly modules *)

Definition module := ptree_module function (globvar Ctypes.type).

Global Instance module_ops:
  ModuleOps ident function (globvar Ctypes.type) module :=
    ptree_module_ops.

Global Instance module_prf:
  Modules ident function (globvar Ctypes.type) module :=
    ptree_module_prf.

(** Here we will instantiate [MakeFundefVarinfoOps] appropriately from
  [liblayers.compcertx.PTreeStencil], so that we can build assembly
  programs from [LAsm.module]s and [compatlayer]s. *)


(** * Semantics *)

(** In addition to Compcert's [ExternalCalls], the semantics of our
  extended assembly language can perform so-called "primitive calls"
  to low-level external functions, which are able to manipulate the
  register state directly (rather that only as reflected by the C
  calling convention.)

  To this end, we define the interfaces below by analogy with
  Compcert's external functions. However unlike C external functions,
  we do not need them to be language-independent or have many of the
  properties which Compcert requires for compilation purposes. *)

Definition primcall_sem `{Mem.MemoryModelOps}: Type :=
  genv -> regset -> mem -> trace -> regset -> mem -> Prop.

(** We also have varying implementations of memory accesses, which are
  given as [exec_load] and [exec_store] in the [LayerConfigurationOps]
  class below. *)

Class LayerConfigurationOps
    `{ec_ops: ExternalCallsOps} :=
  {
    primitive_call:
      external_function -> primcall_sem;
    exec_load {F V} (ge: Genv.t F V):
      memory_chunk -> mem -> addrmode -> regset -> preg -> outcome;
    exec_store {F V} (ge: Genv.t F V):
      memory_chunk -> mem -> addrmode -> regset -> preg -> list preg -> outcome;
    exec_loadex (ge: genv) :=
      exec_load ge;
    exec_storeex (ge: genv) :=
      exec_store ge;
    kern_mode:
      mem -> Prop
  }.

Section LSemantics.
  Context `{lcfg_ops: LayerConfigurationOps}.
  Instance: MemAccessors (@exec_load _ _ _ _) (@exec_store _ _ _ _).

  (** This is the semantics of individual instructions. We extend
    [Asm.exec_instr] following our use of [Asm.instruction]. *)

  Definition privileged (i: instruction) :=
    match i with
      | asm_instruction i =>
        match i with
          (*
          These instructions will eventually need to be included 
          for safety of user programs.
          | Pdiv _ => true
          | Pidiv _ => true
          | Pjmp_l _ => true
          | Pjcc _ _ => true
          | Pjcc2 _ _ _ => true
          | Pjmptbl _ _ => true*)
          | Pallocframe _ _ _ => true
          | Pfreeframe _ _ _ => true
          (*
          | Pbuiltin _ _ _ => true
          | Pannot _ _ => true*)
          | _ => false
        end
      | _ => false
    end.

  Definition exec_instr ge (f: function) (i: instruction) rs m : outcome :=
    match i with
      | asm_instruction i => Asm.exec_instr ge f i rs m
      | Pmov_rm_RA a =>
        exec_loadex ge Mint32 m a rs RA
    (*| Pmov_mr_RA a =>
        exec_storeex Mint32 m a rs RA*)
      | Pmov_ra_RA id =>
        Next (nextinstr_nf (rs#RA <- (symbol_offset ge id Int.zero))) m
      | Ppopl_RA rd => Next (nextinstr (rs#rd <- (rs RA))) m
      | Ppushl_RA rd => Next (nextinstr (rs#RA <- (rs rd))) m
      | PELFLOAD => Next ((undef_regs (RA :: nil) rs) # PC <- (rs#RA)) m
      | Pmov_rm_nop rd a => exec_loadex ge Mint32 m a rs rd
      | Pmov_rm_nop_RA a => exec_loadex ge Mint32 m a rs RA
      | Ptss_switch => Next (nextinstr rs) m
      | Pvmx_load_guest => Next (nextinstr rs) m
      | Pvmx_store_guest => Next (nextinstr rs) m
      | Prdmsr => Next (nextinstr (rs#EAX <- Vzero #EDX <- Vzero)) m
      | Pwrmsr => Next (nextinstr rs) m
      | Prcr0 rd => Next (nextinstr (rs#rd <- Vzero)) m
      | Prcr3 rd => Next (nextinstr (rs#rd <- Vzero)) m
      | Prcr4 rd => Next (nextinstr (rs#rd <- Vzero)) m
      | Pvmptrld id => Next (nextinstr rs) m
      | Pvmread id rd rd' =>
        exec_loadex ge Mint32 m (Addrmode None (Some (rd', Int.repr 4)) (inr (id, Int.repr 8))) rs rd
      | Pvmwrite id rd rd' =>
        exec_storeex ge Mint32 m (Addrmode None (Some (rd', Int.repr 4)) (inr (id, Int.repr 8))) rs rd nil
      | Pinvept rd a => Next (nextinstr rs) m        
    end.

  (** TODO: for now this is copy-and-pasted from [Asm.v] but I suspect
    many things needed for compilation can be removed. -- Jeremie *)

  Inductive step (ge: genv): state -> trace -> state -> Prop :=
    | exec_step_internal:
        forall b ofs f i rs m rs' m' 
               (INSTR_ALLOWED: privileged i = true -> kern_mode m),
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Int.unsigned ofs) f.(fn_code) = Some i ->
        exec_instr ge f i rs m = Next rs' m' ->
        step ge (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m t vl rs' m' (EXT_ALLOWED: kern_mode m),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (asm_instruction (Pbuiltin ef args res)) ->
      external_call' (fun _ => True) ef ge (map rs args) m t vl m' ->
      rs' = nextinstr_nf 
             (set_regs res vl
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
(** [CertiKOS:test-compcert-disable-extcall-as-builtin] We need
to disallow the use of external function calls (EF_external) as
builtins. *)
      forall BUILTIN_ENABLED: match ef with
                                | EF_external _ _ => False
                                | _ => True
                              end,
(** [CompCertX:test-compcert-wt-builtin] We need to prove that registers updated by builtins are
    of the same type as the return type of the builtin. *)
      forall BUILTIN_WT: 
               subtype_list (proj_sig_res' (ef_sig ef)) (map typ_of_preg res) = true,
      step ge (State rs m) t (State rs' m')
  | exec_step_annot:
      forall b ofs f ef args rs m vargs t v m' (EXT_ALLOWED: kern_mode m),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (asm_instruction (Pannot ef args)) ->
      annot_arguments rs m args vargs ->
      external_call' (fun _ => True) ef ge vargs m t v m' ->
      forall BUILTIN_ENABLED: match ef with
                                | EF_external _ _ => False
                                | _ => True
                              end,
      step ge (State rs m) t
           (State (nextinstr rs) m')
    | exec_step_external:
        forall b ef args res rs m t rs' m' (EXT_ALLOWED: kern_mode m),
        rs PC = Vptr b Int.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        (* XXX maybe flip those two to keep the same order as before *)
        extcall_arguments rs m (ef_sig ef) args ->
        external_call' (fun _ => True) ef ge args m t res m' ->
        (** [CompCertX:test-compcert-undef-destroyed-by-call] We erase non-callee-save registers. *)
      (** [CompCertX:test-compcert-ra-vundef] We need to erase the value of RA,
      which is actually popped away from the stack in reality. *)
      rs' = (set_regs (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
        forall STACK:
        forall b o, rs ESP = Vptr b o ->
                    (Ple (Genv.genv_next ge) b /\ Plt b (Mem.nextblock m)),
  (** [CompCertX:test-compcert-protect-stack-arg] The following
      NOT_VUNDEF conditions will allow to later parameterize the
      per-function/module semantics of back-end languages over the stack
      pointer and the return address. *)
        forall SP_NOT_VUNDEF: rs ESP <> Vundef,
        forall RA_NOT_VUNDEF: rs RA <> Vundef,
        step ge (State rs m) t (State rs' m')
    | exec_step_prim_call:
        forall b ef rs m t rs' m',
          rs PC = Vptr b Int.zero ->
          Genv.find_funct_ptr ge b = Some (External ef) ->
          primitive_call ef ge rs m t rs' m' ->
          step ge (State rs m) t (State rs' m').

  Definition semantics (p: program) :=
    Smallstep.Semantics step (initial_state p) final_state (Genv.globalenv p).
End LSemantics.


(** * Layer-based instantiation *)

Section LayerLSemantics.
  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context {D} (L: compatlayer D).

  (** The following should be rewritten as a decision procedure,
      using the Decision class. *)

  Definition accessors_defined: bool :=
    match cl_exec_load L with
      | Errors.OK (Some _) =>
        match cl_exec_store L with
          | Errors.OK (Some _) => true
          | _ => false
        end
      | _ => false
    end.

  Class AccessorsDefined: Prop :=
    {
      accessors_defined_true: accessors_defined = true
    }.

  Context `{acc_def: AccessorsDefined}.

  Definition acc_exec_load_strong:
    {la: load_accessor D | cl_exec_load L = Errors.OK (Some la)}.
  Proof.
    destruct acc_def.
    unfold accessors_defined in accessors_defined_true0.
    destruct (cl_exec_load L); try discriminate.
    destruct o; try discriminate.
    esplit. reflexivity.
  Defined.

  Definition acc_exec_load: load_accessor D :=
    let (la, _) := acc_exec_load_strong in la.

  Definition acc_exec_store_strong:
    {sa: store_accessor D | cl_exec_store L = Errors.OK (Some sa)}.
  Proof.
    destruct acc_def.
    unfold accessors_defined in accessors_defined_true0.
    destruct (cl_exec_load L); try discriminate.
    destruct o; try discriminate.
    destruct (cl_exec_store L); try discriminate.
    destruct o; try discriminate.
    esplit. reflexivity.
  Defined.

  Definition acc_exec_store: store_accessor D :=
    let (sa, _) := acc_exec_store_strong in sa.

  Instance compatlayer_mem_accessors:
    MemAccessors (acc_exec_load) (acc_exec_store).

  (** To instantiate LSemantics using layers, we first need to be able
    to convert the stencil-based [sprimcall_sem] semantics provided by
    the layer into our [primcall_sem] based on global environments. *)

  Inductive compatsem_primcall_sem:
    compatsem D -> primcall_sem (mem := mwd D) := 
      compatsem_primcall_sem_intro (σ: sprimcall_primsem D) ge s rs m rs' m':
        stencil_matches s ge ->
        sprimcall_step σ s rs m rs' m' ->
        compatsem_primcall_sem (compatsem_inr σ) ge rs m E0 rs' m'.

  Lemma compatsem_primcall_le
        (σ1 σ2: compatsem D)
        (LE: σ1 ≤ σ2)
        ge rs m rs' m' t
        (Hsem: compatsem_primcall_sem σ1 ge rs m t rs' m')
        (Hvalid_ge: forall s, stencil_matches s ge -> 
                              match σ2 with
                                | inr s2 => sprimcall_valid s2 s = true
                                | _ => True
                              end)

  :
    compatsem_primcall_sem σ2 ge rs m t rs' m'.
  Proof.
    inv Hsem. specialize (Hvalid_ge _ H).
    inversion LE; subst; clear LE.
    inversion H; subst; clear H.
    destruct H2 as [Hstep Hsig Hvalid].
    destruct σ; subst; simpl in *.
    destruct y; subst; simpl in *.
    subst; simpl in *.
    repeat (econstructor; eauto).
    simpl; eauto.
    apply Hstep; eauto 1.
  Qed.

  (** Now we can instantiate [LayerConfigurationOps] for a specific
    layer, as defined as [compatlayer] in our framework. To this end we
    extend [compatlayer_extcall_ops] and friends to provide the extra
    parameters in [LayerConfigurationOps]. *)

  Instance compatlayer_configuration_ops:
    LayerConfigurationOps (ec_ops := compatlayer_extcall_ops L) :=
      {
        primitive_call ef ge rs m t rs' m' :=
          exists i sg σ,
            ef = EF_external i sg /\
            get_layer_primitive i L = Errors.OK (Some σ) /\
            compatsem_primcall_sem σ ge rs m t rs' m';
        exec_load := acc_exec_load;
        exec_store := acc_exec_store;
        kern_mode m := kernel_mode (π_data m)
      }.

  (** ** Semantics of whole programs *)

  Definition Lsemantics :=
    semantics (lcfg_ops := compatlayer_configuration_ops).

  (** ** Properties *)
  Section SEMANTICS_PROPERTIES.

    Lemma eval_addrmode_correct:
      forall {F V} (ge1 ge2: Genv.t F V),
      forall a rs r0 f s,
        (forall reg : PregEq.t,
           val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) 
        -> inject_incr (Mem.flat_inj (genv_next s)) f
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> val_inject f (eval_addrmode ge1 a rs) (eval_addrmode ge2 a r0).
    Proof.
      intros.
      unfold eval_addrmode.
      destruct a.
      apply val_add_inject.
      destruct base; eauto; constructor.
      apply val_add_inject.
      - destruct ofs; try constructor.
        destruct p.
        destruct (Int.eq i0 Int.one); eauto.
        unfold Pregmap.get in *. specialize (H i).
        destruct (rs i); destruct (Vint i0); try constructor.
        inv H; constructor.
      - destruct const; try constructor.
        destruct p.
        unfold symbol_offset. inv H1. inv H2.
        erewrite stencil_matches_symbols0.
        erewrite <- stencil_matches_symbols.
        case_eq (Genv.find_symbol ge1 i); auto.
        rewrite <- stencil_matches_genv_next in H0.
        intros. econstructor; eauto.
        eapply find_symbol_inject; eauto.
        rewrite Int.add_zero. reflexivity.
    Qed.

  End SEMANTICS_PROPERTIES.

  (** To prove that we can flip the forward simulaiton to the backward simulation,
we have to prove primcall function properties *)

  Definition sprimcall_props_defined {D} (σ: res (option (compatsem D))): bool :=
    match σ with
      | OK (Some (inr f)) =>
        match sprimcall_props _ f with
          | Error _ => false
          | _ => true
        end
      | _ => true
    end.

  Definition PrimitiveCallsXDefined {D} (L: compatlayer D): Prop :=
    forall i, (fun f => sprimcall_props_defined f = true) (get_layer_primitive i L).

  (* Declaring this instance is necessary to avoid [Existing Class]
getting in the way of instance resolution *)
  Instance primitive_calls_x_defined_dec: forall {D} (L: _ D), Decision (PrimitiveCallsXDefined L) := _.

  Existing Class ExternalCallsXDefined.

End LayerLSemantics.

(** The following hint allows to automatically find instances of
AccessorsDefined for layers containing [exec_load] and
[exec_store]. *)

Hint Extern 10 (AccessorsDefined _) =>
(constructor; reflexivity):
  typeclass_instances.
