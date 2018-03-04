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
Require Import CertiKOSAux.
(*Require Import mcertikos.mm.BootGenLink.*)
Require Import mcertikos.mm.ALInitGenLink.
Require Import mcertikos.mm.ALOpGenLink.
Require Import mcertikos.mm.ALGenLink.
Require Import mcertikos.mm.ContainerGenLink.
Require Import mcertikos.mm.PTIntroGenLink.
Require Import mcertikos.mm.PTOpGenLink.
Require Import mcertikos.mm.PTCommGenLink.
Require Import mcertikos.mm.PTKernGenLink.
Require Import mcertikos.mm.PTInitGenLink.
Require Import mcertikos.mm.PTNewGenLink.
Require Import mcertikos.mm.ShareIntroGenLink.
Require Import mcertikos.mm.ShareOpGenLink.
Require Import mcertikos.mm.ShareGenLink.
Require Import mcertikos.proc.KContextGenLink.
Require Import mcertikos.proc.KContextNewGenLink.
Require Import mcertikos.proc.ThreadIntroGenLink.
Require Import mcertikos.proc.ThreadInitGenLink.
Require Import mcertikos.proc.QueueIntroGenLink.
Require Import mcertikos.proc.QueueInitGenLink.
Require Import mcertikos.proc.AbQueueGenLink.
Require Import mcertikos.proc.CurIDGenLink.
Require Import mcertikos.proc.ThreadSchedGenLink.
Require Import mcertikos.proc.ThreadGenLink.
Require Import mcertikos.proc.IPCIntroGenLink.
Require Import mcertikos.proc.IPCGenLink.
Require Import mcertikos.proc.UCtxtIntroGenLink.
Require Import mcertikos.proc.ProcGenLink.
Require Import mcertikos.trap.TrapArgGenLink.
Require Import mcertikos.trap.TrapGenLink.
Require Import mcertikos.trap.DispatchGenLink.
Require Import mcertikos.trap.SysCallGenLink.
(*
Require Import mcertikos.virt.intel.EPTIntroGenLink.
Require Import mcertikos.virt.intel.EPTOpGenLink.
Require Import mcertikos.virt.intel.EPTInitGenLink.
Require Import mcertikos.virt.intel.VMCSIntroGenLink.
Require Import mcertikos.virt.intel.VMCSInitGenLink.
Require Import mcertikos.virt.intel.VMXIntroGenLink.
Require Import mcertikos.virt.intel.VMXInitGenLink.
*)
Require Import Behavior.

Remove Hints
    MemimplX.memory_model
    MemimplX.memory_model_x
    StencilImpl.ptree_stencil_ops
    StencilImpl.ptree_stencil_prf
  : typeclass_instances.

(** Intermediate correctness -- note that this has to be a [Prop] or a lot
    of the internal proofs have to be changed to [Type]. *)

Inductive exists_forward_simulation
    (s : stencil)
    (CTXT : LAsm.module)
    {CDATA}
    (HLayer : CompatLayerDef.compatlayer CDATA)
    (HSem LSem : LAsm.program -> Smallstep.semantics Integers.Int.int)
    (pl : LAsm.program) : Prop :=
  exists_forward_simulation_intro :
    forall ph : LAsm.program,
      forward_simulation (HSem ph) (LSem pl) ->
      make_program s CTXT HLayer = OK ph ->
      exists_forward_simulation s CTXT HLayer HSem LSem pl.

Inductive exists_backward_simulation
    (s : stencil)
    (CTXT : LAsm.module)
    {CDATA}
    (HLayer : CompatLayerDef.compatlayer CDATA)
    (HSem LSem : LAsm.program -> Smallstep.semantics Integers.Int.int)
    (pl : LAsm.program) : Prop :=
  exists_backward_simulation_intro :
    forall ph : LAsm.program,
      backward_simulation (HSem ph) (LSem pl) ->
      make_program s CTXT HLayer = OK ph ->
      exists_backward_simulation s CTXT HLayer HSem LSem pl.

Theorem CertiKOS_correct'_forward:
  forall (s: stencil) (CTXT: LAsm.module) combined_module combined
         (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
    CertiKOS.certikos_plus_ctxt CTXT = OK combined_module ->
    make_program s combined_module (MBoot.mboot ⊕ L64) = OK combined ->
    exists_forward_simulation
      s CTXT (TSysCall.tsyscall ⊕ L64)
      (LAsm.semantics (lcfg_ops := LC (TSysCall.tsyscall ⊕ L64)))
      (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)))
      combined.
Proof.
  intros s CTXT cM combined ? Hkern Hcomb.

  assert (pl_single_events :
      single_events (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)) combined)).
  { apply LAsmModuleSemEvent.LAsm_single_events;
      [ Decision.decision | assumption ].
  }

  unfold CertiKOS.certikos_plus_ctxt in *.
  unfold CertiKOS.add_loc in *.
  inv_monad' Hkern.
  unfold ret, res_monad_ops in *.
  unfold_all_into_link_impl.

  (*destruct_mpe BootGenLink.make_program_exists.*)
  destruct_mpe ALInitGenLink.make_program_exists.
  destruct_mpe ALOpGenLink.make_program_exists.
  destruct_mpe ALGenLink.make_program_exists.
  destruct_mpe ContainerGenLink.make_program_exists.
  destruct_mpe PTIntroGenLink.make_program_exists.
  destruct_mpe PTOpGenLink.make_program_exists.
  destruct_mpe PTCommGenLink.make_program_exists.
  destruct_mpe PTKernGenLink.make_program_exists.
  destruct_mpe PTInitGenLink.make_program_exists.
  destruct_mpe PTNewGenLink.make_program_exists.
  destruct_mpe ShareIntroGenLink.make_program_exists.
  destruct_mpe ShareOpGenLink.make_program_exists.
  destruct_mpe ShareGenLink.make_program_exists.

  destruct_mpe KContextGenLink.make_program_exists.
  destruct_mpe KContextNewGenLink.make_program_exists.
  destruct_mpe ThreadIntroGenLink.make_program_exists.
  destruct_mpe ThreadInitGenLink.make_program_exists.
  destruct_mpe QueueIntroGenLink.make_program_exists.
  destruct_mpe QueueInitGenLink.make_program_exists.
  destruct_mpe AbQueueGenLink.make_program_exists.
  destruct_mpe CurIDGenLink.make_program_exists.
  destruct_mpe ThreadSchedGenLink.make_program_exists.
  destruct_mpe ThreadGenLink.make_program_exists.
  destruct_mpe IPCIntroGenLink.make_program_exists.
  destruct_mpe IPCGenLink.make_program_exists.
  destruct_mpe UCtxtIntroGenLink.make_program_exists.
  destruct_mpe ProcGenLink.make_program_exists.

(*
  destruct_mpe EPTIntroGenLink.make_program_exists.
  destruct_mpe EPTOpGenLink.make_program_exists.
  destruct_mpe EPTInitGenLink.make_program_exists.
  destruct_mpe VMCSIntroGenLink.make_program_exists.
  destruct_mpe VMCSInitGenLink.make_program_exists.
  destruct_mpe VMXIntroGenLink.make_program_exists.
  destruct_mpe VMXInitGenLink.make_program_exists.
*)

  destruct_mpe TrapArgGenLink.make_program_exists.
  destruct_mpe TrapGenLink.make_program_exists.
  destruct_mpe DispatchGenLink.make_program_exists.
  destruct_mpe SysCallGenLink.make_program_exists.

  eapply exists_forward_simulation_intro; [ | eassumption].

  compose_forward_simulation SysCallGenLink.cl_forward_simulation.
  compose_forward_simulation DispatchGenLink.cl_forward_simulation.
  compose_forward_simulation TrapGenLink.cl_forward_simulation.
  compose_forward_simulation TrapArgGenLink.cl_forward_simulation.

(*
  compose_forward_simulation VMXInitGenLink.cl_forward_simulation.
  compose_forward_simulation VMXIntroGenLink.cl_forward_simulation.
  compose_forward_simulation VMCSInitGenLink.cl_forward_simulation.
  compose_forward_simulation VMCSIntroGenLink.cl_forward_simulation.
  compose_forward_simulation EPTInitGenLink.cl_forward_simulation.
  compose_forward_simulation EPTOpGenLink.cl_forward_simulation.
  compose_forward_simulation EPTIntroGenLink.cl_forward_simulation.
*)

  compose_forward_simulation ProcGenLink.cl_forward_simulation.
  compose_forward_simulation UCtxtIntroGenLink.cl_forward_simulation.
  compose_forward_simulation IPCGenLink.cl_forward_simulation.
  compose_forward_simulation IPCIntroGenLink.cl_forward_simulation.
  compose_forward_simulation ThreadGenLink.cl_forward_simulation.
  compose_forward_simulation ThreadSchedGenLink.cl_forward_simulation.

  compose_forward_simulation CurIDGenLink.cl_forward_simulation.
  compose_forward_simulation AbQueueGenLink.cl_forward_simulation.
  compose_forward_simulation QueueInitGenLink.cl_forward_simulation.
  compose_forward_simulation QueueIntroGenLink.cl_forward_simulation.
  compose_forward_simulation ThreadInitGenLink.cl_forward_simulation.
  compose_forward_simulation ThreadIntroGenLink.cl_forward_simulation.
  compose_forward_simulation KContextNewGenLink.cl_forward_simulation.
  compose_forward_simulation KContextGenLink.cl_forward_simulation.

  compose_forward_simulation ShareGenLink.cl_forward_simulation.
  compose_forward_simulation ShareOpGenLink.cl_forward_simulation.
  compose_forward_simulation ShareIntroGenLink.cl_forward_simulation.
  compose_forward_simulation PTNewGenLink.cl_forward_simulation.
  compose_forward_simulation PTInitGenLink.cl_forward_simulation.
  compose_forward_simulation PTKernGenLink.cl_forward_simulation.
  compose_forward_simulation PTCommGenLink.cl_forward_simulation.
  compose_forward_simulation PTOpGenLink.cl_forward_simulation.
  compose_forward_simulation PTIntroGenLink.cl_forward_simulation.
  compose_forward_simulation ContainerGenLink.cl_forward_simulation.
  compose_forward_simulation ALGenLink.cl_forward_simulation.
  compose_forward_simulation ALOpGenLink.cl_forward_simulation.
  last_simulation ALInitGenLink.cl_forward_simulation.
Qed.

Theorem CertiKOS_correct':
  forall (s: stencil) (CTXT: LAsm.module) combined_module combined
         (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
    CertiKOS.certikos_plus_ctxt CTXT = OK combined_module ->
    make_program s combined_module (MBoot.mboot ⊕ L64) = OK combined ->
    exists_backward_simulation
      s CTXT (TSysCall.tsyscall ⊕ L64)
      (LAsm.semantics (lcfg_ops := LC (TSysCall.tsyscall ⊕ L64)))
      (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)))
      combined.
Proof.
  intros s CTXT cM combined ? Hkern Hcomb.

  assert (pl_single_events :
      single_events (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)) combined)).
  { apply LAsmModuleSemEvent.LAsm_single_events;
      [ Decision.decision | assumption ].
  }

  unfold CertiKOS.certikos_plus_ctxt in *.
  unfold CertiKOS.add_loc in *.
  inv_monad' Hkern.
  unfold ret, res_monad_ops in *.
  unfold_all_into_link_impl.

  (*destruct_mpe BootGenLink.make_program_exists.*)
  destruct_mpe ALInitGenLink.make_program_exists.
  destruct_mpe ALOpGenLink.make_program_exists.
  destruct_mpe ALGenLink.make_program_exists.
  destruct_mpe ContainerGenLink.make_program_exists.
  destruct_mpe PTIntroGenLink.make_program_exists.
  destruct_mpe PTOpGenLink.make_program_exists.
  destruct_mpe PTCommGenLink.make_program_exists.
  destruct_mpe PTKernGenLink.make_program_exists.
  destruct_mpe PTInitGenLink.make_program_exists.
  destruct_mpe PTNewGenLink.make_program_exists.
  destruct_mpe ShareIntroGenLink.make_program_exists.
  destruct_mpe ShareOpGenLink.make_program_exists.
  destruct_mpe ShareGenLink.make_program_exists.

  destruct_mpe KContextGenLink.make_program_exists.
  destruct_mpe KContextNewGenLink.make_program_exists.
  destruct_mpe ThreadIntroGenLink.make_program_exists.
  destruct_mpe ThreadInitGenLink.make_program_exists.
  destruct_mpe QueueIntroGenLink.make_program_exists.
  destruct_mpe QueueInitGenLink.make_program_exists.
  destruct_mpe AbQueueGenLink.make_program_exists.
  destruct_mpe CurIDGenLink.make_program_exists.
  destruct_mpe ThreadSchedGenLink.make_program_exists.
  destruct_mpe ThreadGenLink.make_program_exists.
  destruct_mpe IPCIntroGenLink.make_program_exists.
  destruct_mpe IPCGenLink.make_program_exists.
  destruct_mpe UCtxtIntroGenLink.make_program_exists.
  destruct_mpe ProcGenLink.make_program_exists.

(*
  destruct_mpe EPTIntroGenLink.make_program_exists.
  destruct_mpe EPTOpGenLink.make_program_exists.
  destruct_mpe EPTInitGenLink.make_program_exists.
  destruct_mpe VMCSIntroGenLink.make_program_exists.
  destruct_mpe VMCSInitGenLink.make_program_exists.
  destruct_mpe VMXIntroGenLink.make_program_exists.
  destruct_mpe VMXInitGenLink.make_program_exists.
*)

  destruct_mpe TrapArgGenLink.make_program_exists.
  destruct_mpe TrapGenLink.make_program_exists.
  destruct_mpe DispatchGenLink.make_program_exists.
  destruct_mpe SysCallGenLink.make_program_exists.

  eapply exists_backward_simulation_intro; [ | eassumption].

  compose_backward_simulation SysCallGenLink.cl_backward_simulation.
  compose_backward_simulation DispatchGenLink.cl_backward_simulation.
  compose_backward_simulation TrapGenLink.cl_backward_simulation.
  compose_backward_simulation TrapArgGenLink.cl_backward_simulation.

(*
  compose_backward_simulation VMXInitGenLink.cl_backward_simulation.
  compose_backward_simulation VMXIntroGenLink.cl_backward_simulation.
  compose_backward_simulation VMCSInitGenLink.cl_backward_simulation.
  compose_backward_simulation VMCSIntroGenLink.cl_backward_simulation.
  compose_backward_simulation EPTInitGenLink.cl_backward_simulation.
  compose_backward_simulation EPTOpGenLink.cl_backward_simulation.
  compose_backward_simulation EPTIntroGenLink.cl_backward_simulation.
*)

  compose_backward_simulation ProcGenLink.cl_backward_simulation.
  compose_backward_simulation UCtxtIntroGenLink.cl_backward_simulation.
  compose_backward_simulation IPCGenLink.cl_backward_simulation.
  compose_backward_simulation IPCIntroGenLink.cl_backward_simulation.
  compose_backward_simulation ThreadGenLink.cl_backward_simulation.
  compose_backward_simulation ThreadSchedGenLink.cl_backward_simulation.

  compose_backward_simulation CurIDGenLink.cl_backward_simulation.
  compose_backward_simulation AbQueueGenLink.cl_backward_simulation.
  compose_backward_simulation QueueInitGenLink.cl_backward_simulation.
  compose_backward_simulation QueueIntroGenLink.cl_backward_simulation.
  compose_backward_simulation ThreadInitGenLink.cl_backward_simulation.
  compose_backward_simulation ThreadIntroGenLink.cl_backward_simulation.
  compose_backward_simulation KContextNewGenLink.cl_backward_simulation.
  compose_backward_simulation KContextGenLink.cl_backward_simulation.

  compose_backward_simulation ShareGenLink.cl_backward_simulation.
  compose_backward_simulation ShareOpGenLink.cl_backward_simulation.
  compose_backward_simulation ShareIntroGenLink.cl_backward_simulation.
  compose_backward_simulation PTNewGenLink.cl_backward_simulation.
  compose_backward_simulation PTInitGenLink.cl_backward_simulation.
  compose_backward_simulation PTKernGenLink.cl_backward_simulation.
  compose_backward_simulation PTCommGenLink.cl_backward_simulation.
  compose_backward_simulation PTOpGenLink.cl_backward_simulation.
  compose_backward_simulation PTIntroGenLink.cl_backward_simulation.
  compose_backward_simulation ContainerGenLink.cl_backward_simulation.
  compose_backward_simulation ALGenLink.cl_backward_simulation.
  compose_backward_simulation ALOpGenLink.cl_backward_simulation.
  last_simulation ALInitGenLink.cl_backward_simulation.
Qed.

Theorem CertiKOS_correct_simulation:
  forall (p: Observation.principal) (s: stencil) (CTXT: LAsm.module) 
         kernel combined_program user_program
         (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
    CertiKOS.certikos = OK kernel ->
    make_program s (CTXT ⊕ kernel) (MBoot.mboot ⊕ L64) = OK combined_program ->
    make_program s CTXT (TSysCall.tsyscall ⊕ L64) = OK user_program ->
    inhabited 
      (simulation 
         (LAsm.semantics (lcfg_ops := LC (TSysCall.tsyscall ⊕ L64)) user_program)
         (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)) combined_program)
         (observe_lasm _ p) (observe_lasm _ p)).
Proof.
  intros p s CTXT kernel combined_program user_program ? Hkernel Hcp Hup.
  edestruct (CertiKOS_plus_context CTXT) as (comb & Hcomb & Heqv); [ eassumption | ].
  eapply make_program_equiv in Hcp; [ | eassumption].

  assert (pl_single_events :
      single_events (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)) combined_program)).
  { apply LAsmModuleSemEvent.LAsm_single_events;
      [ Decision.decision | assumption ].
  }

  unfold CertiKOS.certikos_plus_ctxt in *.
  unfold CertiKOS.add_loc in *.
  inv_monad' Hcomb.
  unfold ret, res_monad_ops in *.
  unfold_all_into_link_impl.

  (*destruct_mpe BootGenLink.make_program_exists.*)
  destruct_mpe ALInitGenLink.make_program_exists.
  destruct_mpe ALOpGenLink.make_program_exists.
  destruct_mpe ALGenLink.make_program_exists.
  destruct_mpe ContainerGenLink.make_program_exists.
  destruct_mpe PTIntroGenLink.make_program_exists.
  destruct_mpe PTOpGenLink.make_program_exists.
  destruct_mpe PTCommGenLink.make_program_exists.
  destruct_mpe PTKernGenLink.make_program_exists.
  destruct_mpe PTInitGenLink.make_program_exists.
  destruct_mpe PTNewGenLink.make_program_exists.
  destruct_mpe ShareIntroGenLink.make_program_exists.
  destruct_mpe ShareOpGenLink.make_program_exists.
  destruct_mpe ShareGenLink.make_program_exists.

  destruct_mpe KContextGenLink.make_program_exists.
  destruct_mpe KContextNewGenLink.make_program_exists.
  destruct_mpe ThreadIntroGenLink.make_program_exists.
  destruct_mpe ThreadInitGenLink.make_program_exists.
  destruct_mpe QueueIntroGenLink.make_program_exists.
  destruct_mpe QueueInitGenLink.make_program_exists.
  destruct_mpe AbQueueGenLink.make_program_exists.
  destruct_mpe CurIDGenLink.make_program_exists.
  destruct_mpe ThreadSchedGenLink.make_program_exists.
  destruct_mpe ThreadGenLink.make_program_exists.
  destruct_mpe IPCIntroGenLink.make_program_exists.
  destruct_mpe IPCGenLink.make_program_exists.
  destruct_mpe UCtxtIntroGenLink.make_program_exists.
  destruct_mpe ProcGenLink.make_program_exists.

(*
  destruct_mpe EPTIntroGenLink.make_program_exists.
  destruct_mpe EPTOpGenLink.make_program_exists.
  destruct_mpe EPTInitGenLink.make_program_exists.
  destruct_mpe VMCSIntroGenLink.make_program_exists.
  destruct_mpe VMCSInitGenLink.make_program_exists.
  destruct_mpe VMXIntroGenLink.make_program_exists.
  destruct_mpe VMXInitGenLink.make_program_exists.
*)

  destruct_mpe TrapArgGenLink.make_program_exists.
  destruct_mpe TrapGenLink.make_program_exists.
  destruct_mpe DispatchGenLink.make_program_exists.
  destruct_mpe SysCallGenLink.make_program_exists.

  constructor.

  compose_simulation SysCallGenLink.cl_simulation.
  compose_simulation DispatchGenLink.cl_simulation.
  compose_simulation TrapGenLink.cl_simulation.
  compose_simulation TrapArgGenLink.cl_simulation.

(*
  compose_simulation VMXInitGenLink.cl_simulation.
  compose_simulation VMXIntroGenLink.cl_simulation.
  compose_simulation VMCSInitGenLink.cl_simulation.
  compose_simulation VMCSIntroGenLink.cl_simulation.
  compose_simulation EPTInitGenLink.cl_simulation.
  compose_simulation EPTOpGenLink.cl_simulation.
  compose_simulation EPTIntroGenLink.cl_simulation.
*)

  compose_simulation ProcGenLink.cl_simulation.
  compose_simulation UCtxtIntroGenLink.cl_simulation.
  compose_simulation IPCGenLink.cl_simulation.
  compose_simulation IPCIntroGenLink.cl_simulation.
  compose_simulation ThreadGenLink.cl_simulation.
  compose_simulation ThreadSchedGenLink.cl_simulation.

  compose_simulation CurIDGenLink.cl_simulation.
  compose_simulation AbQueueGenLink.cl_simulation.
  compose_simulation QueueInitGenLink.cl_simulation.
  compose_simulation QueueIntroGenLink.cl_simulation.
  compose_simulation ThreadInitGenLink.cl_simulation.
  compose_simulation ThreadIntroGenLink.cl_simulation.
  compose_simulation KContextNewGenLink.cl_simulation.
  compose_simulation KContextGenLink.cl_simulation.

  compose_simulation ShareGenLink.cl_simulation.
  compose_simulation ShareOpGenLink.cl_simulation.
  compose_simulation ShareIntroGenLink.cl_simulation.
  compose_simulation PTNewGenLink.cl_simulation.
  compose_simulation PTInitGenLink.cl_simulation.
  compose_simulation PTKernGenLink.cl_simulation.
  compose_simulation PTCommGenLink.cl_simulation.
  compose_simulation PTOpGenLink.cl_simulation.
  compose_simulation PTIntroGenLink.cl_simulation.
  compose_simulation ContainerGenLink.cl_simulation.
  compose_simulation ALGenLink.cl_simulation.
  compose_simulation ALOpGenLink.cl_simulation.
  last_simulation ALInitGenLink.cl_simulation.
Qed.

Theorem CertiKOS_correct_forward:
  forall (s: stencil) (CTXT: LAsm.module) kernel combined_program user_program
         (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
    CertiKOS.certikos = OK kernel ->
    make_program s (CTXT ⊕ kernel) (MBoot.mboot ⊕ L64) = OK combined_program ->
    make_program s CTXT (TSysCall.tsyscall ⊕ L64) = OK user_program ->
    inhabited
      (forward_simulation
        (LAsm.semantics (lcfg_ops := LC (TSysCall.tsyscall ⊕ L64)) user_program)
        (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)) combined_program)).
Proof.
  intros s CTXT kernel combined_program user_program ? Hkernel Hcp Hup.
  edestruct (CertiKOS_plus_context CTXT) as (comb & Hcomb & Heqv); [ eassumption | ].
  eapply make_program_equiv in Hcp; [ | eassumption].
  edestruct CertiKOS_correct'_forward; try eassumption.
  constructor.
  setoid_rewrite H in Hup.
  congruence.
Qed.

Theorem CertiKOS_correct:
  forall (s: stencil) (CTXT: LAsm.module) kernel combined_program user_program
         (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
    CertiKOS.certikos = OK kernel ->
    make_program s (CTXT ⊕ kernel) (MBoot.mboot ⊕ L64) = OK combined_program ->
    make_program s CTXT (TSysCall.tsyscall ⊕ L64) = OK user_program ->
    inhabited
      (backward_simulation
        (LAsm.semantics (lcfg_ops := LC (TSysCall.tsyscall ⊕ L64)) user_program)
        (LAsm.semantics (lcfg_ops := LC (MBoot.mboot ⊕ L64)) combined_program)).
Proof.
  intros s CTXT kernel combined_program user_program ? Hkernel Hcp Hup.
  edestruct (CertiKOS_plus_context CTXT) as (comb & Hcomb & Heqv); [ eassumption | ].
  eapply make_program_equiv in Hcp; [ | eassumption].
  edestruct CertiKOS_correct'; try eassumption.
  constructor.
  setoid_rewrite H in Hup.
  congruence.
Qed.
