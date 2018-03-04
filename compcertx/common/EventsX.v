Require compcert.common.Events.

Import Coqlib.
Import Values.
Import Memory.
Import Globalenvs.
Export Events.

(** [CompCertX:test-compcert-protect-stack] For CompCertX, we are
 going to instantiate CompCert with a non-trivial predicate for
 "writable memory blocks", ensuring that the stack locations of the
 caller are not "writable", and thus not overwritten by the compiled code.
 *)

Class WritableBlockAllowGlobals
      WB
      `{wb_ops: WritableBlockOps WB} :=
  {
    writable_block_allow_globals:
      forall {F V} (ge: Genv.t F V) i b,
        Genv.find_symbol ge i = Some b ->
        writable_block ge b
  }.

Section WITHMEM.
Context `{memory_model_ops: Mem.MemoryModelOps}.

Lemma protect_inject:
  forall (m_init: mem) f
         (Hincr: inject_incr (Mem.flat_inj (Mem.nextblock m_init)) f)
         (Hsep: inject_separated (Mem.flat_inj (Mem.nextblock m_init)) f m_init m_init)
         b1 b2 o
         (Hf: f b1 = Some (b2, o))
         n
         (Hn: Ple n (Mem.nextblock m_init))
  ,
        ((Ple n b1 /\ Plt b1 (Mem.nextblock m_init)) <-> (Ple n b2 /\ Plt b2 (Mem.nextblock m_init))).
Proof.
  intros.
  case_eq (Mem.flat_inj (Mem.nextblock m_init) b1).
   intros ? Hinj.
   generalize Hinj.
   unfold Mem.flat_inj. destruct (plt b1 (Mem.nextblock m_init)); try discriminate.
   injection 1; intros; subst.
   apply Hincr in Hinj.
   replace b2 with b1  in * by congruence.
   tauto.
  intro.
  exploit Hsep; eauto.
  unfold Mem.valid_block.
  xomega.
Qed.

Definition writable_block
           (m_init: mem)
           (F V: Type)
           (ge: Genv.t F V)
           (b: block)
: Prop
  :=
    ~ (Ple (Genv.genv_next ge) b /\ Plt b (Mem.nextblock m_init)).
Global Arguments writable_block _ [_ _] _ _.

Theorem global_writable_block:
  forall m_init
         (F V: Type)
         (ge: Genv.t F V)
         i b,
    Genv.find_symbol ge i = Some b ->
    writable_block m_init ge b.
Proof.
  intros.
  exploit Genv.genv_symb_range; eauto.
  unfold writable_block. xomega.
Qed.

Theorem callee_writable_block:
  forall m_init b,
    ~ Mem.valid_block m_init b ->
    forall (F V: Type)
           (ge: Genv.t F V),
      writable_block m_init ge b.
Proof.
  unfold Mem.valid_block, writable_block.
  intros. xomega.
Qed.

Theorem writable_block_genv_next:
  forall m_init 
         (F1 V1 F2 V2: Type) (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2)
         (Hnext: Genv.genv_next ge2 = Genv.genv_next ge1)
         b,
    writable_block m_init ge2 b = writable_block m_init ge1 b.
Proof.
  unfold writable_block. intros. congruence.
Qed.

Theorem writable_block_inject:
  forall m_init
         (F V: Type)
         (ge: Genv.t F V)
         (Hn: Ple (Genv.genv_next ge) (Mem.nextblock m_init))
         f
         (Hincr: inject_incr (Mem.flat_inj (Mem.nextblock m_init)) f)
         (Hsep: inject_separated (Mem.flat_inj (Mem.nextblock m_init)) f m_init m_init)
         b1 b2 o
         (Hf: f b1 = Some (b2, o))
  ,
  writable_block m_init ge b1 -> writable_block m_init ge b2.
Proof.
  unfold writable_block. intros.
  rewrite <- protect_inject; eauto.
Qed.

Global Instance writable_block_with_init_mem_ops:
  WritableBlockWithInitMemOps writable_block.
Proof.
  constructor.
  intro. constructor.
Defined.

Global Instance writable_block_with_init_mem:
  WritableBlockWithInitMem writable_block.
Proof.
  constructor.
  intro. constructor.
   unfold Events.writable_block, writable_block_with_init_mem, writable_block.
   congruence.
  unfold writable_block_with_init_mem, writable_block.
  intros; eapply writable_block_inject; eauto.
Qed.  

Global Instance writable_block_ops
       (m: mem):
  WritableBlockOps (writable_block m).
Proof.
  eauto using writable_block_with_init_mem_writable_block_ops.
Defined.

Global Instance Hwritable_block
       (m: mem):
  WritableBlock (writable_block m).
Proof.
  typeclasses eauto.
Qed.

Global Instance Hwritable_block_allow_globals
       (m: mem):
  WritableBlockAllowGlobals (writable_block m).
Proof.
  constructor. 
  apply global_writable_block.
Qed.

End WITHMEM.
