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
Require Import Coq.Program.Basics.
Require Import Coq.Classes.Morphisms.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import liblayers.lib.Functor.
Require Import liblayers.lib.Monad.
Require Import liblayers.lib.Lens.
Require Export liblayers.lib.Lift.

(** * Prerequisites *)

(** We're going to lift the memory operations and theorems from a base
  type [bmem] to a "richer" type [mem], which contains [bmem] as a
  component. Formally, this means that we have a [Lens mem bmem] which
  provides us with well-behaved accessors to the [bmem] component
  inside of [mem]. While this is enough to lift most of the memory
  operations and theorems, we also need to know the value of
  the empty memory state of the richer type [mem]; indeed there's no
  way we would be able to construct that just from [empty : bmem].
  However, the simpler memory state contained within this empty [mem]
  should correspond to the empty [bmem] from the base memory states. *)

Class LiftMemoryModelOps {mem bmem: Type} (π: mem -> bmem)
  `{bmem_ops: Mem.MemoryModelOps bmem}
  `{bmem_set: !LensOps π} :=
{
  liftmem_empty: mem
}.

Class LiftMemoryModel {mem bmem: Type} (π: mem -> bmem)
  `{mem_liftops: LiftMemoryModelOps mem bmem π}: Prop :=
{
  liftmem_lens :> Lens π;
  liftmem_get_empty: π liftmem_empty = Mem.empty
}.

(** Using all of this, we can build a set of memory operations on the
  source type [mem] from the operations on the view type [bmem]. *)

Section LIFTOPS.
  Global Instance liftmem_ops `{mem_liftops: LiftMemoryModelOps}:
    Mem.MemoryModelOps mem :=
  {
    empty :=
      liftmem_empty;
    alloc wm lo hi :=
      lift π (fun m => Mem.alloc m lo hi) wm;
    nextblock wm :=
      lift π Mem.nextblock wm;
    free wm b lo hi :=
      lift π (fun m => Mem.free m b lo hi) wm;
    load chunk wm b ofs :=
      lift π (fun m => Mem.load chunk m b ofs) wm;
    store chunk wm b ofs v :=
      lift π (fun m => Mem.store chunk m b ofs v) wm;
    loadbytes wm b ofs n :=
      lift π (fun m => Mem.loadbytes m b ofs n) wm;
    storebytes wm b ofs vs :=
      lift π (fun m => Mem.storebytes m b ofs vs) wm;
    perm wm b ofs k p :=
      lift π (fun m => Mem.perm m b ofs k p) wm;
    valid_pointer wm b ofs :=
      lift π (fun m => Mem.valid_pointer m b ofs) wm;
    drop_perm wm b lo hi p :=
      lift π (fun m => Mem.drop_perm m b lo hi p) wm;
    extends wm1 wm2 :=
      lift π Mem.extends wm1 wm2;
    inject f wm1 wm2 :=
      lift π (Mem.inject f) wm1 wm2;
    inject_neutral thr wm :=
      lift π (Mem.inject_neutral thr) wm;
    unchanged_on P wm1 wm2 :=
      Mem.unchanged_on P (π wm1) (π wm2)
  }.
End LIFTOPS.

(** ** Properties of the [inject_incr] relation *)

(** Those are needed to enable rewriting using [liftmem_inject_same_context]. *)

Global Instance: Reflexive inject_incr.
Proof.
  firstorder.
Qed.

Global Instance: Transitive inject_incr.
Proof.
  firstorder.
Qed.

(** * Lifting the properties *)

Section LIFTDERIVED.
  Context `{HW: LiftMemoryModel}.

  (** Show that the operations derived from the [Mem.MemoryBaseOps]
    instance above are equivalent to lifting the operations derived
    from the original [Mem.MemoryBaseOps]. *)

  Theorem lift_loadv chunk wm addr:
    Mem.loadv chunk wm addr =
    lift π (fun m => Mem.loadv chunk m addr) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_storev chunk a v wm:
    Mem.storev chunk wm a v =
    lift π (fun m => Mem.storev chunk m a v) wm.
  Proof.
    unfold Mem.storev.
    destruct a; reflexivity.
  Qed.

  Theorem lift_free_list l wm:
    Mem.free_list wm l =
    lift π (fun m => Mem.free_list m l) wm.
  Proof with lift_auto.
    revert wm.
    induction l as [ | [[b lo] hi] l IHl]; intros...
    destruct (Mem.free (π wm) b lo hi)...
    rewrite IHl...
    destruct (Mem.free_list b0 l)...
  Qed.

  Theorem lift_valid_block (wm: mem) (b: block):
    Mem.valid_block wm b <->
    lift π (fun m => Mem.valid_block m b) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_range_perm (wm: mem) b lo hi k p:
    Mem.range_perm wm b lo hi k p <->
    lift π (fun m => Mem.range_perm m b lo hi k p) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_valid_access (wm: mem) chunk b ofs p:
    Mem.valid_access wm chunk b ofs p <->
    lift π (fun m => Mem.valid_access m chunk b ofs p) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_weak_valid_pointer (wm: mem) b ofs:
    Mem.weak_valid_pointer wm b ofs =
    lift π (fun m => Mem.weak_valid_pointer m b ofs) wm.
  Proof.
    reflexivity.
  Qed.
End LIFTDERIVED.

Hint Rewrite
  @lift_loadv
  @lift_storev
  @lift_free_list
  @lift_valid_block
  @lift_range_perm
  @lift_valid_access
  @lift_weak_valid_pointer
  using typeclasses eauto : lift.

(** Replace [(get Mem.empty)] by the underlying [Mem.empty]. *)
Hint Rewrite
  @liftmem_get_empty
  using typeclasses eauto: lens.

Section LIFTMEM.
  Context mem bmem `{Hmem: LiftMemoryModel mem bmem}.

  Local Arguments fmap : simpl never.

  Global Instance liftmem_spec:
    Mem.MemoryModel bmem -> Mem.MemoryModel mem.
  Proof.
    intro Hbmem; esplit.
    lift π Mem.valid_not_valid_diff.
    lift π Mem.perm_implies.
    lift π Mem.perm_cur_max.
    lift π Mem.perm_cur.
    lift π Mem.perm_max.
    lift π Mem.perm_valid_block.
    lift π Mem.range_perm_implies.
    lift π Mem.range_perm_cur.
    lift π Mem.range_perm_max.
    lift π Mem.valid_access_implies.
    lift π Mem.valid_access_valid_block.
    lift π Mem.valid_access_perm.
    lift π Mem.valid_pointer_nonempty_perm.
    lift π Mem.valid_pointer_valid_access.
    lift π Mem.weak_valid_pointer_spec.
    lift π Mem.valid_pointer_implies.
    lift π Mem.nextblock_empty.
    lift π Mem.perm_empty.
    lift π Mem.valid_access_empty.
    lift π Mem.valid_access_load.
    lift π Mem.load_valid_access.
    lift π Mem.load_type.
    lift π Mem.load_cast.
    lift π Mem.load_int8_signed_unsigned.
    lift π Mem.load_int16_signed_unsigned.
    lift π Mem.loadv_int64_split.
    lift π Mem.range_perm_loadbytes.
    lift π Mem.loadbytes_range_perm.
    lift π Mem.loadbytes_load.
    lift π Mem.load_loadbytes.
    lift π Mem.loadbytes_length.
    lift π Mem.loadbytes_empty.
    lift π Mem.loadbytes_concat.
    lift π Mem.loadbytes_split.
    lift π Mem.nextblock_store.
    lift π Mem.store_valid_block_1.
    lift π Mem.store_valid_block_2.
    lift π Mem.perm_store_1.
    lift π Mem.perm_store_2.
    lift π Mem.store_valid_access_1.
    lift π Mem.store_valid_access_2.
    lift π Mem.store_valid_access_3.
    lift π Mem.valid_access_store.
    lift π Mem.load_store_similar.
    lift π Mem.load_store_similar_2.
    lift π Mem.load_store_same.
    lift π Mem.load_store_other.
    lift π Mem.load_store_pointer_overlap.
    lift π Mem.load_store_pointer_mismatch.
    lift π Mem.load_pointer_store.
    lift π Mem.loadbytes_store_same.
    lift π Mem.loadbytes_store_other.
    lift π Mem.store_signed_unsigned_8.
    lift π Mem.store_signed_unsigned_16.
    lift π Mem.store_int8_zero_ext.
    lift π Mem.store_int8_sign_ext.
    lift π Mem.store_int16_zero_ext.
    lift π Mem.store_int16_sign_ext.
    lift π Mem.store_float32_truncate.
    lift π Mem.storev_int64_split.
    lift π Mem.storebytes_range_perm.
    lift π Mem.perm_storebytes_1.
    lift π Mem.perm_storebytes_2.
    lift π Mem.storebytes_valid_access_1.
    lift π Mem.storebytes_valid_access_2.
    lift π Mem.nextblock_storebytes.
    lift π Mem.storebytes_valid_block_1.
    lift π Mem.storebytes_valid_block_2.
    lift π Mem.range_perm_storebytes.
    lift π Mem.storebytes_store.
    lift π Mem.store_storebytes.
    lift π Mem.loadbytes_storebytes_same.
    lift π Mem.loadbytes_storebytes_other.
    lift π Mem.load_storebytes_other.
    lift π Mem.loadbytes_storebytes_disjoint.
    lift π Mem.storebytes_concat.
    lift π Mem.storebytes_split.
    lift π Mem.alloc_result.
    lift π Mem.nextblock_alloc.
    lift π Mem.valid_block_alloc.
    lift π Mem.fresh_block_alloc.
    lift π Mem.valid_new_block.
    lift π Mem.valid_block_alloc_inv.
    lift π Mem.perm_alloc_1.
    lift π Mem.perm_alloc_2.
    lift π Mem.perm_alloc_3.
    lift π Mem.perm_alloc_4.
    lift π Mem.perm_alloc_inv.
    lift π Mem.valid_access_alloc_other.
    lift π Mem.valid_access_alloc_same.
    lift π Mem.valid_access_alloc_inv.
    lift π Mem.load_alloc_unchanged.
    lift π Mem.load_alloc_other.
    lift π Mem.load_alloc_same.
    lift π Mem.load_alloc_same'.
    lift π Mem.loadbytes_alloc_unchanged.
    lift π Mem.loadbytes_alloc_same.
    lift π Mem.free_range_perm.
    lift π Mem.range_perm_free.
    lift π Mem.nextblock_free.
    lift π Mem.valid_block_free_1.
    lift π Mem.valid_block_free_2.
    lift π Mem.perm_free_1.
    lift π Mem.perm_free_2.
    lift π Mem.perm_free_3.
    lift π Mem.perm_free_list.
    lift π Mem.valid_access_free_1.
    lift π Mem.valid_access_free_2.
    lift π Mem.valid_access_free_inv_1.
    lift π Mem.valid_access_free_inv_2.
    lift π Mem.load_free.
    lift π Mem.loadbytes_free.
    lift π Mem.loadbytes_free_2.
    lift π Mem.nextblock_drop.
    lift π Mem.drop_perm_valid_block_1.
    lift π Mem.drop_perm_valid_block_2.
    lift π Mem.range_perm_drop_1.
    lift π Mem.range_perm_drop_2.
    lift π Mem.perm_drop_1.
    lift π Mem.perm_drop_2.
    lift π Mem.perm_drop_3.
    lift π Mem.perm_drop_4.
    lift π Mem.load_drop.
    lift π Mem.loadbytes_drop.
    lift π Mem.mext_next.
    lift π Mem.extends_refl.
    lift π Mem.load_extends.
    lift π Mem.loadv_extends.
    lift π Mem.loadbytes_extends.
    lift π Mem.store_within_extends.
    lift π Mem.store_outside_extends.
    lift π Mem.storev_extends.
    lift π Mem.storebytes_within_extends.
    lift π Mem.storebytes_outside_extends.
    lift π Mem.alloc_extends.
    lift π Mem.free_left_extends.
    lift π Mem.free_right_extends.
    lift π Mem.free_parallel_extends.
    lift π Mem.valid_block_extends.
    lift π Mem.perm_extends.
    lift π Mem.valid_access_extends.
    lift π Mem.valid_pointer_extends.
    lift π Mem.weak_valid_pointer_extends.
    lift π Mem.mi_freeblocks.
    lift π Mem.mi_mappedblocks.
    lift π Mem.mi_no_overlap.
    lift π Mem.valid_block_inject_1.
    lift π Mem.valid_block_inject_2.
    lift π Mem.perm_inject.
    lift π Mem.range_perm_inject.
    lift π Mem.valid_access_inject.
    lift π Mem.valid_pointer_inject.
    lift π Mem.weak_valid_pointer_inject.
    lift π Mem.address_inject.
    lift π Mem.valid_pointer_inject_no_overflow.
    lift π Mem.weak_valid_pointer_inject_no_overflow.
    lift π Mem.valid_pointer_inject_val.
    lift π Mem.weak_valid_pointer_inject_val.
    lift π Mem.inject_no_overlap.
    lift π Mem.different_pointers_inject.
    lift π Mem.disjoint_or_equal_inject.
    lift π Mem.aligned_area_inject.
    lift π Mem.load_inject.
    lift π Mem.loadv_inject.
    lift π Mem.loadbytes_inject.
    lift π Mem.store_mapped_inject.
    lift π Mem.store_unmapped_inject.
    lift π Mem.store_outside_inject.
    lift π Mem.storev_mapped_inject.
    lift π Mem.storebytes_mapped_inject.
    lift π Mem.storebytes_unmapped_inject.
    lift π Mem.storebytes_outside_inject.
    lift π Mem.storebytes_empty_inject.
    lift π Mem.alloc_right_inject.
    lift π Mem.alloc_left_unmapped_inject.
    lift π Mem.alloc_left_mapped_inject.
    lift π Mem.alloc_parallel_inject.
    lift π Mem.free_inject.
    lift π Mem.free_left_inject.
    lift π Mem.free_list_left_inject.
    lift π Mem.free_right_inject.
    lift π Mem.drop_outside_inject.
    lift π Mem.neutral_inject.
    lift π Mem.empty_inject_neutral.
    lift π Mem.alloc_inject_neutral.
    lift π Mem.store_inject_neutral.
    lift π Mem.drop_inject_neutral.
    lift π Mem.unchanged_on_refl.
    lift π Mem.perm_unchanged_on.
    lift π Mem.perm_unchanged_on_2.
    lift π Mem.loadbytes_unchanged_on_1.
    lift π Mem.loadbytes_unchanged_on.
    lift π Mem.load_unchanged_on_1.
    lift π Mem.load_unchanged_on.
    lift π Mem.store_unchanged_on.
    lift π Mem.storebytes_unchanged_on.
    lift π Mem.alloc_unchanged_on.
    lift π Mem.free_unchanged_on.
    lift π Mem.unchanged_on_empty.
    lift π Mem.unchanged_on_trans.
    lift π Mem.unchanged_on_weak.
    lift π Mem.unchanged_on_or.
    lift π Mem.unchanged_on_exists.
  Qed.
End LIFTMEM.
