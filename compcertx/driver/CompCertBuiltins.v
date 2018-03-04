Require SelectLongproofX.
Require I64helpers.

Import Coqlib.
Import AST.
Import Values.
Import Memory.
Import Events.
Import SelectLong.
Import I64helpers.
Import SelectLongproofX.

  Ltac norepet_inv :=
    match goal with
      | [ K: list_norepet (?a :: ?l) |- _] =>
        let Z1 := fresh "Z" in
        let Z2 := fresh "Z" in
        let K1 := fresh "K" in
        let K2 := fresh "K" in
        inversion K as [| Z1 Z2 K1 K2];
          clear K;
          subst Z1 Z2;
          simpl in K1
    end.

  Ltac norepet_solve :=
    repeat norepet_inv;
    exfalso;
    now intuition eauto using eq_sym.

(** In this file, we provide an instantiation of builtin_functions_sem
that contains I64 builtins.

For now, we do not reflect the behavior of CompCert's builtins
(defined in ../compcert/ia32/PrintAsm.ml: [print_builtin_inline]). We
should do it later at some point.
*)

  Inductive builtin_functions_sem
            `{memory_model_ops: Mem.MemoryModelOps}
            (i: ident) (sg: signature)
            (WB: block -> Prop)
            (F V: Type) (ge: Globalenvs.Genv.t F V):
    list val -> mem -> trace -> val -> mem -> Prop
    :=

  | builtin_sem_i64_neg
      (Hi: i = (hf).(i64_neg))
      (Hsg: sg = sig_l_l)
      x z
      (Hy: z = Val.negl x)
      m :
      builtin_functions_sem i sg WB _ _ ge (x :: nil) m E0 z m

  | builtin_sem_i64_add
      (Hi: i = (hf).(i64_add))
      (Hsg: sg = sig_ll_l)
      x y z
      (Hy: z = Val.addl x y)
      m :
      builtin_functions_sem i sg WB _ _ ge (x :: y :: nil) m E0 z m

  | builtin_sem_i64_sub
      (Hi: i = (hf).(i64_sub))
      (Hsg: sg = sig_ll_l)
      x y z
      (Hy: z = Val.subl x y)
      m :
      builtin_functions_sem i sg WB _ _ ge (x :: y :: nil) m E0 z m

  | builtin_sem_i64_mul
      (Hi: i = (hf).(i64_mul))
      (Hsg: sg = sig_ii_l)
      x y z
      (Hy: z = Val.mull' x y)
      m :
      builtin_functions_sem i sg WB _ _ ge (x :: y :: nil) m E0 z m

  .

  Class BuiltinIdentsNorepet: Prop :=
    {
      builtin_idents_norepet:
             list_norepet (
                 (i64_neg hf) ::
                              (i64_add hf) ::
                              (i64_sub hf) ::
                              (i64_mul hf) ::
                              nil
               )
    }.  

Section WITHMEM.
  Context `{memory_model: Mem.MemoryModel}.

  Global Instance builtin_functions_i64:
    ExternalCallI64Builtins
      builtin_functions_sem
      hf.
  Proof.
    constructor; intros; intro; intros.
    - eapply builtin_sem_i64_neg; eauto.
    - eapply builtin_sem_i64_add; eauto.
    - eapply builtin_sem_i64_sub; eauto.
    - eapply builtin_sem_i64_mul; eauto.
  Qed.

  Context `{builtin_idents_norepet_prf: BuiltinIdentsNorepet}.

  Theorem builtin_functions_properties
          i sg:
    extcall_properties (builtin_functions_sem i sg) sg.
  Proof.
    generalize builtin_idents_norepet. intro NOREPET.
    constructor.

    + (* type *)
      inversion 1; subst; simpl.
      destruct x; simpl; eauto.
      destruct x; destruct y; simpl; eauto.
      destruct x; destruct y; simpl; eauto.
      destruct x; destruct y; simpl; eauto.

    + (* symbols_preserved *)
      inversion 4; subst.
      eapply builtin_sem_i64_neg; eauto.
      eapply builtin_sem_i64_add; eauto.
      eapply builtin_sem_i64_sub; eauto.
      eapply builtin_sem_i64_mul; eauto.

    + (* valid_block *)
      inversion 1; subst; eauto.

    + (* perm *)
      inversion 1; subst; eauto.

    + (* unchanged on not writable *)
      inversion 1; subst; eapply Mem.unchanged_on_refl.

    + (* extends *)
      inversion 1; subst.
       - (* neg *)
         inversion 2; subst. inv H6.
         esplit. esplit. split.
         eapply builtin_sem_i64_neg; eauto.
         split.
         inv H4; eauto.
         split; auto using Mem.unchanged_on_refl.
       - (* add *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply builtin_sem_i64_add; eauto.
         split.
         inv H4; inv H5; simpl; eauto.
         destruct v2; simpl; eauto.
         split; auto using Mem.unchanged_on_refl.
       - (* sub *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply builtin_sem_i64_sub; eauto.
         split.
         inv H4; inv H5; simpl; eauto.
         destruct v2; simpl; eauto.
         split; auto using Mem.unchanged_on_refl.
       - (* mul *)
         inversion 2; subst. inv H6. inv H8.
         esplit. esplit. split.
         eapply builtin_sem_i64_mul; eauto.
         split.
         inv H4; inv H5; simpl; eauto.
         destruct v2; simpl; eauto.
         split; auto using Mem.unchanged_on_refl.

     + (* inject *)
       inversion 2; subst.

       - (* neg *)
         inversion 2; subst.
         inv H7.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_neg; eauto.
         split.
         inversion H5; simpl; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

       - (* add *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_add; eauto.
         split.
         inversion H5; inversion H6; simpl; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

       - (* sub *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_sub; eauto.
         split.
         inversion H5; inversion H6; simpl; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

       - (* mul *)
         inversion 2; subst.
         inv H7. inv H9.
         exists f. esplit. esplit. split.
         eapply builtin_sem_i64_mul; eauto.
         split.
         inversion H5; inversion H6; simpl; eauto.
         split; auto.
         split; auto using Mem.unchanged_on_refl.
         split; auto using Mem.unchanged_on_refl.
         split; auto.
         unfold inject_separated. congruence.

     + (* trace length *)
       inversion 1; subst; simpl; omega.

     + (* receptive *)
       inversion 1; subst; inversion 1; subst; eauto.

     + (* determinate *)
       Opaque hf.
       inversion 1; subst; inversion 1; subst; try norepet_solve;
       split; constructor; reflexivity.
       Transparent hf.

     + (* not writable *)
       inversion 1; subst; intros.
       - eapply builtin_sem_i64_neg; eauto.
       - eapply builtin_sem_i64_add; eauto.
       - eapply builtin_sem_i64_sub; eauto.
       - eapply builtin_sem_i64_mul; eauto.

     + (* unchanged at not writable *)
       inversion 1; subst; eauto.

  Qed.

End WITHMEM.

(**
We now expose an [ExternalCallsOpsX] class that only contains
external_calls_sem, so that ExternalCalls can be constructed from the
builtins defined here (and no inline assembly functions).  *)

  Class ExternalCallsOpsX
        (mem: Type)
        `{memory_model_ops: Mem.MemoryModelOps mem}
  : Type :=
    {
      external_functions_sem: ident -> signature -> extcall_sem
    }.

  Class ExternalCallsX
        (mem: Type)
        `{external_calls_ops_x: ExternalCallsOpsX mem}
  : Prop :=
    {
      external_functions_properties:
        forall id sg, extcall_properties (external_functions_sem id sg) sg
    }.

  Global Instance external_calls_ops_x_to_external_calls_ops
         (mem: Type)
         `{external_calls_ops_x: ExternalCallsOpsX mem}
  : ExternalCallsOps mem :=
    {|
      external_functions_sem := external_functions_sem;
      builtin_functions_sem := builtin_functions_sem;
      inline_assembly_sem := fun _ _ _ _ _ _ _ _ _ _ => False
    |}.

  Global Instance external_calls_ops_x_to_external_calls
         (mem: Type)
         `{memory_model: Mem.MemoryModel mem}
         `{external_calls_ops_x: !ExternalCallsOpsX mem}
         `{external_calls_x: !ExternalCallsX mem}
         `{builtin_idents_norepet_prf: BuiltinIdentsNorepet}
  : ExternalCalls mem.
  Proof.
    constructor.
    apply external_functions_properties.
    apply builtin_functions_properties.
    constructor; simpl; contradiction.
  Qed.
