Require compcert.backend.RTLtyping.

Import Values.
Export RTLtyping.

Lemma has_type_list_normalize:
  forall l tyl,
    Val.has_type_list l tyl ->
    Val.has_type_list l (normalize_list tyl).
Proof.
  intros.
  eapply Val.has_subtype_list; eauto.
  clear l H.
  induction tyl; simpl.
   reflexivity.
  rewrite normalize_subtype. assumption.
Qed.
