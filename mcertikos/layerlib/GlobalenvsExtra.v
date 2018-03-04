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
(*          Jérémie Koenig <jk@jk.fr.eu.org>                           *)
(*          Tahina Ramananandro <tahina.ramananandro@yale.edu>         *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide to the extension to the [Compcert] global evironment*)
Require Recdef.
Require Import Zwf.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import MemWithTags.
Require Import StackOrHeap.
Require Import MemWithData.
Require Export Globalenvs.
Require Import MemoryExtra.

(** * Properties related to store_zeros*)
Section STORE_ZEROS.
  Context `{Hmem: Mem.MemoryBaseStates}.

  (** From Globalenvs.v in Tahina's prototype *)
  Remark store_zeros_nextblock m b p n m':
    store_zeros m b p n = Some m' ->
    Mem.nextblock m' = Mem.nextblock m.
  Proof.
    functional induction (store_zeros m b p n); intros.
    * inv H; auto.
    * rewrite IHo; eauto with mem.
    * congruence.
  Qed.

  Remark store_zeros_valid_block m b p n m' b':
    store_zeros m b p n = Some m' ->
    Mem.valid_block m b' ->
    Mem.valid_block m' b'.
  Proof.
    intros.
    unfold Mem.valid_block in *.
    rewrite (store_zeros_nextblock _ _ _ _ _ H).
    trivial.
  Qed.

End STORE_ZEROS.

(** * Properties related to global environment*)
Module Genv.

  Export Globalenvs.Genv.

  Lemma find_funct_ptr_not_varinfo:
    forall {F V: Type} (p: program F V) b f v,
      find_funct_ptr (globalenv p) b = Some f ->
      find_var_info (globalenv p) b = Some v ->
      False.
  Proof.
    intros until p.
    unfold globalenv.
    apply add_globals_preserves.
    unfold add_global, find_var_info, find_funct_ptr.
    destruct g as [ [ | ] | ]; simpl; auto.
    intros.
    rewrite ZMap.gsspec in H1.
    destruct (ZIndexed.eq b0 (genv_next ge)); eauto.
    subst. exploit Genv.genv_vars_range; eauto. omega.
    intros.
    rewrite ZMap.gsspec in H2.
    destruct (ZIndexed.eq b0 (genv_next ge)); eauto.
    subst. exploit Genv.genv_funs_range; eauto. omega.
    intros until 1. intros _. revert H.
    unfold find_funct_ptr, empty_genv; simpl.
    rewrite ZMap.gi. discriminate.
  Qed. 


  Section ALLOC_GLOBALS_VALID.

    Context `{Hmem: Mem.WithTags tag}.
    Context {F V: Type}.

    Section GE.

      Variable ge: Genv.t F V.

      Lemma alloc_global_valid_block:
        forall g m m',
          Genv__alloc_global ge m g = Some m' ->
          forall b, Mem.valid_block m b ->
                    Mem.valid_block m' b.
      Proof.
        unfold Mem.valid_block. intros. erewrite Genv.alloc_global_nextblock; eauto with typeclass_instances. omega.
      Qed.

      Lemma alloc_globals_valid_block:
        forall gl m m',
          Genv__alloc_globals ge m gl = Some m' ->
          forall b, Mem.valid_block m b ->
                    Mem.valid_block m' b.
      Proof.
        induction gl; simpl.
         congruence.
        intro m.
        destruct (Genv__alloc_global ge m a) as [ | ] eqn:?; intros; eauto using alloc_global_valid_block; discriminate.
      Qed.

      Lemma alloc_globals_valid_access:
        forall chunk prm b' q gl m m',
          Genv__alloc_globals ge m gl = Some m' ->
          (Mem.valid_access m chunk b' q prm -> Mem.valid_access m' chunk b' q prm).
      Proof.
        inversion 2; subst.
        split; auto.
        intro. intros.
        apply -> (Genv.alloc_globals_perm (Mem__alloc := Mem.alloc Tag_global)); eauto.
        eapply Mem.valid_access_valid_block; eauto.
        eapply Mem.valid_access_implies; eauto.
        constructor.
      Qed.

    End GE.

  End ALLOC_GLOBALS_VALID.

  Section INIT_MEM_TGET.

    Context `{Hmem: Mem.WithTags tag}.

    Lemma store_zeros_tget:
      forall m b lo hi m',
        store_zeros m b lo hi = Some m' ->
        forall b', Mem.tget m' b' = Mem.tget m b'.
    Proof.
      intros until hi.
      functional induction (store_zeros m b lo hi); try congruence.
      intros.
      erewrite IHo by eassumption.
      now eauto using Mem.tget_store.
    Qed.

    Variables (F V: Type).

    Section GE.

      Variable (ge: Genv.t F V).

    Lemma store_init_data_tget: 
      forall m b z i m',
        store_init_data ge m b z i = Some m' ->
        forall b',
          Mem.tget m' b' = Mem.tget m b'.
    Proof.
      destruct i; simpl; try congruence; eauto using Mem.tget_store.
      destruct (find_symbol ge i); eauto using Mem.tget_store.
      discriminate.
    Qed.

    Lemma store_init_data_list_tget: 
      forall l m b z m',
        store_init_data_list ge m b z l = Some m' ->
        forall b',
          Mem.tget m' b' = Mem.tget m b'.
    Proof.
      induction l; simpl.
       congruence.
      intros until m'.
      destruct (store_init_data ge m b z a) as [ m1 | ] eqn:? ; try discriminate.
      intros.
      erewrite IHl by eassumption.
      now eauto using store_init_data_tget.
    Qed.

    Lemma alloc_global_tget :
      forall s b,
        Genv.find_symbol ge s = Some b ->
        forall m,
        (forall t, Mem.tget m b = Some t -> t = Tag_global) ->
        forall bg m', Genv__alloc_global ge m bg = Some m' ->          
          forall tg,
          Mem.tget m' b = Some tg ->
          tg = Tag_global.
    Proof.
      intros.
      destruct bg as [? [? [ [ | ] | ] ]]; simpl in *.
      + (* functions *)
        destruct (Mem.alloc Tag_global m 0 1) as [] eqn:?.
        erewrite Mem.tget_drop in H2 by eassumption.
        destruct (zeq b b0).
         subst. erewrite Mem.tget_alloc_same in H2 by eassumption. congruence.
        erewrite Mem.tget_alloc_other in H2 by eassumption. auto.
      + (* variables *)
        destruct (Mem.alloc Tag_global m 0 (init_data_list_size (gvar_init v))) as [m0 b0] eqn:?.
        destruct (store_zeros m0 b0 0 (init_data_list_size (gvar_init v))) as [ m1 | ] eqn:? ; try discriminate.
        destruct (store_init_data_list ge m1 b0 0 (gvar_init v)) as [ m2 | ] eqn:? ; try discriminate.
        erewrite Mem.tget_drop in H2 by eassumption.
        erewrite store_init_data_list_tget in H2 by eassumption.
        erewrite store_zeros_tget in H2 by eassumption.
        destruct (zeq b b0).
         subst. erewrite Mem.tget_alloc_same in H2 by eassumption. congruence.
        erewrite Mem.tget_alloc_other in H2 by eassumption. auto.
      + (* none *)
        destruct (Mem.alloc Tag_global m 0 0) as [] eqn:?.
        inv H1.
        destruct (zeq b b0).
         subst. erewrite Mem.tget_alloc_same in H2 by eassumption. congruence.
        erewrite Mem.tget_alloc_other in H2 by eassumption. auto.        
    Qed.

    Lemma alloc_globals_tget :
      forall s b,
        Genv.find_symbol ge s = Some b ->
        forall l m m', Genv__alloc_globals ge m l = Some m' ->          
          (forall t, Mem.tget m b = Some t -> t = Tag_global) ->
          forall tg,
          Mem.tget m' b = Some tg ->
          tg = Tag_global.
    Proof.
      induction l; simpl.
       inversion 1; subst; eauto.
      intros until 1.
      destruct (Genv__alloc_global ge m a) as [ | ] eqn:? ; try discriminate.
      intro.
      eapply IHl.
      eassumption.
      eapply alloc_global_tget; eauto.
    Qed.

    End GE.

    Lemma init_mem_tget :
      forall (p: _ F V) m,
        Genv__init_mem p = Some m ->
        forall s b,
          find_symbol (globalenv p) s = Some b ->
          Mem.tget m b = Some Tag_global.
    Proof.
      intros.
      exploit Genv.genv_symb_range; eauto.
      rewrite (init_mem_genv_next _ H).
      intros [ZERO VALID].
      eapply Mem.tget_valid in VALID.
      destruct (Mem.tget m b) as [ | ] eqn:? ; try congruence.
      f_equal.
      eapply alloc_globals_tget.
      eassumption.
      eassumption.
      intros.
      assert (VALID': Mem.valid_block Mem.empty b).
       eapply Mem.tget_valid.
       congruence.
      unfold Mem.valid_block in VALID'.
      rewrite (Mem.nextblock_empty) in VALID'.
      omega.
      assumption.
    Qed.

  End INIT_MEM_TGET.

  Section INITMEM_GET_ABSTRACT_DATA.
    Context `{Hmem: Mem.WithGetData}.

    Lemma store_zeros_get_abstract_data:
      forall m b lo hi m',
        store_zeros m b lo hi = Some m' ->
        Mem.get_abstract_data m = Mem.get_abstract_data m'.
    Proof.
      intros until hi.
      functional induction (store_zeros m b lo hi); try congruence.
      intros.
      etransitivity.
      eapply Mem.store_get_abstract_data; eauto.
      eauto.
    Qed.

    Context {F V: Type}.

    Section GE.

      Variable (ge: Genv.t F V).

    Lemma store_init_data_get_abstract_data: 
      forall m b z i m',
        store_init_data ge m b z i = Some m' ->
        Mem.get_abstract_data m = Mem.get_abstract_data m'.
    Proof.
      destruct i; simpl; try congruence; eauto using Mem.store_get_abstract_data.
      destruct (find_symbol ge i); eauto using Mem.store_get_abstract_data.
      discriminate.
    Qed.

    Lemma store_init_data_list_get_abstract_data:
      forall l m b z m',
        store_init_data_list ge m b z l = Some m' ->
        Mem.get_abstract_data m = Mem.get_abstract_data m'.
    Proof.
      induction l; simpl.
       congruence.
      intros until m'.
      destruct (store_init_data ge m b z a) as [ m1 | ] eqn:? ; try discriminate.
      intros.
      etransitivity.
      eapply store_init_data_get_abstract_data; eauto.
      eauto.
    Qed.

    Lemma alloc_global_get_abstract_data:
        forall m,
        forall bg m', Genv__alloc_global ge m bg = Some m' ->          
                      Mem.get_abstract_data m = Mem.get_abstract_data m'.
    Proof.
      intros.
      destruct bg as [? [? [ [ | ] | ] ]]; simpl in *.
      + (* functions *)
        destruct (Mem.alloc Tag_global m 0 1) as [] eqn:?.
        etransitivity.
         eapply Mem.alloc_get_abstract_data; eauto.
         eapply Mem.drop_perm_get_abstract_data; eauto.
      + (* variables *)
        destruct (Mem.alloc Tag_global m 0 (init_data_list_size (gvar_init v))) as [m0 b0] eqn:?.
        destruct (store_zeros m0 b0 0 (init_data_list_size (gvar_init v))) as [ m1 | ] eqn:? ; try discriminate.
        destruct (store_init_data_list ge m1 b0 0 (gvar_init v)) as [ m2 | ] eqn:? ; try discriminate.
        etransitivity.
         eapply Mem.alloc_get_abstract_data; eauto.
        etransitivity.
         eapply store_zeros_get_abstract_data; eauto.
        etransitivity.
         eapply store_init_data_list_get_abstract_data; eauto.
        eapply Mem.drop_perm_get_abstract_data; eauto.
      + (* none *)
        destruct (Mem.alloc Tag_global m 0 0) as [] eqn:?.
        inv H.
        eapply Mem.alloc_get_abstract_data; eauto.
    Qed.

    Lemma alloc_globals_get_abstract_data :
      forall l m m', Genv__alloc_globals ge m l = Some m' ->
                     Mem.get_abstract_data m = Mem.get_abstract_data m'.
    Proof.
      induction l; simpl.
       inversion 1; subst; eauto.
      intros until 1.
      destruct (Genv__alloc_global ge m a) as [ | ] eqn:? ; try discriminate.
      etransitivity.
       eapply alloc_global_get_abstract_data; eauto.
      eauto.
    Qed.

    End GE.

      Lemma init_mem_get_abstract_data:
        forall (p: program F V) m,
          Genv__init_mem p = Some m ->
          Mem.get_abstract_data m = empty_data.
      Proof.
        unfold Genv.init_mem.
        intros.
        etransitivity.
         symmetry.
         eapply alloc_globals_get_abstract_data; eauto.
        eapply Mem.empty_get_abstract_data.
      Qed.

  End INITMEM_GET_ABSTRACT_DATA.


  Section GENV.
    Variable F: Type.  (**r The type of function descriptions *)
    Variable V: Type.  (**r The type of information attached to variables *)

    (** ** Properties related to find_symbol*)
    Theorem find_symbol_exists_ex:
      forall (p: program F V) id,
        In id (prog_defs_names p) ->
        exists b, find_symbol (globalenv p) id = Some b.
    Proof.
      intros.
      unfold prog_defs_names in H.
      specialize (in_map_iff fst (prog_defs p) id).
      intros.
      inv H0.
      specialize (H1 H).
      destruct H1 as [[x [? ?]] [HP1 HP2]]; simpl in *; subst; eauto using find_symbol_exists.
    Qed.

    Lemma find_symbol_inversion_ex :
      forall (p: program F V) x b,
        find_symbol (globalenv p) x = Some b ->
        exists g, In (x,g) (prog_defs p).
    Proof.
      intros until b; unfold globalenv.
      eapply add_globals_preserves.
      (* preserves *)
      unfold find_symbol.
      simpl.
      intros. rewrite PTree.gsspec in H1. 
      destruct (peq x id). subst x. 
       esplit; eassumption.
      auto.
      (* base *)
      unfold find_symbol; simpl; intros. rewrite PTree.gempty in H. discriminate.
    Qed.

    (** ** Properties about the init data*)
    Section INITMEM_DATA.

      Section INITMEM.
        Variable ge: (Genv.t F V).

        Lemma init_data_list_size_pos:
          forall il, init_data_list_size il >= 0.
        Proof.
          induction il; simpl; try omega.
          specialize (init_data_size_pos a).
          intros.
          omega.
        Qed.

      End INITMEM.

    End INITMEM_DATA.

    (** ** Properties related to the augment global variables during the code translation*)
    Section INITMEM_AUG_LAYER.

      Context {smem tmem Mem__inject}
            `{Hinj: Mem.WithTagsInjections tag smem tmem Mem__inject}
            `{Hsmem: !Mem.WithTags tag smem}
            `{Htmem: !Mem.WithTags tag tmem}.

      Variable ge: (Genv.t F V).
      Variable thr: block.

      Lemma store_init_data_augment_ex: 
        forall m1 m2 b p id m2',
          Mem__inject (Mem.flat_inj thr) m1 m2 -> 
          b >= thr -> 
          store_init_data ge m2 b p id = Some m2' ->
          Mem__inject (Mem.flat_inj thr) m1 m2'.
      Proof. 
        intros until m2'. intros INJ BND ST. 
        assert (P: forall chunk ofs v m2', 
                     Mem.store chunk m2 b ofs v = Some m2' -> 
                     Mem__inject (Mem.flat_inj thr) m1 m2'). 
        intros. eapply Mem.store_outside_inject; eauto. 
        intros. unfold Mem.flat_inj in H0.
        destruct (zlt b' thr); inversion H0; subst. omega. 
        destruct id; simpl in ST; try (eapply P; eauto; fail).
        congruence.
        revert ST.  caseEq (find_symbol ge i); try congruence. intros; eapply P; eauto. 
      Qed.

      Lemma store_init_data_list_augment_ex:
        forall b idl m1 m2 p m2',
          Mem__inject (Mem.flat_inj thr) m1 m2 -> 
          b >= thr -> 
          store_init_data_list ge m2 b p idl = Some m2' ->
          Mem__inject (Mem.flat_inj thr) m1 m2'.
      Proof. 
        induction idl; simpl.
        intros; congruence.
        intros until m2'; intros INJ FB.
        caseEq (store_init_data ge m2 b p a); try congruence. intros. 
        apply IHidl with t0 (p+init_data_size a); auto. eapply store_init_data_augment_ex; eauto.  
      Qed.

      Lemma store_zeros_augment:
        forall m2 b lo hi m3,
          store_zeros m2 b lo hi = Some m3 ->
          forall thr m1, Mem__inject (Mem.flat_inj thr) m1 m2 ->
                         b >= thr ->
                         Mem__inject (Mem.flat_inj thr) m1 m3.
      Proof.
        intros until hi.
        functional induction (store_zeros m2 b lo hi); try congruence.
        intros.
        exploit @Mem.store_outside_inject; eauto.
        intro b'. unfold Mem.flat_inj. destruct (zlt b' thr0); try discriminate. injection 1; intros; subst; exfalso; omega.
      Qed.

      Lemma alloc_global_augment_ex:
        forall idg m1 m2 m2',
          Genv__alloc_global ge m2 idg = Some m2' ->
          Mem__inject (Mem.flat_inj thr) m1 m2 -> 
          Mem.nextblock m2 >= thr -> 
          Mem__inject (Mem.flat_inj thr) m1 m2'.
      Proof.
        intros. destruct idg as [id [? [ [f|v] | ]]]; simpl in *.
        (* function *)
      * destruct (Mem.alloc Tag_global m2 0 1) as [m3 b] eqn:?.
        assert (b >= thr). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto.
        eapply Mem.drop_outside_inject. 2: eassumption.
        eapply Memtype.Mem.alloc_right_inject; eauto.
        intros. unfold Mem.flat_inj in H3. destruct (zlt b' thr); inversion H3. 
        subst; exfalso; omega.
        (* variable *)
      * set (init := gvar_init v) in *.
        set (sz := init_data_list_size init) in *.
        destruct (Mem.alloc Tag_global m2 0 sz) as [m3 b] eqn:?.
        destruct (store_zeros m3 b 0 sz) as [m4|] eqn:?; try discriminate.
        destruct (store_init_data_list ge m4 b 0 init) as [m5|] eqn:?; try discriminate.
        assert (b >= thr). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto.
        eapply Mem.drop_outside_inject. 2: eauto. 
        eapply store_init_data_list_augment_ex. 3: eauto. 2: eauto.
        eapply store_zeros_augment; try eassumption.
        eapply Memtype.Mem.alloc_right_inject; eauto.
        intros. unfold Mem.flat_inj in H3. destruct (zlt b' thr); inversion H3. 
        subst; exfalso; omega.
        (* none *)
      * destruct (Mem.alloc Tag_global m2 0 0) as [m3 b] eqn:?.
        inv H.
        assert (b >= thr). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto.
        eapply Memtype.Mem.alloc_right_inject; eauto.
      Qed.

      Lemma alloc_globals_augment_ex:
        forall gl m1 m2 m2',
          Genv__alloc_globals ge m2 gl = Some m2' ->
          Mem__inject (Mem.flat_inj thr) m1 m2 ->
          Mem.nextblock m2 >= thr ->
          Mem__inject (Mem.flat_inj thr) m1 m2'.
      Proof.
        induction gl; simpl.
        intros. congruence.        
        intros ? ? ?. 
        case_eq (Genv__alloc_global ge m2 a); try congruence. intros.
        eapply IHgl; eauto.  
        eapply alloc_global_augment_ex; eauto. 
        rewrite (alloc_global_nextblock _ _ _ H). 
        unfold block in *; omega. 
      Qed.

    End INITMEM_AUG_LAYER.

  End GENV.

  Section ALLOC_GLOBALS_EXIST.
    Context {mem} `{Hmwt: Mem.WithTags tag mem}.

      Definition well_form_init_data (id: init_data) : bool :=
        match id with
          | Init_addrof _ _ => false
          | _ => true
        end.

      Context {F V: Type} (ge: (Genv.t F V)).

        Remark store_init_data_perm:
          forall k prm b' q id b m p m',
            store_init_data ge m b p id = Some m' ->
            (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
        Proof.
          intros.
          unfold store_init_data in H.
          assert (forall chunk v,
                    Mem.store chunk m b p v = Some m' ->
                    (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
          intros; split; eauto with mem. 


          destruct id; simpl in H; eauto.
          inv H; tauto.
          destruct (find_symbol ge i). eauto. discriminate.
        Qed.

      Lemma store_init_data_augment_exist: 
        forall m b id p,
          well_form_init_data id = true
          -> Mem.range_perm m b p (p + (init_data_size id)) Cur Writable
          -> (( init_data_size id) | p)
          -> {m'| store_init_data ge m b p id = Some m'}.
      Proof. 
        intros.
        unfold store_init_data.
        unfold init_data_size in *.
        unfold well_form_init_data in *.
        induction id; inversion H;
        try apply Mem.valid_access_store;
        unfold Mem.valid_access;
        unfold align_chunk;
        unfold size_chunk;
        try split; trivial.
        exists m.
        trivial.
      Qed.

      Fixpoint well_form_init_data_list (idl: list init_data): bool :=
        match idl with
          | nil => true
          | id :: idtail => match (well_form_init_data id) with
                              | true => well_form_init_data_list idtail
                              | false => false
                            end
        end.

      Fixpoint consistent_init_data_list (idl: list init_data) : option Z :=
        match idl with
          | nil => Some 1
          | id :: idtail => match (consistent_init_data_list idtail) with
                              | Some i => if zeq i 1 then
                                            Some (init_data_size id)
                                          else if zeq i (init_data_size id) then
                                                 Some i
                                               else None
                              | None => None
                            end
        end.

      Lemma store_init_data_list_augment_exist:
        forall b idl m p sz, 
          well_form_init_data_list idl = true
          -> consistent_init_data_list idl = Some sz
          -> (sz | p )
          -> Mem.range_perm m b p (p + init_data_list_size idl) Cur Freeable
          -> {m'| store_init_data_list ge m b p idl = Some m'}.
      Proof. 
        induction idl; simpl.
        intros; eauto.
        intros.
        caseEq (well_form_init_data a).
        intros HT.
        rewrite HT in *.
        caseEq (consistent_init_data_list idl).
        intros.
        rewrite H3 in H0.
        assert(HP: Mem.range_perm m b p (p + (init_data_size a)) Cur Writable).
        apply Mem.range_perm_implies with Freeable.
        unfold Mem.range_perm in *.
        intros.
        apply H2.
        specialize (init_data_list_size_pos idl).
        intros.  
        omega.
        constructor.

        caseEq (zeq z 1).
        intros.
        rewrite H4 in H0.
        subst z.
        inv H0.
        
        
        specialize (store_init_data_augment_exist _ _ _ _ HT HP H1).
        intros.
        destruct X as [m' HQ].
        rewrite HQ.
        apply IHidl with 1; auto. 
        apply Zone_divide.
        unfold Mem.range_perm in *.
        intros.
        specialize (store_init_data_perm Cur Freeable b ofs _ _ _ _ _ HQ).
        intros.
        inv H5.
        apply H6.  
        apply H2.
        specialize (init_data_size_pos a).
        intros.
        omega.
        
        intros.
        rewrite H4 in H0.
        caseEq ( zeq z (init_data_size a)).
        intros.
        rewrite H5 in H0.
        inv H0.
        rewrite <- H7 in H1.
        specialize (store_init_data_augment_exist _ _ _ _ HT HP H1).
        intros.
        destruct X as [m' HQ].
        rewrite HQ.
        apply IHidl with (init_data_size a) ; auto. 
        apply Zdivide_plus_r; auto.
        apply Zdivide_refl.

        unfold Mem.range_perm in *.
        intros.
        specialize (store_init_data_perm Cur Freeable b ofs _ _ _ _ _ HQ).
        intros.
        inv H5.
        apply H6.  
        apply H2.
        specialize (init_data_size_pos a).
        intros.
        omega.
        
        intros.
        rewrite H5 in H0.
        inv H0.
        
        intros.
        rewrite H3 in H0.
        inv H0.
        
        intros.
        rewrite H3 in H.
        inv H.
      Qed.

      Definition well_idglob (idg: (ident * option (globdef F V))) : bool :=
        match idg with
          | (_, v) => 
            match v with
              | Some (Gvar gl) => 
                match well_form_init_data_list (gvar_init gl) with
                  | true => 
                    match consistent_init_data_list (gvar_init gl) with
                      | Some _ => true
                      | _ => false
                    end
                  | _ => false
                end
              | _ => true
            end
        end.

      Lemma store_zeros_augment_exist:
        forall n m b p,
          Mem.range_perm m b p (p + n) Cur Freeable
          -> { m'| store_zeros m b p n = Some m'}.
      Proof.
        intros.
        functional induction (store_zeros m b p n ).
        exists m.
        trivial.
        
        apply IHo.
        unfold Mem.range_perm in *.
        intros.
        specialize (Mem.perm_store_1 _ _ _ _ _ _ e0).
        intros HP.
        apply HP.
        apply H.
        omega.
        
        assert (HP: Mem.valid_access m Mint8unsigned b p Writable).
        unfold Mem.valid_access.
        split.
        unfold size_chunk.
        unfold Mem.range_perm in *.
        intros.
        apply Mem.perm_implies with Freeable.
        apply H.  
        omega.
        
        constructor.
        unfold align_chunk.
        apply Zone_divide.
        
        specialize (Mem.valid_access_store _ _ _ _ Vzero HP).
        intro HQ.
        destruct HQ as [m' HQ].
        rewrite e0 in HQ.
        inv HQ.
      Qed.
      
      Lemma alloc_global_augment_exist:
        forall idg m,
          well_idglob idg = true
          -> {m'| Genv__alloc_global ge m (no_event_symbols idg) = Some m'}.
      Proof.
        intros.
        destruct idg as [id [ [f|v] | ]].
        (* function *)
        simpl.
        destruct (Mem.alloc Tag_global m 0 1) as [m1 b] eqn:?.
        assert(HP: Mem.range_perm m1 b 0 1 Cur Freeable).
        unfold Mem.range_perm.
        intros.
        eapply (Mem.perm_alloc_2); eauto.
        apply Mem.range_perm_drop_2.
        trivial.

        (* variable *)
        simpl in *.
        set (init := gvar_init v) in *.
        set (sz := init_data_list_size init) in *.
        caseEq (well_form_init_data_list init);
          intro HW1.
        rewrite HW1 in H.
        caseEq (consistent_init_data_list init).
        intros z HW2.
        clear H.
        destruct (Mem.alloc Tag_global m 0 sz) as [m1 b] eqn:?.
        assert(HP: Mem.range_perm m1 b 0 sz Cur Freeable).
        unfold Mem.range_perm.
        intros.
        eapply (Mem.perm_alloc_2); eauto.
        
        specialize (store_zeros_augment_exist _ _ _ _ HP).
        intro HZERO.
        destruct HZERO as [m2 HZERO].
        rewrite HZERO.
        assert(HP1: Mem.range_perm m2 b 0 sz Cur Freeable).
        unfold Mem.range_perm in *.
        intros.
        specialize (HP ofs H).
        specialize(store_zeros_perm Cur Freeable b ofs _ _ _ _ HZERO).
        intros.
        inv H0.
        auto.
        
        assert (HDIV: (z | 0)).
        apply Zdivide_0.
        specialize (store_init_data_list_augment_exist _ _ _ _ _ HW1 HW2 HDIV HP1).
        intro HQ.
        destruct HQ as [m' HQ].
        rewrite HQ.
        apply Mem.range_perm_drop_2.  
        
        clear HP.
        unfold Mem.range_perm in *.
        intros.
        specialize (HP1 ofs H).
        specialize(store_init_data_list_perm _ Cur Freeable b ofs _ _ _ _ HQ).
        intros.
        inv H0.
        auto.
        
        intros HW2.
        rewrite HW2 in H.
        inv H.
        
        rewrite HW1 in H.
        inv H.

        (* none *)
        simpl.
        destruct (Mem.alloc Tag_global m 0 0) as [m1 b] eqn:?.
        eauto.
      Qed.

      Fixpoint well_idglob_list (idgl: list (ident * option (globdef F V))) : bool :=
        match idgl with
          | nil => true
          | idg :: idgtail => match well_idglob idg with
                                | true => well_idglob_list idgtail
                                | false => false
                              end
        end.

      Lemma alloc_globals_augment_exist:
        forall gl m,
          well_idglob_list gl = true
          -> {m'| Genv__alloc_globals ge m (map no_event_symbols gl) = Some m'}.
      Proof.
        induction gl; simpl.
        intros. eauto.
        intros.
        caseEq (well_idglob a);
          intro HW;
          rewrite HW in H.
        specialize (alloc_global_augment_exist _ m HW).
        intro HP.
        destruct HP as [m' HP].
        rewrite HP.
        apply IHgl.
        trivial.
        
        inv H.
      Qed.

    End ALLOC_GLOBALS_EXIST.


  (** * Properties related to init memory under code translation with augment global variables*)
  Section TRANSF_PROGRAM_AUGMENT.

    Variable A B V W: Type.

    Lemma transf_globdefs_length_augment:
      forall (transf_fun: A -> res (option B)) (transf_var: V -> res (option W))
        gl gl',
      transf_globdefs_option (transf_fun) (transf_var) gl = OK gl'
        -> length gl = length gl'.
    Proof.
      induction gl.
      intros.
      unfold transf_globdefs_option in H.
      inv H.
      trivial.
      
      intros.
      inv H.
      destruct a as [? [? [ [ | ] | ]]].

      (* functions *)
      destruct (transf_fun f) as [ [ | ] | ]; try discriminate.
      monadInv H1.
      specialize (IHgl x EQ).
      unfold length in *.
      rewrite IHgl.
      trivial.
      monadInv H1.
      specialize (IHgl x EQ).
      unfold length in *.
      rewrite IHgl.
      trivial.
      inv H1.

      (* variables *)
      destruct (transf_globvar_option transf_var v) as [ [ | ] | ]; try discriminate.
      monadInv H0.
      specialize (IHgl x EQ).
      unfold length in *.
      rewrite IHgl.
      trivial.
      monadInv H0.
      specialize (IHgl x EQ).
      unfold length in *.
      rewrite IHgl.
      trivial.

      (* none *)
      monadInv H1.
      specialize (IHgl x EQ).
      unfold length in *.
      rewrite IHgl.
      trivial.
    Qed.

    Lemma transf_globdefs_fst:
      forall (transf_fun: A -> res (option B)) (transf_var: V -> res (option W))
             l x,
        transf_globdefs_option transf_fun transf_var l = OK x
        -> map fst x = map fst l.
    Proof.
      induction l.
      intros.
      unfold transf_globdefs_option in H.
      inv H.
      trivial.
      
      intros.
      inv H.
      destruct a as [? [? [ [ | ] | ]]].

      (* functions *)
      destruct (transf_fun f) as [ [ | ] | ]; try discriminate.
      monadInv H1.
      specialize (IHl _ EQ).
      simpl. congruence.
      monadInv H1.
      specialize (IHl _ EQ).
      simpl. congruence.
      
      (* variables *)
      destruct (transf_globvar_option transf_var v) as [ [ | ] | ]; try discriminate.
      monadInv H1.
      specialize (IHl _ EQ).
      simpl. congruence.
      monadInv H1.
      specialize (IHl _ EQ).
      simpl. congruence.
 
      (* none *)
      monadInv H1.
      specialize (IHl _ EQ).
      simpl. congruence.
    Qed.

    Variable transf_fun: A -> res B.
    Variable transf_var: V -> res W.
    Variable new_globs : list (ident * option (globdef B W)).
    Variable new_main : ident.
    Variable p: program A V.
    Variable p': program B W.

    Hypothesis transf_OK:
      transform_partial_augment_program transf_fun transf_var new_globs new_main p = OK p'.

    Theorem init_glob_augment:
      genv_next (globalenv p') = genv_next (globalenv p) + Z_of_nat(List.length new_globs).
    Proof.
      unfold transform_partial_augment_program, transform_partial_option_augment_program in transf_OK.
      assert(HP1: genv_next (globalenv p') = 1 + Z.of_nat (length (prog_defs p'))).
      unfold globalenv.
      rewrite genv_next_add_globals.
      assert(HP: genv_next (empty_genv B W) =1 ).
      simpl.
      trivial.
      rewrite HP.
      trivial.

      assert(HP2: genv_next (globalenv p) = 1 + Z.of_nat (length (prog_defs p))).
      unfold globalenv.
      rewrite genv_next_add_globals.
      assert(HP: genv_next (empty_genv A V) =1 ).
      simpl.
      trivial.
      rewrite HP.
      trivial.
      
      rewrite HP1.
      rewrite HP2.
      
      clear HP1 HP2.
      monadInv transf_OK.
      assert(HP:  (prog_defs {| prog_defs := x ++ map no_event_symbols new_globs; prog_main := new_main |}) = x ++ map no_event_symbols new_globs).
       simpl.
       trivial.
      rewrite HP.
      clear HP.
      rewrite app_length.
      rewrite Nat2Z.inj_add.
      specialize (transf_globdefs_length_augment _ _ _ _ EQ).
      intro HW.
      rewrite HW.
      assert(HT: forall a b:Z, 1 + (a + b) = 1 + a + b).
      intros.
      omega.
      rewrite map_length.
      apply HT.
    Qed.

    Lemma program_def_augment:
      forall p x,
        transf_globdefs_option (transf_fun' transf_fun) (transf_var' transf_var) (prog_defs p) = OK x
        -> map fst x = prog_defs_names p.
    Proof.
      unfold prog_defs_names.
      intros until x.
      eapply transf_globdefs_fst.
    Qed.
    
    Lemma program_name_augment:
      prog_defs_names p' = prog_defs_names p ++ (map fst new_globs).
    Proof.
      unfold transform_partial_augment_program, transform_partial_option_augment_program in transf_OK.
      monadInv transf_OK.
      unfold prog_defs_names.
      simpl.
      
      rewrite map_app.
      erewrite program_def_augment; eauto.
      unfold prog_defs_names.
      rewrite no_event_symbols_fst.
      constructor.
    Qed.

  End TRANSF_PROGRAM_AUGMENT.

  Section INITMEM_INJECT.
    Context `{mwt_model: Mem.WithTagsModel tag}.
    Context {F V: Type}.

    Lemma initmem_inject: (* should never be used in layer proofs *)
      forall (p: program F V) m,
        Genv__init_mem p = Some m ->
        Memtype.Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
    Proof.
      unfold init_mem; intros.
      apply Mem.neutral_inject. 
      eapply Genv.initmem_inject_neutral; eauto with typeclass_instances.
    Qed.
  End INITMEM_INJECT.

  (** * Theorems which still use the old interface *)

  Section WITHPUTDATA.
    Context {mem1}
            {mem2 DATA2} `{Hmemput: Mem.WithPutData DATA2 mem1 mem2}
            `{Hmem1: !Mem.WithTags tag mem1}
            `{Hmem2: !Mem.WithTags tag mem2}.

      Lemma store_zeros_put_abstract_data m b p n m':
        store_zeros m b p n = Some m' ->
        forall abd,
          store_zeros (Mem.put_abstract_data m abd) b p n = Some (Mem.put_abstract_data m' abd).
      Proof.
        functional induction (store_zeros m b p n); simpl; try congruence.
        + injection 1; intros; subst.
          rewrite store_zeros_equation.
          rewrite e.
          reflexivity.
        + intros.
          rewrite store_zeros_equation.
          rewrite e.
          erewrite Mem.store_put_abstract_data; eauto.
      Qed.

    (** ** Properties about the init data after putting abstract data*)
    Section INITPUT.
      Variable (F V: Type) (ge: t F V).

      Lemma store_init_data_put_abstract_data:
        forall m b (p: program F V) pr id m',
          store_init_data  (globalenv p) m b pr id = Some m' ->
          forall (abd:DATA2),
            store_init_data (globalenv p) (Mem.put_abstract_data m abd) b pr id
            = Some (Mem.put_abstract_data m' abd).
      Proof.
        unfold store_init_data.
        destruct id; try congruence; eauto using Mem.store_put_abstract_data.
        destruct (find_symbol (globalenv p) i); try congruence.
        eauto using Mem.store_put_abstract_data.
      Qed.

      Lemma store_init_data_list_put_abstract_data:
        forall b il m (pr: program F V) p m',
          store_init_data_list (globalenv pr) m b p il = Some m' ->
          forall (abd:DATA2),
            store_init_data_list (globalenv pr) (Mem.put_abstract_data m abd) b p il = Some  (Mem.put_abstract_data m' abd).
      Proof.
        induction il; simpl.
         congruence.
        intros until m'.
        case_eq (store_init_data (globalenv pr) m b p a); try discriminate.
        intros.
        erewrite store_init_data_put_abstract_data; eauto.
      Qed.

      Lemma alloc_global_put_abstract_data:
        forall m (p: program F V) id g m',
          Genv__alloc_global (globalenv p) m (id, g) = Some m' ->
          forall (abd:DATA2),
            Genv__alloc_global (globalenv p) (Mem.put_abstract_data m abd) (id, g) = Some (Mem.put_abstract_data m' abd).
      Proof.
        unfold Genv.alloc_global.
        destruct g as [ ? [ [ | ] | ]].
        + (* functions *)
          intro m'.
          destruct (Mem.alloc Tag_global m 0 1) as [ ] eqn:?.
          intros.
          erewrite Mem.alloc_put_abstract_data; eauto using Mem.drop_perm_put_abstract_data.
        + (* variables *)
          intro m'.
          destruct (Mem.alloc Tag_global m 0 (init_data_list_size (gvar_init v))) as [m1 ?] eqn:?.
          intros.
          erewrite Mem.alloc_put_abstract_data; eauto.
          destruct (store_zeros m1 b 0 (init_data_list_size (gvar_init v))) as [ m2 | ] eqn:? ; try discriminate.
          erewrite store_zeros_put_abstract_data; eauto.
          destruct (store_init_data_list (globalenv p) m2 b 0 (gvar_init v)) as [m3 | ] eqn:? ; try discriminate.
          erewrite store_init_data_list_put_abstract_data; eauto using Mem.drop_perm_put_abstract_data.
        + (* none *)
          intro m'.
          destruct (Mem.alloc Tag_global m 0 0) as [ ] eqn:?.
          intros.
          inv H.
          erewrite Mem.alloc_put_abstract_data; eauto.
      Qed.

      Lemma alloc_globals_put_abstract_data:
        forall gl m (p: program F V) m',
          Genv__alloc_globals (globalenv p) m gl = Some m' ->
          forall (abd:DATA2),
            Genv__alloc_globals (globalenv p) (Mem.put_abstract_data m abd) gl = Some (Mem.put_abstract_data m' abd).
      Proof.
        induction gl; simpl.
         congruence.
        intros.
        destruct (Genv__alloc_global (globalenv p) m a) as [ ? | ] eqn:? ; try discriminate.
        destruct a.
        erewrite alloc_global_put_abstract_data; eauto.
      Qed.

      Lemma init_mem_put_abstract_data:
        forall (p: program F V) m,
          Genv__init_mem p = Some m ->
          Genv__init_mem p =
            Some (Mem.put_abstract_data m empty_data).
      Proof.
        unfold Genv.init_mem.
        intros.
        rewrite <- Mem.empty_put_abstract_data.
        eapply alloc_globals_put_abstract_data.
        assumption.
      Qed.

    End INITPUT.

    End WITHPUTDATA.

    Section WITHDATAINJ.
    Context {mem1 DATA1}
            {mem2 DATA2} `{Hmemput: Mem.WithDataInject DATA1 DATA2 mem1 mem2}
            `{Hmem1: !Mem.WithDataModel DATA1 mem1}
            `{Hmodel2: !Mem.WithTagsModel tag mem2}.

    Section TRANSF_PROGRAM_AUGMENT.
      Variable A B V W: Type.
      Variable transf_fun: A -> res B.
      Variable transf_var: V -> res W.
      Variable new_globs : list (ident * option (globdef B W)).
      Variable new_main : ident.
      Variable p: program A V.
      Variable p': program B W.

      Hypothesis transf_OK:
        transform_partial_augment_program transf_fun transf_var new_globs new_main p = OK p'.

      Theorem init_mem_transf_augment_ex: 
        (forall s', find_symbol (globalenv p) s' <> None ->
                    ~ In s' (map fst new_globs)) ->
        forall (m: mem1), 
          Genv__init_mem p = Some m ->
          Genv__init_mem p' = Genv__alloc_globals (globalenv p') (Mem.put_abstract_data m empty_data) (List.map no_event_symbols new_globs).
      Proof.
        intros. eapply init_mem_match.
        apply prog_match.
        exact transf_OK. 
        now auto.
        apply init_mem_put_abstract_data.
        eassumption.
      Qed.

      Theorem init_mem_inject_transf_augment_ex:
        (forall s', find_symbol (globalenv p) s' <> None -> 
                    ~ In s' (map fst new_globs)) ->
        forall (m: mem1), 
          Genv__init_mem p = Some m ->
          forall (m': mem2),
            Genv__init_mem p' = Some m' -> 
            forall R: DATA1 -> DATA2 -> Prop,
              R empty_data empty_data ->
              Mem.inject R (Mem.flat_inj (Mem.nextblock m)) m m'.
      Proof.
        intros. 
        erewrite init_mem_transf_augment_ex in H1 ; eauto.        
        eapply alloc_globals_augment_ex; eauto with typeclass_instances.
        apply Mem.put_abstract_data_inject_internal_left.
        eapply initmem_inject; eauto.
        erewrite init_mem_get_abstract_data.
        assumption.
        eassumption.
        rewrite Mem.nextblock_put_abstract_data.
        omega.
      Qed.

      End TRANSF_PROGRAM_AUGMENT.

  End WITHDATAINJ.

End Genv.
