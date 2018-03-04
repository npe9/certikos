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
(*          Layers of PROC                                             *)
(*                                                                     *)
(*          Refinement Proof for PAbQueue.v                            *)
(*                                                                     *)
(*          Yu Guo <yu.guo@yale.edu>                                   *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Asm.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import FlatMemory.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import RealParams.
Require Import LoadStoreSem2.
Require Import AsmImplLemma.
Require Import GenSem.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import XOmega.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.
Require Import LayerCalculusLemma.
Require Import AbstractDataType.

Require Import PQueueInit.
Require Import PAbQueue.
Require Import LayerCalculusLemma.
Require Import CalRealProcModule.

(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := pabqueue_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pqueueinit_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Section REFINEMENT_REL.
      
      Fixpoint abqueue_match_next_prev_rec (l : list Z) (ending: Z) (hd tl: Z) (starting: Z) 
               (tcb: TCBPool) : Prop := 
        match l with
          | nil => hd = num_proc /\ tl = num_proc
          | cons t nil => hd = t /\ tl = t /\ exists st, 
                                                ZMap.get t tcb = TCBValid st ending starting
                                                                          
          | cons t l' => tl = t /\ exists st, exists prev,
                                                ZMap.get t tcb = TCBValid st prev starting
                                                /\ abqueue_match_next_prev_rec l' ending hd prev t tcb
        end.
      
      Definition abqueue_match_dllist (abq: AbQueuePool) (tcb: TCBPool) (tdq: TDQueuePool): Prop := 
        forall qi l, 
          0<= qi <= num_chan
          -> ZMap.get qi abq = AbQValid l 
          -> exists hd, exists tl, 
                          ZMap.get qi tdq = TDQValid hd tl
                          /\ abqueue_match_next_prev_rec l num_proc hd tl num_proc tcb.

      Definition abtcbpool_tcbpool (abtcb: AbTCBPool) (tcb: TCBPool) : Prop :=
        forall i tds inq, 
          0 <= i < num_proc ->
          ZMap.get i abtcb = AbTCBValid tds inq
          -> exists pv, exists nx,
                          ZMap.get i tcb = TCBValid tds pv nx.

      Inductive AbQ_RealQ: AbTCBPool -> AbQueuePool -> TCBPool -> TDQueuePool -> Prop:=
      | AbQ_RealQ_con : 
          forall abtcb abq tcb tdq,
            abqueue_match_dllist abq tcb tdq
            -> abtcbpool_tcbpool abtcb tcb
            -> AbQ_RealQ abtcb abq tcb tdq.

      (** Relation between raw data at two layers*)
      Record relate_RData (f: meminj) (hadt: HDATA) (ladt: LDATA) :=
        mkrelate_RData {
            flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
            vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
            devout_re: devout hadt = devout ladt;
            CR3_re:  CR3 hadt = CR3 ladt;
            ikern_re: ikern hadt = ikern ladt;
            pg_re: pg hadt = pg ladt;
            ihost_re: ihost hadt = ihost ladt;
            AC_re: AC hadt = AC ladt;
            ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
            ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
            LAT_re: LAT hadt = LAT ladt;
            nps_re: nps hadt = nps ladt;
            init_re: init hadt = init ladt;

            pperm_re: pperm hadt = pperm ladt;
            PT_re:  PT hadt = PT ladt;
            ptp_re: ptpool hadt = ptpool ladt;
            idpde_re: idpde hadt = idpde ladt;
            ipt_re: ipt hadt = ipt ladt;
            smspool_re: smspool hadt = smspool ladt;

            kctxt_re: kctxt_inj f num_proc (kctxt hadt) (kctxt ladt);
            abq_re: AbQ_RealQ (abtcb hadt) 
                              (abq hadt) 
                              (tcb ladt) 
                              (tdq ladt) 
          }.

      Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
      | MATCH_RDATA: forall habd m f s, match_RData s habd m f.   

      Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
        {
          relate_AbData s f d1 d2 := relate_RData f d1 d2;
          match_AbData s d1 m f := match_RData s d1 m f;
          new_glbl := nil
        }.    

    End REFINEMENT_REL.

    Local Hint Resolve MATCH_RDATA.

    (** ** Properties of relations*)
    Section Rel_Property.

      (** Prove that after taking one step, the refinement relation still holds*)    
      Lemma relate_incr:  
        forall abd abd' f f',
          relate_RData f abd abd'
          -> inject_incr f f'
          -> relate_RData f' abd abd'.
      Proof.
        inversion 1; subst; intros; inv H; constructor; eauto.
        - eapply kctxt_inj_incr; eauto.
      Qed.

      Lemma relate_kernel_mode:
        forall abd abd' f,
          relate_RData f abd abd' 
          -> (kernel_mode abd <-> kernel_mode abd').
      Proof.
        inversion 1; simpl; split; congruence.
      Qed.

      Lemma relate_observe:
        forall p abd abd' f,
          relate_RData f abd abd' ->
          observe p abd = observe p abd'.
      Proof.
        inversion 1; simpl; unfold ObservationImpl.observe; congruence.
      Qed.

      Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
      Proof.
        constructor; intros; simpl; trivial.
        eapply relate_incr; eauto.
        eapply relate_kernel_mode; eauto.
        eapply relate_observe; eauto.
      Qed.

    End Rel_Property.

    (** * Proofs the initial state of low level specifications can be matched*)
    Section Init_Relation.

      Lemma AbQ_RealQ_init:
        AbQ_RealQ (ZMap.init AbTCBUndef) (ZMap.init AbQUndef) (ZMap.init TCBUndef) (ZMap.init TDQUndef).
      Proof.
        constructor.
        * intros qi l Hqi Hl.
          rewrite ZMap.gi in Hl.
          discriminate Hl.
        * intros i tds inq Hi H.
          rewrite ZMap.gi in H.
          discriminate H.
      Qed.

    End Init_Relation.

    Lemma match_next_prev_presv_set_notin : 
      forall l start ending hd tl tcbp,
        abqueue_match_next_prev_rec l ending hd tl start tcbp
        -> forall i, ~ In i l
                     -> forall tcb, abqueue_match_next_prev_rec l ending hd tl start (ZMap.set i tcb tcbp).
    Proof.
      intros l start ending hd tl tcbp.
      assert (forall start tl, abqueue_match_next_prev_rec l ending hd tl start tcbp
                               -> forall i : Z,
                                    ~ In i l ->
                                    forall tcb : TCB,
                                      abqueue_match_next_prev_rec l ending hd tl start (ZMap.set i tcb tcbp)).
      clear.
      induction l; simpl in *.
      intros; trivial.
      
      intros.
      destruct l.
      destruct H as [Hhd [Htl [st Hst]]].
      split; trivial.
      split; trivial.
      exists st.
      rewrite ZMap.gsspec.
      unfold ZIndexed.eq.
      destruct (zeq a i); trivial.
      apply False_ind.
      apply H0.
      left; trivial.
      (* induction step *)
      destruct H.
      split; trivial.
      destruct H1 as [st [pv' H1]].
      exists st; exists pv'.
      split.
      destruct H1.
      rewrite ZMap.gsspec.
      unfold ZIndexed.eq.
      destruct (zeq a i); trivial.
      apply False_ind.
      apply H0.
      left; trivial.
      destruct H1.
      apply IHl; auto.
      intros.
      apply H; auto.
    Qed.

    Definition abqueue_valid_Q (abq: AbQueuePool) : Prop :=
      forall qi, 
        0<= qi <= num_chan
        -> exists l, ZMap.get qi abq = AbQValid l.

    Definition abqueue_valid_abtcb (abtcb: AbTCBPool) : Prop :=
      forall i, 
        0<= i < num_proc
        -> exists s inq, ZMap.get i abtcb = AbTCBValid s inq.

    Definition abqueue_valid_inQ (abtcb: AbTCBPool) (abq: AbQueuePool) : Prop :=
      forall i qi l, 
        0<= i < num_proc
        -> 0<= qi <= num_chan
        -> ZMap.get qi abq = AbQValid l
        -> In i l
        -> exists s, ZMap.get i abtcb = AbTCBValid s qi.          

    Definition abqueue_abq_range (abtcb: AbTCBPool) (abq: AbQueuePool) : Prop :=
      forall qi i l, 
        0<= qi <= num_chan
        -> ZMap.get qi abq = AbQValid l
        -> In i l
        -> 0 <= i < num_proc.

    Definition abqueue_disjoint (abtcb: AbTCBPool) (abq: AbQueuePool) : Prop :=
      forall qi i l,
        0 <= qi <= num_chan
        -> 0<= i < num_proc
        -> ZMap.get qi abq = AbQValid l 
        -> In i l
        -> forall qi' l',
             0 <= qi' <= num_chan
             -> qi' <> qi
             -> ZMap.get qi' abq = AbQValid l'
             -> ~ In i l'.

    Definition abqueue_notinQ (abtcb: AbTCBPool) (abq: AbQueuePool) : Prop :=
      forall i tds, 
        0<= i < num_proc
        -> ZMap.get i  abtcb = AbTCBValid tds (-1)
        -> forall qi l,
             0<= qi <= num_chan
             -> ZMap.get qi abq = AbQValid l
             -> ~ In i l.

    Definition abqueue_valid_count (abtcb: AbTCBPool) (abq: AbQueuePool) : Prop :=
      forall i s inq, 
        0<= i < num_proc
        -> ZMap.get i abtcb = AbTCBValid s inq
        -> (forall qi l,
              0<= qi <= num_chan
              -> ZMap.get qi abq = AbQValid l
              -> ((qi = inq -> count_occ zeq l i = 1%nat)
                  /\ (qi <> inq -> ~ In i l))).

    Definition abqueue_abq_mapto_abtcb  (abtcb: AbTCBPool) (abq: AbQueuePool) : Prop := 
      forall i, 
        0 <= i < num_proc 
        -> exists st inq, ZMap.get i abtcb = AbTCBValid st inq
                          /\ ((inq = -1) \/ (0 <= inq <= num_chan)).

    Definition abqueue_queue_disjoint (abtcb: AbTCBPool) (abq: AbQueuePool) : Prop :=
      forall qi l,
        0 <= qi <= num_chan
        -> ZMap.get qi abq = AbQValid l
        -> forall i,
             0<=i < num_proc
             -> In i l
             -> count_occ zeq l i = 1%nat.

    Lemma abqueue_INV_implies_queue_disjoint : 
      forall abtcb abq,
        abqueue_valid_count abtcb abq
        -> abqueue_valid_inQ abtcb abq
        -> abqueue_queue_disjoint abtcb abq.
    Proof.
      clear.
      unfold abqueue_valid_count, abqueue_valid_inQ, abqueue_queue_disjoint.
      intros abtcb abq.
      intros Hcount HinQ.
      intros qi l Hqi Hgetqi i Hi Hin.
      destruct (HinQ _ _ _ Hi Hqi Hgetqi Hin) as [s Hgeti].
      destruct (Hcount _ _ _ Hi Hgeti qi l Hqi Hgetqi).
      apply H; trivial.
    Qed.    

    Lemma abqueue_INV_implies_disjoint : 
      forall abtcb abq,
        abqueue_abq_mapto_abtcb abtcb abq
        -> abqueue_valid_count abtcb abq
        -> abqueue_valid_inQ abtcb abq
        -> abqueue_disjoint abtcb abq.
    Proof.
      clear.
      unfold abqueue_valid_count, abqueue_valid_inQ, abqueue_disjoint, abqueue_abq_mapto_abtcb.
      intros abtcb abq.
      intros Habq_abtcb Hcount HinQ.
      intros qi i l Hqi Hi Hgetqi Hil.
      intros qi' l' Hqi' Hneq Hgetqi'.
      destruct (Habq_abtcb i Hi) as [st [inq [Hgeti _]]].
      destruct (HinQ _ _ _ Hi Hqi Hgetqi Hil) as [st' Hx].
      rewrite Hgeti in Hx.
      inversion Hx; subst st' inq.
      destruct (Hcount i st qi Hi Hgeti qi' l' Hqi' Hgetqi').
      auto.
    Qed.    

    Lemma abqueue_INV_implies_notinQ: 
      forall abtcb abq,
        abqueue_abq_mapto_abtcb abtcb abq
        -> abqueue_valid_count abtcb abq
        -> abqueue_valid_inQ abtcb abq
        -> abqueue_notinQ abtcb abq. 
    Proof.
      clear.
      unfold abqueue_valid_count, abqueue_valid_inQ, abqueue_disjoint, abqueue_abq_mapto_abtcb.
      intros abtcb abq.
      intros Habq_abtcb Hcount HinQ.
      intros i s Hi Hgeti qi l Hqi Hgetqi.
      destruct (Hcount i s (-1) Hi Hgeti qi l Hqi Hgetqi).
      apply H0.
      omega.
    Qed.    

    Ltac zeq_simpl :=
      let Heq := fresh "Heq" in
      let Hneq := fresh "Hneq" in
      match goal with 
        | H: _ |- context [ zeq ?z ?z ] => destruct (zeq z z) as [Heq | Hneq]
                                           ; [ | destruct (Hneq (refl_equal _))]
        | H: context [ zeq ?z ?z ] |- _  => destruct (zeq z z) as [Heq | Hneq]
                                            ; [ | destruct (Hneq (refl_equal _))]

        | H : ?z = ?z' |- context [ zeq ?z ?z' ] => destruct (zeq z z') as [ _ | Hneq ]
                                                    ; [ | destruct (Hneq H) ]
        | H : ?z = ?z',
              H1 : context [ zeq ?z ?z' ] |- _ => destruct (zeq z z') as [ _ | Hneq]
                                                  ; [ | destruct (Hneq H) ]

        | H : ?z = ?z' |- context [ zeq ?z' ?z ] => destruct (zeq z' z) as [ _ | Hneq ]
                                                    ; [ | destruct (Hneq (eq_sym H)) ]
        | H : ?z = ?z',
              H1 : context [ zeq ?z' ?z ] |- _ => destruct (zeq z' z) as [ _ | Hneq]
                                                  ; [ | destruct (Hneq (eq_sym H)) ]

        | H : ?z <> ?z' |- context [ zeq ?z ?z' ] => destruct (zeq z z') as [Heq | _ ]
                                                     ; [ destruct (H Heq) | ]

        | H : ?z <> ?z',
              H1 : context [ zeq ?z ?z' ] |- _ => destruct (zeq z z') as [Heq | _ ]
                                                  ; [ destruct (H Heq) | ]

        | H : ?z <> ?z' |- context [ zeq ?z' ?z ] => destruct (zeq z' z) as [Heq | _ ]
                                                     ; [ destruct (H (eq_sym Heq)) | ]

        | H : ?z <> ?z',
              H1 : context [ zeq ?z' ?z ] |- _ => destruct (zeq z' z) as [Heq | _ ]
                                                  ; [ destruct (H (eq_sym Heq)) | ]

        | H :  context [ zeq ?z ?z' ] |- _ => destruct (zeq z z') as [Heq | Hneq ]
        | H : _ |- context [ zeq ?z ?z' ] => destruct (zeq z z') as [Heq | Hneq ]

      end.

    Ltac rew_arith t :=
      let Hx := fresh "Hx" in 
      assert (Hx : t); [try omega; try (clear; intros; omega) | rewrite Hx; clear Hx].

    Ltac rew_arith_H t H :=
      let Hx := fresh "Hx" in 
      assert (Hx : t); [try omega; try (clear; intros; omega) | rewrite Hx in H; clear Hx].

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      (** ** The low level specifications exist*)
      Section Exists.

        (*Lemma trapin_exist:
          forall habd habd' labd f,
            PAbQueue.trapin_spec habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', PQueueInit.trapin_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PAbQueue.trapin_spec, PQueueInit.trapin_spec; intros until f; exist_simpl.          
        Qed.

        Lemma trapout_exist:
          forall habd habd' labd f,
            PAbQueue.trapout_spec habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', PQueueInit.trapout_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.trapout_spec, PAbQueue.trapout_spec; intros until f; exist_simpl.
        Qed.

        Lemma hostin_exist:
          forall habd habd' labd f,
            PAbQueue.hostin_spec habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', PQueueInit.hostin_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.hostin_spec, PAbQueue.hostin_spec; intros until f; exist_simpl.          
        Qed.

        Lemma hostout_exist:
          forall habd habd' labd f,
            PAbQueue.hostout_spec habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', PQueueInit.hostout_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.hostout_spec, PAbQueue.hostout_spec; intros until f; exist_simpl.
        Qed.

        Lemma ptin_exist:
          forall habd habd' labd f,
            PAbQueue.ptin_spec habd = Some habd'
            -> relate_RData f habd labd
            -> PAbQueue.high_level_invariant habd
            -> exists labd', PQueueInit.ptin_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.ptin_spec, PAbQueue.ptin_spec; intros until f; exist_simpl.
        Qed.

        Lemma ptout_exist:
          forall habd habd' labd f,
            PAbQueue.ptout_spec habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', PQueueInit.ptout_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.ptout_spec, PAbQueue.ptout_spec; intros until f; exist_simpl.
        Qed.

        Lemma pfree_exist:
          forall habd habd' labd i f,
            PAbQueue.pfree_spec habd i = Some habd'
            -> relate_RData f habd labd
            -> exists labd', PQueueInit.pfree_spec labd i = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.pfree_spec, PAbQueue.pfree_spec; intros until f; exist_simpl.
        Qed.

        Lemma palloc_exist:
          forall habd habd' labd i f,
            PAbQueue.palloc_spec habd = Some (habd', i)
            -> relate_RData f habd labd
            -> exists labd', PQueueInit.palloc_spec labd = Some (labd', i) /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.palloc_spec, PAbQueue.palloc_spec; intros until f; exist_simpl.
        Qed.

        Lemma setPT_exist:
          forall habd habd' labd i f,
            PAbQueue.setPT_spec habd i = Some habd'
            -> relate_RData f habd labd
            -> PAbQueue.high_level_invariant habd
            -> exists labd', PQueueInit.setPT_spec labd i = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PQueueInit.setPT_spec, PAbQueue.setPT_spec; intros until f; exist_simpl. 
        Qed.

        Lemma ptRead_exist:
          forall habd labd n vadr z f,
            PAbQueue.ptRead_spec habd n vadr = Some z
            -> relate_RData f habd labd
            -> PQueueInit.ptRead_spec labd n vadr = Some z.
        Proof.
          unfold PAbQueue.ptRead_spec, PAbQueue.ptRead_Arg, PQueueInit.ptRead_spec, PQueueIntro.ptRead_Arg; 
          intros until f; exist_simpl.
        Qed.

        Lemma ptResv_exist:
          forall habd habd' labd n vadr perm f,
            PAbQueue.ptResv_spec habd n vadr perm = Some habd'
            -> relate_RData f habd labd
            -> PAbQueue.high_level_invariant habd
            -> exists labd', PQueueInit.ptResv_spec labd n vadr perm = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold PAbQueue.ptResv_spec, PQueueInit.ptResv_spec, PQueueIntro.ptResv_Arg, PAbQueue.ptResv_Arg.
          unfold PAbQueue.palloc_spec, PQueueInit.palloc_spec.
          intros until f; exist_simpl.
        Qed.

        Lemma kctxt_new_exist:
          forall s habd habd' labd b b' ofs' n f,
            PAbQueue.kctxt_new_spec habd b b' ofs' = Some (habd', n)
            -> relate_RData f habd labd
            -> PAbQueue.high_level_invariant habd
            -> find_symbol s STACK_LOC = Some b
            -> (exists id, find_symbol s id = Some b') 
            -> inject_incr (Mem.flat_inj (genv_next s)) f
            -> exists labd', PQueueInit.kctxt_new_spec labd b b' ofs' = Some (labd', n) 
                             /\ relate_RData f habd' labd'.
        Proof.
          unfold PAbQueue.kctxt_new_spec, PQueueInit.kctxt_new_spec.
          intros until f; intros HP HR; inv HR.
          intros HH Hsys Hsys' Hincr.
          revert HP; subrewrite'; intros HQ; subdestruct; simpl.
          destruct a as [Hrange1 _]. 
          inv HQ. refine_split'; eauto 2.
          econstructor; eauto 2; simpl.
          unfold kctxt_inj in *; kctxt_inj_simpl.
          destruct Hsys' as [id Hsys'].
          eapply stencil_find_symbol_inject'; eauto.
          rewrite Int.add_zero; trivial.
          eapply stencil_find_symbol_inject'; eauto.
          rewrite Int.add_zero; trivial.          
        Qed.        
        
        Lemma kctxt_switch_exist:
          forall habd habd' labd n n' rs r' rs0 f,
            PAbQueue.kctxt_switch_spec 
              habd n n' (Pregmap.init Vundef)#ESP <- (rs#ESP)#EDI <- (rs#EDI)#ESI <- (rs#ESI)
              #EBX <- (rs#EBX)#EBP <- (rs#EBP)#RA <- (rs#RA) = Some (habd', rs0)
            -> relate_RData f habd labd
            -> PAbQueue.high_level_invariant habd
            -> (forall reg : PregEq.t,
                  val_inject f (Pregmap.get reg rs) (Pregmap.get reg r'))
            -> let  r'0 := ZMap.get n' (PQueueInit.kctxt labd) in
               exists labd', PQueueInit.kctxt_switch_spec 
                               labd n n' (Pregmap.init Vundef)#ESP <- (r'#ESP)#EDI <- (r'#EDI)#ESI <- (r'#ESI)
                               #EBX <- (r'#EBX)#EBP <- (r'#EBP)#RA <- (r'#RA) = Some (labd', r'0)
                             /\ relate_RData f habd' labd'
                             /\ (forall i r,
                                   ZtoPreg i = Some r -> val_inject f (rs0#r) (r'0#r))
                             /\ 0<= n' < num_proc.
        Proof.
          unfold PAbQueue.kctxt_switch_spec, PQueueInit.kctxt_switch_spec.
          intros until f. exist_simpl.
          kctxt_inj_simpl.
          unfold kctxt_inj, Pregmap.get in *; eauto. 
        Qed.

        Lemma trap_info_get_exist:
          forall habd labd z f,
            PAbQueue.trap_info_get_spec habd = z
            -> relate_RData f habd labd
            -> PQueueInit.trap_info_get_spec labd = z.
        Proof.
          unfold PQueueInit.trap_info_get_spec; unfold PAbQueue.trap_info_get_spec.
          intros. inv H0. congruence.
        Qed.*)

        Lemma real_data : forall abtcb abq tcb tdq, 
                            AbQ_RealQ (real_abtcb abtcb) (real_abq abq)
                                      (real_tcb tcb) (real_tdq tdq).
        Proof.
          constructor.
          * unfold abqueue_match_dllist, real_abq, real_tcb, real_tdq.
            intros qi l Hqi.
            rewrite !init_zmap_inside by omega.
            intro H; inv H.
            exists 64.
            exists 64.
            unfold abqueue_match_next_prev_rec.
            tauto.
          * unfold abtcbpool_tcbpool, real_abtcb, real_tcb.
            intros i tds inq Hi.
            rewrite !init_zmap_inside by assumption.
            intro H; inv H.
            exists 64.
            exists 64.
            reflexivity.
        Qed.

        Lemma tdqueue_init_exists :
          forall mbi_adr adt adt' ladt f,
            tdqueue_init0_spec (Int.unsigned mbi_adr) adt = Some adt'
            -> relate_RData f adt ladt
            -> exists ladt',
                 tdqueue_init_spec (Int.unsigned mbi_adr) ladt = Some ladt'
                 /\ relate_RData f adt' ladt'.
        Proof.
          unfold tdqueue_init_spec, tdqueue_init0_spec.
          intros until f. exist_simpl.
          apply real_data.
        Qed.

        (*Lemma thread_free_exists :
          forall n adt adt' ladt f,
            PAbQueue.thread_free_spec adt (Int.unsigned n) = Some adt'
            -> relate_RData f adt ladt
            -> PAbQueue.high_level_invariant adt
            -> exists ladt',
                 PQueueInit.thread_free_spec ladt (Int.unsigned n) = Some ladt'
                 /\ relate_RData f adt' ladt'.
        Proof.
          unfold PQueueInit.thread_free_spec, PAbQueue.thread_free_spec.
          intros. inv H0. subrewrite'. rename H1 into INV.
          caseEq (pe adt); intros HIP; rewrite HIP in *; contra_inv.
          caseEq (ikern adt); intros HIK; rewrite HIK in *; contra_inv.
          caseEq (ihost adt); intros HIH; rewrite HIH in *; contra_inv.
          caseEq (ipt adt); intros HIT; rewrite HIT in *; contra_inv.
          
          assert (Hvalid_abq: abqueue_valid_Q (PAbQueue.abq adt)). 
          {
            inversion INV.
            unfold abqueue_valid_Q.
            intros i Hi. 
            destruct (valid_TDQ HIP i Hi).
            destruct H0.
            exists x; trivial.
          }

          assert (Hvalid_abtcb: abqueue_valid_abtcb (PAbQueue.abtcb adt)). 
          {
            inversion INV.
            unfold abqueue_valid_abtcb.
            intros i Hi. 
            destruct (valid_TCB HIP i Hi).
            destruct H0.
            destruct H0.
            exists x, x0; trivial.
          }

          assert (Habq_abtcb: abqueue_abq_mapto_abtcb (PAbQueue.abtcb adt) 
                                                      (PAbQueue.abq adt)). 
          {
            inversion INV.
            unfold abqueue_abq_mapto_abtcb.
            intros i Hi.
            destruct (valid_TCB HIP i Hi) as [s [inq [Hget Hinq]]].
            exists s, inq.
            split; trivial.
            omega.
          }

          assert (Hvalid_count: abqueue_valid_count (PAbQueue.abtcb adt) 
                                                    (PAbQueue.abq adt)). 
          {
            inversion INV.
            unfold abqueue_valid_count.
            eapply (valid_count HIP); eauto.
          }

          assert (Hvalid_inQ: abqueue_valid_inQ (PAbQueue.abtcb adt) 
                                                (PAbQueue.abq adt)). 
          {
            inversion INV.
            unfold abqueue_valid_inQ.
            apply (valid_inQ HIP).
          }

          assert (Hvalid_notinQ': abqueue_notinQ (PAbQueue.abtcb adt) (PAbQueue.abq adt)). 
          {
            apply abqueue_INV_implies_notinQ; trivial.
          }
          destruct (zlt 0 (Int.unsigned n)); contra_inv.
          destruct (zlt (Int.unsigned n) num_proc); contra_inv.
          caseEq (ZMap.get (Int.unsigned n) (pb adt)); intro Hget; 
          rewrite Hget in H; contra_inv.
          caseEq (ZMap.get (Int.unsigned n) (abtcb adt)); 
            [intro Hgetn | intros tds inQ Hgetn]; rewrite Hgetn in H;
            contra_inv.
          caseEq (zeq inQ (-1)); intros HinQ HinQ'; rewrite HinQ' in H; contra_inv.
          clear HinQ'.
          refine_split'; eauto.
          inv H; econstructor; eauto 2; simpl.
          constructor.
          - intros qi l' Hqi Hget'.
            inv abq_re0.
            rename H0 into Habtcb.
            unfold abqueue_match_dllist in H.
            destruct (H _ _ Hqi Hget') as [hd [tl [HLget H1]]].
            exists hd; exists tl.
            split; auto.
            assert (~ In (Int.unsigned n) l').
            {
              eapply Hvalid_notinQ'; eauto.
              split; trivial. omega.
            }
            apply match_next_prev_presv_set_notin; eauto.
          - inv abq_re0.
            unfold abtcbpool_tcbpool in *.
            intros i tds0 inq Hi H1.
            destruct (zeq i (Int.unsigned n)); subst.
            + rewrite ZMap.gss in *.
              inv H1. refine_split'; trivial.
            + rewrite ZMap.gso in *; eauto.
        Qed.*)

        Lemma get_state_exists :
          forall n i adt ladt f,
            get_state0_spec (Int.unsigned n) adt = Some i
            -> relate_RData f adt ladt
            -> get_state_spec (Int.unsigned n) ladt = Some i.
        Proof.
          unfold get_state_spec, get_state0_spec; 
          intros. inv H0. revert H. subrewrite. subdestruct.
          destruct (ZMap.get (Int.unsigned n) (abtcb adt)) eqn: Hget; contra_inv.
          inv Hdestruct4. inv HQ.
          inv abq_re0.
          unfold abtcbpool_tcbpool in H0.
          apply H0 in Hget; try omega.
          destruct Hget as [pv [nx HT]].
          rewrite HT. trivial.
        Qed.

        Lemma match_next_prev_presv_set_state : 
          forall start ending hd tl l itcbp,
            abqueue_match_next_prev_rec l ending hd tl start itcbp
            -> forall i tds pv nx, 
                 ZMap.get i itcbp = TCBValid tds pv nx
                 -> forall tds', abqueue_match_next_prev_rec l ending hd tl start (ZMap.set i (TCBValid tds' pv nx) itcbp).
        Proof.
          clear.
          intros start ending hd tl l itcbp Hitcbp.
          assert (forall start tl, 
                    abqueue_match_next_prev_rec l ending hd tl start itcbp
                    -> forall i tds prev next, 
                         ZMap.get i itcbp = TCBValid tds prev next
                         -> forall tds', abqueue_match_next_prev_rec l ending hd tl start
                                                                     (ZMap.set i (TCBValid tds' prev next) itcbp)).
          clear Hitcbp.
          induction l; simpl in *.
          intros; trivial.
          
          intros.
          destruct l.
          destruct H as [Hhd [Htl [st Hst]]].
          split; trivial.
          split; trivial.
          rewrite ZMap.gsspec.
          unfold ZIndexed.eq.
          destruct (zeq a i); trivial.
          subst i.
          rewrite H0 in Hst.
          inversion Hst.
          subst tds prev next.
          exists tds'; trivial.
          exists st; trivial.
          (* induction step *)
          destruct H.
          split; trivial.
          destruct H1 as [st [pv' [Hget H1]]].
          rewrite ZMap.gsspec.
          unfold ZIndexed.eq.
          destruct (zeq a i); trivial.
          subst i.
          rewrite Hget in H0.
          inversion H0.
          subst tds prev next.
          exists tds'; exists pv'.
          split; trivial.
          eapply IHl; eauto.
          rewrite Hget.
          exists st, pv'.
          split; trivial.
          eapply IHl; eauto.
          intros.
          eapply H; eauto.
        Qed.

        Lemma set_state_exists: 
          forall f n ts adt adt' ladt, 
            set_state0_spec (Int.unsigned n) ts adt = Some adt'
            -> relate_RData f adt ladt
            -> exists ladt', 
                 set_state_spec (Int.unsigned n) ts ladt = Some ladt'
                 /\ relate_RData f adt' ladt'.
        Proof.
          intros f n ts adt adt' ladt HQ H.
          inversion_clear H. 
          revert HQ.
          unfold set_state0_spec, set_state_spec.
          subrewrite.
          subdestruct.
          destruct (ZMap.get (Int.unsigned n) (abtcb adt)) eqn:Hgetn; contra_inv.
          assert (Hget' : exists pv nx,
                            ZMap.get (Int.unsigned n) (tcb ladt) 
                            = TCBValid tds pv nx).
          {
            inv abq_re0.
            unfold abtcbpool_tcbpool in H0. inv Hdestruct5.
            apply H0 with inQ; trivial.
          }
          destruct Hget' as [pv [nx Hget']].
          rewrite Hget'.
          destruct (ZtoThreadState ts); contra_inv.
          eexists. 
          split; eauto.              
          inv HQ.  constructor; eauto; simpl.
          inv abq_re0.
          constructor; trivial.
          - simpl in * .
            intros qi l' Hqi Hgetl'.
            destruct (H _ _ Hqi Hgetl') as [hd [tl [HgetQ Hx]]].
            exists hd; exists tl.
            split; trivial.
            apply match_next_prev_presv_set_state with tds; trivial.
          - unfold abtcbpool_tcbpool in * .
            simpl in * .
            intros i tds' inq Hi HT.
            destruct (zeq i (Int.unsigned n)); subst.
            + rewrite ZMap.gss in *. inv HT.
              refine_split'; eauto.
            + rewrite ZMap.gso in *; eauto.
        Qed.

        Section Lists_Ext.

          Variable A: Type.

          Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

          Ltac eq_dec_simpl :=
            let Heq := fresh "Heq" in
            let Hneq := fresh "Hneq" in
            match goal with 
              | H: _ |- context [ eq_dec ?z ?z ] => destruct (eq_dec z z) as [Heq | Hneq]
                                                    ; [ | destruct (Hneq (refl_equal _))]
              | H: context [ eq_dec ?z ?z ] |- _  => destruct (eq_dec z z) as [Heq | Hneq]
                                                     ; [ | destruct (Hneq (refl_equal _))]

              | H : ?z = ?z' |- context [ eq_dec ?z ?z' ] => destruct (eq_dec z z') as [ _ | Hneq ]
                                                             ; [ | destruct (Hneq H) ]
              | H : ?z = ?z',
                    H1 : context [ eq_dec ?z ?z' ] |- _ => destruct (eq_dec z z') as [ _ | Hneq]
                                                           ; [ | destruct (Hneq H) ]

              | H : ?z = ?z' |- context [ eq_dec ?z' ?z ] => destruct (eq_dec z' z) as [ _ | Hneq ]
                                                             ; [ | destruct (Hneq (eq_sym H)) ]
              | H : ?z = ?z',
                    H1 : context [ eq_dec ?z' ?z ] |- _ => destruct (eq_dec z' z) as [ _ | Hneq]
                                                           ; [ | destruct (Hneq (eq_sym H)) ]

              | H : ?z <> ?z' |- context [ eq_dec ?z ?z' ] => destruct (eq_dec z z') as [Heq | _ ]
                                                              ; [ destruct (H Heq) | ]

              | H : ?z <> ?z',
                    H1 : context [ eq_dec ?z ?z' ] |- _ => destruct (eq_dec z z') as [Heq | _ ]
                                                           ; [ destruct (H Heq) | ]

              | H : ?z <> ?z' |- context [ eq_dec ?z' ?z ] => destruct (eq_dec z' z) as [Heq | _ ]
                                                              ; [ destruct (H (eq_sym Heq)) | ]

              | H : ?z <> ?z',
                    H1 : context [ eq_dec ?z' ?z ] |- _ => destruct (eq_dec z' z) as [Heq | _ ]
                                                           ; [ destruct (H (eq_sym Heq)) | ]

              | H :  context [ eq_dec ?z ?z' ] |- _ => destruct (eq_dec z z') as [Heq | Hneq ]
              | H : _ |- context [ eq_dec ?z ?z' ] => destruct (eq_dec z z') as [Heq | Hneq ]

            end.

          Let count_occ := count_occ eq_dec.

          Lemma count_occ_zero_notin:
            forall (l : list A) (x : A),
              count_occ l x = 0%nat 
              -> ~ In x l.
          Proof.
            induction l; simpl; auto.
            intros x Hx.
            destruct (eq_dec a x) as [ Heq | Hneq ].
            subst a.
            discriminate.
            intro H.
            destruct H.
            destruct (Hneq H).
            apply (IHl _ Hx); trivial.
          Qed.

          Lemma count_occ_notin_zero:
            forall (l : list A) (x : A),
              ~ In x l
              -> count_occ l x = 0%nat.
          Proof.
            induction l; simpl; auto.
            intros x Hx.
            destruct (eq_dec a x) as [ Heq | Hneq ].
            subst a.
            apply False_ind. 
            apply Hx.
            left; trivial.
            apply IHl.
            intro HF.
            apply Hx.
            right; trivial.
          Qed.

          Lemma count_occ_plus_app:
            forall (l1 l2 : list A) (x : A),
              count_occ (l1 ++ l2) x = (count_occ l1 x + count_occ l2 x) % nat.
          Proof.
            induction l1; simpl; auto.
            intros l2 x.
            destruct (eq_dec a x) as [ Heq | Hneq ].
            subst a.
            assert (forall n m, Datatypes.S n + m = Datatypes.S (n + m))%nat.
            clear.
            intros n m.
            omega.
            rewrite H.
            rewrite IHl1.
            trivial.
            rewrite IHl1; trivial.
          Qed.

          Lemma count_occ_app_plus :
            forall (l1 l2 : list A) (x : A) (m n : nat),
              count_occ (l1 ++ l2) x = (m + n) % nat
              -> count_occ l2 x = n
              -> count_occ l1 x = m.
          Proof.
            intros l1 l2 x m n Hplus H.
            rewrite count_occ_plus_app in Hplus.
            rewrite H in Hplus.
            rewrite plus_comm in Hplus.
            rewrite (plus_comm m n) in Hplus.
            rewrite (plus_reg_l _ _ _ Hplus).
            trivial.
          Qed.

          Lemma count_occ_app_plus' :
            forall (l1 l2 : list A) (x : A) (m n : nat),
              count_occ (l1 ++ l2) x = (m + n) % nat
              -> count_occ l1 x = m
              -> count_occ l2 x = n.
          Proof.
            intros l1 l2 x m n Hplus H.
            rewrite count_occ_plus_app in Hplus.
            rewrite H in Hplus.
            rewrite (plus_reg_l _ _ _ Hplus).
            trivial.
          Qed.

          Lemma count_occ_app_r :
            forall (l1 l2 : list A) (x : A) (n : nat),
              count_occ (l1 ++ l2) x = n % nat
              -> count_occ l2 x = n
              -> count_occ l1 x = 0%nat.
          Proof.
            intros l1 l2 x n Hplus H.
            rewrite count_occ_plus_app in Hplus.
            rewrite H in Hplus.
            omega. 
          Qed.

          Lemma count_occ_plus_cons:
            forall (l: list A) t t',
              count_occ (t :: l) t' = (count_occ (t :: nil) t' + count_occ l t')%nat.
          Proof.
            intros.
            assert (t :: l = (t::nil) ++ l).
            simpl; trivial.
            rewrite H.
            rewrite count_occ_plus_app.
            trivial.
          Qed.

          Lemma count_occ_sig_one: 
            forall t,
              count_occ (t :: nil) t = 1%nat.
          Proof.
            intros.
            simpl.
            eq_dec_simpl; trivial.
          Qed.

          Lemma count_occ_sig_zero: 
            forall t t',
              t <> t'
              -> count_occ (t :: nil) t' = 0%nat.
          Proof.
            intros.
            simpl.
            eq_dec_simpl; trivial.
          Qed.

          Lemma count_occ_1_mid_elim :
            forall (l : list A) l' z t,
              count_occ l t = 1%nat
              -> l = z :: l'
              -> z <> t
              -> (exists l'' tl, l = l'' ++ (tl :: nil) /\ tl <> t)
              -> (exists l' l'', l = l' ++ (t::nil) ++ l'' 
                                 /\ l' <> nil /\ count_occ l' t = 0%nat
                                 /\ l'' <> nil /\ count_occ  l'' t = 0%nat).
          Proof.
            induction l.

            intros.
            inversion H0.

            intros.
            destruct l.
            destruct l'.

            simpl in H.
            eq_dec_simpl.
            subst a.
            destruct H2 as [l'' [tl [Htl Htl']]].
            elimtype False.
            apply Htl'.
            clear Htl'.
            generalize t tl Htl.
            clear.
            rename l'' into l.
            induction l.
            simpl.
            intros.
            inversion Htl.
            trivial.
            intros.
            simpl in Htl.
            inversion Htl.
            destruct (app_cons_not_nil _ _ _ H1).

            inversion H.

            destruct l'.
            
            inversion H0.
            inversion H0.

            assert (z = a).
            inversion H0; trivial.
            subst a.
            destruct (eq_dec a0 t).
            subst a0.
            destruct l.
            destruct H2 as [l'' [tl [Htl Htl']]].
            assert (z :: t :: nil = (z ::nil) ++ (t::nil)).
            rewrite <- app_comm_cons.
            simpl; trivial.
            rewrite H2 in Htl.
            destruct (app_inj_tail _ _ _ _ Htl).
            subst t.
            destruct (Htl' (refl_equal _)).
            destruct H2 as [l'' [tl [H2 Htl]]].
            exists (z::nil), (a::l).
            split.
            simpl.
            trivial.
            split.
            intro HF.
            inversion HF.
            split.
            simpl.
            eq_dec_simpl.
            trivial.
            split.
            intro HF.
            inversion HF.
            apply count_occ_app_plus' with (z::t::nil) 1%nat.
            rewrite <- app_comm_cons.
            unfold app.
            rewrite H.
            simpl; trivial.
            simpl.
            eq_dec_simpl.
            eq_dec_simpl.
            trivial.
            assert (count_occ (a0 :: l) t = 1%nat).
            apply count_occ_app_plus' with (z::nil) 0%nat.
            unfold app.
            rewrite H.
            simpl; trivial.
            simpl.
            eq_dec_simpl.
            trivial.
            destruct H2 as [l'' [tl [Htl Htl']]].
            destruct l'' as [ | x l''].
            simpl in Htl.
            inversion Htl.
            assert (exists l''' tl, a0 :: l = l''' ++ tl :: nil /\ tl <> t).
            exists l'', tl.
            split.
            rewrite <- app_comm_cons in Htl.
            inversion Htl.
            trivial.
            trivial.
            destruct l'.
            inversion H0.
            assert (a0 = a).
            inversion H0.
            trivial.
            subst a0.
            assert (a :: l = a :: l').
            inversion H0; trivial.
            destruct (IHl _ _ _ H3 H4 n H2) as [l1 [l2 [Hl [Hl1 [Hl1t [Hl2 Hl2t]]]]]].
            exists (z::l1), l2.
            split.
            rewrite Hl.
            rewrite <- app_comm_cons.
            simpl.
            trivial.
            split.
            intro HF; inversion HF.
            split.
            simpl.
            eq_dec_simpl.
            trivial.
            split.
            trivial.
            trivial.
          Qed.

          Lemma app_tail_dec : 
            forall (l : list A),
              l = nil \/ exists l', exists tl, l = l' ++ (tl :: nil).
          Proof.
            intros.
            destruct l.
            left; trivial.
            right.
            exists (removelast (a::l)), (last (a::l) a).
            rewrite <- app_removelast_last; trivial.
            intro HF.
            discriminate.
          Qed.

          Lemma count_occ_1_elim :
            forall (l : list A) t,
              count_occ l t = 1%nat
              -> (l = t ::nil)
                 \/ (exists l', l = t::l' /\ l' <> nil /\ count_occ l' t = 0%nat)
                 \/ (exists l', l = l'++ (t::nil) /\ l' <> nil /\ count_occ l' t = 0%nat)
                 \/ (exists l' l'', l = l' ++ (t::nil) ++ l'' 
                                    /\ l' <> nil /\ count_occ l' t = 0%nat
                                    /\ l'' <> nil /\ count_occ l'' t = 0%nat).
          Proof.
            intros l t Hocc.
            generalize Hocc; intro Hocc'.
            destruct l.
            simpl in Hocc.
            inversion Hocc.
            destruct l.
            simpl in Hocc.
            destruct (eq_dec a t).
            subst a; left; trivial.
            inversion Hocc.
            simpl in Hocc.
            destruct (eq_dec a t).
            subst t.
            destruct (eq_dec a0 a).
            subst a0.
            simpl in Hocc.
            inversion Hocc.
            inversion Hocc.
            right; left.
            exists (a0::l).
            split; trivial.
            split.
            intro HF; inversion HF.
            simpl.
            eq_dec_simpl.
            trivial.
            eq_dec_simpl.
            inversion Hocc.
            destruct l as [ | z1 l].
            right.
            right.
            left.
            exists (a ::nil).
            split.
            rewrite <- app_comm_cons.
            simpl.
            subst t.
            trivial.
            split.
            intro HF.
            inversion HF.
            rewrite H0.
            simpl.
            eq_dec_simpl.
            trivial.
            subst a0.
            right; right; right.
            exists (a::nil), (z1::l).
            split.
            rewrite <- app_comm_cons.
            simpl.
            trivial.
            split.
            intro HF.
            inversion HF.
            split.
            rewrite H0.
            simpl.
            eq_dec_simpl.
            trivial.
            split.
            intros HF.
            inversion HF.
            trivial.
            destruct (app_tail_dec (a :: a0 :: l)).
            inversion H.
            destruct H as [l' [tl Hl']].
            destruct (eq_dec t tl) as [Hteq | Htneq].
            subst tl.
            right.
            right.
            left.
            rewrite Hl'.
            exists l'.
            split; trivial.
            split.
            intros HF.
            subst l'.
            simpl in Hl'.
            inversion Hl'.
            apply count_occ_app_plus with (t::nil) 1%nat.
            simpl.
            rewrite <- Hl'.
            trivial.
            simpl.
            eq_dec_simpl.
            trivial.
            right.
            right.
            right.
            eapply count_occ_1_mid_elim; eauto.
          Qed.

          Lemma last_nil : forall (l : list A) (x0 : A), 
                             last l x0 = x0
                             -> (forall x, In x l -> x <> x0)
                             -> l = nil.
          Proof.
            intros  l x0 Hlast H.
            assert (forall t l', l = t::l' -> False).
            intros.
            assert (l <> nil).
            intro HF.
            rewrite H0 in HF.
            discriminate.
            rewrite (app_removelast_last x0) in H; trivial.
            apply (H x0); trivial.
            rewrite Hlast.
            apply in_or_app.
            right; simpl; trivial.
            left; trivial.
            destruct l.
            trivial.
            elimtype False.
            destruct (eq_dec a x0).
            apply H with a; trivial.
            simpl; trivial.
            left; trivial.
            apply H0 with a l; trivial.
          Qed.

          Lemma last_In : forall (l : list A) (x x0 : A), 
                            last l x0 = x
                            -> In x l \/ x = x0.
          Proof.
            intros l x x0 Hlast.
            destruct (eq_dec x x0).
            right; trivial.
            left.
            induction l.
            simpl in Hlast.
            subst x0.
            destruct (n (refl_equal _)).

            simpl in *.
            destruct l.
            left; trivial.
            right; auto.
          Qed.

          Lemma last_In' : forall (l : list A) (x0 : A), 
                             last l x0 <> x0
                             -> In (last l x0) l.
          Proof.
            intros.
            destruct (last_In _ _ _ (refl_equal (last l x0))).
            trivial.
            destruct (H H0).
          Qed.

          Lemma removelast_dec : forall (l:list A), 
                                   removelast l = nil \/ removelast l <> nil.
          Proof.
            intros.
            destruct (removelast l).
            simpl.
            left; trivial.
            right.
            intro H.
            discriminate.
          Qed.

          Lemma last_app : forall (l l': list A) x0,
                             l' <> nil
                             -> last (l ++ l') x0 = last l' x0.
          Proof.
            induction l; simpl; auto.
            destruct l.
            intros.
            simpl in * .
            destruct l'.
            destruct (H (refl_equal _)).
            trivial.
            intros.
            rewrite <- app_comm_cons.
            apply IHl; trivial.
          Qed.

          Let remove := remove eq_dec.

          Lemma remove_count_occ_neq:
            forall l x y, y <> x -> count_occ (remove x l) y = count_occ l y.
          Proof.
            intros.
            induction l.
            simpl.
            trivial.
            simpl.
            destruct (eq_dec x a).
            destruct (eq_dec a y).
            subst.
            destruct (H (refl_equal _)).
            trivial.
            destruct (eq_dec a y).
            subst.
            unfold count_occ in * .
            rewrite count_occ_cons_eq; trivial.
            rewrite IHl.
            trivial.
            unfold count_occ in * .
            rewrite count_occ_cons_neq; auto.
          Qed.

          Lemma count_occ_remove_neq:
            forall l x, count_occ l x = 0%nat -> remove x l = l.
          Proof.
            induction l.
            simpl; trivial.
            simpl.
            intros x H.
            destruct (eq_dec x a).
            subst a.
            destruct (eq_dec x x) as [ _ | Hneq ]; [ | destruct (Hneq (refl_equal _))].
            discriminate.
            destruct (eq_dec a x) as [ Heq | Hneq ].
            subst a.
            destruct (n (refl_equal _)).
            rewrite IHl; trivial.
          Qed.

          Lemma remove_app:
            forall l l' x, remove x (l++l') = remove x l ++ remove x l'.
          Proof.
            induction l.
            simpl; trivial.
            simpl.
            intros l' x.
            destruct (eq_dec x a).
            subst a.
            trivial.
            rewrite IHl; trivial.
          Qed.

          Lemma remove_sig_eq : 
            forall x,
              remove x (x :: nil) = nil.
          Proof.
            intros.
            simpl.
            eq_dec_simpl; trivial.
          Qed.

          Lemma remove_sig_neq : 
            forall x x',
              x <> x'
              -> remove x (x' :: nil) = (x' :: nil).
          Proof.
            intros.
            simpl; eq_dec_simpl; trivial.
          Qed.

          Lemma remove_cons_eq : 
            forall x l,
              remove x (x :: l) = remove x l.
          Proof.
            intros.
            simpl; eq_dec_simpl; trivial.
          Qed.

          Lemma remove_cons_neq : 
            forall x x' l,
              x <> x'
              -> remove x (x' :: l) = x' :: remove x l.
          Proof.
            intros.
            simpl; eq_dec_simpl; trivial.
          Qed.

          Lemma remove_neq : 
            forall x l,
              ~ In x l
              -> remove x l = l.
          Proof.
            intros.
            apply count_occ_notin_zero in H.
            apply count_occ_remove_neq; trivial.
          Qed.

          Lemma remove_removelast : 
            forall l x0,
              (forall x, In x l -> count_occ l x = 1%nat)
              -> In (last l x0) l
              -> remove (last l x0) l = removelast l.
          Proof.
            intros l x0 Hocc Hin.
            destruct l.
            destruct (in_nil Hin).
            assert ((a::l) = removelast (a::l) ++ last (a :: l) x0 :: nil).
            assert (a::l <> nil).
            intro HF.
            discriminate.
            rewrite <- (app_removelast_last x0 H). 
            trivial.
            set (e := last (a :: l) x0) in * .
            assert (count_occ (a::l) e = 1%nat).
            apply Hocc; trivial.
            rewrite H.
            rewrite H in H0.
            rewrite count_occ_plus_app in H0.
            assert (count_occ (e :: nil) e = 1%nat).
            simpl.
            destruct (eq_dec e e) as [_|Hneq]; [|destruct (Hneq (refl_equal _))].
            trivial.
            rewrite H1 in H0.
            assert (count_occ (removelast (a :: l)) e = 0%nat).
            destruct (count_occ (removelast (a :: l)) e); trivial.
            rewrite plus_comm in H0. 
            simpl in H0.
            discriminate.
            assert (e ::nil <> nil).
            intro HF.
            discriminate.
            rewrite removelast_app; trivial.
            rewrite remove_app; trivial.
            rewrite count_occ_remove_neq; trivial.
            assert (remove e (e :: nil) = removelast (e::nil)).
            simpl.
            destruct (eq_dec e e) as [_ | Hneq ]; [ | destruct (Hneq (refl_equal _))].
            trivial.
            rewrite H4; trivial.
          Qed.

          Lemma removelast_notnil : 
            forall (l : list A),
              removelast l <> nil 
              -> exists t t' l'', l = l'' ++ (t' :: t :: nil).
          Proof.
            induction l.
            simpl.
            intros.
            destruct (H (refl_equal _)).
            intros.
            simpl in H.
            destruct l.
            destruct (H (refl_equal _)).
            simpl in H.
            destruct l.
            exists a0, a, nil.
            rewrite app_nil_l.
            trivial.
            assert (removelast (a0 :: a1 :: l) <> nil).
            assert (a0 :: a1 :: l = (a0::nil) ++ a1 ::l).
            simpl.
            trivial.
            rewrite H0.
            rewrite removelast_app.
            simpl.
            intro HF.
            discriminate.
            intro HF.
            discriminate.
            destruct IHl as [t [t' [l'' IH]]]; trivial.
            exists t, t',(a::l'').
            rewrite IH.
            rewrite app_comm_cons.
            trivial.
          Qed.

          Lemma removelast_last_singleton : 
            forall (l: list A) x0,
              last l x0 <> x0
              -> removelast l = nil
              -> exists x, l = x::nil /\ last l x0 = x.
          Proof.
            intros l x0 Hlast Hrm.
            assert (H:= last_In' l _ Hlast).
            destruct l.
            simpl in H.
            destruct H.
            simpl in Hrm.
            destruct l.
            exists a; trivial.
            split; trivial.
            discriminate.
          Qed.                                    

        End Lists_Ext.

        Lemma match_prev_next_intro_tail: 
          forall l start ending l' tcb hd tl st hd',
            l = l' ++ hd :: nil
            -> l' <> nil
            -> abqueue_match_next_prev_rec l' hd hd' tl start tcb
            -> ZMap.get hd tcb = TCBValid st ending hd'
            -> abqueue_match_next_prev_rec l ending hd tl start tcb.
        Proof.
          induction l.
          simpl; auto.
          intros.
          assert (l' ++ hd :: nil = nil).
          auto.
          destruct (app_eq_nil _ _ H3).
          discriminate.
          intros.
          destruct l.
          assert (a = hd /\ l' = nil).
          assert (a :: nil = nil ++ a :: nil).
          rewrite app_nil_l.
          trivial.
          rewrite H3 in H.
          destruct (app_inj_tail _ _ _ _ H).
          split; trivial.
          rewrite H4; trivial.
          destruct H3.
          destruct (H0 H4).
          destruct l' as [ | a' l'].
          destruct (H0 (refl_equal _)).
          rewrite <- app_comm_cons in H.
          inversion H; subst a'; clear H.
          assert (l' = nil \/ exists a' l'', l' = a' :: l'').
          destruct l'.
          left; trivial.
          right.
          exists z0, l'.
          trivial.
          destruct H as [H | H].
          (* l' = nil *)
          subst l'.
          simpl in H1.
          assert (
              (tl = a /\ exists st, exists prev,
                                      ZMap.get a tcb = TCBValid st prev start
                                      /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)
              -> abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb ).
          simpl.
          trivial.
          apply H.
          clear H.
          destruct H1 as [Hhd' [Htl [st' H1]]].
          split; trivial.
          exists st', hd.
          split; trivial.
          simpl in H5.
          inversion H5.
          subst z l.
          simpl.
          split; trivial.
          split; trivial.
          subst hd'.
          exists st; trivial.
          (* l' = not nil *)
          destruct l'.
          destruct H as [a' [l'' H]].
          discriminate.
          clear H.
          rename z0 into a'.
          clear H0.
          assert ( (tl = a /\ exists st, exists prev,
                                           ZMap.get a tcb = TCBValid st prev start
                                           /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)
                   -> abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb ).
          simpl.
          trivial.
          apply H.
          clear H.
          assert (abqueue_match_next_prev_rec (a :: a' :: l') hd hd' tl start tcb
                  -> (tl = a /\ exists st, exists prev,
                                             ZMap.get a tcb = TCBValid st prev start
                                             /\ abqueue_match_next_prev_rec (a' :: l') hd hd' prev a tcb)).
          simpl.
          trivial.
          destruct (H H1) as [Htl [st' [pv [Hgeta Hm]]]].
          clear H H1.
          split; trivial.
          exists st', pv.
          split; trivial.
          eapply IHl; eauto.
          intro HF.
          discriminate.
        Qed.

        Lemma match_prev_next_elim3 : 
          forall l t ending hd tl starting tcb,
            abqueue_match_next_prev_rec (t :: l) ending hd tl starting tcb 
            -> l <> nil
            -> (tl = t /\ exists st, exists prev,
                                       ZMap.get t tcb = TCBValid st prev starting
                                       /\ abqueue_match_next_prev_rec l ending hd prev t tcb).
        Proof.
          simpl; intros; trivial.
          destruct l.
          destruct (H0 (refl_equal _)).
          trivial.
        Qed.                                

        Lemma match_prev_next_intro3 : 
          forall l t ending hd tl starting tcb,
            l <> nil
            -> (tl = t /\ exists st, exists prev,
                                       ZMap.get t tcb = TCBValid st prev starting
                                       /\ abqueue_match_next_prev_rec l ending hd prev t tcb)
            -> abqueue_match_next_prev_rec (t :: l) ending hd tl starting tcb.
        Proof.
          simpl; intros; trivial.
          destruct l.
          destruct (H (refl_equal _)).
          trivial.
        Qed.

        Lemma match_next_prev_intro_tail: 
          forall l l' i start ending tcb hd tl,
            l = l' ++ i :: nil
            -> l' <> nil
            -> (exists hd', 
                  hd = i
                  /\ abqueue_match_next_prev_rec l' hd hd' tl start tcb
                  /\ exists st, ZMap.get hd tcb = TCBValid st ending hd')
            -> abqueue_match_next_prev_rec l ending hd tl start tcb.
        Proof.
          induction l.
          simpl; auto.
          intros.
          assert (l' ++ i :: nil = nil).
          auto.
          destruct (app_eq_nil _ _ H2).
          discriminate.
          intros.
          destruct l.
          assert (a = hd /\ l' = nil).
          simpl in H1.
          destruct H1.
          destruct H1.
          assert (a :: nil = nil ++ a :: nil).
          rewrite app_nil_l.
          trivial.
          rewrite H3 in H.
          subst hd.
          destruct (app_inj_tail _ _ _ _ H).
          split; trivial.
          rewrite H1; trivial.
          destruct H2.
          destruct (H0 H3).
          destruct l' as [ | a' l'].
          destruct (H0 (refl_equal _)).
          rewrite <- app_comm_cons in H.
          inversion H; subst a'; clear H.
          assert (l' = nil \/ exists a' l'', l' = a' :: l'').
          destruct l'.
          left; trivial.
          right.
          exists z0, l'.
          trivial.
          destruct H as [H | H].
          (* l' = nil *)
          subst l'.
          assert ((tl = a /\ exists st, exists prev,
                                          ZMap.get a tcb = TCBValid st prev start
                                          /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)
                  -> abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb).
          simpl.
          trivial.
          apply H.
          clear H.
          simpl in H4.
          inversion H4.
          subst z l.
          destruct H1 as [hd' [Hhd [Hpv [st Hget]]]].
          simpl.
          subst hd.
          simpl in Hpv.
          destruct Hpv as [Hhd' [Htl [st' Hx]]].
          split; trivial.
          exists st', i.
          split; trivial.
          split; trivial.
          split; trivial.
          subst hd'.
          exists st; trivial.
          (* l' = not nil *)
          destruct l'.
          destruct H as [a' [l'' H]].
          discriminate.
          clear H.
          rename z0 into a'.
          clear H0.
          assert ((tl = a /\ exists st, exists prev,
                                          ZMap.get a tcb = TCBValid st prev start
                                          /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)
                  -> abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb).
          simpl.
          trivial.
          apply H.
          clear H.
          destruct H1 as [hd' [Hhd [Hm Hx]]].
          apply match_prev_next_elim3 in Hm.
          destruct Hm as [Htl [st [pv [Hgeta Hm]]]].
          subst hd tl.
          split; trivial.
          exists st, pv.
          split; trivial.
          apply IHl with (a' :: l') i; trivial.
          intro HF; discriminate HF.
          exists hd'.
          split; trivial.
          split; trivial.
          intro HF; discriminate HF.
        Qed.  

        Lemma match_next_prev_elim_tail: 
          forall l l' i start ending tcb hd tl,
            l = l' ++ i :: nil
            -> l' <> nil
            -> abqueue_match_next_prev_rec l ending hd tl start tcb
            -> exists hd', 
                 hd = i
                 /\ abqueue_match_next_prev_rec l' hd hd' tl start tcb
                 /\ exists st, ZMap.get hd tcb = TCBValid st ending hd'.
        Proof.
          induction l.
          simpl; auto.
          intros.
          assert (l' ++ i :: nil = nil).
          auto.
          destruct (app_eq_nil _ _ H2).
          discriminate.
          intros.
          destruct l.
          assert (a = hd /\ l' = nil).
          simpl in H1.
          destruct H1.
          assert (a :: nil = nil ++ a :: nil).
          rewrite app_nil_l.
          trivial.
          subst a.
          rewrite H3 in H.
          destruct (app_inj_tail _ _ _ _ H).
          split; trivial.
          rewrite H1; trivial.
          destruct H2.
          destruct (H0 H3).
          destruct l' as [ | a' l'].
          destruct (H0 (refl_equal _)).
          rewrite <- app_comm_cons in H.
          inversion H; subst a'; clear H.
          assert (l' = nil \/ exists a' l'', l' = a' :: l'').
          destruct l'.
          left; trivial.
          right.
          exists z0, l'.
          trivial.
          destruct H as [H | H].
          (* l' = nil *)
          subst l'.
          assert (abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb
                  -> (tl = a /\ exists st, exists prev,
                                             ZMap.get a tcb = TCBValid st prev start
                                             /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)).
          simpl.
          trivial.
          apply H in H1.
          clear H.
          simpl in H4.
          inversion H4.
          subst z l.
          destruct H1 as [Htl [st' [pv [H1 H2]]]].
          simpl in H2.
          destruct H2 as [Hhd [Hpv Hget]].
          simpl.
          subst hd pv.
          exists a.
          split; trivial.
          split; trivial.
          split; trivial.
          split; trivial.
          exists st'; trivial.
          (* l' = not nil *)
          destruct l'.
          destruct H as [a' [l'' H]].
          discriminate.
          clear H.
          rename z0 into a'.
          clear H0.
          assert (abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb
                  -> (tl = a /\ exists st, exists prev,
                                             ZMap.get a tcb = TCBValid st prev start
                                             /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)).
          simpl.
          trivial.
          apply H in H1.
          clear H.
          destruct H1 as [Htl [st' [pv [Hgeta Hm]]]].
          assert (a' :: l' <> nil).
          intro HF.
          discriminate.
          destruct (IHl _ _ _ _ _ _ _ H4 H Hm) as [hd' [Hx [Hy Hz]]].
          exists hd'.
          assert ((tl = a /\ exists st, exists prev,
                                          ZMap.get a tcb = TCBValid st prev start
                                          /\ abqueue_match_next_prev_rec (a' :: l') hd hd' prev a tcb)
                  -> abqueue_match_next_prev_rec (a :: a' :: l') hd hd' tl start tcb).
          simpl.
          trivial.
          split; trivial.
          split.
          apply H0.
          clear H0.
          split; trivial.
          exists st', pv.
          split; trivial.
          trivial.
        Qed.  

        Lemma match_prev_next_elim_tail: 
          forall l start ending l' tcb hd tl,
            l = l' ++ hd :: nil
            -> l' <> nil
            -> abqueue_match_next_prev_rec l ending hd tl start tcb
            -> exists hd', 
                 abqueue_match_next_prev_rec l' hd hd' tl start tcb
                 /\ exists st, ZMap.get hd tcb = TCBValid st ending hd'.
        Proof.
          induction l.
          simpl; auto.
          intros.
          assert (l' ++ hd :: nil = nil).
          auto.
          destruct (app_eq_nil _ _ H2).
          discriminate.
          intros.
          destruct l.
          assert (a = hd /\ l' = nil).
          assert (a :: nil = nil ++ a :: nil).
          rewrite app_nil_l.
          trivial.
          rewrite H2 in H.
          destruct (app_inj_tail _ _ _ _ H).
          split; trivial.
          rewrite H3; trivial.
          destruct H2.
          destruct (H0 H3).
          destruct l' as [ | a' l'].
          destruct (H0 (refl_equal _)).
          rewrite <- app_comm_cons in H.
          inversion H; subst a'; clear H.
          assert (l' = nil \/ exists a' l'', l' = a' :: l'').
          destruct l'.
          left; trivial.
          right.
          exists z0, l'.
          trivial.
          destruct H as [H | H].
          (* l' = nil *)
          subst l'.
          assert (abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb
                  -> (tl = a /\ exists st, exists prev,
                                             ZMap.get a tcb = TCBValid st prev start
                                             /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)).
          simpl.
          trivial.
          apply H in H1.
          clear H.
          simpl in H4.
          inversion H4.
          subst z l.
          destruct H1 as [Htl [st' [pv [H1 H2]]]].
          simpl in H2.
          destruct H2 as [Hhd [Hpv Hget]].
          simpl.
          exists a.
          split; trivial.
          split; trivial.
          split; trivial.
          subst pv.
          exists st'; trivial.
          (* l' = not nil *)
          destruct l'.
          destruct H as [a' [l'' H]].
          discriminate.
          clear H.
          rename z0 into a'.
          clear H0.
          assert (abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb
                  -> (tl = a /\ exists st, exists prev,
                                             ZMap.get a tcb = TCBValid st prev start
                                             /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)).
          simpl.
          trivial.
          apply H in H1.
          clear H.
          destruct H1 as [Htl [st' [pv [Hgeta Hm]]]].
          assert (a' :: l' <> nil).
          intro HF.
          discriminate.
          destruct (IHl _ _ _ _ _ _ H4 H Hm) as [hd' [Hx Hy]].
          exists hd'.
          assert ((tl = a /\ exists st, exists prev,
                                          ZMap.get a tcb = TCBValid st prev start
                                          /\ abqueue_match_next_prev_rec (a' :: l') hd hd' prev a tcb)
                  -> abqueue_match_next_prev_rec (a :: a' :: l') hd hd' tl start tcb).
          simpl.
          trivial.
          split.
          apply H0.
          clear H0.
          split; trivial.
          exists st', pv.
          split; trivial.
          trivial.
        Qed.  

        Lemma match_prev_next_elim2_tail: 
          forall l start ending l' tcb hd tl,
            l = l' ++ hd :: nil
            -> l' = nil
            -> abqueue_match_next_prev_rec l ending hd tl start tcb
            -> exists hd', exists st, ZMap.get hd tcb = TCBValid st ending hd'.
        Proof.
          intros.
          subst l'.
          simpl in H.
          subst l.
          simpl in H1.
          destruct H1 as [Hhd [Htl [st H]]].
          exists start, st. 
          trivial.
        Qed.

        Lemma match_next_prev_implies_tl : 
          forall l t ending hd tl start tcb,
            abqueue_match_next_prev_rec (t :: l) ending hd tl start tcb
            -> tl = t.
        Proof.
          intros.
          simpl in H.
          destruct l.
          destruct H as [H1 [H2 H]].
          subst t; trivial.
          destruct H.
          subst tl; trivial.
        Qed.

        Lemma match_next_prev_implies_hd : 
          forall l t ending hd tl start tcb,
            abqueue_match_next_prev_rec (l ++ t :: nil) ending hd tl start tcb
            -> hd = t.
        Proof.
          intros.
          destruct l.
          unfold app in H.
          simpl in H.
          destruct H; trivial.
          apply (match_next_prev_elim_tail ((z :: l) ++ t :: nil) (z::l) t) in H; auto.
          destruct H as [hd' [H Hx]].
          trivial.
          intro HF.
          discriminate.
        Qed.
        
        Lemma match_prev_next_match_tail: 
          forall l t start ending l' tcb hd tl,
            l = l' ++ t :: nil
            -> abqueue_match_next_prev_rec l ending hd tl start tcb
            -> t = hd.
        Proof.
          induction l.
          simpl.
          intros.
          destruct l'.
          simpl in H.
          discriminate.
          rewrite <- app_comm_cons in H.
          discriminate.
          intros.
          destruct l.
          assert (a :: nil = nil ++ a :: nil).
          rewrite app_nil_l.
          trivial.
          rewrite H1 in H.
          destruct (app_inj_tail _ _ _ _ H).
          subst l' a.
          simpl in H0.
          destruct H0; auto.
          assert (abqueue_match_next_prev_rec (a :: z :: l) ending hd tl start tcb
                  -> (tl = a /\ exists st, exists prev,
                                             ZMap.get a tcb = TCBValid st prev start
                                             /\ abqueue_match_next_prev_rec (z :: l) ending hd prev a tcb)).
          simpl.
          trivial.
          apply H1 in H0.
          clear H1.
          destruct H0 as [Htl [st [pv [Hgeta Hm]]]].
          destruct l'.
          simpl in H.
          inversion H.
          rewrite <- app_comm_cons in H.
          inversion H.
          eapply IHl; eauto.
        Qed.  

        Lemma match_next_prev_split: 
          forall l l' ending hd tl start tcb,
            l <> nil
            -> l' <> nil  
            -> abqueue_match_next_prev_rec (l ++ l') ending hd tl start tcb
            -> (exists tl', exists hd', 
                              abqueue_match_next_prev_rec l' ending hd tl' hd' tcb
                              /\ abqueue_match_next_prev_rec l tl' hd' tl start
                                                             tcb).
        Proof.
          induction l as [ | t l] .
          (* case 1 *)
          intros.
          destruct (H (refl_equal _)).
          
          (* case 2 *)
          destruct l' as [ | t' l'].
          intros.
          destruct (H0 (refl_equal _)).
          
          (* case 3 *)
          intros ending hd tl start tcb Htlnnil Ht'l'nnil Hm.
          rewrite <-app_comm_cons in Hm.
          destruct (match_prev_next_elim3 _ _ _ _ _ _ _ Hm) as [Htl [st [pv [Ht Hml]]]].
          intro HF.
          destruct (app_cons_not_nil _ _ _ (eq_sym HF)).
          
          destruct l as [ | t1 l].
          (* case 4 *)
          unfold app in Hml.
          exists pv, t.
          split; trivial.
          simpl.
          split; trivial.
          split; trivial.
          exists st; trivial.
          
          (* case 5 *)
          assert (t1 :: l <> nil).
          intro HF; discriminate HF.
          assert (t' :: l' <> nil).
          intro HF; discriminate HF.
          destruct (IHl (t' :: l') _ _ _ _ _ H H0 Hml) as [tl' [hd' [Hm2 Hm3]]].
          exists tl', hd'.
          split; trivial.
          apply match_prev_next_intro3.
          intro HF; discriminate HF.
          split; trivial.
          exists st, pv; split; trivial.
        Qed.

        Lemma match_next_prev_split_into_three: 
          forall l l' i ending hd tl start tcb,
            l <> nil
            -> l' <> nil  
            -> abqueue_match_next_prev_rec
                 (l ++ (i :: nil) ++ l') 
                 ending hd tl start
                 tcb
            -> (exists tl', exists hd', exists st,
                                          ZMap.get i tcb = TCBValid st tl' hd'
                                          /\ abqueue_match_next_prev_rec 
                                               l'
                                               ending hd tl' i 
                                               tcb
                                          /\ abqueue_match_next_prev_rec 
                                               l
                                               i hd' tl start
                                               tcb).
        Proof.
          intros.  
          assert ((i::nil) ++ l' <> nil).
          simpl.
          intro HF; discriminate HF.
          destruct (match_next_prev_split _ _ _ _ _ _ _ H H2 H1) as [tl' [hd' [Hm1 Hm2]]].
          unfold app in Hm1.  
          destruct l' as [ | t l'].
          destruct (H0 (refl_equal _)).
          destruct (match_prev_next_elim3 _ _ _ _ _ _ _ Hm1) as [Htl [st [pv [Hx Hm]]]].
          intro HF; discriminate HF.
          subst tl'.
          exists pv, hd', st.
          split; trivial.
          split; trivial.
        Qed.

        Lemma match_next_prev_merge:
          forall l l' ending start hd tl tcb hd' tl',
            l <> nil
            -> l' <> nil
            -> abqueue_match_next_prev_rec l tl' hd' tl start tcb
            -> abqueue_match_next_prev_rec l' ending hd tl' hd' tcb
            -> abqueue_match_next_prev_rec (l++l') ending hd tl start tcb.
        Proof.
          induction l as [ | t l].
          intros.
          destruct (H (refl_equal _)).
          intros.
          rewrite <- app_comm_cons.
          apply match_prev_next_intro3.
          destruct l'.
          destruct (H0 (refl_equal _)). 
          intro HF.
          destruct (app_cons_not_nil _ _ _ (eq_sym HF)).
          assert (Htl := match_next_prev_implies_tl _ _ _ _ _ _ _ H1).
          destruct l' as [| t' l'].
          destruct (H0 (refl_equal _)). 
          split; trivial.
          destruct l as [| t2 l].
          simpl in H1.
          destruct H1 as [Hhd' [_ [st Ht]]].
          exists st, tl'.
          split; trivial.
          unfold app.
          subst hd'.
          trivial.
          destruct (match_prev_next_elim3 _ _ _ _ _ _ _ H1) as [Htl' [st' [pv [Ht Hm]]]].
          intro HF; discriminate HF.
          exists st', pv; trivial.
          split; trivial.
          eapply IHl; eauto.
          intro HF; discriminate HF.
        Qed.

        Lemma dequeue_exists: 
          forall f n i adt adt' ladt, 
            dequeue0_spec (Int.unsigned n) adt = Some (adt', i)
            -> relate_RData f adt ladt
            -> high_level_invariant adt
            -> exists ladt', 
                 dequeue_spec (Int.unsigned n) ladt = Some (ladt', i)
                 /\ relate_RData f adt' ladt'.
        Proof.
          intros f n i adt adt' ladt HQ H INV.
          inversion_clear H.
          revert HQ.
          unfold dequeue_spec, dequeue0_spec.
          subrewrite.
          destruct (ikern ladt) eqn: HIK; contra_inv.
          destruct (pg ladt) eqn: HIP; contra_inv.
          destruct (ihost ladt) eqn: HIH; contra_inv.
          destruct (ipt ladt) eqn: HIT; contra_inv.
          destruct (zle_le 0 (Int.unsigned n) num_proc); contra_inv.
          destruct (ZMap.get (Int.unsigned n) (abq adt)) eqn: Hgetl; contra_inv.
          assert (Hvalid_q : AbQCorrect (ZMap.get (Int.unsigned n) (abq adt))).
          {
            inversion INV.
            eapply valid_TDQ; eauto.
          }
          assert (Habq_abtcb: abqueue_abq_mapto_abtcb (abtcb adt) (abq adt)). 
          {
            inversion INV.
            unfold abqueue_abq_mapto_abtcb.
            intros i' Hi'. 
            destruct (valid_TCB pg_re0 i' Hi') as [s [inq [Hget Hinq]]].
            exists s, inq.
            split; trivial.
            omega.
          }
          assert (Hvalid_inQ: abqueue_valid_inQ (abtcb adt) (abq adt)).
          {
            inversion INV.
            unfold abqueue_valid_inQ.
            intros i' qi l'' Hi' Hqi Hget' Hl'.
            destruct (valid_inQ pg_re0 i' qi l'' Hi' Hqi Hget' Hl'); eauto.
          }
          assert (Hvalid_count: abqueue_valid_count (abtcb adt) (abq adt)). 
          {
            inversion INV.
            unfold abqueue_valid_count.
            specialize (valid_count pg_re0).
            intros. unfold QCount in *.
            destruct (zeq qi inq); subst.
            - specialize (valid_count _ _ _ H H0 H1).
              destruct valid_count as (l' & HR1 & HR2).
              rewrite H2 in HR1. inv HR1.
              split; trivial.
              intros HF. elim HF. trivial.
            - split; intros.
              + congruence.
              + red; intros.
                unfold InQ in *.
                destruct (valid_inQ pg_re0 _ _ _ H H1 H2 H4)
                         as (s' & HR').
                rewrite H0 in HR'. inv HR'.
                elim n0; trivial.
          }
          assert (Hvalid_notinQ': abqueue_notinQ (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_notinQ; trivial.
          }
          assert (Hvalid_disjoint: abqueue_disjoint (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_disjoint; trivial.
          }
          assert (Hvalid_queue_disjoint: abqueue_queue_disjoint (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_queue_disjoint; trivial.
          }
          destruct (zeq (last l num_proc) num_proc) as [ Hl | Hl].

          - (* l = nil *)
            assert (Hl_nil : l = nil).
            {
              apply (last_nil _ zeq) with num_proc; trivial.
              unfold AbQCorrect in Hvalid_q.
              destruct Hvalid_q as [l'' [Hl' Hl'valid]].
              rewrite Hgetl in Hl'.
              inversion Hl'.
              subst l''.
              clear - Hl'valid.
              intros.
              destruct (Hl'valid x H).
              omega.
            }
            subst l. pose proof abq_re0 as abq_re1. inv abq_re0.
            unfold abqueue_match_dllist in H.
            destruct (H _ nil a Hgetl) as [hd [tl [Hget Hx]]].
            rewrite Hget.
            simpl in Hx.
            destruct Hx as [Hhd Htl].
            destruct (zeq hd num_proc) as [_ | Hx]; [ | destruct (Hx Hhd) ].
            inv HQ. refine_split'; eauto.
            constructor; eauto.

          - (* l = _ :: _ *)
            destruct (removelast_dec _ l) as [Hl2 | Hl2].
            + (* l = _ :: nil *)
              caseEq (ZMap.get (last l num_proc) (abtcb adt)); 
              [intro Hgettl | intros st inq Hgettl]; rewrite Hgettl in HQ; contra_inv.
              assert (exists t, l = t:: nil /\ last l num_proc = t).
              {
                eapply (removelast_last_singleton _ zeq); eauto.
              }
              inv abq_re0.
              destruct H as [t [Ht Hlast]].
              unfold abqueue_match_dllist in H0.
              destruct (H0 (Int.unsigned n) l a Hgetl) as [hd [tl [Hqnode Hdllist]]].
              rewrite Hqnode.
              rewrite Ht in Hdllist.
              simpl in Hdllist.
              destruct Hdllist as [Hhd [Htl [st' Hnodet]]].
              assert (Hhd2: hd <> num_proc).
              {
                subst t.
                unfold AbQCorrect in Hvalid_q.
                destruct Hvalid_q as [l'' [Hgetl' Hrange]].
                rewrite Hgetl in Hgetl'.
                inversion Hgetl'.
                subst l''.
                rewrite Ht in Hrange.
                rewrite <- Hhd in Hrange.
                simpl in Hrange.
                omega.
              }
              destruct (zeq hd num_proc) as [Hhd1 | Hhd1 ].
              destruct (Hhd2 Hhd1).
              clear Hhd2.
              rewrite <- Hhd in Hnodet.
              rewrite Hnodet.
              destruct (zeq num_proc num_proc) as [ _ | Hneq]; [| destruct (Hneq (refl_equal))].
              inversion HQ.
              subst i hd.
              rewrite Ht.
              refine_split'; eauto.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor; auto.
              * (* 1st branch : abqueue_match_dllist *)
                clear HQ.
                rewrite <- Ht.
                destruct (zeq t t) as [_|Hneq]; [ | destruct (Hneq (refl_equal _))].
                unfold abqueue_match_dllist.
                intros qi l'' Hqi Hgetl'.
                destruct (zeq qi (Int.unsigned n)) as [ Heq | Hneq ].
                subst qi. rewrite ZMap.gss in *.
                inversion Hgetl'.
                subst l''. refine_split'; eauto.
                econstructor; trivial.
                rewrite ZMap.gso in *; eauto.

              * (* 2nd branch: abtcbpool_tcbpool *)
                clear HQ.
                unfold abtcbpool_tcbpool in * .
                intros i tds inq' Hi Hget.
                destruct (zeq i t) as [ Heq | Hneq ].
                subst i. rewrite ZMap.gss in *.
                rewrite Hlast in Hgettl.
                inversion Hget; subst tds inq'; clear Hget.
                eauto. rewrite ZMap.gso in *; eauto.

            + (* l = ... :: t' :: t :: nil *)
              caseEq (ZMap.get (last l num_proc) (abtcb adt)); [| intros st inq]; intro Hget; 
              rewrite Hget in HQ; contra_inv.
              assert (inq = Int.unsigned n).
              {
                clear HQ.
                unfold abqueue_valid_inQ in Hvalid_inQ.
                assert (Hin: In (last l num_proc) l).
                {
                  destruct (last_In _ zeq l _ num_proc refl_equal); trivial.
                  omega.
                }

                assert (Hrange: 0<= (last l num_proc) < num_proc).
                {
                  unfold AbQCorrect in Hvalid_q.
                  destruct Hvalid_q as [l'' [Hgetl' Hx]].
                  apply Hx.
                  rewrite Hgetl in Hgetl'.
                  inversion Hgetl'; subst l''; clear Hgetl'.
                  trivial.
                }
                
                destruct (Hvalid_inQ (last l num_proc) (Int.unsigned n) l Hrange a Hgetl Hin) as [st' Hget'].
                rewrite Hget in Hget'.
                inversion Hget'; subst st' inq; clear Hget'.
                trivial.
              }
              subst inq.
              inv HQ.
              destruct (removelast_notnil _ _ Hl2) as [t [t' [l'' Hl'']]].
              assert (exists tl, ZMap.get (Int.unsigned n) (tdq ladt) = TDQValid t tl
                                 /\ 0 <= t < num_proc 
                                 /\ exists st pv, 
                                      ZMap.get t (tcb ladt) = TCBValid st pv t'
                                      /\ 0 <= t' < num_proc 
                                      /\ exists st' nx', 
                                           ZMap.get t' (tcb ladt) = TCBValid st' t nx'
                                           /\ ((l'' <> nil /\ abqueue_match_next_prev_rec l'' t' nx' tl num_proc
                                                                                          (tcb ladt))
                                               \/ l'' = nil /\ (tl = t' /\ nx' = num_proc))).
              {
                unfold AbQCorrect in Hvalid_q.
                destruct Hvalid_q as [l''' [Hgetl' Hx]].
                inversion abq_re0. 
                subst abtcb abq tcb tdq.
                rewrite Hgetl in Hgetl'.
                inversion Hgetl'; subst l'''; clear Hgetl'.
                destruct (H (Int.unsigned n) l a Hgetl) as [hd [tl [Hqnode Hm]]].
                assert (Hl3 : l = (l'' ++ (t' ::nil)) ++ t::nil).
                {
                  assert (t' :: t :: nil = (t' :: nil) ++ (t :: nil))
                    by (simpl; trivial).
                  rewrite H1 in Hl''.
                  rewrite <- app_assoc.
                  trivial.
                }
                assert (Heq : t = hd).
                {
                  eapply match_prev_next_match_tail; eauto.
                }
                subst hd.
                exists tl.
                split; trivial.
                assert (Hin : In t l).
                {
                  clear - Hl''.
                  rewrite Hl''.
                  apply in_or_app.
                  right; simpl; trivial.
                  right; left; trivial.
                }
                split.
                apply Hx; trivial.

                assert (Haddi : (l'' ++ t' :: nil) <> nil).
                {
                  clear.
                  destruct l''.
                  simpl.
                  intro HF.
                  discriminate.
                  rewrite <- app_comm_cons.
                  intros HF.
                  discriminate.
                }
                destruct (match_next_prev_elim_tail _ _ _ _ _ _ _ _ Hl3 Haddi Hm) as [hd' [_ [Hm' [st' Hgethd]]]].
                exists st', num_proc.
                assert (Ht'in : In t' l).
                {
                  clear - Hl''.
                  subst l.
                  apply in_or_app.
                  right. simpl.
                  left; trivial.
                }
                assert (Ht' : t' = hd').
                {
                  eapply match_prev_next_match_tail; eauto.
                }
                subst hd'.
                split; trivial.
                split.
                apply Hx; trivial.
                
                assert (Hl''_dec: l'' <> nil \/ l'' = nil).
                {
                  clear.
                  destruct l''.
                  right; trivial. left. intro HF.
                  discriminate.
                }
                destruct Hl''_dec as [Hl''_notnil | Hl''_nil].
                destruct (match_next_prev_elim_tail _ _ _ _ _ _ _ _ (refl_equal (l'' ++ t' :: nil)) Hl''_notnil Hm')
                  as [hd'' [_ [Hm'' [st'' Hgethd'']]]].
                exists st'', hd''.
                split; trivial.
                left.
                intros; auto.
                
                destruct (match_prev_next_elim2_tail _ _ _ _ _ _ _ (refl_equal (l'' ++ t' :: nil)) Hl''_nil Hm')
                  as [hd'' [st'' Hgethd'']].
                exists st'', hd''.
                split; trivial.
                right.
                split; auto.
                subst l''.
                simpl in Hm'.
                destruct Hm' as [Hxx [Hxy [st''' Hm']]].
                rewrite Hgethd'' in Hm'.
                inversion Hm'; subst st''' hd''.
                split; trivial.
              }
              destruct H as [tl [Hgetn [Ht [st0 [pv [Hgett [Ht' [st' [nx' [Hgett' Hrec]]]]]]]]]].
              rewrite Hgetn.
              destruct (zeq t num_proc) as [Heq | _].
              elimtype False.
              clear - Ht Heq.
              omega.
              rewrite Hgett.
              destruct (zeq t' num_proc) as [Heq | _].
              elimtype False.
              clear - Ht' Heq.
              omega.
              rewrite Hgett'.
              eexists.
              assert (last l num_proc = t).
              {
                clear - Hl''.
                rewrite Hl''.
                rewrite last_app.
                simpl; trivial.
                intro H.
                discriminate.
              }
              rewrite H.
              split; eauto.
              constructor; eauto.

              (* to prove AbQ_RealQ *)
              simpl.
              constructor; auto.

              * (* 1st branch : abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l''' Hqi Hgetl'.
                destruct (zeq qi (Int.unsigned n)) as [ Heq | Hneq ].
                subst qi. rewrite ZMap.gss in *.
                inversion Hgetl'; clear Hgetl'.

                assert (Hl''_dec: l'' = nil \/ l'' <> nil).
                {
                  clear.
                  destruct l''.
                  left; trivial.
                  right.
                  intro HF.
                  discriminate.
                }
                assert (Hrm: remove zeq t l = removelast l).
                {
                  subst t.
                  apply remove_removelast.
                  unfold abqueue_queue_disjoint in Hvalid_queue_disjoint.
                  intros x Hxin.
                  eapply Hvalid_queue_disjoint; eauto.
                  unfold AbQCorrect in Hvalid_q.
                  destruct Hvalid_q as [lx [Hgx Hx]].
                  rewrite Hgetl in Hgx.
                  inversion Hgx; subst lx; clear Hgx.
                  apply Hx; trivial.
                  apply (last_In' _ zeq); trivial.
                }
                rewrite Hrm.
                assert (Hrm': removelast l = l'' ++ t' :: nil).
                {
                  subst l.
                  assert (t' :: t :: nil = (t' :: nil) ++ (t :: nil)).
                  {
                    simpl; trivial.
                  }
                  assert (t' :: t :: nil <> nil).
                  {
                    intro HF.
                    discriminate.
                  }
                  rewrite removelast_app; trivial.
                }
                rewrite Hrm'.
                destruct Hl''_dec as [Hl''_nil | Hl''_notnil].
                subst l''.
                simpl.
                destruct Hrec.
                destruct H0. elim H0. trivial.

                destruct H0. destruct H2.
                refine_split'; trivial.
                rewrite ZMap.gss. subst nx'; trivial.

                destruct Hrec as [ [_ Hrec] | [HF _] ]; [ | destruct (Hl''_notnil HF)].
                assert (Hxx: abqueue_match_next_prev_rec l'' t' nx' tl num_proc
                                                         (ZMap.set t' (TCBValid st' num_proc nx') (tcb ladt))).
                {
                  apply match_next_prev_presv_set_notin; auto.
                  assert (count_occ zeq l t' = 1%nat).
                  unfold abqueue_queue_disjoint in Hvalid_queue_disjoint.
                  subst l.
                  apply Hvalid_queue_disjoint with (Int.unsigned n); trivial.
                  apply in_or_app.
                  right.
                  simpl.
                  left; trivial.
                  assert (count_occ zeq l'' t' = 0%nat).
                  subst l.
                  apply count_occ_app_r with (t' :: t :: nil) 1%nat; simpl; auto.
                  destruct (zeq t' t') as [ _ | Hneq ]; [ | destruct (Hneq (refl_equal _))].
                  assert (t <> t').
                  {
                    intro HF.
                    subst t'.
                    rewrite count_occ_plus_app in H0.
                    simpl in H0.
                    destruct (zeq t t) as [_ | Hneq]; [| destruct (Hneq (refl_equal _))].
                    clear - H0.
                    omega.
                  }
                  destruct (zeq t t') as [Heq | _].
                  elim H2; trivial.
                  trivial.
                  eapply count_occ_zero_notin; eauto.
                }
                assert (remove zeq t l = removelast l).
                {
                  subst t.
                  apply remove_removelast.
                  unfold abqueue_queue_disjoint in Hvalid_queue_disjoint.
                  intros x Hxin.
                  eapply Hvalid_queue_disjoint; eauto.
                  unfold AbQCorrect in Hvalid_q.
                  destruct Hvalid_q as [lx [Hgx Hx]].
                  rewrite Hgetl in Hgx.
                  inversion Hgx; subst lx; clear Hgx.
                  apply Hx; trivial.
                  apply (last_In' _ zeq); trivial.
                }
                refine_split'; trivial.
                eapply match_prev_next_intro_tail; eauto.
                rewrite ZMap.gss. trivial.

                assert (~ In t' l''').
                {
                  unfold abqueue_disjoint in Hvalid_disjoint.
                  assert (In t' l).
                  {
                    subst l.
                    apply in_or_app.
                    right.
                    simpl.
                    left; trivial.
                  }
                  assert (exists s, ZMap.get t' (abtcb adt) =
                                    AbTCBValid s (Int.unsigned n)).
                  {
                    unfold abqueue_valid_inQ in Hvalid_inQ.
                    apply Hvalid_inQ with l; trivial.
                  }
                  destruct H1.
                  apply (Hvalid_disjoint _ _ _ a Ht' Hgetl H0 qi l''' Hqi) ; eauto.
                  rewrite ZMap.gso in *; eauto.
                }
                inversion abq_re0.
                subst abtcb abq tcb tdq.
                unfold abqueue_match_dllist in H2.
                rewrite ZMap.gso in *; eauto.
                destruct (H1 _ _ Hqi Hgetl') as [hd' [tl' [Hgetqi Hm]]].            
                refine_split'; eauto.
                apply match_next_prev_presv_set_notin; auto.          

              * (* 2nd branch: abtcbpool_tcbpool *)
                inversion abq_re0.
                subst abtcb abq tcb tdq.
                unfold abtcbpool_tcbpool in * .
                intros i tds inq' Hi Hgeti.
                assert (Ht_t': t <> t').
                {
                  unfold abqueue_queue_disjoint in Hvalid_queue_disjoint.
                  assert (Htin: In t l).
                  {
                    subst l.
                    apply in_or_app; trivial.
                    right.
                    simpl.
                    right.
                    left; trivial.
                  }
                  assert (Hocc := Hvalid_queue_disjoint _ _ a Hgetl t  Ht Htin).
                  intro HF.
                  subst t'.
                  rewrite Hl'' in Hocc.
                  rewrite count_occ_plus_app in Hocc.
                  rewrite plus_comm in Hocc.
                  assert (count_occ zeq (t :: t :: nil) t = 2%nat).
                  clear.
                  simpl.
                  destruct (zeq t t) as [ _ | Hneq]; [ | destruct (Hneq (refl_equal _))].
                  trivial.
                  rewrite H2 in Hocc.
                  simpl in Hocc.
                  omega.
                }
                destruct (zeq i t) as [ Heq | Hneq ].
                subst i.
                rewrite ZMap.gss in *.
                inversion Hgeti; subst tds inq'; clear Hgeti.
                rewrite ZMap.gso; auto. subst t.
                destruct (H1 _ _ _ Hi Hget) as [pvx [nxx Hxx]].
                rewrite Hgett in Hxx.
                inversion Hxx; subst st0 pvx nxx; clear Hxx.
                exists pv, t'.
                trivial.
                destruct (zeq i t') as [ Heq | Hneqit' ].
                subst i. rewrite ZMap.gss.
                rewrite ZMap.gso in *; eauto.
                destruct (H1 _ _ _ Hi Hgeti) as [pvx [nxx Hxx]].
                rewrite Hgett' in Hxx.
                inversion Hxx; subst tds pvx nxx; clear Hxx.
                exists num_proc, nx'; trivial.
                rewrite ZMap.gso in *; eauto.
        Qed.

        Lemma enqueue_exists : 
          forall f n i adt adt' ladt, 
            enqueue0_spec (Int.unsigned n) i adt = Some adt'
            -> relate_RData f adt ladt
            -> high_level_invariant adt
            -> exists ladt', 
                 enqueue_spec (Int.unsigned n) i ladt = Some ladt'
                 /\ relate_RData f adt' ladt'.
        Proof.
          intros f n i adt adt' ladt HQ H INV.
          inversion_clear H.
          revert HQ.
          unfold enqueue_spec, enqueue0_spec.
          subrewrite. subdestruct; subst. functional inversion Hdestruct3.
          assert (Hvalid_q : AbQCorrect (ZMap.get (Int.unsigned n) (abq adt))).
          {
            inversion INV.
            eapply valid_TDQ; eauto.
          }
          assert (Habq_abtcb: abqueue_abq_mapto_abtcb (abtcb adt) (abq adt)). 
          {
            inversion INV.
            unfold abqueue_abq_mapto_abtcb.
            intros i' Hi'.
            destruct (valid_TCB pg_re0 i' Hi') as [s [inq' [Hget Hinq]]].
            exists s, inq'.
            split; trivial.
            omega.
          }
          assert (Hvalid_inQ: abqueue_valid_inQ (abtcb adt) (abq adt)).
          {
            inversion INV.
            unfold abqueue_valid_inQ.
            intros i' qi l' Hi' Hqi Hget' Hl'.
            destruct (valid_inQ pg_re0 i' qi l' Hi' Hqi Hget' Hl'); eauto.
          }
          assert (Hvalid_count: abqueue_valid_count (abtcb adt) (abq adt)). 
          {
            inversion INV.
            unfold abqueue_valid_count.
            specialize (valid_count pg_re0).
            intros. unfold QCount in *.
            destruct (zeq qi inq); subst.
            - specialize (valid_count _ _ _ H1 H2 H3).
              destruct valid_count as (l' & HR1 & HR2).
              rewrite H4 in HR1. inv HR1.
              split; trivial.
              intros HF. elim HF. trivial.
            - split; intros.
              + congruence.
              + red; intros.
                unfold InQ in *.
                destruct (valid_inQ pg_re0 _ _ _ H1 H3 H4 H6)
                         as (s' & HR').
                rewrite H2 in HR'. inv HR'.
                elim n0; trivial.
          }
          assert (Hvalid_notinQ': abqueue_notinQ (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_notinQ; trivial.
          }
          assert (Hvalid_disjoint: abqueue_disjoint (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_disjoint; trivial.
          }
          assert (Hvalid_queue_disjoint: abqueue_queue_disjoint (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_queue_disjoint; trivial.
          }

          inversion abq_re0.
          subst abtcb abq tcb tdq.
          unfold abqueue_match_dllist in H1.
          destruct (H1 _ _ _x Hdestruct5) as [hd [tl [Hgetqi Hm]]].
          rewrite Hgetqi.

          destruct l as [ | t l].
          - (* l = nil *)
            simpl in Hm.
            destruct Hm as [Hhd Htl].
            destruct (zeq tl num_proc) as [ _ | Hneq ]; [| destruct (Hneq Htl)].
            destruct (H2 _ _ _ _x0 Hdestruct6) as [pv [nx HLgeti]].
            rewrite HLgeti.
            refine_split'; eauto.
            inversion HQ.
            constructor; eauto; simpl.
            
            (* to prove AbQ_RealQ *)
            constructor.
            + (* 1st: abqueue_match_dllist *)
              unfold abqueue_match_dllist.
              intros qi l Hqi Hget.
              destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
              * subst qi. rewrite ZMap.gss in *.
                refine_split'; trivial.
                inversion Hget.
                subst l.
                simpl.
                split; trivial.
                split; trivial.
                rewrite ZMap.gss. eauto.
              * rewrite ZMap.gso in *; eauto.
                destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hm]]].
                refine_split'; eauto.
                apply match_next_prev_presv_set_notin; eauto.

            + (* 2nd: abtcbpool_tcbpool *)
              unfold abtcbpool_tcbpool.
              intros i' st' inq' Hi' Hgeti'.
              destruct (zeq i' i) as [ Hieq | Hineq ].
              subst i. rewrite ZMap.gss in *.
              inversion Hgeti'.
              subst st'. eauto.
              rewrite ZMap.gso in *; eauto.
              
          - destruct l as [ | t' l].
            + (* l = t :: nil *)
              destruct (H2 _ _ _ _x0 Hdestruct6) as [pv [nx HLgeti]].
              rewrite HLgeti.
              simpl in Hm.
              destruct Hvalid_q as [l' [Hl' Hvalid_q]].
              rewrite Hdestruct5 in Hl'.
              inversion Hl'; subst l'; clear Hl'.
              destruct Hm as [Hhd [Htl Hm]].
              subst tl.
              assert (Ht: 0<= t < num_proc). 
              {
                apply Hvalid_q; trivial.
                simpl.
                left; trivial.
              }
              destruct (zeq t num_proc) as [Hteq | Htneq].
              omega.
              destruct Hm as [st' Hm].
              rewrite Hm.
              inv HQ; refine_split'; eauto.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.
              * (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l Hqi Hget.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi. rewrite ZMap.gss in *.
                assert (i <> t).
                {
                  assert (~ In i (t :: nil)).
                  {
                    eapply Hvalid_notinQ'; eauto.
                  }
                  intro HF.
                  subst i. eapply H3.
                  left; trivial.
                }
                inversion Hget. subst l.
                refine_split'; eauto.
                split; trivial.
                rewrite ZMap.gss.
                refine_split'; eauto.
                split; trivial.
                split; trivial.
                rewrite ZMap.gso; auto.
                rewrite ZMap.gss. eauto.

                rewrite ZMap.gso in *; eauto.
                destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hmm]]].
                refine_split'; eauto.
                eapply match_next_prev_presv_set_notin; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                assert (exists ts, ZMap.get t (abtcb adt) = AbTCBValid ts (Int.unsigned n)).
                {
                  eapply Hvalid_inQ; eauto.
                  left; trivial.
                }
                destruct H3 as [ts H3].
                assert (Htin: In t (t :: nil)).
                {
                  simpl; left; trivial.
                }
                apply (Hvalid_disjoint _ t (t::nil) _x Ht Hdestruct5 Htin 
                                       qi l Hqi Hqineq Hget).
                
              * (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i. rewrite ZMap.gss in *.
                inversion Hgeti'.
                subst tds'. eauto.
                rewrite ZMap.gso in *; eauto.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'. rewrite ZMap.gss.
                assert (st' = tds').
                {
                  destruct (H2 _ _ _ Hi' Hgeti') as [pv' [nx' Hxx]].
                  rewrite Hm in Hxx.
                  inversion Hxx.
                  trivial.
                }
                subst st'. eauto.
                rewrite ZMap.gso; eauto.

            + (* l = t :: t' :: l' *)
              destruct (H2 _ _ _ _x0 Hdestruct6) as [pv [nx HLgeti]].
              rewrite HLgeti.
              assert (abqueue_match_next_prev_rec (t :: t' :: l) num_proc hd tl num_proc
                                                  (tcb ladt)
                      -> (tl = t /\ exists st, exists prev,
                                                 ZMap.get t (tcb ladt) = TCBValid st prev num_proc
                                                 /\ abqueue_match_next_prev_rec (t' :: l) num_proc hd prev t (tcb ladt))).
              {
                simpl. trivial.
              }
              apply H3 in Hm; clear H3.
              destruct Hvalid_q as [l' [Hl' Hvalid_q]].
              rewrite Hdestruct5 in Hl'.
              inversion Hl'; subst l'; clear Hl'.
              destruct Hm as [Htl [st' [pv' [Htl' Hm]]]].
              subst tl.
              assert (Ht: 0<= t < num_proc). 
              {
                apply Hvalid_q; trivial.
                simpl.
                left; trivial.
              }
              destruct (zeq t num_proc) as [Hteq | Htneq].
              omega.
              rewrite Htl'.
              inv HQ. refine_split'; eauto.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.
              * (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                rename l into l''.
                intros qi l Hqi Hget.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi. rewrite ZMap.gss in *.
                assert (i <> t).
                {
                  assert (~ In i (t :: t' :: l'')).
                  {
                    apply (Hvalid_notinQ' _ _ _x0 Hdestruct6 _ _ _x); trivial.
                  }
                  intro HF.
                  subst i. 
                  simpl in H3.
                  apply H3.
                  left; trivial.
                }
                refine_split'; eauto.
                inversion Hget.
                subst l.
                split; trivial.
                rewrite ZMap.gss.
                refine_split'; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                assert ((t = t /\ 
                         exists st, exists prev,
                                      ZMap.get t (ZMap.set t (TCBValid st' pv' i) (tcb ladt)) = TCBValid st prev i
                                      /\ abqueue_match_next_prev_rec (t' :: l'') num_proc hd prev t 
                                                                     (ZMap.set t (TCBValid st' pv' i) (tcb ladt)))
                        -> abqueue_match_next_prev_rec (t :: t' :: l'') 
                                                       num_proc hd t i
                                                       (ZMap.set t (TCBValid st' pv' i) (tcb ladt))).
                {
                  clear. intro H. exact H.
                }
                apply H4; clear H4.
                split; trivial.
                rewrite ZMap.gss.
                refine_split'; eauto.
                assert (~ In t (t' :: l'')).
                {
                  unfold abqueue_queue_disjoint in Hvalid_queue_disjoint.
                  intro Htin.
                  assert (Htin2: In t (t::t'::l'')).
                  {
                    simpl; left; trivial.
                  }
                  assert (Hocc := Hvalid_queue_disjoint _ _ _x Hdestruct5 t  Ht Htin2).
                  simpl in Hocc. rewrite zeq_true in Hocc.
                  destruct (zeq t' t); inversion Hocc.
                  apply count_occ_zero_notin in H5.
                  simpl in Htin.
                  destruct Htin.
                  destruct (n0 H4).
                  destruct (H5 H4).
                }
                apply match_next_prev_presv_set_notin; eauto.
                rewrite ZMap.gso in *; eauto.
                destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hmm]]].
                refine_split'; eauto.
                assert (i <> t).
                {
                  assert (~ In i (t :: t' :: l'')).
                  {
                    apply (Hvalid_notinQ' _ _ _x0 Hdestruct6 _ _ _x); trivial.
                  }
                  intro HF.
                  subst i.
                  simpl in H3.
                  apply H3.
                  left; trivial.
                }
                apply match_next_prev_presv_set_notin; eauto.
                assert (~ In t l).
                {
                  assert (In t (t :: t' :: l'')).
                  {
                    simpl; left; trivial.
                  }
                  eapply (Hvalid_disjoint _ _ _ _x Ht Hdestruct5 H4 qi l Hqi Hqineq Hget); trivial.
                }
                apply match_next_prev_presv_set_notin; eauto.

              * (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i. rewrite ZMap.gss in *.
                inversion Hgeti'.
                subst tds'. eauto.
                rewrite ZMap.gso in *; eauto.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'. rewrite ZMap.gss.
                assert (st' = tds').
                {
                  destruct (H2 _ _ _ Hi' Hgeti') as [pvx [nxx Hxx]].
                  rewrite Htl' in Hxx.
                  inversion Hxx.
                  trivial.
                }
                subst st'. eauto.
                rewrite ZMap.gso; eauto.
        Qed.

        Lemma queue_rmv_exists : 
          forall f n i adt adt' ladt, 
            queue_rmv0_spec (Int.unsigned n) i adt = Some adt'
            -> relate_RData f adt ladt
            -> PAbQueue.high_level_invariant adt
            -> exists ladt', 
                 queue_rmv_spec (Int.unsigned n) i ladt = Some ladt'
                 /\ relate_RData f adt' ladt'.
        Proof.
          intros f n i adt adt' ladt HQ H INV.
          inversion_clear H. revert HQ.
          unfold queue_rmv_spec, queue_rmv0_spec.
          subrewrite. subdestruct. functional inversion Hdestruct3.
          rename _x into Hn, _x0 into Hi, Hdestruct4 into Hgetl, Hdestruct5 into Hgeti. subst.
          assert (Hvalid_q : AbQCorrect (ZMap.get (Int.unsigned n) (abq adt))).
          {
            inversion INV.
            eapply valid_TDQ; eauto.
          }
          assert (Habq_abtcb: abqueue_abq_mapto_abtcb (abtcb adt) (abq adt)). 
          {
            inversion INV.
            unfold abqueue_abq_mapto_abtcb.
            intros i' Hi'.
            destruct (valid_TCB pg_re0 i' Hi') as [s [inq' [Hget Hinq]]].
            exists s, inq'.
            split; trivial.
            omega.
          }
          assert (Hvalid_inQ: abqueue_valid_inQ (abtcb adt) (abq adt)).
          {
            inversion INV.
            unfold abqueue_valid_inQ.
            intros i' qi l' Hi' Hqi Hget' Hl'.
            destruct (valid_inQ pg_re0 i' qi l' Hi' Hqi Hget' Hl'); eauto.
          }
          assert (Hvalid_count: abqueue_valid_count (abtcb adt) (abq adt)). 
          {
            inversion INV.
            unfold abqueue_valid_count.
            specialize (valid_count pg_re0).
            intros. unfold QCount in *.
            destruct (zeq qi inq); subst.
            - specialize (valid_count _ _ _ H1 H2 H3).
              destruct valid_count as (l' & HR1 & HR2).
              rewrite H4 in HR1. inv HR1.
              split; trivial.
              intros HF. elim HF. trivial.
            - split; intros.
              + congruence.
              + red; intros.
                unfold InQ in *.
                destruct (valid_inQ pg_re0 _ _ _ H1 H3 H4 H6)
                         as (s' & HR').
                rewrite H2 in HR'. inv HR'.
                elim n0; trivial.
          }
          assert (Hvalid_notinQ': abqueue_notinQ (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_notinQ; trivial.
          }
          assert (Hvalid_disjoint: abqueue_disjoint (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_disjoint; trivial.
          }
          assert (Hvalid_queue_disjoint: abqueue_queue_disjoint (abtcb adt) (abq adt)). 
          {
            apply abqueue_INV_implies_queue_disjoint; trivial.
          }
          assert (Hvalid_abq_range: abqueue_abq_range (abtcb adt) (abq adt)). 
          {
            unfold abqueue_abq_range.
            intros qi' i' l' Hqi' Hgetqi' Hin'.
            inversion INV.
            destruct (valid_TDQ pg_re0 qi' Hqi') as [ll' [Hgetll' Hx]].
            rewrite Hgetqi' in Hgetll'.
            inversion Hgetll'; subst ll'; clear Hgetll'.
            apply Hx; trivial.
          }

          inversion abq_re0.
          subst abtcb abq tcb tdq.
          unfold abqueue_match_dllist in H.
          destruct (H1 _ _ Hn Hgetl) as [hd [tl [Hgetqi Hm]]].
          rewrite Hgetqi.

          assert (Hioccl: count_occ zeq l i = 1 %nat).
          {
            unfold abqueue_valid_count in Hvalid_count.
            destruct (Hvalid_count _ _ _ Hi Hgeti _ l Hn Hgetl) as [Hinq1 Hinq2].
            apply Hinq1; trivial.
          }
          destruct (count_occ_1_elim _ zeq l i Hioccl) as [Hsig | [Hhead | [Htail | Hmid ]]].
          
          - (* cast1: l = i :: nil *)
            subst l.
            simpl in Hm.
            destruct Hm as [Hhd [Htl [st' HLgeti ]]].
            destruct (H2 _ _ _ Hi Hgeti) as [pv [nx HLgeti']].
            rewrite HLgeti in HLgeti'.
            inversion HLgeti'.
            subst st' pv nx.
            rewrite HLgeti.
            zeq_simpl.
            eexists; split; eauto.
            inversion  HQ.
            constructor; eauto; simpl.
            
            (* to prove AbQ_RealQ *)
            constructor.
            + (* 1st: abqueue_match_dllist *)
              unfold abqueue_match_dllist.
              intros qi l Hqi Hget.
              rewrite ZMap.gsspec in Hget.
              unfold ZIndexed.eq in Hget.
              rewrite ZMap.gsspec.
              unfold ZIndexed.eq.
              destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
              zeq_simpl.
              exists num_proc, num_proc.
              split; trivial.
              inversion Hget.
              subst l.
              simpl.
              split; trivial.
              destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hm]]].
              exists hd', tl'.
              split; trivial.

            + (* 2nd: abtcbpool_tcbpool *)
              unfold abtcbpool_tcbpool.
              intros i' st' inq' Hi' Hgeti'.
              rewrite ZMap.gsspec in Hgeti'.
              unfold ZIndexed.eq in Hgeti'.
              destruct (zeq i' i) as [ Hieq | Hineq ].
              subst i'.
              inversion Hgeti'; subst st' inq'; clear Hgeti'.
              exists num_proc, num_proc.
              trivial.
              apply H2 with inq'; eauto.
          (* AbQ_RealQ proved *)
              
          - (* case2: l = t::l' ,  l' <> nil *)
            destruct Hhead as [l' [Hl [Hl' Hoccl']]].
            destruct (H2 _ _ _ Hi Hgeti) as [pv [nx HLgeti]].
            rewrite HLgeti.
            subst l.
            
            destruct l' as [ | t l'].
            destruct (Hl' (refl_equal _)).
            clear Hl'.
            assert (t :: l' <> nil).
            intro HF; discriminate HF.
            apply match_prev_next_elim3 in Hm; trivial.
            destruct Hm as [Htl [st' [pv' [HLgeti_ Hm]]]].
            subst tl.
            rewrite HLgeti in HLgeti_. 
            inversion HLgeti_; subst st' pv' nx; clear HLgeti_.

            destruct l' as [ | t' l'].
            * (* case2-1: l = t::t'::nil  *)
              simpl in Hm.
              destruct Hm as [Hhd [Hpv [st' HLgett]]].
              subst hd pv.
              assert (Ht: 0 <= t < num_proc). 
              apply (Hvalid_abq_range (Int.unsigned n) t (i :: t :: nil) Hn); trivial.
              simpl.
              right; left; trivial.
              assert (t <> num_proc).
              omega.
              zeq_simpl. 
              rewrite zeq_false; trivial.
              rewrite HLgett.
              eexists; split; eauto.
              inversion HQ.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.
              {
                (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l Hqi Hget.
                rewrite ZMap.gsspec in Hget.
                unfold ZIndexed.eq in Hget.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                {
                  subst qi.
                  assert (i <> t).
                  {
                    intro HF.
                    subst i.
                    simpl in Hioccl.
                    zeq_simpl.
                    inversion Hioccl.
                  }
                  rewrite zeq_false in *; trivial.
                  inversion Hget.
                  subst l.
                  exists t, t.
                  split; trivial.
                  simpl.
                  split; trivial.
                  split; trivial.
                  rewrite ZMap.gsspec.
                  unfold ZIndexed.eq.
                  zeq_simpl.
                  exists st'; trivial.
                }
                {
                  destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hmm]]].
                  exists hd', tl'.
                  split; trivial.
                  apply match_next_prev_presv_set_notin; eauto.
                  eapply (Hvalid_disjoint (Int.unsigned n)); eauto.
                  simpl; right; auto.
                }              
              }
              {
                (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool in *. 
                intros i' tds' inq' Hi' Hgeti'.
                assert (i <> t).
                {
                  intro HF.
                  subst i.
                  simpl in Hioccl.
                  zeq_simpl.
                  inversion Hioccl.
                }
                destruct (zeq i i'). subst.
                rewrite ZMap.gss in *.
                inv Hgeti'.
                rewrite ZMap.gso; eauto. 
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'.
                rewrite ZMap.gss. rewrite ZMap.gso in *; eauto.
                assert (st' = tds').
                {
                  destruct (H2 _ _ _ Hi' Hgeti') as [pv' [nx' Hxx]].
                  rewrite HLgett in Hxx.
                  inversion Hxx.
                  trivial.
                }
                subst st'. eauto.
                rewrite ZMap.gso in *; eauto.
              }

            * (* case2-2: l = t::t'::t'' :: l'  *)
              assert (t' :: l' <> nil).
              {
                intro HF.
                discriminate.
              }
              apply match_prev_next_elim3 in Hm; trivial.
              destruct Hm as [Ht' [st' [pv' [HLgett' Hm]]]].
              subst pv.
              assert (Ht: 0<= t < num_proc). 
              {
                apply (Hvalid_abq_range (Int.unsigned n) t (i :: t :: t' :: l') Hn); trivial.
                simpl.
                right; left; trivial.
              }
              assert (t <> num_proc).
              {
                omega.
              }
              zeq_simpl. 
              rewrite zeq_false; trivial.
              rewrite HLgett'.
              assert (remove zeq i (i :: t :: t' :: l') = t :: t' :: l').
              assert (i :: t :: t' :: l' = (i :: nil) ++ (t :: t' :: l')).
              rewrite <- app_comm_cons.
              simpl; trivial.
              rewrite H6.
              rewrite remove_app.
              assert (remove zeq i (i::nil) = nil ).
              {
                simpl.
                zeq_simpl.
                trivial.
              }
              rewrite H7.
              unfold app.
              apply count_occ_remove_neq; eauto.
              rewrite H6 in HQ.
              eexists; split; eauto.
              inversion  HQ.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.
              (* 1st: abqueue_match_dllist *)
              unfold abqueue_match_dllist.
              intros qi l Hqi Hget.
              rewrite ZMap.gsspec in Hget.
              unfold ZIndexed.eq in Hget.
              rewrite ZMap.gsspec.
              unfold ZIndexed.eq.
              destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
              subst qi.
              assert (i <> t).
              intro HF.
              subst i.
              simpl in Hioccl.
              zeq_simpl.
              inversion Hioccl.
              exists hd, t.
              split; trivial.
              inversion Hget; subst l; clear Hget.
              apply match_prev_next_intro3.
              intro HF; discriminate HF.
              split; trivial.
              rewrite ZMap.gsspec.
              unfold ZIndexed.eq.
              zeq_simpl.
              exists st', pv'.
              split; trivial.
              apply match_next_prev_presv_set_notin; trivial.
              assert (count_occ zeq ((i :: nil) ++ (t :: nil) ++ t' :: l') t = 1%nat).
              rewrite <- app_comm_cons.
              unfold app.
              eapply (Hvalid_queue_disjoint (Int.unsigned n)); eauto.
              simpl.
              right; left; trivial.
              apply (count_occ_zero_notin _ zeq). 
              apply (count_occ_app_plus') with ((i :: nil) ++ (t :: nil)) 1%nat.
              rewrite <- app_comm_cons.
              unfold app.
              rewrite <- app_comm_cons in H9.
              unfold app in H9.
              rewrite H9.
              simpl; trivial.
              rewrite <- app_comm_cons. 
              unfold app.
              simpl.
              zeq_simpl.
              rewrite zeq_false; trivial.
              destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hmm]]].
              exists hd', tl'.
              split; trivial.
              apply match_next_prev_presv_set_notin; eauto.
              eapply (Hvalid_disjoint (Int.unsigned n)); eauto.
              simpl.
              right; left; trivial.
              
              (* 2nd: abtcbpool_tcbpool *)
              unfold abtcbpool_tcbpool.
              intros i' tds' inq' Hi' Hgeti'.
              rewrite ZMap.gsspec in Hgeti'.
              unfold ZIndexed.eq in Hgeti'.
              rewrite ZMap.gsspec.
              unfold ZIndexed.eq.
              destruct (zeq i' i) as [ Hieq | Hineq ].
              subst i'.
              exists t, num_proc.
              inversion Hgeti'.
              subst tds.
              assert (i <> t).
              intro HF.
              subst i.
              simpl in Hioccl.
              zeq_simpl.
              inversion Hioccl.
              rewrite zeq_false; trivial.
              destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
              subst i'.
              assert (st' = tds').
              { 
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett' in Hxx.
                inversion Hxx.
                trivial.
              }
              subst st'.
              exists pv', num_proc.
              trivial.
              apply H2 with inq'; eauto.
          (* AbQ_RealQ proved *)

          - (* case3: l = l' ++ i :: nil ,  l' <> nil *)
            destruct Htail as [l' [Hl [Hl'notnil Hoccl']]].
            destruct (H2 _ _ _ Hi Hgeti) as [pv [nx HLgeti]].
            rewrite HLgeti.
            subst l.
            
            rename l' into lx.
            destruct (app_tail_dec _ lx) as [ Hl' | [l' [t Hl']]]; subst lx.
            destruct (Hl'notnil (refl_equal _)).
            clear Hl'notnil.
            assert (Htin: In t ((l' ++ t :: nil) ++ i :: nil)).
            apply in_or_app.
            left.
            apply in_or_app.
            right.
            simpl; left; trivial.
            assert (Ht: 0 <= t < num_proc).
            apply (Hvalid_abq_range (Int.unsigned n) _ ((l' ++ t :: nil) ++ i :: nil)); eauto.
            assert (Hti: i <> t).
            intro HF.
            subst i.
            rewrite count_occ_plus_app in Hoccl'.
            rewrite plus_comm in Hoccl'.
            simpl in Hoccl'.
            zeq_simpl.
            simpl in Hoccl'.
            inversion Hoccl'.
            rename l' into lx.
            destruct (app_tail_dec _ lx) as [ Hl' | [l' [t' Hl']]]; subst lx.

            + (* case3-1: l = nil ++ (t::nil) ++ i :: nil ,  l' <> nil *)
              unfold app in * .
              simpl in Hm.
              destruct Hm as [Htl [st'' [pv' [HLgett [Hhd [Hpv [st' HLgeti']]]]]]].
              subst tl hd pv'.
              rewrite HLgeti in HLgeti'.
              inversion HLgeti'; subst st' pv nx; clear HLgeti'.
              zeq_simpl.
              assert (t <> num_proc).
              omega.
              zeq_simpl.
              rewrite HLgett.
              assert (remove zeq i (t::i ::nil) = t ::nil).
              simpl.
              zeq_simpl.
              rewrite zeq_false; trivial.
              rewrite zeq_false; trivial.
              rewrite H4 in HQ.
              clear H4.
              eexists; split; eauto.
              inversion  HQ.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.
              * (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l Hqi Hget.
                rewrite ZMap.gsspec in Hget.
                unfold ZIndexed.eq in Hget.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi.
                exists t, t.
                split; trivial.
                inversion Hget; subst l; clear Hget.
                simpl.
                split; trivial.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st''.
                trivial.
                destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hmm]]].
                exists hd', tl'.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.
                
              * (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                rewrite ZMap.gsspec in Hgeti'.
                unfold ZIndexed.eq in Hgeti'.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i'.
                zeq_simpl.
                inversion Hgeti'.
                subst tds.
                exists num_proc, t; trivial.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'.
                assert (st'' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett in Hxx.
                inversion Hxx.
                trivial.
                subst st''.
                exists num_proc, num_proc.
                trivial.
                apply H2 with inq'; eauto.
            (* AbQ_RealQ proved *)

            + (* case3-2: l = l' ++ (t::nil) ++ i :: nil ,  l' <> nil *)
              assert (Hi_l': ~ In i l').
              intro HF.
              rewrite count_occ_plus_app in Hoccl'.
              rewrite count_occ_plus_app in Hoccl'.
              rewrite <- plus_assoc in Hoccl'.
              clear - HF Hoccl'.
              apply (count_occ_zero_notin _ zeq) in HF; trivial.
              destruct (count_occ zeq l' i); trivial.
              simpl in Hoccl'.
              inversion Hoccl'.
              assert (Ht'in: In t' (((l' ++ t' :: nil) ++ t:: nil) ++ i :: nil)).
              apply in_or_app.
              left.
              apply in_or_app.
              left.
              apply in_or_app.
              right.
              simpl; left; trivial.
              assert (Ht': 0 <= t' < num_proc).
              apply (Hvalid_abq_range (Int.unsigned n) _ (((l' ++ t' :: nil) ++ t:: nil) ++ i :: nil)); eauto.
              assert (Hit': i <> t').
              intro HF.
              subst i.
              rewrite count_occ_plus_app in Hoccl'.
              rewrite count_occ_plus_app in Hoccl'.
              rewrite <- plus_assoc in Hoccl'.
              rewrite <- plus_comm in Hoccl'.
              simpl in Hoccl'.
              zeq_simpl.
              simpl in Hoccl'.
              inversion Hoccl'.
              assert (Htt': t <> t').
              intro HF.
              subst t'.
              assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
              rewrite count_occ_plus_app in Hx.
              rewrite <- app_assoc in Hx.
              rewrite count_occ_plus_app in Hx.
              rewrite <- app_comm_cons in Hx.
              unfold app in Hx.
              rewrite <- plus_assoc in Hx.
              rewrite <- plus_comm in Hx.
              assert (count_occ zeq (t :: t :: nil) t = 2%nat).
              simpl.
              zeq_simpl; trivial.
              rewrite H3 in Hx.
              simpl in Hx.
              inversion Hx.

              assert (((l' ++ t' :: nil) ++ t :: nil) <> nil).
              intro HF.
              apply app_eq_nil in HF.
              destruct HF.
              inversion H4.
              destruct (match_next_prev_elim_tail _ _ _ _ _ _ _ _ (refl_equal _) H3 Hm)
                as [hd' [Hhd [Hm' [st' HLgeti_]]]].
              subst hd.
              rewrite HLgeti in HLgeti_; inversion HLgeti_; subst st' hd' pv; clear HLgeti_.
              assert (Hnil2: ((l' ++ t' :: nil)) <> nil).
              intros HF.
              apply app_eq_nil in HF.
              destruct HF.
              inversion H5.
              destruct (match_next_prev_elim_tail _ _ _ _ _ _ _ _ (refl_equal _) Hnil2 Hm')
                as [hd' [Hhd' [Hm'' [st' HLgett]]]].
              subst nx.
              assert (Htneq : t <> num_proc).
              omega.
              zeq_simpl.
              rewrite zeq_false; trivial.
              rewrite HLgett.

              eexists; split; eauto.
              inversion  HQ.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.
              * (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l Hqi Hget.
                rewrite ZMap.gsspec in Hget.
                unfold ZIndexed.eq in Hget.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi.
                exists t, tl.
                split; trivial.
                inversion Hget; subst l; clear Hget.
                assert (remove zeq i (((l' ++ t' :: nil) ++ t :: nil) ++ i :: nil) = ((l' ++ t' :: nil) ++ t :: nil)).
                rewrite remove_app.
                rewrite remove_app.
                rewrite remove_app.
                assert (count_occ zeq l' i = 0%nat).
                apply count_occ_notin_zero; auto.
                rewrite (count_occ_remove_neq _ zeq _ i); trivial.
                assert (remove zeq i (t'::nil) = t' :: nil).
                simpl.
                rewrite zeq_false; trivial.
                rewrite H6.
                assert (remove zeq i (t::nil) = t :: nil).
                simpl.
                rewrite zeq_false; trivial.
                rewrite H7.
                assert (remove zeq i (i::nil) = nil).
                simpl.
                zeq_simpl; trivial.
                rewrite H8.
                rewrite app_nil_r.
                trivial.
                rewrite H4.
                clear H4. 
                (* new *)
                assert (Hhd':= match_next_prev_implies_hd _ _ _ _ _ _ _ Hm'').
                subst hd'.
                apply match_prev_next_intro_tail with (l' ++ t' :: nil) st' t'; eauto.
                apply match_next_prev_presv_set_notin; auto.
                apply (count_occ_zero_notin _ zeq).
                assert (Hx:=Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite plus_comm in Hx.
                simpl in Hx.
                rewrite plus_comm in Hx.
                simpl in Hx.
                rewrite plus_comm in Hx.
                simpl in Hx.
                rewrite count_occ_plus_app.
                rewrite count_occ_sig_zero; auto.
                rewrite plus_comm.
                simpl.
                inversion Hx; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                trivial.

                destruct (H1 _ _ Hqi Hget) as [hd'' [tl' [HLget Hmm]]].
                exists hd'', tl'.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.
                
              * (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                rewrite ZMap.gsspec in Hgeti'.
                unfold ZIndexed.eq in Hgeti'.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i'. 
                rewrite zeq_false; trivial.
                inversion Hgeti'.
                subst tds'.
                exists num_proc, t; trivial.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'.
                assert (st' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett in Hxx.
                inversion Hxx.
                trivial.
                subst st'.
                exists num_proc, hd'.
                trivial.
                apply H2 with inq'; eauto.
          (* AbQ_RealQ proved *)

          - (* case4: l = l' ++ (i :: nil) ++ l'',  l' <> nil, l'' <> nil *)
            destruct Hmid as [l' [l'' [Hl [Hl'nnil [Hoccl' [Hl''nnil Hoccl'']]]]]].
            destruct (H2 _ _ _ Hi Hgeti) as [pv [nx HLgeti]].
            rewrite HLgeti.
            subst l.
            
            rename l' into lx.
            destruct (app_tail_dec _ lx) as [ Hl | [l [t Hl]]]; subst lx.
            destruct (Hl'nnil (refl_equal _)).
            rename Hl'nnil into Hltnnil.
            assert (Htin: In t ((l ++ t :: nil) ++ (i :: nil) ++ l'')).
            apply in_or_app.
            left.
            apply in_or_app.
            right.
            simpl; left; trivial.
            assert (Ht: 0 <= t < num_proc).
            apply (Hvalid_abq_range (Int.unsigned n) _ ((l ++ t :: nil) ++ (i :: nil) ++ l'')); eauto.
            assert (Hti: i <> t).
            intro HF.
            subst i.
            rewrite count_occ_plus_app in Hoccl'.
            rewrite plus_comm in Hoccl'.
            simpl in Hoccl'.
            zeq_simpl.
            simpl in Hoccl'.
            inversion Hoccl'.
            rename l'' into lx.
            destruct lx as [ | t' l'].
            destruct (Hl''nnil (refl_equal _)).
            assert (Ht'in: In t' ((l ++ t :: nil) ++ (i :: nil) ++ (t' ::l'))).
            apply in_or_app.
            right.
            apply in_or_app.
            right.
            simpl; left; trivial.
            assert (Ht': 0 <= t' < num_proc).
            apply (Hvalid_abq_range (Int.unsigned n) _ ((l ++ t :: nil) ++ (i :: nil) ++ (t'::l'))); eauto.
            assert (Ht'i: i <> t').
            intro HF.
            subst i.
            simpl in Hoccl''.
            zeq_simpl.
            inversion Hoccl''.
            
            destruct (match_next_prev_split_into_three _ _ _ _ _ _ _ _ Hltnnil Hl''nnil Hm)
              as [tl' [hd' [st' [HLgeti_ [Hmleft Hmright]]]]].
            rewrite HLgeti in HLgeti_.
            inversion HLgeti_; subst st' tl' hd'; clear HLgeti_.

            assert (Hhd := match_next_prev_implies_tl _ _ _ _ _ _ _ Hmleft).
            subst pv.
            assert (Htl := match_next_prev_implies_hd _ _ _ _ _ _ _ Hmright).
            subst nx.
            destruct (zeq t' num_proc) as [Hx | _].
            elimtype False.
            omega.
            destruct (zeq t num_proc) as [Hx | _].
            elimtype False.
            omega.

            rename l into lx.
            destruct (app_tail_dec _ lx) as [ Hl | [l [t1 Hl]]]; subst lx.
            rename l' into lx.
            destruct lx as [ | t2 l'].

            + (* case4-1: l = (nil ++ (t1::nil) ++ (t::nil) ++ (i::nil) ++ (t'::nil) *)

              unfold app in * .
              simpl in Hmright.
              destruct Hmright as [Hnx [Htl [st'' HLgett]]].
              subst tl. clear Hnx.

              simpl in Hmleft.
              destruct Hmleft as [Hhd [_ [st' HLgett']]].
              rewrite HLgett.
              rewrite HLgett'.
              
              assert (remove zeq i (t :: i :: t' :: nil) = t :: t' :: nil).
              simpl.
              repeat zeq_simpl. 
              trivial.
              rewrite H3 in HQ; clear H3.

              eexists; split; eauto.
              inversion  HQ.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.

              * (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l Hqi Hget.
                rewrite ZMap.gsspec in Hget.
                unfold ZIndexed.eq in Hget.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi.
                exists hd, t.
                split; trivial.
                inversion Hget; subst l; clear Hget.
                simpl.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st'', t'.
                split; trivial.
                split; trivial.
                split; trivial.
                exists st'.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                assert (Htt' : t <> t').
                intro HF.
                subst t' hd.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                simpl in Hx.
                repeat zeq_simpl. 
                inversion Hx.
                repeat zeq_simpl. rewrite ZMap.gss. trivial.
                destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hmm]]].
                exists hd', tl'.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                
              * (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                rewrite ZMap.gsspec in Hgeti'.
                unfold ZIndexed.eq in Hgeti'.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i'.
                zeq_simpl.
                inversion Hgeti'.
                subst tds'.
                exists t', t; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                repeat zeq_simpl; auto.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'.
                assert (st'' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett in Hxx.
                inversion Hxx.
                trivial.
                subst st''.
                exists t', num_proc.
                trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq i' t') as [ Hi'eqt' | Hi'neqt' ].
                subst i'.
                assert (st' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett' in Hxx.
                inversion Hxx.
                trivial.
                subst st'.
                exists num_proc, t.
                trivial.
                apply H2 with inq'; eauto.
            (* AbQ_RealQ proved *)

            + (* case4-2: l = (nil ++ (t1::nil) ++ (t::nil) ++ (i::nil) ++ (t'::t2::nil) *)

              assert (Hit2: i <> t2).
              intro HF.
              subst t2.
              simpl in Hoccl''.
              repeat zeq_simpl.
              inversion Hoccl''.
              assert (Hi_l': ~ In i l').
              simpl in Hoccl''.
              repeat zeq_simpl.
              apply (count_occ_zero_notin _ zeq); trivial.
              assert (Ht2in: In t2 ((nil ++ t :: nil) ++ (i:: nil) ++ (t' :: t2 :: l'))).
              apply in_or_app.
              right.
              apply in_or_app.
              right.
              simpl; right; left; trivial.
              assert (Ht2: 0 <= t2 < num_proc).
              apply (Hvalid_abq_range (Int.unsigned n) _ 
                                      ((nil ++ t :: nil) ++ (i :: nil) ++ t' :: t2 :: l')); eauto.
              assert (Htt': t' <> t2).
              intro HF.
              subst t2.
              assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t' Ht' Ht'in).
              rewrite count_occ_plus_app in Hx.
              rewrite count_occ_plus_app in Hx.
              rewrite count_occ_plus_app in Hx.
              rewrite plus_assoc in Hx.
              rewrite plus_comm in Hx.

              rewrite count_occ_plus_cons in Hx.
              rewrite (count_occ_plus_cons _ zeq l') in Hx.
              assert (count_occ zeq (t' :: nil) t' = 1 % nat).
              simpl.
              repeat zeq_simpl; trivial.
              rewrite H3 in Hx.
              simpl in Hx.
              inversion Hx.

              unfold app in * .
              simpl in Hmright.
              destruct Hmright as [Hnx [Htl [st'' HLgett]]].
              subst tl. clear Hnx.

              destruct (match_prev_next_elim3 _ _ _ _ _ _ _ Hmleft) as [_ [st' [pv' [HLgett' Hmleft']]]]. 
              intro HF; discriminate HF.
              rewrite HLgett.
              rewrite HLgett'.
              
              assert (remove zeq i (t :: i :: t' :: t2 :: l') = t :: t' :: t2 :: l').
              simpl.
              repeat zeq_simpl. 
              rewrite count_occ_remove_neq.
              trivial.
              apply count_occ_notin_zero; trivial.
              rewrite H3 in HQ; clear H3.

              eexists; split; eauto.
              inversion  HQ.
              constructor; eauto; simpl.

              (* to prove AbQ_RealQ *)
              constructor.

              * (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l Hqi Hget.
                rewrite ZMap.gsspec in Hget.
                unfold ZIndexed.eq in Hget.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi.
                exists hd, t.
                split; trivial.
                inversion Hget; subst l; clear Hget.
                apply match_prev_next_intro3.
                intro HF; discriminate HF.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st'', t'.
                split; trivial. 
                apply match_next_prev_presv_set_notin; eauto.
                apply match_prev_next_intro3.
                intro HF; discriminate HF.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st', pv'.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t' Ht' Ht'in).
                assert (t :: i :: t' :: t2 :: l' = (t :: i :: nil) ++ (t' :: nil) ++ (t2 :: l')).
                simpl.
                trivial.
                rewrite H3 in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                assert (count_occ zeq (t' :: nil) t' = 1 %nat).
                simpl; zeq_simpl; trivial.
                rewrite H5 in Hx.
                apply (count_occ_zero_notin _ zeq); trivial.
                rewrite plus_comm in Hx.
                rewrite <- plus_assoc in Hx.
                assert (forall n, 1 + n = 1 -> n = 0)%nat.
                clear; intro n; omega.
                apply H6 in Hx.
                apply plus_is_O in Hx.
                destruct Hx; trivial.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                assert (t :: i :: t' :: t2 :: l' = (t :: i :: nil) ++ (t' :: t2 :: l')).
                simpl.
                trivial.
                rewrite H3 in Hx.
                rewrite count_occ_plus_app in Hx.
                assert (count_occ zeq (t :: i:: nil) t = 1 %nat).
                simpl. 
                repeat zeq_simpl. 
                trivial.
                rewrite H5 in Hx.
                apply (count_occ_zero_notin _ zeq); trivial.
                assert (forall n, 1 + n = 1 -> n = 0)%nat.
                clear; intro n; omega.
                apply H6 in Hx.
                trivial.

                destruct (H1 _ _ Hqi Hget) as [hd' [tl' [HLget Hmm]]].
                exists hd', tl'.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                
              * (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                rewrite ZMap.gsspec in Hgeti'.
                unfold ZIndexed.eq in Hgeti'.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i'.
                zeq_simpl.
                inversion Hgeti'.
                subst tds'.
                exists t', t; trivial.
                repeat zeq_simpl; auto.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'.
                assert (st'' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett in Hxx.
                inversion Hxx.
                trivial.
                subst st''.
                exists t', num_proc.
                trivial.
                destruct (zeq i' t') as [ Hi'eqt' | Hi'neqt' ].
                subst i'.
                assert (st' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett' in Hxx.
                inversion Hxx.
                trivial.
                subst st'.
                exists pv', t.
                trivial.
                apply H2 with inq'; eauto.
            (* AbQ_RealQ proved *)

            + rename l' into lx.
              destruct lx as [ | t2 l'].

              * (* case4-3: l = (l ++ (t1::nil) ++ (t::nil) ++ (i::nil) ++ (t'::nil) *)

                assert (Hit1: i <> t1).
                intro HF.
                subst t1.
                rewrite count_occ_plus_app in Hoccl'.
                apply plus_is_O in Hoccl'.
                destruct Hoccl'.
                rewrite count_occ_plus_app in H3.
                apply plus_is_O in H3.
                destruct H3.
                simpl in H5.
                zeq_simpl.
                inversion H5.
                assert (Hi_l': ~ In i l).
                rewrite count_occ_plus_app in Hoccl'.
                apply plus_is_O in Hoccl'.
                destruct Hoccl'.
                rewrite count_occ_plus_app in H3.
                apply plus_is_O in H3.
                destruct H3.
                apply (count_occ_zero_notin _ zeq) ; trivial.
                assert (Htt1: t <> t1).
                intro HF.
                subst t1.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).

                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.

                rewrite count_occ_sig_one in Hx.
                rew_arith_H (forall n m,  n + 1 + 1 + m = Datatypes.S (Datatypes.S (n+m)))%nat Hx.
                inversion Hx.

                assert (Htt': t <> t').
                intro HF.
                subst t'.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 1 + (m + 1) = Datatypes.S (Datatypes.S (n+m)))%nat Hx.
                inversion Hx.

                assert (Htnin: ~ In t l).
                apply (count_occ_zero_notin _ zeq).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rew_arith_H (forall n m,  n + 1 + m = Datatypes.S (n+m))%nat Hx.

                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                simpl in Hx.
                inversion Hx.
                rewrite plus_comm.
                simpl.
                rewrite plus_comm.
                simpl.
                trivial.

                assert (Htnin_2: ~ In t (l ++ t1 :: nil)).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 1 + (0 + m) = Datatypes.S (n+m))%nat Hx.
                apply (count_occ_zero_notin _ zeq).
                rewrite count_occ_plus_app.
                rewrite count_occ_sig_zero; auto.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx; clear H3.
                apply plus_is_O in Hx.
                destruct Hx.
                omega.

                assert (Ht2in: In t1 (((l ++ t1 :: nil) ++ (t::nil)) ++ (i:: nil) ++ (t' :: nil))).
                apply in_or_app.
                left.
                apply in_or_app.
                left.
                apply in_or_app.
                right; simpl; left; trivial.
                assert (Ht2: 0 <= t1 < num_proc).
                apply (Hvalid_abq_range (Int.unsigned n) _ 
                                        (((l ++ t1 ::nil) ++ t :: nil) ++ (i :: nil) ++ t' :: nil)); eauto.
                assert (Ht't1: t' <> t1).
                intro HF.
                subst t1.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t' Ht' Ht'in).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx.
                rewrite count_occ_sig_zero in Hx.
                simpl in Hx.
                rewrite plus_comm in Hx.
                simpl in Hx.
                rewrite plus_comm in Hx.
                simpl in Hx.
                rewrite plus_comm in Hx.
                simpl in Hx.
                inversion Hx.
                auto.
                auto.
                assert (Htinin : ~ In t' (l ++ t1 :: nil)).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t' Ht' Ht'in).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 0 + (m + 1) = Datatypes.S (n+m))%nat Hx.
                apply (count_occ_zero_notin _ zeq).
                rewrite count_occ_plus_app.
                rewrite count_occ_sig_zero; auto.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx; clear H3.
                apply plus_is_O in Hx.
                destruct Hx.
                omega.

                simpl in Hmleft.
                destruct Hmleft as [Hhd [_ [st'' HLgett']]].
                subst hd. 

                assert (Hx : (l++t1::nil) <> nil).
                intro HF. 
                destruct (app_cons_not_nil _ _ _ (eq_sym HF)). 
                destruct (match_next_prev_elim_tail _ (l++t1::nil) t _ _ _ _ _ (refl_equal _) Hx Hmright) 
                  as [hd' [Hhd [Hmright' [st' HLgett]]]]. 
                rewrite HLgett.
                rewrite HLgett'.
                
                assert ((remove zeq i (((l ++ t1 :: nil) ++ t :: nil) 
                                         ++ (i :: nil) ++ t' :: nil)) = l ++ t1 :: t :: t' :: nil).
                simpl.
                rewrite remove_app.
                rewrite remove_app.
                rewrite remove_app.

                rewrite remove_cons_eq.
                rewrite remove_sig_neq; auto.
                rewrite remove_sig_neq; auto.
                rewrite remove_sig_neq; auto.
                rewrite remove_neq; auto.
                rewrite <- app_assoc.
                rewrite <- app_assoc.
                rewrite <- app_comm_cons.
                rewrite <- app_comm_cons.
                simpl.
                trivial.
                rewrite H3 in HQ; clear H3.

                eexists; split; eauto.
                inversion  HQ.
                constructor; eauto; simpl.

                (* to prove AbQ_RealQ *)
                constructor.

                (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi l' Hqi Hget.
                rewrite ZMap.gsspec in Hget.
                unfold ZIndexed.eq in Hget.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi.
                exists t', tl.
                split; trivial.
                inversion Hget; subst l'; clear Hget.

                assert (HL : l ++ t1 :: t :: t' :: nil = (l ++ t1 ::nil) ++ (t :: t' :: nil)).
                rewrite <- app_assoc.
                rewrite <- app_comm_cons.
                simpl.
                trivial.
                rewrite HL.
                apply match_next_prev_merge with hd' t; auto.
                intro HF; discriminate HF.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_prev_next_intro3.
                intro HF; discriminate HF.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st', t'.
                split; trivial. 
                apply match_next_prev_presv_set_notin; eauto.
                simpl.
                split; trivial.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st''; trivial.
                intro HF.
                simpl in HF.
                destruct HF; auto.

                destruct (H1 _ _ Hqi Hget) as [hdx [tlx [HLget Hmm]]].
                exists hdx, tlx.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                
                (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                rewrite ZMap.gsspec in Hgeti'.
                unfold ZIndexed.eq in Hgeti'.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i'.
                zeq_simpl.
                inversion Hgeti'.
                subst tds'.
                repeat zeq_simpl.
                exists t', t; trivial.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'.
                assert (st' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett in Hxx.
                inversion Hxx.
                trivial.
                subst st'.
                exists t', hd'.
                trivial.
                destruct (zeq i' t') as [ Hi'eqt' | Hi'neqt' ].
                subst i'.
                assert (st'' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett' in Hxx.
                inversion Hxx.
                trivial.
                subst st''.
                exists num_proc, t.
                trivial.
                apply H2 with inq'; eauto.
              (* AbQ_RealQ proved *)

              * (* case4-4: l = (l ++ (t1::nil) ++ (t::nil) ++ (i::nil) ++ (t':: t2 :: l') *)
                assert (Hit1: i <> t1).
                intro HF.
                subst t1.
                rewrite count_occ_plus_app in Hoccl'.
                apply plus_is_O in Hoccl'.
                destruct Hoccl'.
                rewrite count_occ_plus_app in H3.
                apply plus_is_O in H3.
                destruct H3.
                simpl in H5.
                zeq_simpl.
                inversion H5.
                assert (Hi_l': ~ In i l).
                rewrite count_occ_plus_app in Hoccl'.
                apply plus_is_O in Hoccl'.
                destruct Hoccl'.
                rewrite count_occ_plus_app in H3.
                apply plus_is_O in H3.
                destruct H3.
                apply (count_occ_zero_notin _ zeq) ; trivial.
                assert (Htt1: t <> t1).
                intro HF.
                subst t1.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).

                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.

                rewrite count_occ_sig_one in Hx.
                rew_arith_H (forall n m,  n + 1 + 1 + m = Datatypes.S (Datatypes.S (n+m)))%nat Hx.
                inversion Hx.

                assert (Htt': t <> t').
                intro HF.
                subst t'.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite (count_occ_cons_eq zeq (t2::l')) in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 1 + (0 + Datatypes.S m) = Datatypes.S (Datatypes.S (n+m)))%nat Hx.
                inversion Hx.

                assert (Htnin: ~ In t l).
                apply (count_occ_zero_notin _ zeq).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 1 + ( 0 + m) = Datatypes.S (n+m))%nat Hx.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx.
                apply plus_is_O in Hx.
                destruct Hx; trivial.

                assert (Ht't1: t' <> t1).
                intro HF.
                subst t1.
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t' Ht' Ht'in).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 1 + 0 + (0 + m) = Datatypes.S (n+m))%nat Hx.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx.
                apply plus_is_O in Hx.
                destruct Hx.
                rewrite count_occ_cons_eq in H5; trivial.
                inversion H5.

                assert (Htinin : ~ In t' (l ++ t1 :: nil)).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t' Ht' Ht'in).
                apply (count_occ_zero_notin _ zeq).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite (count_occ_cons_eq zeq (t2::l') (refl_equal t')) in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 0 + ( 0 + Datatypes.S m) = Datatypes.S (n+m))%nat Hx.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx.
                apply plus_is_O in Hx.
                destruct Hx; trivial.
                rewrite count_occ_plus_app.
                rewrite H4.
                rewrite count_occ_cons_neq; auto.

                assert (Htnin_2 : ~ In t (l ++ t1 :: nil)).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                apply (count_occ_zero_notin _ zeq).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 1 + ( 0 + m) = Datatypes.S (n+m))%nat Hx.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx.
                apply plus_is_O in Hx.
                destruct Hx; trivial.
                rewrite count_occ_plus_app.
                rewrite H4.
                rewrite count_occ_cons_neq; auto.

                assert (Hit2: i <> t2).
                intro HF.
                subst t2.
                assert (t' :: i :: l' = (t' :: nil) ++ (i::nil) ++ l').
                simpl.
                trivial.
                rewrite H3 in Hoccl''. 
                rewrite count_occ_plus_app in Hoccl''.
                rewrite count_occ_plus_app in Hoccl''.
                apply plus_is_O in Hoccl''.
                destruct Hoccl''.
                apply plus_is_O in H5.
                destruct H5.
                simpl in H5.
                zeq_simpl.
                inversion H5.

                assert (Hinin : ~ In i l').
                assert (t' :: t2 :: l' = (t' :: nil) ++ (t2::nil) ++ l').
                simpl.
                trivial.
                rewrite H3 in Hoccl''. 
                rewrite count_occ_plus_app in Hoccl''; auto.
                rewrite count_occ_plus_app in Hoccl''; auto.
                apply plus_is_O in Hoccl''.
                destruct Hoccl''.
                apply plus_is_O in H5.
                destruct H5.
                apply (count_occ_zero_notin _ zeq) ; trivial.
                

                assert (Htnin_3:  ~ In t (t' :: t2 :: l')).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t Ht Htin).
                apply (count_occ_zero_notin _ zeq).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_sig_one in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 1 + ( 0 + m) = Datatypes.S (n+m))%nat Hx.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx.
                apply plus_is_O in Hx.
                destruct Hx; trivial.

                assert (Ht'nin: ~ In t' (t2 :: l')).
                assert (Hx := Hvalid_queue_disjoint (Int.unsigned n) _ Hn Hgetl t' Ht' Ht'in).
                apply (count_occ_zero_notin _ zeq).
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite count_occ_plus_app in Hx.
                rewrite (count_occ_cons_eq zeq (t2::l') (refl_equal t')) in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rewrite count_occ_sig_zero in Hx; auto.
                rew_arith_H (forall n m,  n + 0 + 0 + ( 0 + Datatypes.S m) = Datatypes.S (n+m))%nat Hx.
                assert (forall n, Datatypes.S n = 1 -> n = 0)%nat.
                clear. intros. omega.
                apply H3 in Hx.
                apply plus_is_O in Hx.
                destruct Hx; trivial.

                destruct (match_prev_next_elim3 _ _ _ _ _ _ _ Hmleft) as [_ [st' [pv' [HLgett' Hmleft']]]].
                intro HF; discriminate HF.

                assert (Hx : (l++t1::nil) <> nil).
                intro HF.
                destruct (app_cons_not_nil _ _ _ (eq_sym HF)).
                destruct (match_next_prev_elim_tail _ (l++t1::nil) t _ _ _ _ _ (refl_equal _) Hx Hmright) 
                  as [hd' [_ [Hmright' [st'' HLgett]]]]. 
                rewrite HLgett.
                rewrite HLgett'.
                
                assert ((remove zeq i (((l ++ t1 :: nil) ++ t :: nil) 
                                         ++ (i :: nil) ++ t' :: t2 :: l')) = l ++ t1 :: t :: t' :: t2 :: l').
                simpl.
                rewrite remove_app.
                rewrite remove_app.
                rewrite remove_app.

                rewrite remove_cons_eq.
                rewrite remove_sig_neq; auto.
                rewrite remove_sig_neq; auto.
                rewrite remove_neq; auto.
                rewrite <- app_assoc.
                rewrite <- app_assoc.
                rewrite <- app_comm_cons.
                rewrite <- app_comm_cons.
                rewrite remove_cons_neq; auto.
                rewrite remove_cons_neq; auto.
                rewrite remove_neq; auto.
                rewrite H3 in HQ; clear H3.

                eexists; split; eauto.
                inversion  HQ.
                constructor; eauto; simpl.

                (* to prove AbQ_RealQ *)
                constructor.

                (* 1st: abqueue_match_dllist *)
                unfold abqueue_match_dllist.
                intros qi lx Hqi Hget.
                rewrite ZMap.gsspec in Hget.
                unfold ZIndexed.eq in Hget.
                destruct (zeq qi (Int.unsigned n)) as [ Hqieq | Hqineq].
                subst qi.
                exists hd, tl.
                split; trivial.
                inversion Hget; subst lx; clear Hget.

                assert (HL : l ++ t1 :: t :: t' :: t2 :: l' = (l ++ t1 ::nil) ++ (t :: nil) ++ (t' :: t2 :: l')).
                simpl.
                rewrite <- app_assoc.
                simpl.
                trivial.
                rewrite HL.
                apply match_next_prev_merge with hd' t; auto.
                intro HF; discriminate HF.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_prev_next_intro3.
                intro HF; discriminate HF.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st'', t'.
                split; trivial. 
                apply match_next_prev_presv_set_notin; eauto.
                apply match_prev_next_intro3.
                intro HF; discriminate HF.
                split; trivial.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                zeq_simpl.
                exists st', pv'; trivial.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.

                destruct (H1 _ _ Hqi Hget) as [hdx [tlx [HLget Hmm]]].
                exists hdx, tlx.
                split; trivial.
                apply match_next_prev_presv_set_notin; eauto.
                apply match_next_prev_presv_set_notin; eauto.
                
                (* 2nd: abtcbpool_tcbpool *)
                unfold abtcbpool_tcbpool.
                intros i' tds' inq' Hi' Hgeti'.
                rewrite ZMap.gsspec in Hgeti'.
                unfold ZIndexed.eq in Hgeti'.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                rewrite ZMap.gsspec.
                unfold ZIndexed.eq.
                destruct (zeq i' i) as [ Hieq | Hineq ].
                subst i'.
                zeq_simpl.
                inversion Hgeti'.
                subst tds'.
                repeat zeq_simpl.
                exists t', t; trivial.
                destruct (zeq i' t) as [ Hi'eq | Hi'neq ].
                subst i'.
                assert (st'' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett in Hxx.
                inversion Hxx.
                trivial.
                subst st''.
                exists t', hd'.
                trivial.
                destruct (zeq i' t') as [ Hi'eqt' | Hi'neqt' ].
                subst i'.
                assert (st' = tds').
                destruct (H2 _ _ _ Hi' Hgeti') as [pv'x [nx'x Hxx]].
                rewrite HLgett' in Hxx.
                inversion Hxx.
                trivial.
                subst st'.
                exists pv', t.
                trivial.
                apply H2 with inq'; eauto.
        (* AbQ_RealQ proved *)
        Qed.

      End Exists.
      
      Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
      Proof.
        accessor_prop_tac.
        - eapply flatmem_store_exists; eauto.
      Qed.          

      Ltac sim_oplus_split_final D :=
        match goal with
          | |- sim _ ?T1 ?T2 =>
            let L1 := construct_passthrough_layer T1 T2 in
            let L2 := construct_left_layer T1 T2 D in
            match L2 with
              | ∅ => change T2 with L1; sim_oplus_split_straight
              | _ => change T2 with (L1 ⊕ L2); apply sim_left; sim_oplus_split_straight
            end
        end.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) pabqueue pqueueinit.
      Proof.
        sim_oplus.
        - apply fload_sim.
        - apply fstore_sim.
        - apply flatmem_copy_sim.
        - apply vmxinfo_get_sim.
        - apply device_output_sim.
        - apply pfree_sim.
        - apply setPT_sim.
        - apply ptRead_sim. 
        - apply ptResv_sim.
        - apply kctxt_new_sim.
        - apply shared_mem_status_sim.
        - apply offer_shared_mem_sim.
        - (* get_state *)
          layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
          match_external_states_simpl.
          erewrite get_state_exists; simpl; eauto 1; reflexivity.
        - (* set_state *)
          layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
          exploit set_state_exists; eauto 1; intros (labd' & HP & HM).
          match_external_states_simpl.
        - (* tdqueue_init *)
          layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
          exploit tdqueue_init_exists; eauto 1; intros (labd' & HP & HM).
          match_external_states_simpl.
        - (* enqueue *)
          layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
          exploit enqueue_exists; eauto 1; intros (labd' & HP & HM).
          match_external_states_simpl.
        - (* dequeue *)
          layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
          exploit dequeue_exists; eauto 1; intros (labd' & HP & HM).
          match_external_states_simpl.
        - (* queue_rmv *)
          layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
          exploit queue_rmv_exists; eauto 1; intros (labd' & HP & HM).
          match_external_states_simpl.
        - apply ptin_sim.
        - apply ptout_sim.
        - apply clearCR2_sim.
        - apply container_get_nchildren_sim.
        - apply container_get_quota_sim.
        - apply container_get_usage_sim.
        - apply container_can_consume_sim.
        - apply alloc_sim. 
        - apply trapin_sim.
        - apply trapout_sim.
        - apply hostin_sim.
        - apply hostout_sim.
        - apply trap_info_get_sim.
        - apply trap_info_ret_sim.
        - apply kctxt_switch_sim.
        - layer_sim_simpl.
          + eapply load_correct2.
          + eapply store_correct2.
        (*- (* thread_free *)
          exploit thread_free_exists; eauto 1; intros (labd' & HP & HM).
          match_external_states_simpl.*)
      Qed.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
