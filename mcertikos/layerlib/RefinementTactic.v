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

(** This file provide the tactic for refinement proof between layers*)
Require Import Values.
Require Import AsmX.
Require Import Coqlib.
Require Import Integers.
Require Import LAsm.
Require Import Maps.
Require Import Memory.
Require Import CommonTactic.
Require Import Smallstep.
Require Import Errors.
Require Import Events.
Require Import AuxLemma.
Require Import Globalenvs.
Require Import AuxStateDataType.
Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.

(*
Require Import LayerTemplate.
*)

(*Ltac exist_simpl :=
  intros HP HR; inv HR; revert HP;
  subrewrite'; intros HQ; subdestruct; simpl;
  esplit; split; eauto 1;
  inv HQ; split; simpl; try reflexivity; eauto;
  constructor; simpl; try reflexivity; trivial.*)

Ltac accessor_prop_tac :=
repeat match goal with
         | |- forall _, _ => idtac
         | _ => constructor
       end; try (inversion 2); try (inversion 1); intros; trivial; try (econstructor; simpl; eauto 2; fail).

Ltac exist_simpl :=
  intros HP HR; pose proof HR as HR'; inv HR; revert HP; simpl;
  subrewrite'; intros HQ; subdestruct; simpl;
  inv HQ; simpl; refine_split; eauto 1;
  simpl; try reflexivity; eauto;
  try constructor; simpl; try reflexivity; trivial
  ;try (inv HR'; assumption; fail).


Ltac compatsim_simpl' :=
  match goal with
    | [ |- compatsim_def _ _ _ ] =>
      constructor; split; try reflexivity;
      match goal with
        | |- res_le ⊤%signature _ _ =>
          repeat constructor
        | _ =>
          idtac
      end;
      try (simpl; intros s WB1 WB2 ι vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 HWB _ Hlow Hhigh Hhigh' H Hι Hmd;
           let Hmatch1 := fresh "Hmatch_ext" in
           pose proof Hmd as Hmatch1;
           inv_generic_sem H; inv Hmd)
    | _ => idtac
  end.

Ltac reduce_to_sim_step :=
  split; simpl in *; try reflexivity;
          match goal with
          | |- (_ -> _ -> true = true) /\ _ => split; [ reflexivity | idtac ]
	  | |- exists X, Some ?Y = Some X /\ _ => exists Y; split; [ reflexivity |]
          | |- res_le ⊤ _ _ => repeat constructor
          | |- res_le (@rel_top _ _) _ _ => repeat constructor
          | |- option_le _ _ _ => repeat constructor
          | _ => idtac
          end.

Ltac compatsim_simpl_inv_match H Hmd match_D :=
     let Hmatch1 := fresh "Hmatch_ext" in
     pose proof Hmd as Hmatch1; inv_generic_sem H; inv Hmd;
     match goal with
     | Hmatch':context [match_D]
       |- _ =>
           let Hmatch := fresh "Hmatch" in
           pose proof Hmatch' as Hmatch; inv Hmatch
     | _ => idtac
     end.

Ltac compatsim_simpl match_D :=
  simpl;
   match goal with
   | |- compatsim_def _ _ _ =>
     constructor;
     match goal with
     | |- sextcall_sim _ _ _ =>
       reduce_to_sim_step;
       intros s WB1 WB2 ι vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 HWB _
         Hlow Hhigh Hhigh' H Hι Hmd;
       compatsim_simpl_inv_match H Hmd match_D
     | |- sprimcall_sim _ _ _ =>
       reduce_to_sim_step;
       intros s ι rs1 m1 d1 rs1' m1' d1' rs2 m2 d2 _
         Hlow Hhigh Hhigh' ? H Hmd;
       compatsim_simpl_inv_match H Hmd match_D
     | |- sextcall_sprimcall_sim _ _ _ =>
       reduce_to_sim_step;
       intros s b ι WB1 vargs1 vargs2 vres m1 d1 m1' d1' rs2 m2 d2 _
         Hlow Hhigh Hhigh' H Hmd Hsi Hpc Hι;
       compatsim_simpl_inv_match H Hmd match_D
     end
   | _ => idtac
   end.

(*Ltac compatsim_simpl match_D :=
  match goal with
    | [ |- compatsim _ _ _ ] =>
      constructor; split; simpl in *; try reflexivity;
      match goal with
        | |- (_ -> _ -> true = true) /\ _ =>
          split; [reflexivity|]
        | |- res_le ⊤%signature _ _ =>
          repeat constructor
        | _ =>
          idtac
      end;
      try (intros s WB1 WB2 ι vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 HWB _ Hlow Hhigh Hhigh' H Hι Hmd;
           inv_generic_sem H; inv Hmd;
           match goal with
             | [Hmatch': context [match_D] |- _] =>
               pose proof Hmatch' as Hmatch; inv Hmatch
                                           | _ => idtac
           end)
  | _ => simpl
  end.*)

Ltac rewrite_store_nextblock :=
  repeat progress 
         match goal with
           | [HST: Mem.store _ _ _ _ _ = Some ?m2' |- context[Mem.nextblock ?m2']] => 
             rewrite (Mem.nextblock_store _ _ _ _ _ _ HST)
         end.

Ltac rewrite_store_outside_inject :=
  repeat progress match goal with
    | [HST: Mem.store _ ?m2 _ _ _ = Some ?m2'|- 
       Mem.inject ?ι _ ?m2'] => 
      eapply Mem.store_outside_inject in HST; try eapply HST; intros;
      match goal with
        | [Hsome: ι _ = _, Hperm: context[~ Mem.perm _ _ _ _ _] |- _] =>  
          eapply inject_forward_equal in Hsome; eauto; inv Hsome;
          eapply Hperm; try eassumption; simpl; eauto
        | _ => try eassumption                                             
      end
  end.

Ltac pattern2_refinement_simpl' relate_D:= 
  match goal with
    | [HST: Mem.store _ ?m2 _ _ _ = Some ?m2'|- Mem.inject ?ι _ ?m2'] => rewrite_store_outside_inject
    | [Hrelate: context[relate_D] |- context[relate_D]] =>
      inv Hrelate; simpl in *; split; simpl; try eassumption
    | [ |- (Mem.nextblock _ <= Mem.nextblock ?m2')%positive] => 
      rewrite_store_nextblock; try xomega
    | _ => idtac
  end.

Ltac layer_sim_simpl :=
  match goal with
    | |- sim _ (accessors ↦ _) _ =>
      apply cl_accessors_sim_intro
    | _ => apply layer_sim_intro; simpl
  end.

(*Ltac layer_sim_simpl :=
  (apply layer_sim_intro; simpl) ||
  (apply cl_accessors_sim_intro).

          Ltac move_to_head a T := 
            lazymatch T with
              | a ↦ _ => idtac
              | ?A ⊕ ?B => 
                lazymatch A with
                  | context [ a ] => 
                    lazymatch A with
                      | ?C ⊕ ?D => 
                        lazymatch C with
                          | context [a] => rewrite (associativity C D B);
                                          move_to_head a C
                          | _ => 
                              rewrite (oplus_assoc_comm_equiv C D B); 
                              move_to_head a D
                        end
                      | _ => idtac
                    end
                  | _ => 
                        rewrite (commutativity A B); move_to_head a B
                end
            end.


          Ltac oplus_assoc_simpl:=
            repeat match goal with
                     | [ |- sim _ _ ?B] => oplus_assoc_simpl_term B
                   end.

          Ltac get_head T := 
            lazymatch T with
              | ?A ⊕ ?B => 
                lazymatch A with
                  | ?C ⊕ ?D => 
                    rewrite (associativity C D B);
                      get_head C
                  | _ => idtac
               end
              |  _ => idtac 
            end.

          Ltac oplus_split:=
          lazymatch goal with
            | [ |- sim _ ?A ?B] =>
              lazymatch A with
                | (?a ↦ _) => move_to_head a B; oplus_assoc_simpl; try rewrite <- left_upper_bound
                | (?a ↦ _ ⊕ _ ) => 
                  move_to_head a B; oplus_assoc_simpl;
                    lazymatch goal with
                      | [ |- sim _ (a ↦ _ ⊕ _ ) (a ↦ _ ⊕ _ )] =>
                        apply oplus_sim_monotonic; [| oplus_split]
                      | _ => idtac
                    end
                | _ => get_head A; oplus_split
              end
            | _ => idtac
          end.

          Ltac oplus_split_simpl:= oplus_split; layer_sim_simpl; eauto 1.*)

          Ltac match_external_states_simpl :=
            refine_split; 
            match goal with
              | |- inject_incr ?f ?f => apply inject_incr_refl
              | _ => repeat (econstructor; eauto; try congruence)
            end;
            match goal with
              | |- _ PC = Vptr _ _ => eapply reg_symbol_inject; eassumption
              | |- forall _, val_inject _ _ _ => val_inject_simpl
              | _ => idtac
            end.

        Ltac kctxt_inj_simpl :=
          eapply kctxt_inj_set; eauto;
          intros; unfold Pregmap.get in *;
          repeat (rewrite Pregmap_Simpl);
          reg_destruct_simpl.


(*

Ltac match_state_simpl :=
  match goal with
    | [|- context[val_inject]] => Next_NF_Simpl; reg_destruct; eauto 1
    | _ => try (eapply Mem.put_abstract_data_inject; eauto)
  end.

Ltac primitive_simpl_aux prim functions_translated term := 
  esplit; split;
  match goal with
    | [|- context[plus]] => 
      apply plus_one; eapply LSemantics.exec_step_prim_call with (ef := prim); eauto 1;
      exploit functions_translated; eauto 1; intros [tf' [A B]]; monadInv B; trivial;
      inv_val_inject; econstructor; eauto 1; 
      try match goal with
            | [HLOW: context[term] |-_] => inv HLOW; trivial
          end
    | [|- _] => eapply TEMPLATE.MATCH_STATE; mem_norm; eauto 1
  end; match_state_simpl.

Ltac external_simpl_aux prim functions_translated term relate_RData :=
  esplit; split;
  match goal with
    | [|- context[plus]] => 
      apply plus_one; eapply LSemantics.exec_step_external with (ef := prim); eauto 1;
      exploit functions_translated; eauto 1; intros [tf' [A B]]; monadInv B; trivial;
      inv_val_inject; unfold Pregmap.get in *;
      match goal with
        | [|- context[@external_call]] => repeat (econstructor; eauto 1)
        | [|- context[Vundef]] => eapply reg_val_inject_defined; eauto 1
        | [Hinj: forall r, val_inject ?f _ _|- _ ] => 
          generalize (Hinj ESP); inversion 1; subst; try congruence; injection 1; intros; subst;
          erewrite (Mem.tget_inject (Mem__inject := Mem.inject (relate_RData f))); eauto
      end
    | [|- context[term]] => eapply TEMPLATE.MATCH_STATE; mem_norm; eauto 1
  end; try match_state_simpl.

Ltac apply_spec_aux functions_translated relate_RData := 
  match goal with
    | [|- context[Genv.find_funct_ptr]] => 
      exploit functions_translated; eauto; intros [tf' [A B]]; monadInv B; trivial
    | [|- context[@extcall_arguments]] => inv_val_inject
    | [Hinj: forall r, val_inject ?f _ _ |- context[@Mem.tget]] =>  
      intros; unfold Pregmap.get in Hinj; generalize (Hinj ESP);
      inversion 1; subst; try congruence;
      match goal with
        | [HESP: ?r0 _ = Vptr ?b1 _, HESP': Vptr ?b3 _ = ?r0 _|- _] => 
          replace b1 with b3 by congruence; 
            erewrite (Mem.tget_inject (Mem__inject := Mem.inject (relate_RData f))); eauto
      end
    | [|- ?r0 _ <> Vundef] => eapply reg_val_inject_defined; eauto 1
    | [|- (exists _, _) -> _] => 
      intros [f'[m0'[r_ [Hincr[HInj [Hle HPlus]]]]]];
        destruct HPlus as [HPlus [Hres [H_PC [H_ESP HCALLEESAVE]]]];
        esplit; simpl; mem_norm; split; [apply HPlus|]
    | _ => trivial
  end.

Ltac match_state_spec :=
  match goal with
    | [Hinj: forall r, val_inject _ _ _ |- context[val_inject]] => 
      Next_NF_Simpl; reg_destruct; subst; unfold Pregmap.get in *; eauto 1;
      match goal with
        | [H_PC: ?_r PC = _|- context[PC]] => rewrite H_PC; eauto
        | [Hres: context[loc_external_result]|- context[loc_external_result]] => simpl in Hres; rewrite Hres; eauto
        | [H_ESP: context [ESP]|- val_inject _ (_ ?reg) _] => 
          eapply val_inject_lessdef_compose; [eapply Hinj|]; destruct (preg_eq reg ESP); subst;
          [rewrite H_ESP; constructor|
           exploit (AsmExtra.reg_inv reg); eauto; destruct 1 as [? [? [? ?]]]; subst; eauto]
      end
    | _ => idtac
  end.

Ltac pattern1_match_state :=
  eapply TEMPLATE.MATCH_STATE; mem_norm; simpl; eauto; match_state_spec;
  match goal with
    | [HT: Mem.inject ?r ?f _ _, HInj: Memtype.Mem.inject ?f' _ _, Hincr: inject_incr _ ?f' |- Mem.inject ?r ?f _ _] =>
      try eapply Mem.put_abstract_data_inject; eauto;
      try instantiate (1:= r);
      rewrite  (compose_inject _ _ _ _ HT Hincr) at 2;
      apply (Mem.inject_compose_internal_right _ _ _ _ _ _ HT HInj)
    | [ |- _ <= _] => try omega
    | _ => idtac
  end.

Ltac kctxt_inj_simpl :=
  eapply kctxt_inj_set; eauto;
  intros; unfold Pregmap.get in *;
  repeat (rewrite Pregmap_Simpl);
  reg_destruct_simpl.


Notation kctxt_switch_state r' r'0 m'0 labd':= 
  (State (((((((undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: IR EDX :: IR ECX :: IR EAX :: RA :: nil) r')
                 # ESP <- (r'0 ESP)) # EDI <- (r'0 EDI))# ESI <-(r'0 ESI)) 
              # EBX <- (r'0 EBX)) # EBP <- (r'0 EBP)) 
            # PC <-(r'0 RA)) (Mem.put_abstract_data m'0 labd')).

Notation sched_state r' r'0 m'0 labd':= 
  (State (((((((undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: IR EDX :: IR ECX :: IR EAX :: RA :: nil)
                           (undef_regs (map preg_of Conventions1.temporary_regs)
                                       (undef_regs (map preg_of Conventions1.destroyed_at_call_regs) r')))
                 # ESP <- (r'0 ESP)) # EDI <- (r'0 EDI))# ESI <-(r'0 ESI)) 
              # EBX <- (r'0 EBX)) # EBP <- (r'0 EBP)) 
            # PC <-(r'0 RA)) (Mem.put_abstract_data m'0 labd')).

Ltac sched_register_refinement_simpl prim functions_translated HT Hrinj:=
  match goal with
    | [|- context[plus]] => 
      apply plus_one; eapply LSemantics.exec_step_prim_call with (ef := prim); eauto 1;
      exploit functions_translated; eauto 1; intros [tf' [A B]]; monadInv B; trivial;
      inv_val_inject; econstructor; eauto 1; try eapply HT;
      match goal with
        | [Hrgeg: ?rs ?reg = Vint ?n, Hinj: forall _, val_inject _ (Pregmap.get _ ?rs) (Pregmap.get _ ?r')
                                                     |- ?r' ?reg = Vint ?n] =>
          unfold Pregmap.get in *; specialize (Hinj reg); rewrite Hreg in Hinj; inv Hinj; trivial
      end
    | [|- _] => eapply TEMPLATE.MATCH_STATE; mem_norm; eauto 1
  end; match_state_simpl; try (eapply Hrinj; apply PregToZ_correct; simpl; eauto).

Ltac kctxt_switch_refinement_simpl r' m'0 labd' prim functions_translated:=
  match goal with
    | [HP: _ = Some (labd', ?r'0), HOS: 0<= Int.unsigned _ < 64, 
                                        Hrinj: forall _ _, _ -> val_inject _ _ (?r'0 _) |- _ ] =>
      intros HT; specialize (HT _ HOS); simpl in HT;
      exists(kctxt_switch_state r' r'0 m'0 labd'); split;
      sched_register_refinement_simpl prim functions_translated HT Hrinj
  end.

Ltac thread_sched_refinement_simpl r' m'0 labd' prim functions_translated:=
  match goal with
    | [HP: _ = Some (labd', ?r'0), HOS: 0<= _ < 64, 
                                        Hrinj: forall _ _, _ -> val_inject _ _ (?r'0 _) |- _ ] =>
      intros HT; specialize (HT _ HOS); simpl in HT;
      exists(sched_state r' r'0 m'0 labd'); split;
      sched_register_refinement_simpl prim functions_translated HT Hrinj
  end.
*)
