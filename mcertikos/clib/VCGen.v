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
(*  Tactics for proving Clight code of the Compcert verified compiler  *)
(*                                                                     *)
(*                 Developed by Xiongnan (Newman) Wu                   *)
(*                                                                     *)
(*                         Yale University                             *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the tactics for proving the Clight code using the
    Compcert verified compiler. The main tactic vcgen is the
    verification condition generator for special Clight code. It applies
    the Bigstep operational semantics of the Clight 2 language to generate
    verification conditions for a loop-free clight statement where all the
    expression can be evaluated out using the knowledge in the context,
    e.g., if the statement contains conditional statement, appropiate
    case analysis on the conditional expressions need to be applied before
    the application of the vcgen tactic so that the evaluation can go through.
    In presense of loops, the loops have to be proved separately for their
    specifications and terminations. This can be done using a saparate
    frameworks deleloped in LoopProof.v. We recommand to use the version
    of the framework with while loop with no Break, Continue, or Return
    statement in the while body, so that the proof of the loop body can
    still be automated with the vcgen tactic.

Currently we assume:
- We never take address of a local variable in the stack.
- No use of C union.

*)

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import EventsX.
Require Import Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import ClightBigstepX.
Require Import Cop.
Require Import Ctypes.
Require Import ZArith.
Require Import CDataTypes.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.  
Require Import liblayers.compat.CompatClightSem.
Require Import liblayers.compcertx.MakeProgram.
Require Import Globalenvs.
Require Import CompatClightSem.
Require Export CLemmas.
Require Import Observation.

 Hint Unfold Int.max_unsigned.
 Hint Unfold Int.modulus.
 Hint Unfold Int.half_modulus.
 Hint Unfold Int64.max_unsigned.
 Hint Unfold Int64.modulus.
 Hint Unfold Int64.half_modulus.

 Global Opaque PTree.get PTree.set "!" Z.land Z.lor.
 Open Scope Z_scope.


 (** * Auxiliary tactics used by other main tactics below. *)

 Ltac ICS H := inversion H; clear H; subst.
 Ltac Caseeq H := generalize H; apply or_ind; clear H.
 Ltac diff_ident I1 I2 := try unfold I1; try unfold I2; Coqlib.xomega.
 Ltac isn_evar v t:= match v with
                       | _ => is_evar v; fail 2
                       | _ => t
                     end.
 Ltac hasn_evar v t:= match v with
                       | _ => has_evar v; fail 2
                       | _ => t
                      end.
 Ltac seassumption := match goal with 
                        | [|- ?le ! _ = Some _] => isn_evar le eassumption
                        | [|- 0 <= ?x <= Int.max_unsigned] => hasn_evar x eassumption
                        | [|- 0 <= ?x <= Int64.max_unsigned] => hasn_evar x eassumption
                        | [|- 0 <= ?x] => hasn_evar x eassumption
                        | [|- ?x <= Int.max_unsigned] => hasn_evar x eassumption
                        | [|- ?x <= Int64.max_unsigned] => hasn_evar x eassumption
                        | _ => eassumption
                      end.
 Ltac sreflexivity := match goal with
                        | [|- _ <= _] => fail 1
                        | _ => reflexivity
                      end.

 Ltac simpleproof := assumption || omega || trivial || sreflexivity || seassumption || auto || idtac.

 Ltac clearAll :=  
   repeat match goal with
            | [H: _ |- _] => clear H
          end.

 Ltac clearAllExceptOne H := 
   generalize H; clearAll; intro.

 Ltac clearAllExceptTwo H1 H2 := 
   generalize H1 H2; clearAll; intros.

 Ltac clearAllExceptThree H1 H2 H3 := 
   generalize H1 H2 H3; clearAll; intros.

 Ltac autorewritearith := autorewrite with arith using simpleproof.

 Ltac solve_unsigned_range c x := assert(cge0: c > 0) by omega; assert(zlez: 0 <= 0) by omega; generalize(zdiv_range_le_le 0 Int.max_unsigned c (Int.unsigned x) zlez max_unsigned_gt0 cge0 (Int.unsigned_range_2 x)); omega; clear cge0 zlez.
 Ltac solve_unsigned_range_lt c x := assert(cge0: c > 0) by omega; assert(zlez: 0 <= 0) by omega; assert(xpre: 0 <= x < Int.max_unsigned) by omega; generalize(zdiv_range_le_lt 0 Int.max_unsigned c x zlez max_unsigned_gt0 cge0 xpre); omega; clear cge0 zlez xpre.

 Ltac solve_unsigned64_range c x := assert(cge0: c > 0) by omega; assert(zlez: 0 <= 0) by omega; generalize(zdiv_range_le_le 0 Int64.max_unsigned c (Int64.unsigned x) zlez max_unsigned64_gt0 cge0 (Int64.unsigned_range_2 x)); omega; clear cge0 zlez.
 Ltac solve_unsigned64_range_lt c x := assert(cge0: c > 0) by omega; assert(zlez: 0 <= 0) by omega; assert(xpre: 0 <= x < Int64.max_unsigned) by omega; generalize(zdiv_range_le_lt 0 Int64.max_unsigned c x zlez max_unsigned64_gt0 cge0 xpre); omega; clear cge0 zlez xpre.

 Ltac dischange_cmp_range_aux af :=
   match af with
                                                               | Z.shiftl _ _ => simpl; omega
                                                               | Z.shiftr _ _ => simpl; omega
                                                               | Z.land ?x ?y => apply Z_land_range; try (simpl; omega)
                                                               | Z.lor ?x ?y => apply Z_lor_range; try (simpl; omega)
                                                               | _ => repeat (match goal with
                                                                                | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                                                                | _ => fail
                                                                              end); omega
                                                             end.

 Ltac discharge_cmp := simpl; 
                    repeat (unfold sem_cmp, sem_add, sem_sub, sem_mul, sem_mod, sem_div, sem_and, sem_or, sem_xor, sem_shl, sem_shr, sem_binarith, Int.cmpu, Int.eq, Int.ltu, Int.add, Int.sub, Int.mul, Int.divu, Int.modu, Int.and, Int.or, Int.xor, Int.shl, Int.shr, Int.shru, Int64.cmpu, Int64.eq, Int64.ltu, Int64.add, Int64.sub, Int64.mul, Int64.divu, Int64.modu, Int64.and, Int64.or, Int64.xor, Int64.shl, Int64.shr, Int64.shru; repeat (autorewrite with arith);
                    match goal with
                      | [|- context[Int.unsigned Int.zero]] => change (Int.unsigned Int.zero) with 0
                      | [|- context[Int.unsigned Int.one]] => change (Int.unsigned Int.one) with 1
                      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; try omega
                      | [|- context[Int64.unsigned Int64.zero]] => change (Int64.unsigned Int64.zero) with 0
                      | [|- context[Int64.unsigned Int64.one]] => change (Int64.unsigned Int64.one) with 1
                      | [|- context[Int64.unsigned (Int64.repr _)]] => rewrite Int64.unsigned_repr; try omega
                      | [|- context [zle ?z1 ?z2]] => destruct (zle z1 z2); try omega
                      | [|- context [zlt ?z1 ?z2]] => destruct (zlt z1 z2); try omega
                      | [|- context [zeq ?z1 ?z2]] => destruct (zeq z1 z2); try omega
                      | [|- 0 <= ?af <= Int.max_unsigned] => dischange_cmp_range_aux af
                      | [|- 0 <= ?af <= Int64.max_unsigned] => dischange_cmp_range_aux af
                      | [|- bool_val _ _ = Some _] => simpl; unfold bool_val; simpl; repeat (autorewrite with arith); reflexivity
                      | _ => repeat (autorewrite with arith); (simpleproof || simpl)
                    end).

 Ltac computedivmul := match goal with
      | [|- context [?x / ?y]] => let val := eval compute in (x / y) in change (x / y) with val
      | [|- context [?x * ?y]] => let val := eval compute in (x * y) in change (x * y) with val
 end.


  (** * The tactic to automate the proof for arithmatic destructs. *)

  Ltac zdestruct := match goal with
                     | [|- context [zle ?z1 ?z2]] => destruct (zle z1 z2); try omega
                     | [|- context [zlt ?z1 ?z2]] => destruct (zlt z1 z2); try omega
                     | [|- context [zeq ?z1 ?z2]] => destruct (zeq z1 z2); try omega
                     | [H: context [zle ?z1 ?z2] |- _] => destruct (zle z1 z2); try omega
                     | [H: context [zlt ?z1 ?z2] |- _] => destruct (zlt z1 z2); try omega
                     | [H: context [zeq ?z1 ?z2] |- _] => destruct (zeq z1 z2); try omega
                     | [H: None = Some _ |- _] => inversion H
                     | [H: Some _ = None |- _] => inversion H
                     | [|- Some ?x = Some ?x \/ Some _ = Some _] => left; trivial
                     | [|- Some _ = Some _ \/ Some ?x = Some ?x] => right; trivial
                   end ; trivial.


 (** * The tactic to prove the integers fit in unsigned range. *)

 Ltac discharge_unsigned_range := match goal with
           | [|- _ /\ _] => split
           | [|- context[Int.unsigned Int.zero]] => change (Int.unsigned Int.zero) with 0
           | [|- context[Int.unsigned Int.one]] => change (Int.unsigned Int.one) with 1
           | [|- context[Int64.unsigned Int64.zero]] => change (Int64.unsigned Int64.zero) with 0
           | [|- context[Int64.unsigned Int64.one]] => change (Int64.unsigned Int64.one) with 1
           | [|- 0 <= ?af] => match af with
                         | Z.shiftl _ _ => simpl; omega
                         | Z.shiftr _ _ => simpl; omega
                         | Z.land ?x ?y => apply Z_land_range_lo; try (simpl; omega)
                         | Z.lor ?x ?y => apply Z_lor_range_lo; try (simpl; omega)
                         | Int.unsigned ?i => generalize (Int.unsigned_range i); repeat autounfold; omega
                         | Int.unsigned ?i + _ => generalize (Int.unsigned_range i); repeat autounfold; omega
                         | Int.unsigned ?i - _ => generalize (Int.unsigned_range i); repeat autounfold; omega
                         | Int.unsigned ?x / ?c => solve_unsigned_range c x
                         | ?x / ?c => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
                         | ?x / ?c + 1 => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
                         | _ => repeat (match goal with
                                          | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                          | _ => fail
                                        end); omega
                         end
           | [|- ?af <= Int.max_unsigned] => match af with
                         | Z.shiftl _ _ => simpl; omega
                         | Z.shiftr _ _ => simpl; omega
                         | Z.land ?x ?y => apply Z_land_range_hi; try (simpl; omega)
                         | Z.lor ?x ?y => apply Z_lor_range_hi; try (simpl; omega)
                         | Int.unsigned ?i => generalize (Int.unsigned_range i); repeat autounfold; omega
                         | Int.unsigned ?i + _ => generalize (Int.unsigned_range i); repeat autounfold; omega
                         | Int.unsigned ?i - _ => generalize (Int.unsigned_range i); repeat autounfold; omega
                         | Int.unsigned ?x / ?c => solve_unsigned_range c x
                         | ?x / ?c => rewrite <- Int.unsigned_repr with (z:= x); solve_unsigned_range c (Int.repr x)
                         | ?x / ?c + 1 => solve_unsigned_range_lt c x
                         | _ => repeat (match goal with
                                          | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                          | _ => fail
                                        end); omega
                         end
 end.


 Ltac discharge_unsigned64_range := match goal with
           | [|- _ /\ _] => split
           | [|- context[Int64.unsigned Int64.zero]] => change (Int64.unsigned Int64.zero) with 0
           | [|- context[Int64.unsigned Int64.one]] => change (Int64.unsigned Int64.one) with 1
           | [|- 0 <= ?af] => match af with
                         | Z.shiftl _ _ => simpl; omega
                         | Z.shiftr _ _ => simpl; omega
                         | Z.land ?x ?y => apply Z_land_range_lo; try (simpl; omega)
                         | Z.lor ?x ?y => apply Z_lor_range_lo; try (simpl; omega)
                         | Int64.unsigned ?i => generalize (Int64.unsigned_range i); repeat autounfold; omega
                         | Int64.unsigned ?i + _ => generalize (Int64.unsigned_range i); repeat autounfold; omega
                         | Int64.unsigned ?i - _ => generalize (Int64.unsigned_range i); repeat autounfold; omega
                         | Int64.unsigned ?x / ?c => solve_unsigned64_range c x
                         | ?x / ?c => rewrite <- Int64.unsigned_repr with (z:= x); solve_unsigned64_range c (Int64.repr x)
                         | ?x / ?c + 1 => rewrite <- Int64.unsigned_repr with (z:= x); solve_unsigned64_range c (Int64.repr x)
                         | _ => repeat (match goal with
                                          | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                          | _ => fail
                                        end); omega
                         end
           | [|- ?af <= Int64.max_unsigned] => match af with
                         | Z.shiftl _ _ => simpl; omega
                         | Z.shiftr _ _ => simpl; omega
                         | Z.land ?x ?y => apply Z64_land_range_hi; try (simpl; omega)
                         | Z.lor ?x ?y => apply Z64_lor_range_hi; try (simpl; omega)
                         | Int64.unsigned ?i => generalize (Int64.unsigned_range i); repeat autounfold; omega
                         | Int64.unsigned ?i + _ => generalize (Int64.unsigned_range i); repeat autounfold; omega
                         | Int64.unsigned ?i - _ => generalize (Int64.unsigned_range i); repeat autounfold; omega
                         | Int64.unsigned ?x / ?c => solve_unsigned64_range c x
                         | ?x / ?c => rewrite <- Int64.unsigned_repr with (z:= x); solve_unsigned64_range c (Int64.repr x)
                         | ?x / ?c + 1 => solve_unsigned64_range_lt c x
                         | _ => repeat (match goal with
                                          | [H: sizeof ?x = _ |- context[sizeof ?x]] => rewrite H
                                          | _ => fail
                                        end); omega
                         end
 end.

 (** * The tactic to automate the proof for the correctness of the function body using the new bigstep semantics for the language Clight 2. *)

 Lemma extcall_generic_sem_intro': forall (obs_ops : ObservationOps) (Obs: @Observation obs_ops)
                                          (stencil mem : Type)
                                          (memory_model_ops : Mem.MemoryModelOps mem) 
                                          (D : Type) (data_ops : CompatDataOps D) (HD : CompatData D)
                                          (T : Type) (targs : typelist) (tres : type)
                                          (Tsemof : GenSem.Semof (cdata D) T targs tres) 
                                          (f : T) (s : stencil) (WB : block -> Prop) (l : list val) 
                                          (m : mem) (d : cdata D) 
                                          (v : val) (d' : cdata D) initm,
                                     initm = (m, d) ->
                                     GenSem.semof f l d v d' ->
                                     sextcall_generic_sem f s WB l 
                                                          initm v (m, d').
 Proof.
   intros; subst.
   econstructor; auto.
 Qed.

 Ltac primSolveUsingHypothesis H := solve[repeat (rewrite Int.unsigned_repr); repeat (rewrite Int64.unsigned_repr); try rewrite H; try reflexivity; try omega].
 Ltac primSolveUsingRewrites spec := unfold spec; repeat progress (match goal with
                                                       | [H: ?x = _ |- context[?x]] => try rewrite H
                                                       | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; try omega
                                                       | [|- context[Int64.unsigned (Int64.repr _)]] => rewrite Int64.unsigned_repr; try omega
                                                     end; try reflexivity; try omega); solve[repeat zdestruct].

 Ltac vcgen_with_bitops := match goal with
      | [H: Some _ = None |- _] => inversion H
      | [H: None = Some _ |- _] => inversion H
      | [H: false = true |- _] => inversion H
      | [H: true = false |- _] => inversion H
      | [|- context[alignof ?x]] => let val := eval simpl in (alignof x) in change (alignof x) with val
      | [|- context[align ?x ?y]] => let val := eval compute in (align x y) in change (align x y) with val
      | [|- sem_binary_operation _ _ _ _ _ _ = Some _] => solve [discharge_cmp]
      | [|- bool_val _ _ = Some _] => solve [discharge_cmp]
      | _ => idtac
      end; simpleproof; match goal with
      | [|- _ /\ _] => split
      | [|- ?x / ?y * ?c <= Int.max_unsigned] => try (computedivmul; omega)
      | [|- ?x / ?y * ?c <= Int64.max_unsigned] => try (computedivmul; omega)
      | [|- context[Int.unsigned Int.zero]] => change (Int.unsigned Int.zero) with 0
      | [|- context[Int.unsigned Int.one]] => change (Int.unsigned Int.one) with 1
      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; try omega
      | [|- context[Int64.unsigned Int64.zero]] => change (Int64.unsigned Int64.zero) with 0
      | [|- context[Int64.unsigned Int64.one]] => change (Int64.unsigned Int64.one) with 1
      | [|- context[Int64.unsigned (Int64.repr _)]] => rewrite Int64.unsigned_repr; try omega
      | [|- 0 <= _] => discharge_unsigned_range; discharge_unsigned64_range
      | [|- _ <= Int.max_unsigned] => discharge_unsigned_range
      | [|- _ <= Int64.max_unsigned] => discharge_unsigned64_range
      | [|- context[Int.unsigned Int.mone]] => rewrite Int.unsigned_mone; simpl
      | [|- context[Int.repr (Int.unsigned _)]] => rewrite Int.repr_unsigned
      | [|- context[Int64.unsigned Int64.mone]] => rewrite Int64.unsigned_mone; simpl
      | [|- context[Int64.repr (Int64.unsigned _)]] => rewrite Int64.repr_unsigned
      | [|- CDataTypes.exec_stmt _ _ _ _ _ _ _ _ _] => unfold CDataTypes.exec_stmt
      | [|- ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _] => match goal with
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (if true then Ssequence _ _ else _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (if false then _ else Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) E0 _ _ _] => eassumption || fail 2
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _] => econstructor
                 | _ => fail 2
                 end
      | [|- eval_expr _ _ _ _ _ _] => econstructor
      | [|- eval_exprlist _ _ _ _ _ _ _] => econstructor
      | [|- eval_funcall _ _ _ _ _ _ _ _] => eapply eval_funcall_external
      | [|- external_call _ _ _ _ _ _ _ _] =>  econstructor; simpl; split; [match goal with
                                                                              | [|- context[?id ↦ ?sem]] => instantiate (1:= sem); reflexivity
                                                                            end 
                                                                           | 
                                                                           econstructor; esplit; repeat progress (split; simpleproof); (econstructor || eapply extcall_generic_sem_intro'); try econstructor; try econstructor; try econstructor; try econstructor; try econstructor; try econstructor; unfold bind; simpl;
                                                                           repeat progress try reflexivity; match goal with
      | [|- context[Int.unsigned (Int.repr 0)]] => change (Int.unsigned (Int.repr 0)) with 0
      | [|- context[Int.unsigned (Int.repr 1)]] => change (Int.unsigned (Int.repr 1)) with 1
      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr
      | [|- context[Int64.unsigned (Int64.repr 0)]] => change (Int64.unsigned (Int64.repr 0)) with 0
      | [|- context[Int64.unsigned (Int64.repr 1)]] => change (Int64.unsigned (Int64.repr 1)) with 1
      | [|- context[Int64.unsigned (Int64.repr _)]] => rewrite Int64.unsigned_repr
      | [H: ?x = _ |- match ?x with |_ => _ end = _] => rewrite H
      | _ => repeat discharge_unsigned_range; repeat discharge_unsigned64_range
   end; try reflexivity]
      | [|- _ = ret _] => match goal with
                            | [H: ?x = _ |- match ?x with |_ => _ end = _] => rewrite H; try reflexivity
                            | [H: ?spec _ _ _ _ _ _ = Some _ |- ?spec _ _ _ _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ _ _ _ = Some _ |- ?spec _ _ _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ _ _ = Some _ |- ?spec _ _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ _ = Some _ |- ?spec _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ = Some _ |- ?spec _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ = Some _ |- ?spec _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ = ret _] => primSolveUsingRewrites spec
                          end
      | [|- assign_loc _ _ _ _ _ _ _] => econstructor
      | [|- context[set_opttemp _ _ _]] => unfold set_opttemp
      | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
      | [|- (PTree.set ?id _ _) ! ?id = Some _] => rewrite PTree.gss
      | [|- (PTree.set ?id1 _ _) ! ?id2 = Some _] => rewrite PTree.gso
      | [|- ?id1 <> ?id2] => diff_ident id1 id2
      | [|- _ -> _] => intro
      | [|- eval_lvalue _ _ _ _ ?expr _ _] => match expr with
                                                  | Evar _ _ => eapply eval_Evar_global
                                                  | Ederef _ _ => eapply eval_Ederef
                                                  | Efield _ _ _ => eapply eval_Efield_struct
                                              end
      | [|- deref_loc _ _ _ _ _] => match goal with
                                | [|- deref_loc ?ty _ _ _ _] => match ty with
                                                | typeof (?var ?name ?type) => change (typeof (var name type)) with type
                                                | Tarray _ _ _ => eapply deref_loc_reference
                                                | Tfunction _ _ _ => eapply deref_loc_reference
                                                | Tstruct _ _ _ => eapply deref_loc_copy
                                                | Tunion _ _ _ => eapply deref_loc_copy
                                                | _ => eapply deref_loc_value
                                                end
                                | [|- _] => idtac
                                end
      | [|- access_mode _ = _] => constructor
      | [|- Events.writable_block _ _] => eapply writable_block_allow_globals
      | [|- _] => unfold Int.eq, Int.add, Int.sub, Int.mul, Int.divu, Int.and, Int.or, Int.xor, Int.shl, Int.shr, Int.shru, Int.modu, Int64.eq, Int64.add, Int64.sub, Int64.mul, Int64.divu, Int64.and, Int64.or, Int64.xor, Int64.shl, Int64.shr, Int64.shru, Int64.modu
  end.


 Ltac vcgensimpl := match goal with
      | [H: Some _ = None |- _] => inversion H
      | [H: None = Some _ |- _] => inversion H
      | [H: false = true |- _] => inversion H
      | [H: true = false |- _] => inversion H
      | [|- context[alignof ?x]] => let val := eval simpl in (alignof x) in change (alignof x) with val
      | [|- context[align ?x ?y]] => let val := eval compute in (align x y) in change (align x y) with val
      | [|- sem_binary_operation _ _ _ _ _ _ = Some _] => solve [discharge_cmp]
      | [|- bool_val _ _ = Some _] => solve [discharge_cmp]
      | _ => idtac
      end; simpleproof; match goal with
      | [|- _ /\ _] => split
      | [|- ?x / ?y * ?c <= Int.max_unsigned] => try (computedivmul; omega)
      | [|- ?x / ?y * ?c <= Int64.max_unsigned] => try (computedivmul; omega)
      | [|- context[Int.unsigned Int.zero]] => change (Int.unsigned Int.zero) with 0
      | [|- context[Int.unsigned Int.one]] => change (Int.unsigned Int.one) with 1
      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr; try omega
      | [|- context[Int64.unsigned Int64.zero]] => change (Int64.unsigned Int64.zero) with 0
      | [|- context[Int64.unsigned Int64.one]] => change (Int64.unsigned Int64.one) with 1
      | [|- context[Int64.unsigned (Int64.repr _)]] => rewrite Int64.unsigned_repr; try omega
      | [|- 0 <= _] => discharge_unsigned_range; discharge_unsigned64_range
      | [|- _ <= Int.max_unsigned] => discharge_unsigned_range
      | [|- _ <= Int64.max_unsigned] => discharge_unsigned64_range
      | [|- context[Int.repr (Int.unsigned _)]] => rewrite Int.repr_unsigned
      | [|- context[Int64.repr (Int64.unsigned _)]] => rewrite Int64.repr_unsigned
      | [|- CDataTypes.exec_stmt _ _ _ _ _ _ _ _ _] => unfold CDataTypes.exec_stmt
      | [|- ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _] => match goal with
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (if true then Ssequence _ _ else _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (if false then _ else Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) E0 _ _ _] => eassumption || fail 2
                 | [|- ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _] => econstructor
                 | _ => fail 2
                 end
      | [|- eval_expr _ _ _ _ _ _] => econstructor
      | [|- eval_exprlist _ _ _ _ _ _ _] => econstructor
      | [|- eval_funcall _ _ _ _ _ _ _ _] => eapply eval_funcall_external
      | [|- external_call _ _ _ _ _ _ _ _] =>  econstructor; simpl; split; [match goal with
                                                                              | [|- context[?id ↦ ?sem]] => instantiate (1:= sem); reflexivity
                                                                            end 
                                                                           | 
                                                                           econstructor; esplit; repeat progress (split; simpleproof); (econstructor || eapply extcall_generic_sem_intro'); try econstructor; try econstructor; try econstructor; try econstructor; try econstructor; try econstructor; unfold bind; simpl;
                                                                           repeat progress try reflexivity; match goal with
      | [|- context[Int.unsigned (Int.repr 0)]] => change (Int.unsigned (Int.repr 0)) with 0
      | [|- context[Int.unsigned (Int.repr 1)]] => change (Int.unsigned (Int.repr 1)) with 1
      | [|- context[Int.unsigned (Int.repr _)]] => rewrite Int.unsigned_repr
      | [|- context[Int64.unsigned (Int64.repr 0)]] => change (Int64.unsigned (Int64.repr 0)) with 0
      | [|- context[Int64.unsigned (Int64.repr 1)]] => change (Int64.unsigned (Int64.repr 1)) with 1
      | [|- context[Int64.unsigned (Int64.repr _)]] => rewrite Int64.unsigned_repr
      | [H: ?x = _ |- match ?x with |_ => _ end = _] => rewrite H
      | _ => repeat discharge_unsigned_range
   end; try reflexivity]
      | [|- _ = ret _] => match goal with
                            | [H: ?x = _ |- match ?x with |_ => _ end = _] => rewrite H; try reflexivity
                            | [H: ?spec _ _ _ _ _ _ = Some _ |- ?spec _ _ _ _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ _ _ _ = Some _ |- ?spec _ _ _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ _ _ = Some _ |- ?spec _ _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ _ = Some _ |- ?spec _ _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ _ = Some _ |- ?spec _ _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ _ = ret _] => primSolveUsingRewrites spec
                            | [H: ?spec _ = Some _ |- ?spec _ = ret _] => primSolveUsingHypothesis H || fail 2
                            | [|- ?spec _ = ret _] => primSolveUsingRewrites spec
                          end
      | [|- assign_loc _ _ _ _ _ _ _] => econstructor
      | [|- context[set_opttemp _ _ _]] => unfold set_opttemp
      | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
      | [|- (PTree.set ?id _ _) ! ?id = Some _] => eapply PTree.gss
      | [|- (PTree.set ?id1 _ _) ! ?id2 = Some _] => rewrite PTree.gso
      | [|- ?id1 <> ?id2] => diff_ident id1 id2
      | [|- _ -> _] => intro
      | [|- eval_lvalue _ _ _ _ ?expr _ _] => match expr with
                                                  | Evar _ _ => eapply eval_Evar_global
                                                  | Ederef _ _ => eapply eval_Ederef
                                                  | Efield _ _ _ => eapply eval_Efield_struct
                                              end
      | [|- deref_loc ?ty _ _ _ _] =>  match ty with
                                        | typeof (?var ?name ?type) => change (typeof (var name type)) with type
                                        | Tarray _ _ _ => eapply deref_loc_reference
                                        | Tfunction _ _ _ => eapply deref_loc_reference
                                        | Tstruct _ _ _ => eapply deref_loc_copy
                                        | Tunion _ _ _ => eapply deref_loc_copy
                                        | _ => eapply deref_loc_value
                                       end
      | [|- access_mode _ = _] => constructor
      | [|- Events.writable_block _ _] => eapply writable_block_allow_globals
      | [|- _] => unfold Int.eq, Int.add, Int.sub, Int.mul, Int.divu, Int.modu, Int64.eq, Int64.add, Int64.sub, Int64.mul, Int64.divu, Int64.modu
  end.

 Ltac vcgenfull := vcgen_with_bitops.
 Ltac vcgen := vcgensimpl.


  (** * The tactic to automate the proof for the whole function definition using the lemma for the function body. *)

  Ltac ptreesolve := repeat (match goal with
                               | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
                               | [|- (PTree.set ?id _ _) ! ?id = Some _] => rewrite PTree.gss
                               | [|- (PTree.set ?id1 _ _) ! ?id2 = Some _] => rewrite PTree.gso
                               | [|- ?id1 <> ?id2] => diff_ident id1 id2
                             end; simpleproof).

  Ltac fbigstep_pre L := match goal with
       | [|- spec_le (?id ↦ _) ( 〚?id ↦ _ 〛_)] => apply clight_sem_intro; try reflexivity; intros until p; intros ec_ops cc_ops writable_block_ops writable_block_allow_globals; unfold L in *; intros spec makeprogram; inversion spec; subst; apply make_program_make_globalenv in makeprogram; generalize makeprogram; intro makeglobalenv; apply make_globalenv_stencil_matches in makeglobalenv; eauto; intro hinv; repeat (match goal with
            | Hs: stencil_matches ?s ?ge, H: find_symbol ?s ?i = Some ?b |- _ =>
                                  rewrite <- (stencil_matches_symbols s ge Hs) in H
          end); inv_make_globalenv makeprogram; lift_unfold; 
          repeat (match goal with
            | H1:  Genv.find_symbol ?ge ?id = Some ?b1, H2:  Genv.find_symbol ?ge ?id = Some ?b2 |- _ =>
                                      replace b2 with b1 in * by congruence; clear b2 H2
            | H0: match ?x with |_ => _ end = Some _ |- _ => let memop := fresh "memop" in (case_eq x; [intros ? memop; rewrite memop in H0 | intro memop; rewrite memop in H0]; simpl in *; [injection H0; intros; subst | discriminate])

          end);
          unfold lift, set in *; simpl in *; generalize max_unsigned_val; intro muval
  end.

  Ltac fbigstep_exploit_lemma l m := exploit l; simpl; destruct m; ptreesolve; eauto; autorewrite with lift_simpl lens_simpl; repeat progress (unfold lift, set; simpl); eauto; repeat progress (try rewrite Int.unsigned_repr); repeat progress (try rewrite Int64.unsigned_repr); repeat progress discharge_unsigned_range; simpl in *; 
  repeat progress match goal with
                    | [H: ?x = _ |- context[?x]] => try rewrite H
  end; eauto; intro stmt; try (destruct stmt as [le' stmt]).

  Ltac fbigstep_post := simpleproof; match goal with
      | [|- exec_stmt _ _ _ _ _ _ _ _ _] => match goal with
                | [|- exec_stmt _ _ _ _ (Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                | [|- exec_stmt _ _ _ _ (if true then Ssequence _ _ else _) E0 _ _ _] => change E0 with (E0 ** E0)
                | [|- exec_stmt _ _ _ _ (if false then _ else Ssequence _ _) E0 _ _ _] => change E0 with (E0 ** E0)
                | [|- exec_stmt _ _ _ _ _ _ _ _ _] => econstructor
                | [|- _] => fail 2
                end
      | [|- eval_expr _ _ _ _ _ _] => econstructor
      | [|- eval_exprlist _ _ _ _ _ _ _] => econstructor
      | [|- eval_funcall _ _ _ _ _ _ _ _] => econstructor
      | [|- eval_lvalue _ _ _ _ ?expr _ _] => match expr with
                                                  | Evar _ _ => eapply eval_Evar_global
                                                  | Ederef _ _ => eapply eval_Ederef
                                                  | Efield _ _ _ => eapply eval_Efield_struct
                                              end
      | [|- deref_loc _ _ _ _ _] => match goal with
                  | [|- deref_loc ?ty _ _ _ _] => match ty with
                            | typeof (?var ?name ?type) => change (typeof (var name type)) with type
                            | Tarray _ _ _ => eapply deref_loc_reference
                            | Tfunction _ _ => eapply deref_loc_reference
                            | Tstruct _ _ _ => eapply deref_loc_copy
                            | Tunion _ _ _ => eapply deref_loc_copy
                            | _ => eapply deref_loc_value
                            end
                  | [|- _] => idtac
                  end
      | [|- bigstep_function_terminates2 _ _ _ _ _ _ _ _] => econstructor
      | [|- function_entry2 _ _ _ _ _ _] => econstructor
      | [|- alloc_variables _ _ _ _ _] => econstructor
      | [|- Val.has_type_list _ _] => repeat econstructor
      | [|- access_mode _ = _] => constructor
      | [|- (PTree.empty _) ! _ = None] => apply PTree.gempty
      | [|- outcome_result_value _ _ _] => simpl; split; [try discriminate | try reflexivity]
      | [|- context[In _ _]] => simpl
      | [|- list_norepet _] => econstructor; simpl || idtac; intro || idtac
      | [|- list_disjoint _ nil] => apply list_disjoint_nil
      | [|- list_disjoint _ (_::_)] => apply list_disjoint_cons_r; simpl || idtac; intro || idtac
      | [|- list_disjoint _ _] => simpl
      | [H: ?x = ?y \/ _ |- False] => destruct H; [try unfold x in *; try unfold y in *; try discriminate | idtac]; try subst; try omega
      | [|- context[Int.repr (Int.unsigned _)]] => rewrite Int.repr_unsigned
      | [|- context[Int64.repr (Int64.unsigned _)]] => rewrite Int64.repr_unsigned
      | [|- forall _, _] => intro
      | [|- _ -> _] => intro
      | [|- _ <> _] => intro
      | [|- _] => idtac
  end.

  Ltac fbigstep l m := fbigstep_exploit_lemma l m; repeat fbigstep_post. 



