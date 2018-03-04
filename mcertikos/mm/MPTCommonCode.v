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
(*                   Proof of functional correctness                   *)
(*          for the C functions implemented in the MPTCommon layer     *)
(*                                                                     *)
(*                        Xiongnan (Newman) Wu                         *)
(*                                                                     *)
(*                          Yale University                            *)
(*                                                                     *)
(* *********************************************************************)
Require Import TacticsForTesting.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import MemoryX.
Require Import EventsX.
Require Import Globalenvs.
Require Import Locations.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import MPTCommon.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import LoopProof.
Require Import VCGen.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import PTKernGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import AbstractDataType.
Require Import MPTCommonCSource.
Require Import TacticsForTesting.
Require Import XOmega.

Module MPTCOMMONCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.




    Section PTINSERT.

      Let L: compatlayer (cdata RData) := pt_read_pde ↦ gensem ptReadPDE_spec
          ⊕ pt_insert_aux ↦ gensem ptInsertAux_spec
          ⊕ pt_alloc_pde ↦ gensem ptAllocPDE_spec
          ⊕ at_get_c ↦ gensem get_at_c_spec
          ⊕ at_set_c ↦ gensem set_at_c0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Section PTInsertBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** pt_read_pde *)

        Variable bpt_read_pde: block.

        Hypothesis hpt_read_pde1 : Genv.find_symbol ge pt_read_pde = Some bpt_read_pde. 
        
        Hypothesis hpt_read_pde2 : Genv.find_funct_ptr ge bpt_read_pde = Some (External (EF_external pt_read_pde (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (** pt_insert_aux *)

        Variable bpt_insert_aux: block.

        Hypothesis hpt_insert_aux1 : Genv.find_symbol ge pt_insert_aux = Some bpt_insert_aux. 
        
        Hypothesis hpt_insert_aux2 : Genv.find_funct_ptr ge bpt_insert_aux = Some (External (EF_external pt_insert_aux (signature_of_type (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint (Tcons tint Tnil)))) Tvoid cc_default).

        (** pt_alloc_pde *)

        Variable bpt_alloc_pde: block.

        Hypothesis hpt_alloc_pde1 : Genv.find_symbol ge pt_alloc_pde = Some bpt_alloc_pde. 
        
        Hypothesis hpt_alloc_pde2 : Genv.find_funct_ptr ge bpt_alloc_pde = Some (External (EF_external pt_alloc_pde (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (** at_get_c *)

        Variable bat_get_c: block.

        Hypothesis hat_get_c1 : Genv.find_symbol ge at_get_c = Some bat_get_c. 
        
        Hypothesis hat_get_c2 : Genv.find_funct_ptr ge bat_get_c = Some (External (EF_external at_get_c (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** at_set_c *)

        Variable bat_set_c: block.

        Hypothesis hat_set_c1 : Genv.find_symbol ge at_set_c = Some bat_set_c. 
        
        Hypothesis hat_set_c2 : Genv.find_funct_ptr ge bat_set_c = Some (External (EF_external at_set_c (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).


        Lemma pt_insert_body_correct: forall m d d' env le proc_index vadr padr perm v,
                                           env = PTree.empty _ ->
                                           PTree.get tproc_index le = Some (Vint proc_index) ->
                                           PTree.get tvadr le = Some (Vint vadr) ->
                                           PTree.get tpadr le = Some (Vint padr) ->
                                           PTree.get tperm le = Some (Vint perm) ->
                                           ptInsert_spec (Int.unsigned proc_index) (Int.unsigned vadr)
                                                         (Int.unsigned padr) (Int.unsigned perm) d = Some (d', Int.unsigned v) ->
                                           high_level_invariant d ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) pt_insert_body E0 le' (m, d') (Out_return (Some (Vint v, tint))).
          Proof.
            generalize max_unsigned_val; intro muval.
            generalize one_k_minus1; intro one_k_minus1.
            intros.
            subst.
            unfold pt_insert_body.
            destruct H5.
            functional inversion H4; subst.
            {
              generalize (valid_nps H9); intro npsrange.
              functional inversion H14; subst.
              functional inversion H6; subst.
              functional inversion H; subst.
              unfold pt, pdi, pti, pt0, pdi0, pti0, pdt', pt' in *.
              esplit.
              repeat vcgen.
              unfold ptReadPDE_spec.
              unfold getPDE_spec.
              rewrite H8, H9, H10, H11.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              rewrite H19.
              instantiate (1:= Int.repr pi0).
              rewrite Int.unsigned_repr.
              reflexivity.
              omega.
              unfold PDX.
              xomega.
              omega.
              discharge_cmp.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              unfold ptInsertAux_spec.
              unfold setPTE_spec.
              rewrite H8, H9, H10, H11, H12, H18, H19, H23.
              unfold PTE_Arg.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              rewrite zle_le_true.
              reflexivity.
              unfold PTX.
              assert (0 < one_k) by omega.
              generalize (Z.mod_pos_bound (Int.unsigned vadr / 4096) one_k H26); intro.
              change ((Int.max_unsigned / 4096) mod 1024) with 1023.
              omega.
              unfold PDX.
              xomega.
              omega.
              unfold get_at_c_spec.
              simpl.
              rewrite H10, H11, H21.
              rewrite zle_lt_true.
              instantiate (1:= Int.repr c).
              rewrite Int.unsigned_repr; try omega.
              reflexivity.
              omega.
              unfold set_at_c0_spec.
              simpl.
              rewrite H10, H11, H21.
              rewrite zle_lt_true.
              rewrite Int.unsigned_repr.
              reflexivity.
              omega.
              omega.
              repeat vcgen.
              simpl.
              rewrite H5.
              rewrite Int.repr_unsigned.
              repeat vcgen.
            }
            {
              generalize (valid_nps H9); intro npsrange.
              unfold pt, pdi, pti in *.
              functional inversion H6; subst.
              functional inversion H; subst.
              esplit.
              repeat vcgen.
              unfold ptReadPDE_spec.
              unfold getPDE_spec.
              rewrite H8, H9, H10, H11, H13.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              change 0 with (Int.unsigned Int.zero).
              reflexivity.
              unfold PDX.
              xomega.
              omega.
              discharge_cmp.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              simpl.
              rewrite H5.
              rewrite Int.repr_unsigned.
              repeat vcgen.
            }
            {
              generalize (valid_nps H9); intro npsrange.
              unfold pt, pdi, pti in *.
              functional inversion H6; subst.
              functional inversion H; subst.
              functional inversion H14.
              unfold pdi0 in *.
              functional inversion H16.
              unfold pt0, pdi1, pti0, pdt', pt' in *. 
              rewrite <- H19, <- H31 in *; simpl in *.
              destruct _x4.
              destruct a0.
              esplit. 
              repeat vcgen.
              unfold ptReadPDE_spec.
              unfold getPDE_spec.
              rewrite H8, H9, H10, H11, H13.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              change 0 with (Int.unsigned Int.zero).
              reflexivity.
              unfold PDX.
              xomega.
              omega.
              discharge_cmp.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              repeat vcgen.
              unfold ptInsertAux_spec.
              unfold setPTE_spec.
              simpl.
              rewrite H5, H8, H9, H10.
              rewrite H11, H12, H27, H36.
              repeat rewrite ZMap.gss.
              unfold PTE_Arg.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              rewrite zle_le_true.
              reflexivity.
              unfold PTX.
              assert (0 < one_k) by omega.
              generalize (Z.mod_pos_bound (Int.unsigned vadr / 4096) one_k H40); intro.
              change ((Int.max_unsigned / 4096) mod 1024) with 1023.
              omega.
              unfold PDX.
              xomega.
              omega.
              unfold get_at_c_spec.
              simpl.
              rewrite H10, H11, H38.
              rewrite zle_lt_true.
              instantiate (1:= Int.repr c0).
              rewrite Int.unsigned_repr; try omega.
              reflexivity.
              omega.
              unfold set_at_c0_spec.
              simpl.
              rewrite H10, H11, H38.
              rewrite zle_lt_true.
              repeat rewrite Int.unsigned_repr; try omega.
              simpl.
              unfold pdt', pt0, pdi1 in *.
              rewrite <- H19; simpl in *.
              assert (HSpeed:
                        forall hp a p ptp ptp' a' ac,
                          Some (d {HP : hp} {AT: a} {pperm: p} {ptpool: ptp} {AC: ac} {ptpool: ptp'} {AT: a'})
                          = ret (d {HP : hp} {AT: a} {pperm: p} {ptpool: ptp} {AC: ac} {AT: a'} {ptpool: ptp'})).
              {
                intros. reflexivity.
              }
              repeat rewrite ZMap.gss.
              apply HSpeed.
              omega.
              repeat vcgen.
              repeat vcgen.

              (* contradiction case *)
              clear H15.
              rewrite H20 in _x.
              contradiction _x.
              reflexivity.
            }
          Qed.

      End PTInsertBody.


      Theorem pt_insert_code_correct:
        spec_le (pt_insert ↦ ptInsert_spec_low) (〚pt_insert ↦ f_pt_insert 〛L).
      Proof.
        set (L' := L) in *. unfold L in *. 
        fbigstep_pre L'.
        fbigstep (pt_insert_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp m'0 labd labd' (PTree.empty _) 
                                      (bind_parameter_temps' (fn_params f_pt_insert)
                                                             (Vint n::Vint vadr::Vint padr::Vint p0::nil)
                                                             (create_undef_temps (fn_temps f_pt_insert)))) H0. 
      Qed.


    End PTINSERT.



    Section PTRMV.

      Let L: compatlayer (cdata RData) := pt_read ↦ gensem ptRead_spec
          ⊕ pt_rmv_aux ↦ gensem ptRmvAux_spec
          ⊕ at_get_c ↦ gensem get_at_c_spec
          ⊕ at_set_c ↦ gensem set_at_c0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Section PTRmvBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** pt_read *)

        Variable bpt_read: block.

        Hypothesis hpt_read1 : Genv.find_symbol ge pt_read = Some bpt_read. 
        
        Hypothesis hpt_read2 : Genv.find_funct_ptr ge bpt_read = Some (External (EF_external pt_read (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (** pt_rmv_aux *)

        Variable bpt_rmv_aux: block.

        Hypothesis hpt_rmv_aux1 : Genv.find_symbol ge pt_rmv_aux = Some bpt_rmv_aux. 
        
        Hypothesis hpt_rmv_aux2 : Genv.find_funct_ptr ge bpt_rmv_aux = Some (External (EF_external pt_rmv_aux (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).

        (** at_get_c *)

        Variable bat_get_c: block.

        Hypothesis hat_get_c1 : Genv.find_symbol ge at_get_c = Some bat_get_c. 
        
        Hypothesis hat_get_c2 : Genv.find_funct_ptr ge bat_get_c = Some (External (EF_external at_get_c (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** at_set_c *)

        Variable bat_set_c: block.

        Hypothesis hat_set_c1 : Genv.find_symbol ge at_set_c = Some bat_set_c. 
        
        Hypothesis hat_set_c2 : Genv.find_funct_ptr ge bat_set_c = Some (External (EF_external at_set_c (signature_of_type (Tcons tint (Tcons tint Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).


        Lemma pt_rmv_body_correct: forall m d d' env le proc_index vadr v,
                                           env = PTree.empty _ ->
                                           PTree.get tproc_index le = Some (Vint proc_index) ->
                                           PTree.get tvadr le = Some (Vint vadr) ->
                                           ptRmv_spec (Int.unsigned proc_index) (Int.unsigned vadr) d = Some (d', Int.unsigned v) ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) pt_rmv_body E0 le' (m, d') (Out_return (Some (Vint v, tint))).
          Proof.
            generalize max_unsigned_val; intro muval.
            generalize one_k_minus1; intro one_k_minus1.
            intros.
            subst.
            unfold pt_rmv_body.
            functional inversion H2; subst.
            {
              unfold pt, pdi, pti, pdt', pt' in *.
              functional inversion H4.
              assert(range: 0 < Int.unsigned v * 4096 + PermtoZ _x0 <= Int.max_unsigned).
              {
                unfold PermtoZ.
                destruct _x0; try omega.
                destruct b; omega.
              }
              assert(divval: (Int.unsigned v * 4096 + PermtoZ _x0) / 4096 = Int.unsigned v).
              {
                destruct _x0; simpl.
                xomega.
                xomega.
                destruct b; xomega.
              }
              esplit.
              repeat vcgen.
              unfold ptRead_spec.
              unfold getPTE_spec.
              rewrite H6, H7, H8, H9.
              unfold PTE_Arg.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              rewrite zle_le_true.
              rewrite H11, H12.
              instantiate (1:= (Int.repr (Int.unsigned v * 4096 + PermtoZ _x0))).
              rewrite Int.unsigned_repr; try omega.
              reflexivity.
              unfold PTX.
              assert (0 < one_k) by omega.
              generalize (Z.mod_pos_bound (Int.unsigned vadr / 4096) one_k H16); intro.
              change ((Int.max_unsigned / 4096) mod 1024) with 1023.
              omega.
              unfold PDX.
              xomega.
              omega.
              discharge_cmp.
              repeat vcgen.
              unfold ptRmvAux_spec.
              unfold rmvPTE_spec.
              rewrite H6, H7, H8, H9.
              unfold PTE_Arg.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              rewrite zle_le_true.
              rewrite H10, H11.
              reflexivity.
              unfold PTX.
              assert (0 < one_k) by omega.
              generalize (Z.mod_pos_bound (Int.unsigned vadr / 4096) one_k H16); intro.
              change ((Int.max_unsigned / 4096) mod 1024) with 1023.
              omega.
              unfold PDX.
              xomega.
              omega.
              rewrite divval.
              unfold get_at_c_spec.
              simpl.
              rewrite H8, H9, H14.
              rewrite zle_lt_true.
              instantiate (1:= Int.repr c).
              rewrite Int.unsigned_repr; try omega.
              reflexivity.
              omega.
              discharge_cmp.
              repeat vcgen.
              rewrite divval.
              unfold set_at_c0_spec.
              simpl.
              rewrite H8, H9, H14.
              rewrite zle_lt_true.
              reflexivity.
              omega.
              repeat vcgen.
              simpl.
              unfold sem_div.
              unfold sem_binarith; simpl.
              discharge_cmp.
              rewrite divval.
              rewrite Int.repr_unsigned.
              reflexivity.
            }
            {
              unfold pt, pdi, pti in *.
              functional inversion H4.
              esplit.
              repeat vcgen.
              unfold ptRead_spec.
              unfold getPTE_spec.
              rewrite H6, H7, H8, H9.
              unfold PTE_Arg.
              unfold PDE_Arg.
              rewrite zle_lt_true.
              rewrite zle_le_true.
              rewrite zle_le_true.
              rewrite H11, H12.
              change 0 with (Int.unsigned Int.zero).
              reflexivity.
              unfold PTX.
              assert (0 < one_k) by omega.
              generalize (Z.mod_pos_bound (Int.unsigned vadr / 4096) one_k H14); intro.
              change ((Int.max_unsigned / 4096) mod 1024) with 1023.
              omega.
              unfold PDX.
              xomega.
              omega.
              discharge_cmp.
              repeat vcgen.
              simpl.
              rewrite PTree.gss.
              f_equal.
              simpl.
              unfold sem_div.
              unfold sem_binarith; simpl.
              discharge_cmp.
              f_equal.
              f_equal.
              erewrite <- unsigned_inj.
              reflexivity.
              rewrite <- H3.
              rewrite Int.unsigned_repr.
              reflexivity.
              xomega.
            }
          Qed.

      End PTRmvBody.


      Theorem pt_rmv_code_correct:
        spec_le (pt_rmv ↦ ptRmv_spec_low) (〚pt_rmv ↦ f_pt_rmv 〛L).
      Proof.
        set (L' := L) in *. unfold L in *. 
        fbigstep_pre L'.
        fbigstep (pt_rmv_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd' (PTree.empty _) 
                                      (bind_parameter_temps' (fn_params f_pt_rmv)
                                                             (Vint n::Vint vadr::nil)
                                                             (create_undef_temps (fn_temps f_pt_rmv)))) H0. 
      Qed.

    End PTRMV.



    Section PTINITKERN.

      Let L: compatlayer (cdata RData) := pt_init_comm ↦ gensem pt_init_comm_spec ⊕ set_PDE ↦ gensem setPDE_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Section PTInitKernBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** set_PDE *)

        Variable bset_PDE: block.

        Hypothesis hset_PDE1 : Genv.find_symbol ge set_PDE = Some bset_PDE. 
        
        Hypothesis hset_PDE2 : Genv.find_funct_ptr ge bset_PDE = Some (External (EF_external set_PDE (signature_of_type (Tcons tint (Tcons tint  Tnil)) Tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) Tvoid cc_default).
        
        (** pt_init_comm *)

        Variable bptinitcomm: block.

        Hypothesis hpt_init_comm1 : Genv.find_symbol ge pt_init_comm = Some bptinitcomm. 
        
        Hypothesis hpt_init_comm2 : Genv.find_funct_ptr ge bptinitcomm = Some (External (EF_external pt_init_comm (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).


        Definition pt_init_kern_mk_rdata adt (index: Z) := adt {ptpool: (Calculate_pt_kern (Z.to_nat (index - 256)) (ptpool adt))}.

        Section pt_init_kern_loop_proof.

          Variable minit: memb.
          Variable adt: RData.

          Hypothesis init: init adt = true.
          Hypothesis ipt: ipt adt = true.
          Hypothesis pg: pg adt = false.
          Hypothesis ihost: ihost adt = true.
          Hypothesis ikern: ikern adt = true.

          Definition pt_init_kern_loop_body_P (le: temp_env) (m: mem): Prop :=
            PTree.get ti le = Some (Vint (Int.repr 256)) /\ 
            m = (minit, adt).

          Definition pt_init_kern_loop_body_Q (le : temp_env) (m: mem): Prop :=    
            m = (minit, pt_init_kern_mk_rdata adt (960 - 1)).

          Lemma pt_init_kern_loop_correct_aux : LoopProofSimpleWhile.t pt_init_kern_while_condition pt_init_kern_while_body ge (PTree.empty _) (pt_init_kern_loop_body_P) (pt_init_kern_loop_body_Q).
          Proof.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le (m: mem) w => exists i,
                                           PTree.get ti le = Some (Vint i) /\
                                           256 <= Int.unsigned i <= 960 /\ 
                                           (Int.unsigned i = 256 /\ m = (minit, adt) \/ Int.unsigned i > 256 /\ m =(minit, pt_init_kern_mk_rdata adt (Int.unsigned i - 1))) /\
                                           w = 960 - Int.unsigned i
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold pt_init_kern_loop_body_P in H.
            destruct H as [tile tmpH].
            destruct tmpH as [pdtvalid msubst].
            subst.
            esplit. esplit. 
            repeat vcgen.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [invar nval].
            subst.
            unfold pt_init_kern_while_condition.
            unfold pt_init_kern_while_body.
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.

            Caseeq ihigh.

            (* i < 960 *)
            intro ihigh.

            destruct m.

            case_eq invar;intros.
            (* i = 256 *)
            destruct a.
            injection e0; intros; subst.

            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            exists (960 - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            
            right.
            split.
            omega.
            unfold pt_init_kern_mk_rdata.
            f_equal.
            f_equal; auto.
            rewrite e in *; simpl.
            unfold Calculate_pt_kern_at_i.
            reflexivity.
            
            (* i > 256 *)
            destruct a as [ilo mval].
            injection mval; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold setPDE_spec.
            simpl.
            rewrite ipt, pg, ihost, ikern, init.
            unfold PDE_Arg.
            unfold zle_lt, zle_le.
            rewrite one_k_minus1.
            repeat zdestruct.
            exists (960 - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            f_equal.
            unfold pt_init_kern_mk_rdata.
            replace (Int.unsigned i + 1 - 1 - 256) with (Z.succ (Int.unsigned i - 1 - 256)) by omega.
            rewrite Z2Nat.inj_succ.
            Opaque Z.of_nat.
            simpl.
            rewrite Nat2Z.inj_succ.
            rewrite Z2Nat.id.
            unfold Z.succ.
            unfold Calculate_pt_kern_at_i.
            assert(tmp2: (Int.unsigned i - 1 - 256 + 1 + 262144 / 1024) = Int.unsigned i).
            {
              change (262144 / 1024) with 256.
              omega.
            }
            rewrite tmp2.
            reflexivity.
            omega.
            omega.

            (* i = 960 *)
            intro ival.
            rewrite ival in *.
            esplit. esplit.
            repeat vcgen.
            unfold pt_init_kern_loop_body_Q.
            Caseeq invar.
            intro.
            destruct H0.
            omega.
            intro tmpH.
            destruct tmpH.
            assumption.
          Qed.

        End pt_init_kern_loop_proof.

        Lemma pt_init_kern_loop_correct: forall m adt adt' le,
                                           PTree.get ti le = Some (Vint (Int.repr 256)) ->
                                           init adt = true ->
                                           ipt adt = true ->
                                           pg adt = false ->
                                           ihost adt = true ->
                                           ikern adt = true ->
                                           adt' = pt_init_kern_mk_rdata adt (960 - 1) ->
                                           exists le', 
                                             exec_stmt ge (PTree.empty _) le ((m, adt): mem) (Swhile pt_init_kern_while_condition pt_init_kern_while_body) E0 le' (m, adt') Out_normal.
        Proof.
          intros.
          generalize (pt_init_kern_loop_correct_aux m adt H0 H1 H2 H3 H4).
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, adt) _)).
          intro pre.
          destruct pre as [le'' pre].
          destruct pre as [m'' pre].
          destruct pre as [pre1 pre2].
          unfold pt_init_kern_loop_body_Q in pre2.
          subst.
          esplit; eassumption.
          unfold pt_init_kern_loop_body_P.
          repeat (split; auto).
        Qed.

        Lemma pt_init_kern_body_correct: forall m d d' env le mbi_adr,
                                           env = PTree.empty _ ->
                                           PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                           pt_init_kern_spec (Int.unsigned mbi_adr) d = Some d' ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) pt_init_kern_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold pt_init_kern_body.
          subst.
          functional inversion H1.
          simpl in *.

          set (initd := d {vmxinfo: real_vmxinfo} {AT : real_AT (AT d)} {nps : real_nps} {AC: real_AC} {init : true} {ptpool: real_ptp (ptpool d)}
                          {idpde : CalRealIDPDE.real_idpde (idpde d)}).
          exploit (pt_init_kern_loop_correct m initd (pt_init_kern_mk_rdata initd (960 - 1)) (PTree.set ti (Vint (Int.repr 256)) (set_opttemp None Vundef le))); try rewrite <- H; try assumption; try reflexivity; try (rewrite PTree.gss; reflexivity).
          intro stmt.
          unfold initd in *.
          destruct stmt as [le' stmt].
          esplit.
          change E0 with (E0**E0).
          econstructor.
          econstructor; vcgen; try simpleproof.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          vcgen.
          unfold pt_init_comm_spec.
          rewrite H2, H3, H4, H5, H6.
          reflexivity.
          change E0 with (E0**E0).
          econstructor.
          repeat vcgen.
          unfold pt_init_kern_mk_rdata, CalRealPT.real_pt in *.
          Opaque Z.sub Z.add.
          simpl in stmt.
          apply stmt.
        Qed.

      End PTInitKernBody.

      Theorem pt_init_kern_code_correct:
        spec_le (pt_init_kern ↦ pt_init_kern_spec_low) (〚pt_init_kern ↦ f_pt_init_kern 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_init_kern_body_correct s (Genv.globalenv p) makeglobalenv b1 Hb1fs Hb1fp b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_init_kern)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_pt_init_kern)))) H0. 
      Qed.

    End PTINITKERN.

  End WithPrimitives.

End MPTCOMMONCODE.
