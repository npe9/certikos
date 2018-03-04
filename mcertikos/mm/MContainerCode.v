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
(*          for the C functions implemented in the MAL layer           *)
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
Require Import MALOp.
Require Import MALT.
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
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import PTIntroGenSpec.
Require Import MContainerCSource.
Require Import AbstractDataType.

Module MCONTAINERCODE.

  Section WithPrimitives.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.

    Lemma tptrsize: sizeof (Tpointer tchar noattr) = 4.
    Proof. reflexivity. Qed.

    Lemma tptsize: sizeof (Tarray (Tpointer tchar noattr) 1024 noattr) = 4096.
    Proof. reflexivity. Qed.

    Lemma tcharptrsize: sizeof (tptr tchar) = 4.
    Proof. reflexivity. Qed.

    Lemma tcharsize: sizeof tchar = 1.
    Proof. reflexivity. Qed.

    Section SETPT.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type
           ⊕ set_cr3 ↦ setCR3_compatsem setCR30_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetPTBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Variable bsetcr3: block.

        Hypothesis hset_cr31 : Genv.find_symbol ge set_cr3 = Some bsetcr3. 
        
        Hypothesis hset_cr32 : Genv.find_funct_ptr ge bsetcr3 = Some (External (EF_external set_cr3 (signature_of_type (Tcons (tptr tvoid) Tnil) Tvoid cc_default)) (Tcons (tptr tvoid) Tnil) Tvoid cc_default).

        Lemma set_pt_body_correct: forall m d d' env le index ofs,
                                     env = PTree.empty _ ->
                                     PTree.get tsetpt_index le = Some (Vint index) ->
                                     ofs = (Int.repr (Int.unsigned index * PgSize)) ->
                                     setCR30_spec d (GLOBP PTPool_LOC ofs) = Some d' ->
                                     0 <= (Int.unsigned index) < num_proc ->
                                     exists le',
                                       exec_stmt ge env le ((m, d): mem) set_pt_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          unfold set_pt_body.
          intros.
          subst.
          esplit.
          d8 vcgen; repeat vcgen.
          simpl.
          unfold sem_add.
          simpl.
          repeat vcgen.
          rewrite Zplus_0_l.
          rewrite Z.mul_comm.
          reflexivity.
          erewrite <- stencil_matches_symbols; eauto.
        Qed.

      End SetPTBody.

      Theorem set_pt_code_correct:
        spec_le (set_pt ↦ setPT_spec_low) (〚set_pt ↦ f_set_pt 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (set_pt_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs b1 Hb1fs Hb1fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_set_pt)
                                                               (Vint n::nil)
                                                               (create_undef_temps (fn_temps f_set_pt)))) H2. 
      Qed.

    End SETPT.



    Section GETPDE.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section GetPDEBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Lemma get_pde_body_correct: forall m d env le proc_index pde_index pi pi',
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tpde_index le = Some (Vint pde_index) ->
                                      0 <= Int.unsigned proc_index < num_proc ->
                                      0 <= Int.unsigned pde_index <= PDX Int.max_unsigned ->
                                      Mem.load Mint32 m bptpool_loc
                                               (Int.unsigned proc_index * PgSize + Int.unsigned pde_index * 4) = Some (Vint pi) ->
                                      Int.unsigned pi' = Int.unsigned pi / PgSize ->
                                      exists le',
                                      exec_stmt ge env le ((m, d): mem) get_PDE_body E0 le' (m, d) (Out_return (Some (Vint pi', tint))).
        Proof.
          intros.
          subst.
          unfold get_PDE_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize one_k_minus1; intro one_k_minus1.
          rewrite <- Int.repr_unsigned with pi'.
          rewrite H5.
          esplit.
          repeat vcgen.
          rewrite tptsize, tcharptrsize.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          rewrite Int.unsigned_repr; try omega.
          rewrite Z.mul_comm.
          rewrite Z.mul_comm with (n:= 4).
          eassumption.
          reflexivity.
          simpl.
          repeat vcgen.
        Qed.

      End GetPDEBody.

      Theorem get_pde_code_correct:
        spec_le (get_PDE ↦ getPDE_spec_low) (〚get_PDE ↦ f_get_PDE 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m'.
        fbigstep (get_pde_body_correct (Genv.globalenv p) b0 H m l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_get_PDE)
                                                          (Vint n::Vint i::nil)
                                                          (create_undef_temps (fn_temps f_get_PDE)))) H4.
      Qed.

    End GETPDE.


    Section SETPDE.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type
                                                     ⊕ IDPMap_LOC ↦ idpmap_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section SetPDEBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Variable bidpmap_loc: block.
        Hypothesis hidpmap_loc1 : Genv.find_symbol ge IDPMap_LOC = Some bidpmap_loc.

        Lemma set_pde_body_correct: forall m m' d env le proc_index pde_index,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tpde_index le = Some (Vint pde_index) ->
                                      0 <= Int.unsigned proc_index < num_proc ->
                                      0 <= Int.unsigned pde_index <= PDX Int.max_unsigned ->
                                      Mem.store Mint32 (m, d) bptpool_loc
                                                (Int.unsigned proc_index * PgSize + Int.unsigned pde_index * 4)
                                                (Vptr bidpmap_loc (Int.repr(Int.unsigned pde_index * PgSize + PT_PERM_PTU))) 
                                      =  Some (m', d) ->
                                      exec_stmt ge env le ((m, d): mem) set_pde_body E0 le (m', d) Out_normal.
        Proof.
          intros.
          subst.
          unfold set_pde_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize one_k_minus1; intro one_k_minus1.
          assert(sizeof (Tarray tint 1024 noattr) = 4096) by reflexivity.
          assert(sizeof (Tarray (Tpointer tchar noattr) 1024 noattr) = 4096) by reflexivity.
          repeat vcgen.
          rewrite H, H5, tcharptrsize.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          destruct H4.
          rewrite Int.unsigned_repr; try omega.
          replace (4096 * Int.unsigned proc_index + 4 * Int.unsigned pde_index) with (Int.unsigned proc_index * 4096 + Int.unsigned pde_index * 4) by omega.
          replace (4096 * Int.unsigned pde_index + 1 * 7) with (Int.unsigned pde_index * 4096 + 7) by omega.
          rewrite H4.
          reflexivity.
        Qed.

      End SetPDEBody.

      Theorem set_pde_code_correct:
        spec_le (set_PDE ↦ setPDE_spec_low) (〚set_PDE ↦ f_set_pde 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_pde_body_correct (Genv.globalenv p) b0 H b1 H0 m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_pde)
                                                          (Vint n::Vint i::nil)
                                                          (create_undef_temps (fn_temps f_set_pde)))) H1.
      Qed.

    End SETPDE.


    Section RMVPDE.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section RmvPDEBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Lemma rmv_pde_body_correct: forall m m' d env le proc_index pde_index,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tpde_index le = Some (Vint pde_index) ->
                                      0 <= Int.unsigned proc_index < num_proc ->
                                      0 <= Int.unsigned pde_index <= PDX Int.max_unsigned ->
                                      Mem.store Mint32 (m, d) bptpool_loc
                                                (Int.unsigned proc_index * PgSize + Int.unsigned pde_index * 4)
                                                (Vint (Int.repr PT_PERM_UP)) =  Some (m', d) ->
                                      exec_stmt ge env le ((m, d): mem) rmv_pde_body E0 le (m', d) Out_normal.
        Proof.
          intros.
          subst.
          unfold rmv_pde_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize one_k_minus1; intro one_k_minus1.
          repeat vcgen.
          rewrite tcharptrsize.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          destruct H4.
          change (Z.max 0 1024) with 1024.
          rewrite Int.unsigned_repr; try omega.
          replace (4 * 1024 * Int.unsigned proc_index + 4 * Int.unsigned pde_index) with (Int.unsigned proc_index * 4096 + Int.unsigned pde_index * 4) by omega.
          rewrite H.
          reflexivity.
        Qed.

      End RmvPDEBody.

      Theorem rmv_pde_code_correct:
        spec_le (rmv_PDE ↦ rmvPDE_spec_low) (〚rmv_PDE ↦ f_rmv_pde 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (rmv_pde_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_rmv_pde)
                                                          (Vint n::Vint i::nil)
                                                          (create_undef_temps (fn_temps f_rmv_pde)))) H0.
      Qed.

    End RMVPDE.



    Section SETPDEU.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section SetPDEUBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Lemma set_pdeu_body_correct: forall m m' d env le proc_index pde_index pi,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tpde_index le = Some (Vint pde_index) ->
                                      PTree.get tpi le = Some (Vint pi) ->
                                      0 <= Int.unsigned proc_index < num_proc ->
                                      0 <= Int.unsigned pde_index <= PDX Int.max_unsigned ->
                                      0 < Int.unsigned pi < nps d ->
                                      Mem.store Mint32 ((m, d): mem) bptpool_loc
                                                (Int.unsigned proc_index * PgSize + Int.unsigned pde_index * 4)
                                                (Vint (Int.repr (Int.unsigned pi * PgSize + PT_PERM_PTU))) 
                                      =  Some (m', d) ->
                                      init d = true ->
                                      high_level_invariant d ->
                                      exec_stmt ge env le ((m, d): mem) set_pdeu_body E0 le (m', d) Out_normal.
        Proof.
          intros.
          subst.
          unfold set_pdeu_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize one_k_minus1; intro one_k_minus1.
          destruct H8.
          generalize (valid_nps H7); intro nps_range.
          repeat vcgen.
          rewrite tcharptrsize.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          change (Z.max 0 1024) with 1024.
          rewrite Int.unsigned_repr; try omega.
          replace (4 * 1024 * Int.unsigned proc_index + 4 * Int.unsigned pde_index) with (Int.unsigned proc_index * 4096 + Int.unsigned pde_index * 4) by omega.
          assumption.
        Qed.

      End SetPDEUBody.

      Theorem set_pdeu_code_correct:
        spec_le (set_PDEU ↦ setPDEU_spec_low) (〚set_PDEU ↦ f_set_pdeu 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigsteptest (set_pdeu_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_pdeu)
                                                          (Vint n::Vint i::Vint pi::nil)
                                                          (create_undef_temps (fn_temps f_set_pdeu)))) H0.
        reflexivity.
        intro.
        repeat fbigstep_post.
      Qed.

    End SETPDEU.



    Section GETPTE.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type ⊕ fload ↦ gensem fload'_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section GetPTEBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv) 
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Variable bfload: block.

        Hypothesis hfload1 : Genv.find_symbol ge fload = Some bfload. 
        
        Hypothesis hfload2 : Genv.find_funct_ptr ge bfload = Some (External (EF_external fload (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        Lemma get_pte_body_correct: forall m d env le proc_index pte_index vadr pi pi' padr,
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tpde_index le = Some (Vint pte_index) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      0 <= Int.unsigned proc_index < num_proc ->
                                      0 <= Int.unsigned pte_index <= PDX Int.max_unsigned ->
                                      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
                                      Mem.load Mint32 ((m, d): mem) bptpool_loc
                                               (Int.unsigned proc_index * PgSize + Int.unsigned pte_index * 4) = Some (Vint pi) ->
                                      Int.unsigned pi = pi' * PgSize + PT_PERM_PTU ->
                                      fload'_spec (pi' * one_k + Int.unsigned vadr) d = Some (Int.unsigned padr) ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) get_pte_body E0 le' (m, d) (Out_return (Some (Vint padr, tint))).
        Proof.
          intros.
          subst.
          unfold get_pte_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize one_k_minus1; intro one_k_minus1.
          rewrite <- Int.repr_unsigned with padr.
          functional inversion H8; subst.
          generalize (Int.unsigned_range pi); intro.
          esplit.
          repeat vcgen.
          rewrite tptsize, tcharptrsize.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          rewrite Int.unsigned_repr; try omega.
          rewrite Z.mul_comm.
          rewrite Z.mul_comm with (n:= 4).
          eassumption.
          reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.      
          rewrite H7 in *.
          replace (pi' * 4096 + 7 - 7) with (pi' * 4096) by omega.
          rewrite Z_div_mult_full; try omega.
          repeat vcgen.
        Qed.

      End GetPTEBody.

      Theorem get_pte_code_correct:
        spec_le (get_PTE ↦ getPTE_spec_low) (〚get_PTE ↦ f_get_pte 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m'.
        fbigstep (get_pte_body_correct s (Genv.globalenv p) makeglobalenv b0 H b2 Hb2fs Hb2fp m l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_get_pte)
                                                          (Vint n::Vint i::Vint vadr::nil)
                                                          (create_undef_temps (fn_temps f_get_pte)))) H4.
      Qed.

    End GETPTE.



    Section SETPTE.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type
                                                     ⊕ fstore ↦ gensem fstore0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section SetPTEBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv) 
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Variable bfstore: block.

        Hypothesis hfstore1 : Genv.find_symbol ge fstore = Some bfstore. 
        
        Hypothesis hfstore2 : Genv.find_funct_ptr ge bfstore = Some (External (EF_external fstore (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        Lemma set_pte_body_correct: forall m d d' env le proc_index pde_index vadr padr perm perm' pi pi',
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tpde_index le = Some (Vint pde_index) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      PTree.get tpadr le = Some (Vint padr) ->
                                      PTree.get tperm le = Some (Vint perm) ->
                                      0 <= Int.unsigned proc_index < num_proc ->
                                      0 <= Int.unsigned pde_index <= PDX Int.max_unsigned ->
                                      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
                                      0 < Int.unsigned padr < nps d->
                                      init d = true ->
                                      Mem.load Mint32 ((m, d): mem) bptpool_loc
                                               (Int.unsigned proc_index * PgSize + Int.unsigned pde_index * 4) = Some (Vint pi) ->
                                      Int.unsigned pi = pi' * PgSize + PT_PERM_PTU ->
                                      fstore0_spec (pi' * one_k + Int.unsigned vadr)  
                                                   (Int.unsigned padr * PgSize + Int.unsigned perm)
                                                   d = Some d' ->
                                      high_level_invariant d ->
                                      ZtoPerm (Int.unsigned perm) = Some perm' ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) set_pte_body E0 le' (m, d') Out_normal.
        Proof.
          intros.
          subst.
          unfold set_pte_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize one_k_minus1; intro one_k_minus1.
          generalize one_k_minus1'; intro one_k_minus1'.
          assert(sizeof (Tarray tint 1024 noattr) = 4096) by reflexivity.
          assert(sizeof (Tarray (Tpointer tchar noattr) 1024 noattr) = 4096) by reflexivity.
          functional inversion H12; subst.
          generalize (Int.unsigned_range padr); intro padrrange.
          generalize (Int.unsigned_range vadr); intro vadrrange.
          generalize (Int.unsigned_range perm); intro permrange.
          destruct H13.
          generalize (valid_nps H9); intro nps_range.
          esplit.
          repeat vcgen.
          rewrite H15, tcharptrsize.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          rewrite Int.unsigned_repr; try omega.
          rewrite Z.mul_comm.
          rewrite Z.mul_comm with (n:= 4).
          eassumption.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          rewrite H11 in *.
          replace (pi' * 4096 + 7 - 7) with (pi' * 4096) by omega.
          rewrite Z_div_mult_full; try omega.
          repeat vcgen.
          functional inversion H14; omega.
        Qed.

      End SetPTEBody.

      Theorem set_pte_code_correct:
        spec_le (set_PTE ↦ setPTE_spec_low) (〚set_PTE ↦ f_set_pte 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        fbigstep (set_pte_body_correct s (Genv.globalenv p) makeglobalenv b0 H b2 Hb2fs Hb2fp m l d (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_pte)
                                                          (Vint n::Vint i::Vint vadr::Vint padr::Vint p0::nil)
                                                          (create_undef_temps (fn_temps f_set_pte)))) H9.
      Qed.

    End SETPTE.


    Section RMVPTE.

      Let L: compatlayer (cdata RData) := PTPool_LOC ↦ ptpool_loc_type
                                                     ⊕ fstore ↦ gensem fstore0_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section RmvPTEBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv) 
                  (STENCIL_MATCHES: stencil_matches sc ge).

        Variable bptpool_loc: block.
        Hypothesis hptpool_loc1 : Genv.find_symbol ge PTPool_LOC = Some bptpool_loc.

        Variable bfstore: block.

        Hypothesis hfstore1 : Genv.find_symbol ge fstore = Some bfstore. 
        
        Hypothesis hfstore2 : Genv.find_funct_ptr ge bfstore = Some (External (EF_external fstore (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        Lemma rmv_pte_body_correct: forall m d d' env le proc_index pde_index vadr pi pi',
                                      env = PTree.empty _ ->
                                      PTree.get tproc_index le = Some (Vint proc_index) ->
                                      PTree.get tpde_index le = Some (Vint pde_index) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      0 <= Int.unsigned proc_index < num_proc ->
                                      0 <= Int.unsigned pde_index <= PDX Int.max_unsigned ->
                                      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
                                      Mem.load Mint32 ((m, d): mem) bptpool_loc
                                               (Int.unsigned proc_index * PgSize + Int.unsigned pde_index * 4) = Some (Vint pi) ->
                                      Int.unsigned pi = pi' * PgSize + PT_PERM_PTU ->
                                      fstore0_spec (pi' * one_k + Int.unsigned vadr) 0 d = Some d' ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) rmv_pte_body E0 le' (m, d'
) Out_normal.
        Proof.
          intros.
          subst.
          unfold rmv_pte_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize one_k_minus1; intro one_k_minus1.
          generalize one_k_minus1'; intro one_k_minus1'.
          generalize (Int.unsigned_range vadr); intro vadrrange.
          functional inversion H8; subst.
          esplit.
          repeat vcgen.
          rewrite tptsize, tcharptrsize.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          rewrite Int.unsigned_repr; try omega.
          rewrite Z.mul_comm.
          rewrite Z.mul_comm with (n:= 4).
          eassumption.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          rewrite H7 in *.
          replace (pi' * 4096 + 7 - 7) with (pi' * 4096) by omega.
          rewrite Z_div_mult_full; try omega.
          repeat vcgen.
          unfold Int.add.
          repeat vcgen.
        Qed.

      End RmvPTEBody.

      Theorem rmv_pte_code_correct:
        spec_le (rmv_PTE ↦ rmvPTE_spec_low) (〚rmv_PTE ↦ f_rmv_pte 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        fbigstep (rmv_pte_body_correct s (Genv.globalenv p) makeglobalenv b0 H b2 Hb2fs Hb2fp m l d (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_rmv_pte)
                                                          (Vint n::Vint i::Vint vadr::nil)
                                                          (create_undef_temps (fn_temps f_rmv_pte)))) H6.
      Qed.

    End RMVPTE.



    Section SETIDPTE.

      Let L: compatlayer (cdata RData) := IDPMap_LOC ↦ idpmap_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
      
      Section SetIDPTEBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bidpmap_loc: block.
        Hypothesis hidpmap_loc1 : Genv.find_symbol ge IDPMap_LOC = Some bidpmap_loc.

        Lemma set_idpte_body_correct: forall m m' d env le pde_index vadr perm perm',
                                      env = PTree.empty _ ->
                                      PTree.get tpde_index le = Some (Vint pde_index) ->
                                      PTree.get tvadr le = Some (Vint vadr) ->
                                      PTree.get tperm le = Some (Vint perm) ->
                                      0 <= Int.unsigned pde_index <= PDX Int.max_unsigned ->
                                      0 <= Int.unsigned vadr <= PTX Int.max_unsigned ->
                                      ZtoPerm (Int.unsigned perm) = Some perm' ->
                                      Mem.store Mint32 ((m, d): mem) bidpmap_loc
                                                (Int.unsigned pde_index * PgSize + Int.unsigned vadr * 4)
                                      (Vint (Int.repr ((Int.unsigned pde_index * one_k + Int.unsigned vadr) * PgSize + Int.unsigned perm)))          
                                      =  Some (m', d) ->
                                      exec_stmt ge env le ((m, d): mem) set_idpte_body E0 le (m', d) Out_normal.
        Proof.
          intros.
          subst.
          unfold set_idpte_body.
          generalize max_unsigned_val; intro muval.
          generalize tptsize; intro tptsize.
          generalize tcharsize; intro tcharsize.
          generalize tcharptrsize; intro tcharptrsize.
          generalize tintsize; intro tintsize.
          generalize one_k_minus1; intro one_k_minus1.
          generalize one_k_minus1'; intro one_k_minus1'.
          assert(sizeof (Tarray tint 1024 noattr) = 4096) by reflexivity.
          repeat vcgen.
          rewrite H.
          Opaque Z.mul.
          simpl.
          lift_unfold.
          rewrite Int.unsigned_repr; try omega.
          rewrite Z.mul_comm.
          rewrite Z.mul_comm with (n:= 4).
          assumption.
        Qed.

      End SetIDPTEBody.

      Theorem set_idpte_code_correct:
        spec_le (set_IDPTE ↦ setIDPTE_spec_low) (〚set_IDPTE ↦ f_set_idpte 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigsteptest (set_idpte_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_idpte)
                                                          (Vint i::Vint vadr::Vint p0::nil)
                                                          (create_undef_temps (fn_temps f_set_idpte)))) H0.
        reflexivity.
        intro.
        repeat fbigstep_post.
      Qed.

    End SETIDPTE.

  End WithPrimitives.

End MCONTAINERCODE.
