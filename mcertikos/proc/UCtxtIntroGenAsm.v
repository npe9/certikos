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
(*           Layers of PM: Assmebly verification for PUctxtIntro       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
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
Require Import Locations.
Require Import AuxStateDataType.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import FlatMemory.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import Constant.
Require Import AsmImplLemma.
Require Import AsmImplTactic.
Require Import GlobIdent.
Require Import CommonTactic.

Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compcertx.MakeProgram.
Require Import LAsmModuleSem.
Require Import LAsm.
Require Import liblayers.compat.CompatGenSem.
Require Import PrimSemantics.
Require Import Conventions.

Require Import PIPC.
Require Import UCtxtIntroGenSpec.
Require Import UCtxtIntroGenAsmSource.

Require Import LAsmModuleSemSpec.
Require Import LRegSet.
Require Import AbstractDataType.

Section ASM_VERIFICATION.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation LDATA := RData.
  Notation LDATAOps := (cdata LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    Ltac accessors_simpl:=
      match goal with
        | |- exec_storeex _ _ _ _ _ _ _ = _ =>
          unfold exec_storeex, LoadStoreSem2.exec_storeex2; 
            simpl; Lregset_simpl_tac; 
            match goal with
              | |- context [Asm.exec_store _ _ _ _ _ _ _] =>
                unfold Asm.exec_store; simpl; 
                Lregset_simpl_tac; lift_trivial
            end
        | |- exec_loadex _ _ _ _ _ _ = _ =>
          unfold exec_loadex, LoadStoreSem2.exec_loadex2; 
            simpl; Lregset_simpl_tac;
            match goal with
              | |- context[Asm.exec_load _ _ _ _ _ _ ] =>
                unfold Asm.exec_load; simpl; 
                Lregset_simpl_tac; lift_trivial
            end
      end.

    (*	
	.globl restore_uctx
restore_uctx:
	movl	0(%esp), %eax	/* %eax <- n */

	sall	$2, %eax
	movl	%eax, %edx
	sall	$4, %eax
	leal	UCTX_LOC(%edx, %eax, 1), %eax
	leal	32(%eax), %esp	/* prepare the stack of trap_out() */
	/* load the user context */
	movl	(%eax), %edi
	movl	4(%eax), %esi
	movl	8(%eax), %ebp
	movl	16(%eax), %ebx
	movl	20(%eax), %edx
	movl	24(%eax), %ecx

        movl    U_ESP(%eax), %esp
        movl    U_EIP(%eax), %eip

	movl	28(%eax), %eax
        jmp     trap_out
     *)

    Lemma Htrap_out: 
      forall s ge,
        make_globalenv s (restore_uctx ↦ restoreuctx_function) pipc = ret ge ->
        (exists b_trap_out, Genv.find_symbol ge trap_out = Some b_trap_out
                            /\ Genv.find_funct_ptr ge b_trap_out = 
                               Some (External (EF_external trap_out null_signature)))
        /\ get_layer_primitive trap_out pipc = OK (Some (primcall_general_compatsem trapout_spec)).
    Proof.
      intros.
      assert (Hprim: get_layer_primitive trap_out pipc = 
                     OK (Some (primcall_general_compatsem trapout_spec)))
        by (unfold pipc; reflexivity).
      split; try assumption.
      eapply make_globalenv_get_layer_primitive; eauto.
    Qed.

    Lemma restoreuctx_spec:
      forall ge (s: stencil) (rs: regset) rs' b (m'0: mem) b0 v0 v1 v2 v4 v5 v6 v7 v8 v9 n labd labd' sig,
        find_symbol s restore_uctx = Some b ->
        make_globalenv s (restore_uctx ↦ restoreuctx_function) pipc = ret ge ->
        rs PC = Vptr b Int.zero ->
        find_symbol s UCTX_LOC = Some b0 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EDI) = Some v0 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ESI * 4) = Some v1 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EBP * 4) = Some v2 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EBX * 4) = Some v4 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EDX * 4) = Some v5 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ECX * 4) = Some v6 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EAX * 4) = Some v7 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_ESP * 4) = Some v8 ->
        Mem.load Mint32 m'0 b0 (Int.unsigned n * UCTXT_SIZE * 4 + U_EIP * 4) = Some v9 ->
        rs' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF 
                              :: IR ECX :: IR EAX :: RA :: nil) 
                          (undef_regs (List.map preg_of destroyed_at_call) rs)) ->
        trapout_spec labd = Some labd' ->
        cid labd = Int.unsigned n ->
        kernel_mode labd ->
        high_level_invariant labd ->
        sig = mksignature (AST.Tint::nil) None cc_default ->
        extcall_arguments rs m'0 sig (Vint n ::nil) ->
        exists r_: regset,
          lasm_step (restore_uctx ↦ restoreuctx_function) (pipc (Hmwd:= Hmwd) (Hmem:= Hmem)) restore_uctx s rs (m'0, labd) r_ (m'0, labd')
          /\ (forall l,
                Val.lessdef (Pregmap.get l (rs'#Asm.EDI <- v0 #Asm.ESI <- v1 #Asm.EBP <- v2 #Asm.ESP<- v8#Asm.EBX <- v4
                                               #EDX<- v5 #ECX<-v6 #EAX <- v7# PC <- v9))
                            (Pregmap.get l r_)).
    Proof.
      simpl; intros.
      rename H12 into HRR, H13 into HTRAP, H14 into HCID, H16 into HCID_RANGE.
      apply valid_curid in HCID_RANGE. rewrite HCID in HCID_RANGE.
      simpl in H15.
      destruct H15 as [Hkern Hhost].
      assert (HOS: 0 <= Int.unsigned n * UCTXT_SIZE * 4 + UCTXT_SIZE * 4 <= Int.max_unsigned)
        by rewrite_omega.
      assert (HOS': 0 <= UCTXT_SIZE <= Int.max_unsigned)
        by rewrite_omega.
      
      exploit Htrap_out; eauto.
      intros [[b_trapout [Htrapout_symbol Htrapout_fun]] prim_trapout].

      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert (Hfunct: Genv.find_funct_ptr ge b = Some (Internal restoreuctx_function)).
      {
        assert (Hmodule: get_module_function restore_uctx (restore_uctx ↦ restoreuctx_function) = OK (Some restoreuctx_function))
          by reflexivity.
        assert (HInternal: make_internal restoreuctx_function = OK (AST.Internal restoreuctx_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H in Hsymbol. inv Hsymbol.
        assumption.
      }

      assert (HLOC: Genv.find_symbol ge UCTX_LOC = Some b0).
      {
        inv Hstencil_matches.
        congruence.
      }          
      
      rewrite (Lregset_rewrite rs).
      esplit; split.
      econstructor; try eassumption. 
      rewrite H1.

      (* movl	0(%esp), %eax *)
      one_step_forward'.
      unfold exec_loadex, LoadStoreSem2.exec_loadex2.
      unfold Asm.exec_load; simpl.
      rewrite Hhost, Hkern.
      simpl; Lregset_simpl_tac.      
      change (Int.add Int.zero Int.zero) with (Int.repr 0).
      inv H18. inv H12. inv H15. simpl in H18.
      destruct (Val.add (rs ESP) (Vint (Int.repr 0))); try (inv H18; fail).
      simpl. simpl in H18. lift_trivial. rewrite H18. trivial.
      Lregset_simpl_tac' 1.

      (*sall	$2, %eax *)
      one_step_forward'.
      simpl. unfold Int.ltu.
      change (Int.unsigned (Int.repr 2)) with 2.
      change  (Int.unsigned Int.iwordsize) with 32.
      rewrite zlt_true; [| omega].
      replace (Int.shl n (Int.repr 2)) with (Int.repr (Int.unsigned n * 4)) by
          (unfold Int.shl; rewrite Z.shiftl_mul_pow2;
           [reflexivity|
            change (Int.unsigned (Int.repr 2)) with 2; omega]).
      Lregset_simpl_tac' 2.

      (* movl	%eax, %edx *)
      one_step_forward'.
      Lregset_simpl_tac' 3.

      (*sall	$4, %eax *)
      one_step_forward'.
      unfold Int.ltu.
      change (Int.unsigned (Int.repr 4)) with 4.
      change (Int.unsigned Int.iwordsize) with 32.
      rewrite zlt_true; [|omega].
      assert (HW: Int.shl (Int.repr (Int.unsigned n * 4)) (Int.repr 4) = Int.repr (Int.unsigned n * 64)).
      {
        unfold Int.shl. 
        change (Int.unsigned (Int.repr 4)) with 4.
        rewrite Z.shiftl_mul_pow2.
        change (2^4) with 16.
        f_equal.
        pc_add_simpl.
        omega.
      }
      rewrite HW. clear HW.
      Lregset_simpl_tac' 4.

      (* leal	UCTX_LOC(%edx, %eax, 1), %eax *)
      one_step_forward'.
      rewrite Int.eq_true.
      Lregset_simpl_tac' 5.
      unfold symbol_offset.
      rewrite HLOC.
      replace (Int.add (Int.add Int.zero (Int.repr (Int.unsigned n * 64)))
                       (Int.repr (Int.unsigned n * 4))) with (Int.repr (Int.unsigned n * 17 * 4)) by
          (pc_add_simpl; rewrite Z.add_0_l;
           f_equal; omega).
      
      assert(HW: forall ofs,
                   0<= ofs <= UCTXT_SIZE * 4 -> 
                   Int.add (Int.repr (Int.unsigned n * 17 * 4))
                           (Int.add Int.zero (Int.repr ofs)) = Int.repr (Int.unsigned n * 17 * 4 + ofs)).
      {
        intros.
        pc_add_simpl.
      }

      (* leal	32(%eax), %esp *)
      one_step_forward'.
      rewrite HW; [|omega].
      Lregset_simpl_tac' 6.

      (*movl    U_EDI(%eax), %edi *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H3. trivial.
      Lregset_simpl_tac' 7. 

      (* movl    U_ESI(%eax), %esi *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H4. trivial.
      Lregset_simpl_tac' 8.

      (* movl    U_EBP(%eax), %ebp *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H5. trivial.
      Lregset_simpl_tac' 9.

      (* movl    U_EBX(%eax), %ebx *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H6. trivial.
      Lregset_simpl_tac' 10.

      (* movl    U_EDX(%eax), %edx *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H7. trivial.
      Lregset_simpl_tac' 11.

      (* movl    U_ECX(%eax), %ecx *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H8. trivial.
      Lregset_simpl_tac' 12.
      
      (* movl    U_ESP(%eax), %esp *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H10. trivial.
      Lregset_simpl_tac' 13.

      (* movl    U_EIP(%eax), %eip *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H11; trivial.
      Lregset_simpl_tac' 14.
      
      (* movl    U_EAX(%eax), %ecx *)
      one_step_forward'.
      accessors_simpl.
      rewrite Hkern, Hhost.
      rewrite HW; [|omega].
      rewrite Int.unsigned_repr by omega.
      rewrite H9; trivial.
      Lregset_simpl_tac' 15.

      (* call trap out*)
      one_step_forward'.
      unfold symbol_offset. unfold fundef.
      rewrite Htrapout_symbol.
      Lregset_simpl_tac.
      
      (* call trapout*)
      eapply star_one; eauto.
      eapply (LAsm.exec_step_prim_call _ b_trapout); eauto 1. 
      econstructor.
      refine_split'; eauto 1.
      econstructor; eauto 1. simpl.
      econstructor.
      apply HTRAP.

      reflexivity.

      Lregset_simpl_tac.
      unfold Lregset_fold.
      simpl. intros reg.
      repeat (rewrite Pregmap.gsspec).
      simpl_destruct_reg.     
      exploit reg_false; try eassumption.
      intros HF. inv HF.
    Qed.

    Lemma restore_uctx_code_correct:
      asm_spec_le (restore_uctx ↦ restore_uctx_spec_low)
                  (〚 restore_uctx ↦ restoreuctx_function 〛 pipc).
    Proof.
      eapply asm_sem_intro; try solve [ reflexivity | eexists; reflexivity ].
      intros. inv H.
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b =
                     Some (Internal restoreuctx_function)).
      {
        assert (Hmodule:
          get_module_function restore_uctx (restore_uctx ↦ restoreuctx_function)
            = OK (Some restoreuctx_function)) by reflexivity.
        assert (HInternal:
          make_internal restoreuctx_function
            = OK (AST.Internal restoreuctx_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }

      exploit restoreuctx_spec; eauto 2.
      intros HW. exploit HW; eauto 2; clear HW.
      intros [r_[Hstep Hv]].

      assert (Hle: (Mem.nextblock m'0 <= Mem.nextblock m'0)%positive)
        by reflexivity.

      refine_split'; try eassumption; try reflexivity.
      inv H17. inv inv_inject_neutral.
      eapply Mem.neutral_inject.
      assert (Plt b0 (Mem.nextblock m'0)).
      {
        eapply genv_symb_range in H3.
        simpl in inv_mem_valid.
        unfold lift in inv_mem_valid; simpl in inv_mem_valid.
        xomega.
      }
      pose proof (inv_reg_le _ _ _ inv_reg_inject_neutral Hle) as Hinv_inject.
      simpl; unfold lift; simpl.
      assumption.
    Qed.

    (*	
	.globl elf_load
elf_load:
        ELF_LOAD
   *)

    Lemma elf_load_code_correct:
      asm_spec_le (elf_load ↦ elf_load_spec_low)
                  (〚elf_load ↦ elfload_function 〛 pipc).
    Proof.
      eapply asm_sem_intro; try reflexivity; simpl.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal elfload_function)).
      {
        assert (Hmodule: get_module_function elf_load (elf_load ↦ elfload_function) = OK (Some elfload_function)) by
            reflexivity.
        assert (HInternal: make_internal elfload_function = OK (AST.Internal elfload_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }
      refine_split'.
      - reflexivity.
      - econstructor; eauto.
        one_step_forward 0.
        + reflexivity.
        + econstructor.
        + reflexivity.
      - reflexivity.
      - inv H6. inv inv_inject_neutral.
        eapply Mem.neutral_inject in inv_mem_inject_neutral.
        assumption.
      - reflexivity.
      - intros reg.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.     
        constructor.
      - esplit; reflexivity.
    Qed.

  End WITHMEM.

End ASM_VERIFICATION.
