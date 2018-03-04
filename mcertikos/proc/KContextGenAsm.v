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
(*           Layers of PM: Assembly Verification for PKContext         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
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

Require Import KContextGenSpec.
Require Import KContextGenAsmSource.

Require Import LAsmModuleSemSpec.
Require Import LRegSet.

Require Import MShare.
Require Import AbstractDataType.

Section ASM_VERIFICATION.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (*	
	.globl cswitch
cswitch:
	/* save the old kernel context */
	leal	(%eax,%eax,2), %eax
	leal	KCtxtPool_LOC(,%eax,8), %eax
	movl	%esp, (%eax)
	movl	%edi, 4(%eax)
	movl	%esi, 8(%eax)
	movl	%ebx, 12(%eax)
	movl	%ebp, 16(%eax)

	popl	%ecx
	movl	%ecx, 20(%eax)

	/* load the new kernel context */
	leal	(%edx,%edx,2), %edx
	leal	KCtxtPool_LOC(,%edx,8), %edx
	movl	(%edx), %esp
	movl	4(%edx), %edi
	movl	8(%edx), %esi
	movl	12(%edx), %ebx
	movl	16(%edx), %ebp
	movl	20(%edx), %ecx
	pushl	%ecx
	xorl	%eax, %eax
	ret

   *)

  Notation LDATA := RData. 
  Notation LDATAOps := (cdata (cdata_ops := mshareintro_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
    Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

    (*Ltac accessors_simpl:=
      match goal with
        | |- exec_storeex _ _ _ _ _ _ _ = _ =>
          unfold exec_storeex, LoadStoreSem.exec_storeex2; simpl;
          subrewrite';
          match goal with
            | |- Asm.exec_store _ _ _ _ _ _ _ = _ =>
              unfold Asm.exec_store; simpl; lift_trivial
          end
        | |- exec_loadex _ _ _ _ _ _ = _ =>
          unfold exec_loadex, LoadStoreSem.exec_loadex2; simpl;
          subrewrite';
          match goal with
            | |- Asm.exec_load _ _ _ _ _ _ = _ =>
              unfold Asm.exec_load; simpl; lift_trivial
          end
      end.*)

    Ltac accessors_simpl:=
      match goal with
        | |- exec_storeex _ _ _ _ _ _ _ = _ =>
          unfold exec_storeex, LoadStoreSem2.exec_storeex2; 
            simpl; Lregset_simpl_tac; subrewrite';
            match goal with
              | |- Asm.exec_store _ _ _ _ _ _ _ = _ =>
                unfold Asm.exec_store; simpl; 
                Lregset_simpl_tac; lift_trivial
            end
        | |- exec_loadex _ _ _ _ _ _ = _ =>
          unfold exec_loadex, LoadStoreSem2.exec_loadex2; 
            simpl; Lregset_simpl_tac; subrewrite';
            match goal with
              | |- Asm.exec_load _ _ _ _ _ _ = _ =>
                unfold Asm.exec_load; simpl; 
                Lregset_simpl_tac; lift_trivial
            end
      end.

    Ltac accessors_rewrite HW1:=
      accessors_simpl;
      erewrite HW1; trivial; try omega;
      rewrite Int.unsigned_repr by omega;
      Lregset_simpl_tac;
      subrewrite'.
    
    Lemma cswitch_spec:
      forall ge (s: stencil) (rs: regset) n n' b b0 (m'0 m0 m1 m2 m3 m4 m5: mwd LDATAOps) v0 v1 v2 v3 v4 v5,
        find_symbol s kctxt_switch = Some b ->
        make_globalenv s (kctxt_switch ↦ cswitch_function) mshare = ret ge ->
        rs PC = Vptr b Int.zero ->
        find_symbol s KCtxtPool_LOC = Some b0 ->
        Mem.store Mint32 m'0 b0 (Int.unsigned n * 24) (rs ESP) = Some m0 ->
        Mem.store Mint32 m0 b0 (Int.unsigned n * 24 + 4) (rs EDI) = Some m1 ->
        Mem.store Mint32 m1 b0 (Int.unsigned n * 24 + 8) (rs ESI) = Some m2 ->
        Mem.store Mint32 m2 b0 (Int.unsigned n * 24 + 12) (rs EBX) = Some m3 ->
        Mem.store Mint32 m3 b0 (Int.unsigned n * 24 + 16) (rs EBP) = Some m4 ->
        Mem.store Mint32 m4 b0 (Int.unsigned n * 24 + 20) (rs RA) = Some m5 ->
        Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 0) = Some v0 ->
        Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 4) = Some v1 ->
        Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 8) = Some v2 ->
        Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 12) = Some v3 ->
        Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 16) = Some v4 ->
        Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 20) = Some v5 ->
        kernel_mode (snd m'0) ->
        rs Asm.EAX = Vint n ->
        rs Asm.EDX = Vint n' ->
        0 <= (Int.unsigned n) < num_proc ->
        0 <= (Int.unsigned n') < num_proc ->
        let rs' := (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF
                                   :: IR EDX :: IR ECX :: IR EAX :: RA :: nil) rs) in
        exists r_: regset,
          lasm_step (kctxt_switch ↦ cswitch_function) (mshare (Hmwd:= Hmwd) (Hmem:= Hmem)) kctxt_switch s rs m'0 r_ m5
          /\ (forall l,
                Val.lessdef (Pregmap.get l  (rs'#ESP<- v0 #EDI <- v1 #ESI <- v2 #EBX <- v3
                                                #EBP <- v4#PC <- v5))
                            (Pregmap.get l r_)).
    Proof.
      intros.
      assert (HOS: 0 <= Int.unsigned n * 24 + 20 <= Int.max_unsigned) by rewrite_omega.
      assert (HOS': 0 <= 24 <= Int.max_unsigned) by rewrite_omega.
      assert (HW1: forall ofs, 
                     0<= ofs <= 20 -> 
                     Int.add (Int.mul n (Int.repr 24)) (Int.add Int.zero (Int.repr ofs)) = Int.repr (Int.unsigned n * 24 +  ofs)).
      {
        intros; pc_add_simpl.
      }
      assert (HW2: Int.add n (Int.add (Int.mul n (Int.repr 2)) Int.zero) = Int.mul n (Int.repr 3)).
      {
        pc_add_simpl; f_equal; omega.
      }
      assert(HW3: Int.add (Int.add Int.zero (Int.mul (Int.mul n (Int.repr 3)) (Int.repr 8))) Int.zero
                  = Int.mul n (Int.repr 24)).
      {
        pc_add_simpl; f_equal; omega.
      }
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert (Hfunct: Genv.find_funct_ptr ge b = Some (Internal cswitch_function)).
      {
        assert (Hmodule: get_module_function kctxt_switch (kctxt_switch ↦ cswitch_function) = OK (Some cswitch_function))
          by apply get_module_function_mapsto.        
        assert (HInternal: make_internal cswitch_function = OK (AST.Internal cswitch_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H in Hsymbol. inv Hsymbol.
        assumption.
      }

      assert (HLOC: Genv.find_symbol ge KCtxtPool_LOC = Some b0).
      {
        inv Hstencil_matches.
        congruence.
      }          
      destruct H15 as [Hikern Hihost].
      destruct m'0 as [m'0 d]. destruct m0, m1, m2, m3, m4, m5.

      lift_unfold.
      store_split.
      rewrite (Lregset_rewrite rs).
      esplit; split.
      econstructor; try eassumption.
      rewrite H1.

      (* leal	(%eax,%eax,2), %eax *)
      one_step_forward'.
      Lregset_simpl_tac. subrewrite'.
      rewrite Int.eq_false; try discriminate.
      simpl. rewrite HW2.

      (* leal	KCtxtPool_LOC(,%eax,8), %eax *)
      one_step_forward'.
      rewrite Int.eq_false; try discriminate.
      unfold symbol_offset. rewrite HLOC; simpl.
      rewrite HW3. 
      Lregset_simpl_tac.

      (* movl    %esp, (%eax) *)
      one_step_forward'.
      accessors_simpl.
      unfold Int.zero.
      erewrite HW1; trivial; try omega.
      rewrite Z.add_0_r.
      rewrite Int.unsigned_repr by omega.
      subrewrite'. 
      
      (* movl    %edi, 4(%eax) *)        
      one_step_forward'.
      accessors_rewrite HW1.
      (*change (Int.add (Int.add (Int.repr 2) Int.one) Int.one) with (Int.repr 4).*)

      (* movl    %esi, 8(%eax) *)
      one_step_forward'.
      accessors_rewrite HW1.

      (* movl    %ebx, 12(%eax) *)
      one_step_forward'.
      accessors_rewrite HW1.
      (*change (Int.add (Int.add (Int.repr 4) Int.one) Int.one) with (Int.repr 6).*)

      (* movl    %ebp, 16(%eax) *)
      one_step_forward'.
      accessors_rewrite HW1.
      
      (* popl *)
      one_step_forward'.
      Lregset_simpl_tac.

      (* movl    %ecx, 20(%eax) *)
      one_step_forward'.
      accessors_rewrite HW1.

      assert (HOS2: 0 <= Int.unsigned n' * 24 + 20 <= Int.max_unsigned)        
        by (rewrite int_max; omega).
      clear HW1 HW2 HW3.
      assert (HW1: forall ofs, 
                     0<= ofs <= 20 -> 
                     Int.add (Int.mul n' (Int.repr 24)) (Int.add Int.zero (Int.repr ofs)) = Int.repr (Int.unsigned n' * 24 +  ofs)).
      {
        intros; pc_add_simpl.
      }
      assert (HW2: Int.add n' (Int.add (Int.mul n' (Int.repr 2)) Int.zero) = Int.mul n' (Int.repr 3)).
      {
        pc_add_simpl; f_equal; omega.
      }
      assert(HW3: Int.add (Int.add Int.zero (Int.mul (Int.mul n' (Int.repr 3)) (Int.repr 8))) Int.zero
                  = Int.mul n' (Int.repr 24)).
      {
        pc_add_simpl; f_equal; omega.
      }

      (* leal	(%edx,%edx,2), %edx *)
      one_step_forward'.
      Lregset_simpl_tac.
      rewrite Int.eq_false; try discriminate.
      simpl. rewrite HW2.
      unfold set; simpl.

      (* leal	KCtxtPool_LOC(,%edx,8), %edx *)
      one_step_forward'.
      Lregset_simpl_tac.
      rewrite Int.eq_false; try discriminate.
      unfold symbol_offset. rewrite HLOC.
      simpl. rewrite HW3. 

      (* movl    %esp, (%eax) *) 
      one_step_forward'.
      accessors_simpl.
      unfold Int.zero.
      erewrite HW1; trivial; try omega.
      rewrite Int.unsigned_repr by omega.
      subrewrite'.
      Lregset_simpl_tac.

      (* movl    4(%edx), %edi *)
      one_step_forward'.
      accessors_rewrite HW1.
      Lregset_simpl_tac.
      
      (* movl    8(%edx), %esi *)
      one_step_forward'.
      accessors_rewrite HW1.
      Lregset_simpl_tac.

      (*movl    12(%edx), %ebx *)
      one_step_forward'.
      accessors_rewrite HW1.
      Lregset_simpl_tac.
      
      (* movl    16(%edx), %ebp*)
      one_step_forward'.
      accessors_rewrite HW1.
      Lregset_simpl_tac.

      (*movl    20(%edx), %ecx*)
      one_step_forward'.
      accessors_rewrite HW1.
      Lregset_simpl_tac.

      (*pushl	%ecx*)
      one_step_forward'.
      Lregset_simpl_tac.

      (*xor     %eax, %eax*)
      one_step_forward'.
      Lregset_simpl_tac.

      (* ret *)
      one_step_forward'.
      Lregset_simpl_tac.

      econstructor.
      reflexivity.

      unfold Lregset_fold; simpl.
      subst rs'.
      intros reg.
      repeat (rewrite Pregmap.gsspec).
      simpl_destruct_reg.
      exploit reg_false; try eassumption.
      intros HF. inv HF.
    Qed.

    Lemma kctxt_switch_code_correct:
      asm_spec_le (kctxt_switch ↦ kctxt_switch_spec_low) 
                  (〚kctxt_switch ↦ cswitch_function〛 mshare).
    Proof.
      eapply asm_sem_intro; try reflexivity.
      intros. inv H.        
      eapply make_program_make_globalenv in H0.
      exploit (make_globalenv_stencil_matches (D:= LDATAOps)); eauto.
      intros Hstencil_matches.
      assert(Hfun: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal cswitch_function)).
      {
        assert (Hmodule: get_module_function kctxt_switch (kctxt_switch ↦ cswitch_function) = OK (Some cswitch_function)) by
            reflexivity.
        assert (HInternal: make_internal cswitch_function = OK (AST.Internal cswitch_function)) by reflexivity.
        eapply make_globalenv_get_module_function in H0; eauto.
        destruct H0 as [?[Hsymbol ?]].
        inv Hstencil_matches.
        rewrite stencil_matches_symbols in Hsymbol.
        rewrite H1 in Hsymbol. inv Hsymbol.
        assumption.
      }
      
      exploit cswitch_spec; eauto 2.
      intros HW. exploit HW; eauto 2; clear HW.
      intros [r_[Hstep Hv]].
 
      assert (Heq: (Mem.nextblock m = Mem.nextblock m')%positive)
          by link_nextblock_asm.

      assert (Hle: (Mem.nextblock m <= Mem.nextblock m')%positive).
      {
        rewrite Heq; reflexivity.
      }

      refine_split'; try eassumption; try reflexivity.
      - inv H17. inv inv_inject_neutral.
        eapply Mem.neutral_inject.
        assert (Plt b0 (Mem.nextblock m)).
        {
          eapply genv_symb_range in H3.
          xomega.
        }
        pose proof (inv_reg_le _ _ _ inv_reg_inject_neutral Hle) as Hinv_inject.
        rewrite <- Heq.
        link_inject_neutral_asm.
      - esplit; reflexivity.
    Qed.
    
  End WITHMEM.
  
End ASM_VERIFICATION.