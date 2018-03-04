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
(*           Layers of PM: Assembly Verification for Thread            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
(*Require Import Errors.*)
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import MemoryExtra.
Require Import EventsExtra.
Require Import GlobalenvsExtra.
Require Import Locations.
Require Import DataType.
Require Import LAsm.
Require Import CDataTypes.
Require Import AsmExtra.
Require Clight.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import ZArith.Zwf.
Require Import EventsExtra.
Require Import GlobalenvsExtra.
Require Import Smallstep.
Require Import Op.
Require Import Values.
Require Import MemoryExtra.
Require Import Maps.
Require Import Heap.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import Implementation.
(*Require Import SeparateCompiler.*)
Require Import ClightImplemExtra.
Require Import LayerDefinition.
Require Import RealParams.
Require Import CInitSpecsMPTOp.
Require Import CInitSpecsMPTCommon.
Require Import CInitSpecsMPTBit.
Require Import CInitSpecsproc.
Require Import CInitSpecsvirt.
Require Import AsmImplLemma.
Require Import ProcDataType.
Require Import VirtDataType.
(*Require Import TrapDataType.*)
Require Import Conventions.
Require Import VSVMIntro.
Require Import VVMCBOp.
Require Import VSVM.
Require Import VSVMSave.

Require Import TrapArgGenAsmData.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

Module TRAPARGGEN_ASM.

  Section ASM_VERIFY.

    Context `{real_params: RealParams}.

    Notation Lfundef := (Asm.fundef (external_function:= VSVMSAVE.primOp)).

    Notation Lprogram := (Asm.program (external_function:= VSVMSAVE.primOp)).
    Variable tprog: Lprogram.
    Notation tge := (Genv.globalenv tprog).

    Notation LDATA :=(VSVMINTRO.AbData (PgSize:=PgSize) (num_proc:=num_proc) (kern_low:=kern_low) (num_chan:= num_chan)
                                       (kern_high:=kern_high) (maxpage:=maxpage)).

    Context `{PageFaultHandler_LOC: ident}.
    Context `{START_USER_FUN_LOC: ident}.

    Section WITHMEM.

      Local Instance LdataOp:AbstractDataOps LDATA:= (VSVMSAVE.abstract_data (Hnpc:= Hnpc)).

      Context {mem__L}
              `{HLmem: !LayerMemoryModel LDATA mem__L}.

      Instance LLayer: LayerDefinition (layer_mem:= HLmem) LDATA VSVMSAVE.primOp mem__L :=
        VSVMSAVE.layer_def (PgSize:=PgSize) (num_proc:=num_proc)(kern_low:=kern_low) (real_abtcb:= real_abtcb)
                       (kern_high:=kern_high) (maxpage:=maxpage) (HPS4:=HPS4) (Hnpc := Hnpc) (STACK_LOC:=STACK_LOC)
                       (Hlow := Hlow) (Hhigh:= Hhigh) (real_ptp := real_ptp) (real_free_pt:= real_free_pt)
                       (real_pt := real_pt) (real_nps:=real_nps) (real_AT := real_AT) (real_ptb := real_ptb)
                       (num_chan := num_chan) (real_abq:= real_abq) (Hnchan:= Hnchan) (real_chpool := real_chpool)
                       (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC := START_USER_FUN_LOC) (real_NPT := real_npt)
                       (real_vmcbz := real_vmcbz).        

      Notation lstep := (VSVMSAVE.step 
                           (PageFaultHandler_LOC:= PageFaultHandler_LOC) (HPS4:= HPS4) (real_chpool:= real_chpool)
                           (real_nps:= real_nps) (real_AT:= real_AT) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_abtcb:= real_abtcb)
                           (real_ptp := real_ptp) (real_pt:= real_pt) (Hnpc := Hnpc) (real_ptb:= real_ptb) (real_abq:= real_abq)
                           (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC)(num_chan:= num_chan) (Hnchan:= Hnchan)
                           (STACK_TOP:= STACK_TOP) (START_USER_FUN_LOC:= START_USER_FUN_LOC) (real_NPT:= real_npt)
                           (real_vmcbz:= real_vmcbz)).

      Notation LADT := VSVMINTRO.ADT.
      Notation LINV := VSVMINTRO.INV.

      Hypothesis Hhostin: exists b_hostin, Genv.find_symbol tge host_in = Some b_hostin
                                             /\ Genv.find_funct_ptr tge b_hostin = Some (External VSVMSAVE.PHostIn).

      Hypothesis Hsave_svm: exists b_save, 
                                  Genv.find_symbol tge svm_state_save = Some b_save
                                  /\ Genv.find_funct_ptr tge b_save = Some (External VSVMSAVE.PSVMStateSave).

      Hypothesis Hrestore_hctx: exists b_restore, 
                                  Genv.find_symbol tge restore_hctx = Some b_restore
                                  /\ Genv.find_funct_ptr tge b_restore = Some (External VSVMSAVE.PRestoreHctx).

      Lemma svm_exit_vm_spec:
        forall r' b m0 labd' r'' sig vargs v0 v1 v2 v3 v4 v5 v6 v7 v8 rs',
          let labd := (Mem.get_abstract_data m0) in
            r' PC = Vptr b Int.zero
            -> Genv.find_funct_ptr tge b = Some (Im_vm_exit)
            -> VSVMSAVE.svm_exit_vm labd (Vint v0) (Vint v1) (Vint v2) (Vint v3)
                                    (Vint v4) (Vint v5) (Vint v6) (Vint v7) (Vint v8) = Some (labd', rs')
            -> asm_invariant tge (State r' m0)
            -> VSVMSAVE.low_level_invariant (Mem.nextblock m0) labd
            -> sig = mksignature (Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::Tint::nil) None
            -> vargs = (Vint v0:: Vint v1 :: Vint v2 :: Vint v3:: Vint v4 :: Vint v5 :: Vint v6
                             :: Vint v7 :: Vint v8 ::nil)
            -> extcall_arguments r' m0 sig vargs
            -> r'' = (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: IR EAX :: RA :: nil) 
                                 (undef_regs (List.map preg_of temporary_regs)
                                             (undef_regs (List.map preg_of destroyed_at_call_regs) r')))
            -> r' ESP <> Vundef
            -> (forall b1 o, r' ESP = Vptr b1 o -> Mem.tget m0 b1 = Some Tag_stack)
            -> exists r_, 
                 plus lstep tge (State r' m0) E0 (State r_ (Mem.put_abstract_data m0 labd'))
                 /\ (forall l,
                       Val.lessdef (Pregmap.get l (r''#ECX <- (rs'#ECX) #EDI <- (rs'#EDI) #ESI <- (rs'#ESI)
                                                      #EBX <- (rs'#EBX) #EBP <- (rs'#EBP)#EDX <- (rs'#EDX)
                                                      #ESP <- (rs'#ESP) #PC <- (rs'#RA)))
                                   (Pregmap.get l r_)).
      Proof.
        intros.
        generalize H; intros HPC. 
        inv H2.
        rename H6 into HAN.
        rename H8 into HESP.
        rename H9 into HESPTAG.

        assert (HOS': 0 <= 64 <= Int.max_unsigned).
        split.
        omega.
        vm_discriminate.

        destruct Hsave_svm as [b_save [Hsave Hsave_fun]].
        destruct Hhostin as [b_hostint [Hhostin_symbol Hhostin_fun]].
        destruct Hrestore_hctx as [b_restore [Hrestore Hrestore_fun]].
        
        destruct (TRAPARGGEN_ASM_DATA.vm_exit_generate _ _ _ _ _ _ _ _ _ _ _ _ H1 H3) as 
            [labd0[HEX1[HEX2[HP[HM1 HM2]]]]].
        clear H1.
        subst labd.

        unfold LdataOp in *.
        unfold TRAPARGGEN_ASM_DATA.LdataOp in *.
        esplit.
        split.
        econstructor; eauto.

        (* call host_in*)
        econstructor; eauto.        
        econstructor; eauto.
        pc_add_simpl.
        simpl.
        rewrite H.
        simpl.
        change (Int.add Int.zero Int.one) with (Int.repr 1).
        unfold symbol_offset.
        rewrite Hhostin_symbol.

        (* call host in body*)
        econstructor; eauto.
        eapply (LSemantics.exec_step_prim_call _ b_hostint); eauto 1; repeat simpl_Pregmap. 
        trivial.
        constructor; trivial.
        simpl.
        econstructor; eauto.

        (* call save_vm*)
        repeat simpl_Pregmap.
        econstructor; eauto.        
        econstructor; eauto.
        repeat simpl_Pregmap.
        trivial.
        pc_add_simpl.
        simpl.
        trivial.
        change (Int.add (Int.repr 1) Int.one) with (Int.repr 2).
        unfold symbol_offset.
        rewrite Hsave.

        (* call save_vm body*)
        econstructor; eauto.
        eapply (LSemantics.exec_step_external _ b_save); eauto 1; repeat simpl_Pregmap.
        econstructor; eauto.
        rewrite Mem.get_put_abstract_data.
        apply HEX2.
        inv HAN.
        simpl in *.
        assert (HAG: forall av1 av2,
                        extcall_arg r' m0 (Locations.S (Outgoing av1 Tint)) (Vint av2) ->
                        extcall_arg
                           ((((r' # RA <- (Vptr b (Int.repr 1))) # PC <- (Vptr b_hostint Int.zero))
                               # PC <- (Vptr b (Int.repr 1))) # RA <- (Vptr b (Int.repr 2))) # PC <-
                           (Vptr b_save Int.zero) (Mem.put_abstract_data m0 labd0)
                           (Locations.S (Outgoing av1 Tint)) (Vint av2)).
        intros.
        inv H1; econstructor; eauto; simpl in *; repeat simpl_Pregmap.
        destruct (r' ESP); try (inv H6; fail);
        simpl in *;
        erewrite Mem.load_put_abstract_data;
        trivial.

        constructor; trivial;
        repeat match goal with
          | [H0: extcall_arg _ _ _ _ |- extcall_arg _ _ _ _] => apply HAG; trivial
          | [H0: extcall_arg _ _ _ _, H1: list_forall2 _ _ _  |- list_forall2 _ _ _] =>
            inv H1;
            constructor; trivial
        end.

        discriminate.
        intros.
        erewrite Mem.tget_put_abstract_data; eauto.

        (* call restore_hctx*)
        unfold loc_external_result.
        simpl.
        repeat simpl_Pregmap.
        rewrite Mem.put_put_abstract_data.
        eapply star_left; eauto.
        econstructor; eauto.        
        repeat simpl_Pregmap.
        trivial.
        pc_add_simpl.
        simpl.
        trivial.
        unfold symbol_offset.
        rewrite Hrestore.

        (* call restore body*)
        eapply star_one; eauto.
        eapply (LSemantics.exec_step_prim_call _ b_restore); eauto 1; repeat simpl_Pregmap. 
        trivial.
        constructor; trivial.                
        econstructor; eauto.
        rewrite Mem.get_put_abstract_data.
        apply HP.
        rewrite Mem.nextblock_put_abstract_data.
        auto.
        
        trivial.
        
        simpl.
        unfold nextinstr_nf.
        unfold nextinstr.
        simpl.
        repeat simpl_Pregmap. 
        intros reg.
        repeat (rewrite Pregmap.gsspec).
        simpl_destruct_reg.
        
        trivial.
      Qed.

    End WITHMEM.

  End ASM_VERIFY.

End TRAPARGGEN_ASM.
