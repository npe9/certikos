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
(*         for the C functions implemented in the PThread layer        *)
(*                                                                     *)
(*                        Xiongnan (Newman) Wu                         *)
(*                                                                     *)
(*                          Yale University                            *)
(*                                                                     *)
(* *********************************************************************)
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
Require Import PThread.
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
Require Import IPCIntroGenSpec.
Require Import TacticsForTesting.
Require Import PThreadCSource.
Require Import AbstractDataType.
Require Import ObjSyncIPC.


Module PTHREADCODE.

  Section WithPrimitives.

  Lemma t_struct_SyncChan_size: sizeof t_struct_SyncIPCChan = 12%Z.
  Proof. reflexivity. Qed.

    Context `{real_params_ops : RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    Local Open Scope Z_scope.


    Section GETKERNELPA.

      Let L: compatlayer (cdata RData) := pt_read ↦ gensem ptRead_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetKernelPABody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** pt_read *)

        Variable bpt_read: block.

        Hypothesis hpt_read1 : Genv.find_symbol ge pt_read = Some bpt_read. 
        
        Hypothesis hpt_read2 : Genv.find_funct_ptr ge bpt_read = Some (External (EF_external pt_read (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma get_kernel_pa_body_correct: forall m d env le pidval vaval val,
                                           env = PTree.empty _ ->
                                           PTree.get _pid le = Some (Vint pidval) ->
                                           PTree.get _va le = Some (Vint vaval) ->
                                           high_level_invariant d ->
                                           get_kernel_pa_spec (Int.unsigned pidval) (Int.unsigned vaval) d = Some (Int.unsigned val) ->
                                           0 <= (Int.unsigned pidval) < num_proc ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) get_kernel_pa_body E0 le' (m, d) (Out_return (Some (Vint val, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold get_kernel_pa_body.
          functional inversion H3; subst.
          assert(0 <= paddr <= Int.max_unsigned).
          {
            functional inversion H7; subst.
            functional inversion H9; subst.
            destruct H2.
            unfold pdi, pti, pt in *.
            unfold PTE_Arg in H10.
            Require Import CommonTactic.
            subdestruct.
            unfold PDE_Arg in Hdestruct.
            subdestruct.
            unfold consistent_pmap_domain in valid_pmap_domain.
            assert(0 <= (Int.unsigned vaval) < 4294967296).
            {
              unfold PDX, PTX in *.
              Require Import XOmega.
              clearAllExceptTwo muval a1.
              xomega.
            }
            generalize (valid_pmap_domain (Int.unsigned pidval) H4 (Int.unsigned vaval) H pdt _x0 H15 padr p H16).
            intro tmp.
            destruct tmp.
            generalize (valid_nps H6); intro.
            destruct p; simpl.
            omega.
            omega.
            destruct b; omega.
            omega.
          }
          
          rewrite <- Int.repr_unsigned with val.
          rewrite <- H5.
          esplit.
          d3 vcgen.
          repeat vcgen.
          instantiate (1:= (Int.repr paddr)).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.
          d3 vcgen.
          repeat vcgen.
          discharge_cmp.
          econstructor.
          ptreesolve.
          xomega.
          xomega.
          xomega.
          xomega.
        Qed.

      End GetKernelPABody.

      Theorem get_kernel_pa_code_correct:
        spec_le (get_kernel_pa ↦ get_kernel_pa_spec_low) (〚get_kernel_pa ↦ f_get_kernel_pa 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (get_kernel_pa_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_get_kernel_pa)
                                                               (Vint pid :: Vint vaddr :: nil)
                                                               (create_undef_temps (fn_temps f_get_kernel_pa)))) H1. 
      Qed.

    End GETKERNELPA.


    Section GETSYNCCHANTO.
      Let L: compatlayer (cdata RData) := SYNCCHPOOL_LOC ↦ syncchpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GETSYNCCHANTOBODY.
        
        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variables bsyncchpool_loc: block.
        Hypothesis hbsyncchpool_loc: Genv.find_symbol ge SYNCCHPOOL_LOC = Some bsyncchpool_loc.


        Lemma get_sync_chan_to_body_correct: 
          forall m d env le chanid to,
          env = PTree.empty _
          -> PTree.get tchanid le = Some (Vint chanid)
          -> Mem.load Mint32 (m, d) bsyncchpool_loc (Int.unsigned chanid * 12) = Some (Vint to)
          -> 0 <= (Int.unsigned chanid) < num_chan
          -> exec_stmt ge env le ((m, d): mem) get_sync_chan_to_body E0 le (m, d) (Out_return (Some (Vint to, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_SyncChan_size; intro.
          intros.
          subst.
          unfold get_sync_chan_to_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 12 * Int.unsigned chanid + 0) with (Int.unsigned chanid * 12) by omega.
          assumption.
        Qed.
      End GETSYNCCHANTOBODY.

        
        Theorem get_sync_chan_to_code_correct:
          spec_le (get_sync_chan_to ↦ get_sync_chan_to_spec_low) (〚get_sync_chan_to ↦ f_get_sync_chan_to 〛L).
        Proof.
          fbigstep_pre L.
          fbigstep (get_sync_chan_to_body_correct 
                   (Genv.globalenv p) b0 H 
                   (fst m') (snd m') 
                   (PTree.empty _)
                   (bind_parameter_temps' (fn_params f_get_sync_chan_to)
                                          (Vint chanid::nil)
                                          (create_undef_temps (fn_temps f_get_sync_chan_to)))) m'.
        Qed.
    End GETSYNCCHANTO.

    Section GETSYNCCHANPADDR.
      Let L: compatlayer (cdata RData) := SYNCCHPOOL_LOC ↦ syncchpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GETSYNCCHANPADDRBODY.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variables bsyncchpool_loc: block.
        Hypothesis hbsyncchpool_loc: Genv.find_symbol ge SYNCCHPOOL_LOC = Some bsyncchpool_loc.

        Lemma get_sync_chan_paddr_body_correct: 
          forall m d env le chanid paddr,
          env = PTree.empty _
          -> PTree.get tchanid le = Some (Vint chanid)
          -> Mem.load Mint32 (m, d) bsyncchpool_loc (Int.unsigned chanid * 12 + 4) = Some (Vint paddr)
          -> 0 <= (Int.unsigned chanid) < num_chan
          -> exec_stmt ge env le ((m, d): mem) get_sync_chan_paddr_body E0 le (m, d) (Out_return (Some (Vint paddr, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_SyncChan_size; intro.
          intros.
          subst.
          unfold get_sync_chan_paddr_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr; try omega.
          replace ((0 + 12 * Int.unsigned chanid + 4)) with (Int.unsigned chanid * 12 + 4) by omega.
          assumption.
        Qed.
        
      End GETSYNCCHANPADDRBODY.

        Theorem get_sync_chan_paddr_code_correct:
          spec_le (get_sync_chan_paddr ↦ get_sync_chan_paddr_spec_low) (〚get_sync_chan_paddr ↦ f_get_sync_chan_paddr 〛L).
        Proof.
          fbigstep_pre L.
          fbigstep (get_sync_chan_paddr_body_correct 
                   (Genv.globalenv p) b0 H 
                   (fst m') (snd m') 
                   (PTree.empty _)
                   (bind_parameter_temps' (fn_params f_get_sync_chan_paddr)
                                          (Vint chanid::nil)
                                          (create_undef_temps (fn_temps f_get_sync_chan_paddr)))) m'.
        Qed.

    End GETSYNCCHANPADDR.

    Section GETSYNCCHANCOUNT.
      Let L: compatlayer (cdata RData) := SYNCCHPOOL_LOC ↦ syncchpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GETSYNCCHANCOUNTBODY.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variables bsyncchpool_loc: block.
        Hypothesis hbsyncchpool_loc: Genv.find_symbol ge SYNCCHPOOL_LOC = Some bsyncchpool_loc.

        Lemma get_sync_chan_count_body_correct: 
          forall m d env le chanid count,
          env = PTree.empty _
          -> PTree.get tchanid le = Some (Vint chanid)
          -> Mem.load Mint32 (m, d) bsyncchpool_loc (Int.unsigned chanid * 12 + 8) = Some (Vint count)
          -> 0 <= (Int.unsigned chanid) < num_chan
          -> exec_stmt ge env le ((m, d): mem) get_sync_chan_count_body E0 le (m, d) (Out_return (Some (Vint count, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_SyncChan_size; intro.
          intros.
          subst.
          unfold get_sync_chan_count_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr; try omega.
          replace ((0 + 12 * Int.unsigned chanid + 8)) with (Int.unsigned chanid * 12 + 8) by omega.
          assumption.
        Qed.
        
      End GETSYNCCHANCOUNTBODY.

        Theorem get_sync_chan_count_code_correct:
          spec_le (get_sync_chan_count ↦ get_sync_chan_count_spec_low) (〚get_sync_chan_count ↦ f_get_sync_chan_count 〛L).
        Proof.
          fbigstep_pre L.
          fbigstep (get_sync_chan_count_body_correct 
                   (Genv.globalenv p) b0 H 
                   (fst m') (snd m') 
                   (PTree.empty _)
                   (bind_parameter_temps' (fn_params f_get_sync_chan_count)
                                          (Vint chanid::nil)
                                          (create_undef_temps (fn_temps f_get_sync_chan_count)))) m'.
        Qed.

    End GETSYNCCHANCOUNT.
    


    Section SETSYNCCHANTO.
      Let L: compatlayer (cdata RData) := SYNCCHPOOL_LOC ↦ syncchpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SETSYNCCHANTOBODY.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bsyncchpool_loc: block.
        Hypothesis hbsyncchpool_loc: Genv.find_symbol ge SYNCCHPOOL_LOC = Some bsyncchpool_loc.
        
        Lemma set_sync_chan_to_body_correct:
          forall m m' d env le chanid to,
            env = PTree.empty _
            -> PTree.get tchanid le = Some (Vint chanid)
            -> PTree.get toval le = Some (Vint to)
            -> Mem.store Mint32 (m, d) bsyncchpool_loc (Int.unsigned chanid * 12) (Vint to) = Some (m', d)
            -> 0 <= (Int.unsigned chanid) < num_chan
            -> exec_stmt ge env le ((m, d): mem) set_sync_chan_to_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_SyncChan_size; intro.
          intros.
          subst.
          unfold set_sync_chan_to_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 12 * Int.unsigned chanid + 0) with (Int.unsigned chanid * 12) by omega.
          assumption.
        Qed.

      End SETSYNCCHANTOBODY.

      Theorem set_sync_chan_to_code_correct:
        spec_le (set_sync_chan_to ↦ set_sync_chan_to_spec_low) (〚set_sync_chan_to ↦ f_set_sync_chan_to 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_sync_chan_to_body_correct
                                   (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_sync_chan_to)
                                                          ((Vint chanid)::(Vint to)::nil)
                                                          (create_undef_temps (fn_temps f_set_sync_chan_to)))) H0.
      Qed.

    End SETSYNCCHANTO.

    Section SETSYNCCHANPADDR.
      Let L: compatlayer (cdata RData) := SYNCCHPOOL_LOC ↦ syncchpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SETSYNCCHANPADDRBODY.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bsyncchpool_loc: block.
        Hypothesis hbsyncchpool_loc: Genv.find_symbol ge SYNCCHPOOL_LOC = Some bsyncchpool_loc.
        
        Lemma set_sync_chan_paddr_body_correct:
          forall m m' d env le chanid paddr,
            env = PTree.empty _
            -> PTree.get tchanid le = Some (Vint chanid)
            -> PTree.get paddrval le = Some (Vint paddr)
            -> Mem.store Mint32 (m, d) bsyncchpool_loc (Int.unsigned chanid * 12 + 4) (Vint paddr) = Some (m', d)
            -> 0 <= (Int.unsigned chanid) < num_chan
            -> exec_stmt ge env le ((m, d): mem) set_sync_chan_paddr_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_SyncChan_size; intro.
          intros.
          subst.
          unfold set_sync_chan_paddr_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 12 * Int.unsigned chanid + 4) with (Int.unsigned chanid * 12 + 4) by omega.
          assumption.
        Qed.

      End SETSYNCCHANPADDRBODY.

      Theorem set_sync_chan_paddr_code_correct:
        spec_le (set_sync_chan_paddr ↦ set_sync_chan_paddr_spec_low) (〚set_sync_chan_paddr ↦ f_set_sync_chan_paddr 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_sync_chan_paddr_body_correct
                                   (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_sync_chan_paddr)
                                                          ((Vint chanid)::(Vint paddr)::nil)
                                                          (create_undef_temps (fn_temps f_set_sync_chan_paddr)))) H0.
      Qed.

    End SETSYNCCHANPADDR.

    Section SETSYNCCHANCOUNT.
      Let L: compatlayer (cdata RData) := SYNCCHPOOL_LOC ↦ syncchpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SETSYNCCHANCOUNTBODY.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bsyncchpool_loc: block.
        Hypothesis hbsyncchpool_loc: Genv.find_symbol ge SYNCCHPOOL_LOC = Some bsyncchpool_loc.
        
        Lemma set_sync_chan_count_body_correct:
          forall m m' d env le chanid count,
            env = PTree.empty _
            -> PTree.get tchanid le = Some (Vint chanid)
            -> PTree.get countval le = Some (Vint count)
            -> Mem.store Mint32 (m, d) bsyncchpool_loc (Int.unsigned chanid * 12 + 8) (Vint count) = Some (m', d)
            -> 0 <= (Int.unsigned chanid) < num_chan
            -> exec_stmt ge env le ((m, d): mem) set_sync_chan_count_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_SyncChan_size; intro.
          intros.
          subst.
          unfold set_sync_chan_count_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 12 * Int.unsigned chanid + 8) with (Int.unsigned chanid * 12 + 8) by omega.
          assumption.
        Qed.

      End SETSYNCCHANCOUNTBODY.

      Theorem set_sync_chan_count_code_correct:
        spec_le (set_sync_chan_count ↦ set_sync_chan_count_spec_low) (〚set_sync_chan_count ↦ f_set_sync_chan_count 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_sync_chan_count_body_correct
                                   (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_sync_chan_count)
                                                          ((Vint chanid)::(Vint count)::nil)
                                                          (create_undef_temps (fn_temps f_set_sync_chan_count)))) H0.
      Qed.

    End SETSYNCCHANCOUNT.

    Section INITSYNCCHAN.

      Let L: compatlayer (cdata RData) := SYNCCHPOOL_LOC ↦ syncchpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section INITSYNCCHANBODY.
        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bsyncchpool_loc: block.
        Hypothesis hbsyncchpool_loc: Genv.find_symbol ge SYNCCHPOOL_LOC = Some bsyncchpool_loc.
        
        Lemma init_sync_chan_body_correct:
          forall m m0 m1 m' d env le chanid,
            env = PTree.empty _
            -> PTree.get tchanid le = Some (Vint chanid)
            -> Mem.store Mint32 (m, d) bsyncchpool_loc (Int.unsigned chanid * 12) (Vint (Int.repr num_chan)) = Some (m0, d)
            -> Mem.store Mint32 (m0, d) bsyncchpool_loc (Int.unsigned chanid * 12 + 4) (Vint Int.zero) = Some (m1, d)
            -> Mem.store Mint32 (m1, d) bsyncchpool_loc (Int.unsigned chanid * 12 + 8) (Vint Int.zero) = Some (m', d)
            -> 0 <= (Int.unsigned chanid) < num_chan
            -> exec_stmt ge env le ((m, d): mem) init_sync_chan_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_SyncChan_size; intro.
          intros.
          subst.
          unfold init_sync_chan_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 12 * Int.unsigned chanid + 0) with (Int.unsigned chanid * 12) by omega.
          eassumption.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 12 * Int.unsigned chanid + 4) with (Int.unsigned chanid * 12 + 4) by omega.
          eassumption.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 12 * Int.unsigned chanid + 8) with (Int.unsigned chanid * 12 + 8) by omega.
          assumption.
        Qed.

      End INITSYNCCHANBODY.

      Theorem init_sync_chan_code_correct:
        spec_le (init_sync_chan ↦ init_sync_chan_spec_low) (〚init_sync_chan ↦ f_init_sync_chan 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m, m', m1, H1, m2, H2.
        fbigstep (init_sync_chan_body_correct
                                   (Genv.globalenv p) b0 H m m1 m2 m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_init_sync_chan)
                                                          (Vint chanid::nil)
                                                          (create_undef_temps (fn_temps f_init_sync_chan)))) H0.
      Qed.
    End INITSYNCCHAN.


(*


    Section GETCHANINFO.

      Let L: compatlayer (cdata RData) := CHPOOL_LOC ↦ chpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetChanInfoBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable bchpool_loc: block.
        Hypothesis hbchpool_loc: Genv.find_symbol ge CHPOOL_LOC = Some bchpool_loc.

        Lemma get_chan_info_body_correct: forall m d env le chan_index info,
                                            env = PTree.empty _ ->
                                            PTree.get tchan_index le = Some (Vint chan_index) ->
                                            Mem.load Mint32 (m, d) bchpool_loc (Int.unsigned chan_index * 8) = Some (Vint info) ->
                                            0 <= (Int.unsigned chan_index) < num_chan ->
                                            exec_stmt ge env le ((m, d): mem) get_chan_info_body E0 le (m, d) (Out_return (Some (Vint info, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_Chan_size; intro.
          intros.
          subst.
          unfold get_chan_info_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 8 * Int.unsigned chan_index + 0) with (Int.unsigned chan_index * 8) by omega.
          assumption.
        Qed.

      End GetChanInfoBody.

      Theorem get_chan_info_code_correct:
        spec_le (get_chan_info ↦ get_chan_info_spec_low) (〚get_chan_info ↦ f_get_chan_info 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_chan_info_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_chan_info)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_get_chan_info)))) m'.
      Qed.

    End GETCHANINFO.

    Section SETCHANINFO.

      Let L: compatlayer (cdata RData) := CHPOOL_LOC ↦ chpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetChanInfoBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bchpool_loc: block.
        Hypothesis hbchpool_loc: Genv.find_symbol ge CHPOOL_LOC = Some bchpool_loc.

        Lemma set_chan_info_body_correct: forall m m' d env le chan_index info,
                                            env = PTree.empty _ ->
                                            PTree.get tchan_index le = Some (Vint chan_index) ->
                                            PTree.get tinfo le = Some (Vint info) ->
                                            Mem.store Mint32 (m, d) bchpool_loc (Int.unsigned chan_index * 8) (Vint info) = Some (m', d) ->
                                            0 <= (Int.unsigned chan_index) < num_chan ->
                                            exec_stmt ge env le ((m, d): mem) set_chan_info_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_Chan_size; intro.
          intros.
          subst.
          unfold set_chan_info_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 8 * Int.unsigned chan_index + 0) with (Int.unsigned chan_index * 8) by omega.
          assumption.
        Qed.

      End SetChanInfoBody.

      Theorem set_chan_info_code_correct:
        spec_le (set_chan_info ↦ set_chan_info_spec_low) (〚set_chan_info ↦ f_set_chan_info 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_chan_info_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_chan_info)
                                                          (Vint n::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_chan_info)))) H0.
      Qed.

    End SETCHANINFO.


    Section GETCHANCONTENT.

      Let L: compatlayer (cdata RData) := CHPOOL_LOC ↦ chpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section GetChanContentBody.

        Context `{Hwb: WritableBlockOps}.

        Variables (ge: genv).

        Variable bchpool_loc: block.
        Hypothesis hbchpool_loc: Genv.find_symbol ge CHPOOL_LOC = Some bchpool_loc.

        Lemma get_chan_content_body_correct: forall m d env le chan_index content,
                                               env = PTree.empty _ ->
                                               PTree.get tchan_index le = Some (Vint chan_index) ->
                                               Mem.load Mint32 (m, d) bchpool_loc (Int.unsigned chan_index * 8 + 4) = Some (Vint content) ->
                                               0 <= (Int.unsigned chan_index) < num_chan ->
                                               exec_stmt ge env le ((m, d): mem) get_chan_content_body E0 le (m, d) (Out_return (Some (Vint content, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_Chan_size; intro.
          intros.
          subst.
          unfold get_chan_content_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 8 * Int.unsigned chan_index + 4) with (Int.unsigned chan_index * 8 + 4) by omega.
          assumption.
        Qed.

      End GetChanContentBody.

      Theorem get_chan_content_code_correct:
        spec_le (get_chan_content ↦ get_chan_content_spec_low) (〚get_chan_content ↦ f_get_chan_content 〛L).
      Proof.
        fbigstep_pre L.
        fbigstep (get_chan_content_body_correct (Genv.globalenv p) b0 H (fst m') (snd m') (PTree.empty _) (bind_parameter_temps' (fn_params f_get_chan_content)
                                                                                                                        (Vint n::nil)
                                                                                                                        (create_undef_temps (fn_temps f_get_chan_content)))) m'.
      Qed.

    End GETCHANCONTENT.


    Section SETCHANCONTENT.

      Let L: compatlayer (cdata RData) := CHPOOL_LOC ↦ chpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetChanContentBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bchpool_loc: block.
        Hypothesis hbchpool_loc: Genv.find_symbol ge CHPOOL_LOC = Some bchpool_loc.

        Lemma set_chan_content_body_correct: forall m m' d env le chan_index content,
                                               env = PTree.empty _ ->
                                               PTree.get tchan_index le = Some (Vint chan_index) ->
                                               PTree.get tcontent le = Some (Vint content) ->
                                               Mem.store Mint32 (m, d) bchpool_loc (Int.unsigned chan_index * 8 + 4) (Vint content) = Some (m', d) ->
                                               0 <= (Int.unsigned chan_index) < num_chan ->
                                               exec_stmt ge env le ((m, d): mem) set_chan_content_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_Chan_size; intro.
          intros.
          subst.
          unfold set_chan_content_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 8 * Int.unsigned chan_index + 4) with (Int.unsigned chan_index * 8 + 4) by omega.
          assumption.
        Qed.

      End SetChanContentBody.

      Theorem set_chan_content_code_correct:
        spec_le (set_chan_content ↦ set_chan_content_spec_low) (〚set_chan_content ↦ f_set_chan_content 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m.
        destruct m'.
        fbigstep (set_chan_content_body_correct (Genv.globalenv p) b0 H m m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_set_chan_content)
                                                          (Vint n::Vint v::nil)
                                                          (create_undef_temps (fn_temps f_set_chan_content)))) H0.
      Qed.

    End SETCHANCONTENT.


    Section INITCHAN.

      Let L: compatlayer (cdata RData) := CHPOOL_LOC ↦ chpool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section InitChanBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable bchpool_loc: block.
        Hypothesis hbchpool_loc: Genv.find_symbol ge CHPOOL_LOC = Some bchpool_loc.

        Lemma init_chan_body_correct: forall m m0 m' d env le chan_index info content,
                                        env = PTree.empty _ ->
                                        PTree.get tchan_index le = Some (Vint chan_index) ->
                                        PTree.get tinfo le = Some (Vint info) ->
                                        PTree.get tcontent le = Some (Vint content) ->
                                        Mem.store Mint32 (m, d) bchpool_loc (Int.unsigned chan_index * 8) (Vint info) = Some (m0, d) ->
                                        Mem.store Mint32 (m0, d) bchpool_loc (Int.unsigned chan_index * 8 + 4) (Vint content) = Some (m', d) ->
                                        0 <= (Int.unsigned chan_index) < num_chan ->
                                        exec_stmt ge env le ((m, d): mem) init_chan_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize t_struct_Chan_size; intro.
          intros.
          subst.
          unfold init_chan_body.
          repeat vcgen.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 8 * Int.unsigned chan_index + 0) with (Int.unsigned chan_index * 8) by omega.
          eassumption.
          rewrite H.
          unfold Mem.storev.
          rewrite Int.unsigned_repr; try omega.
          replace (0 + 8 * Int.unsigned chan_index + 4) with (Int.unsigned chan_index * 8 + 4) by omega.
          eassumption.
        Qed.
        
      End InitChanBody.

      Theorem init_chan_code_correct:
        spec_le (init_chan ↦ init_chan_spec_low) (〚init_chan ↦ f_init_chan 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m, m', m1, H1.
        fbigstep (init_chan_body_correct (Genv.globalenv p) b0 H m m1 m0 l (PTree.empty _) 
                                   (bind_parameter_temps' (fn_params f_init_chan)
                                                          (Vint n::Vint v1::Vint v2::nil)
                                                          (create_undef_temps (fn_temps f_init_chan)))) H0.
      Qed.

    End INITCHAN.
*)

  End WithPrimitives.

End PTHREADCODE.
