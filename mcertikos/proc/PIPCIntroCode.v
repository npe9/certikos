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
(*         for the C functions implemented in the PIPCIntro layer      *)
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
Require Import PIPCIntro.
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
Require Import IPCGenSpec. 
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CalRealProcModule.
Require Import CLemmas.
Require Import TacticsForTesting.
Require Import CalRealProcModule.
Require Import AbstractDataType.
Require Import PIPCIntroCSource.
Require Import ObjProc.


Module PIPCINTROCODE.

  Section WithPrimitives.    

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.


    Section SYNCSENDTOCHANPRE.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
                                        ⊕ get_state ↦ gensem get_state0_spec
                                        ⊕ set_sync_chan_paddr ↦ gensem set_sync_chan_paddr_spec
                                        ⊕ set_sync_chan_to ↦ gensem set_sync_chan_to_spec
                                        ⊕ set_sync_chan_count ↦ gensem set_sync_chan_count_spec
                                        ⊕ get_sync_chan_to ↦ gensem get_sync_chan_to_spec
                                        ⊕ get_kernel_pa ↦ gensem get_kernel_pa_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SyncSendToChanPreBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variable (ge: genv)
                 (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid **)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid.

        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** get_state **)

        Variable bget_state: block.

        Hypothesis hget_state1 : Genv.find_symbol ge get_state = Some bget_state.

        Hypothesis hget_state2 : Genv.find_funct_ptr ge bget_state
          = Some (External (EF_external get_state (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** set_sync_chan_paddr **)

        Variable bset_sync_chan_paddr: block.

        Hypothesis hset_sync_chan_paddr1 : Genv.find_symbol ge set_sync_chan_paddr = Some bset_sync_chan_paddr.

        Hypothesis hset_sync_chan_paddr2 : Genv.find_funct_ptr ge bset_sync_chan_paddr
          = Some (External (EF_external set_sync_chan_paddr (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) 
                                                                               (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** set_sync_chan_to **)

        Variable bset_sync_chan_to: block.

        Hypothesis hset_sync_chan_to1 : Genv.find_symbol ge set_sync_chan_to = Some bset_sync_chan_to.

        Hypothesis hset_sync_chan_to2 : Genv.find_funct_ptr ge bset_sync_chan_to
          = Some (External (EF_external set_sync_chan_to (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) 
                                                                            (Tcons tint (Tcons tint Tnil)) tvoid cc_default).
        
        (** set_sync_chan_count **)

        Variable bset_sync_chan_count: block.

        Hypothesis hset_sync_chan_count1 : Genv.find_symbol ge set_sync_chan_count = Some bset_sync_chan_count.

        Hypothesis hset_sync_chan_count2 : Genv.find_funct_ptr ge bset_sync_chan_count
          = Some (External (EF_external set_sync_chan_count (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) 
                                                                               (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** get_sync_chan_to **)

        Variable bget_sync_chan_to: block.

        Hypothesis hget_sync_chan_to1 : Genv.find_symbol ge get_sync_chan_to = Some bget_sync_chan_to.

        Hypothesis hget_sync_chan_to2 : Genv.find_funct_ptr ge bget_sync_chan_to
          = Some (External (EF_external get_sync_chan_to (signature_of_type (Tcons tint Tnil) tint cc_default))
                                                                            (Tcons tint Tnil) tint cc_default).

        (** get_kernel_pa **)

        Variable bget_kernel_pa: block.

        Hypothesis hget_kernel_pa1 : Genv.find_symbol ge get_kernel_pa = Some bget_kernel_pa.

        Hypothesis hget_kernel_pa2 : Genv.find_funct_ptr ge bget_kernel_pa
          = Some (External (EF_external get_kernel_pa (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default))
                                                                         (Tcons tint (Tcons tint Tnil)) tint cc_default).

        Lemma syncsendto_chan_pre_body_correct:
          forall m d d' env le toid vaddrval scountval retval,
            env = PTree.empty _
            -> PTree.get pid le = Some (Vint toid)
            -> PTree.get vaddr le = Some (Vint vaddrval)
            -> PTree.get scount le = Some (Vint scountval)
            -> high_level_invariant d
            -> syncsendto_chan_pre_spec (Int.unsigned toid) (Int.unsigned vaddrval) (Int.unsigned scountval) d
                 = Some (d', Int.unsigned retval)
            -> exists le',
                 exec_stmt ge env le ((m, d): mem) syncsendto_chan_pre_body E0 le' 
                                      (m, d') (Out_return (Some (Vint retval, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syncsendto_chan_pre_body.
          assert(valid_cid: 0 <= cid d < num_proc) by (destruct H3; auto).
          functional inversion H4; subst.

          esplit.

          repeat vcgen.
          unfold get_state0_spec. rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite H12.
          simpl.
          rewrite Int.unsigned_repr.
          reflexivity.
          rewrite muval. omega.
          omega.
          rewrite zeq_true.
          repeat vcgen. 
          omega.
          rewrite muval. omega. 
          repeat vcgen. 
          discharge_cmp.
          rewrite H6.
          rewrite Int.repr_unsigned.
          reflexivity.

          esplit.

          repeat vcgen.
          unfold get_state0_spec. rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite H12.
          simpl.
          rewrite Int.unsigned_repr.
          reflexivity.
          rewrite muval.
          destruct st; simpl; try omega.
          omega.
          rewrite zeq_false.
          repeat vcgen. 
          destruct st; simpl; try omega.
          destruct _x1. reflexivity.
          destruct st; simpl; try omega.
          rewrite muval.
          destruct st; simpl; try omega.
          repeat vcgen. 
          rewrite zlt_true.
          discharge_cmp.
          omega.
          repeat vcgen.
          discharge_cmp.

          destruct (zlt (Int.unsigned scountval) 1024).
          repeat vcgen.

          unfold get_curid_spec. rewrite H9, H10, H8.
          instantiate (1:=(Int.repr (cid d))).
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          rewrite Int.unsigned_repr.
          rewrite H15.
          instantiate (1:=(Int.repr skpa)).
          rewrite Int.unsigned_repr.
          reflexivity.
          rewrite muval.

          omega.

          omega.

          unfold set_sync_chan_paddr_spec. rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr.
          rewrite H14.
          reflexivity.
          omega.
          rewrite Int.unsigned_repr.
          omega.
          omega.

          unfold set_sync_chan_count_spec.
          simpl.
          rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr.
          rewrite ZMap.gss.
          reflexivity.
          omega.
          rewrite Int.unsigned_repr.
          omega.
          omega.
          unfold get_sync_chan_to_spec.
          simpl.
          rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr.
          rewrite ZMap.gss.
          rewrite Int.unsigned_repr.
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.

          omega.
          omega.
          rewrite Int.unsigned_repr.
          omega.
          omega.
        
          discharge_cmp. 
          omega.
          omega.

          repeat vcgen.
          
          unfold set_sync_chan_to_spec.
          simpl.
          rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite ZMap.gss.
          repeat vcgen.
          repeat (rewrite ZMap.set2).
          unfold asendval.
          assert (Int.unsigned scountval <= 1024).
          omega.
          rewrite <- Z.min_l_iff in H.
          rewrite H.
          repeat vcgen.
          omega.

          rewrite H6.
          repeat vcgen.

          rewrite H6.
          repeat vcgen.
          
          unfold get_curid_spec. rewrite H9, H10, H8.
          instantiate (1:=(cid d)).
          rewrite Int.unsigned_repr.
          reflexivity.
          omega.
          rewrite Int.unsigned_repr.
          rewrite H15.
          instantiate (1:=(Int.repr skpa)).
          rewrite Int.unsigned_repr.
          reflexivity.
          rewrite muval.

          omega.
          omega.

          unfold set_sync_chan_paddr_spec. rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr.
          rewrite H14.
          reflexivity.
          omega.
          rewrite Int.unsigned_repr.
          omega.
          omega.

          unfold set_sync_chan_count_spec.
          simpl.
          rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr.
          rewrite ZMap.gss.
          reflexivity.
          
          omega.
          omega.
          omega.
          omega.
          unfold get_sync_chan_to_spec.
          simpl.
          rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr.
          rewrite ZMap.gss.
          rewrite ZMap.set2.
          reflexivity.
          omega.
          omega.
          omega.
          omega.
          discharge_cmp.
          omega.
          omega.

          unfold asendval.
          assert (1024 <= Int.unsigned scountval).
          omega.
          rewrite <- Z.min_l_iff in H.
          rewrite Z.min_comm in H.
          rewrite H.
          rewrite H6.
          repeat vcgen.

          unfold set_sync_chan_to_spec.
          simpl.
          rewrite H9, H10, H8, H7.
          rewrite zle_lt_true.
          rewrite ZMap.gss.
          repeat vcgen.
          repeat (rewrite ZMap.set2).
          reflexivity.
          omega.

        Qed.

      End SyncSendToChanPreBody.

      Theorem syncsendto_chan_pre_code_correct:
        spec_le (syncsendto_chan_pre ↦ syncsendto_chan_pre_spec_low) (〚syncsendto_chan_pre ↦ f_syncsendto_chan_pre 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (syncsendto_chan_pre_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp m'0 labd labd' (PTree.empty _)
                                        (bind_parameter_temps' (fn_params f_syncsendto_chan_pre)
                                                               (Vint chid :: Vint vaddr :: Vint scount :: nil)
                                                               (create_undef_temps (fn_temps f_syncsendto_chan_pre)))) H0.
      Qed.

    End SYNCSENDTOCHANPRE.


    Section SYNCSENDTOCHANPOST.
     Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
       ⊕ get_sync_chan_to ↦ gensem get_sync_chan_to_spec
       ⊕ get_sync_chan_count ↦ gensem get_sync_chan_count_spec
       ⊕ set_sync_chan_to ↦ gensem set_sync_chan_to_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.
     

        Section SyncSendToChanPostBody.
          Context `{Hwb: WritableBlockOps}.
          Variable (sc: stencil).
          Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

          (** get_curid *)
          Variable bget_curid: block.
          Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
          Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).


           (** get_sync_chan_to *)
           Variable bget_sync_chan_to: block.
           Hypothesis hget_sync_chan_to1: Genv.find_symbol ge get_sync_chan_to = Some bget_sync_chan_to.
           Hypothesis hget_sync_chan_to2: Genv.find_funct_ptr ge bget_sync_chan_to = Some (External (EF_external get_sync_chan_to (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

           (** get_sync_chan_count *)
           Variable bget_sync_chan_count: block.
           Hypothesis hget_sync_chan_count1: Genv.find_symbol ge get_sync_chan_count = Some bget_sync_chan_count.
           Hypothesis hget_sync_chan_count2: Genv.find_funct_ptr ge bget_sync_chan_count = Some (External (EF_external get_sync_chan_count (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

            (** set_sync_chan_to *)
            Variable bset_sync_chan_to: block.
            Hypothesis hset_sync_chan_to1: Genv.find_symbol ge set_sync_chan_to = Some bset_sync_chan_to.
            Hypothesis hset_sync_chan_to2: Genv.find_funct_ptr ge bset_sync_chan_to = Some (External (EF_external set_sync_chan_to (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).


             Lemma syncsendto_chan_post_body_correct: forall m d d' env le val,
                                           env = PTree.empty _ ->
                                           high_level_invariant d ->
                                           syncsendto_chan_post_spec d  = Some (d', Int.unsigned val) ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) syncsendto_chan_post_body E0 le' (m, d') (Out_return (Some (Vint val, tint))).
             Proof.
              generalize max_unsigned_val; intro muval.
              intros.
              unfold syncsendto_chan_post_body.
              functional inversion H1; subst.

              esplit. repeat vcgen.
              unfold get_curid_spec.
              rewrite H6, H7, H5.
              instantiate (1:= Int.repr (cid d')).
              rewrite Int.unsigned_repr.
              reflexivity.

              rewrite muval. destruct H0. try omega.
              repeat vcgen. unfold get_sync_chan_to_spec.
              rewrite H6, H7, H5, H4.
              rewrite zle_lt_true; try omega.
              rewrite H8. reflexivity. apply valid_curid.
              apply H0.
              apply Int.unsigned_range_2. apply Int.unsigned_range_2.
              apply valid_curid. apply H0.
              rewrite muval. destruct H0. try omega.
              rewrite _x; rewrite zeq_true. repeat vcgen. rewrite _x; try omega.
              rewrite _x; rewrite muval; try omega.
                
              repeat vcgen.
              unfold get_sync_chan_count_spec; rewrite H4, H5, H6, H7.
              rewrite zle_lt_true.
              rewrite H8. rewrite H3. reflexivity.
              destruct H0; try omega. destruct H0; try omega. destruct H0; try omega.

              esplit. repeat vcgen.
              unfold get_curid_spec; rewrite H6, H7, H5.
              instantiate (1:= Int.repr (cid d)).
              rewrite Int.unsigned_repr. reflexivity.

              rewrite muval; destruct H0; try omega.
              unfold get_sync_chan_to_spec; rewrite H4, H5, H6, H7.
              rewrite zle_lt_true. rewrite Int.unsigned_repr.
              rewrite H8. rewrite Int.unsigned_repr. reflexivity.
              apply Int.unsigned_range_2.
              rewrite muval; destruct H0; try omega.
              rewrite Int.unsigned_repr; destruct H0; try omega.
              rewrite zeq_false. repeat vcgen. assumption.
              apply Int.unsigned_range_2. apply Int.unsigned_range_2.

              repeat vcgen. unfold set_sync_chan_to_spec; rewrite H4, H5, H6, H7.
              rewrite zle_lt_true; try omega.
              rewrite H8. repeat vcgen.
              destruct H0; omega. destruct H0; omega. destruct H0; rewrite muval; omega.

              discharge_cmp. rewrite H3. rewrite Int.repr_unsigned. reflexivity.
            Qed.
        End SyncSendToChanPostBody.

      Theorem syncsendto_chan_post_code_correct:
        spec_le (syncsendto_chan_post ↦ syncsendto_chan_post_spec_low) (〚syncsendto_chan_post ↦ f_syncsendto_chan_post 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (syncsendto_chan_post_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_syncsendto_chan_post)
                                                               nil
                                                               (create_undef_temps (fn_temps f_syncsendto_chan_post)))) H0. 
      Qed.
        
    End SYNCSENDTOCHANPOST.

    Section SYNCRECEIVECHAN.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
       ⊕ get_state ↦ gensem get_state0_spec
       ⊕ get_sync_chan_to ↦ gensem get_sync_chan_to_spec
       ⊕ get_sync_chan_count ↦ gensem get_sync_chan_count_spec
       ⊕ get_sync_chan_paddr ↦ gensem get_sync_chan_paddr_spec
       ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
       ⊕ get_kernel_pa ↦ gensem get_kernel_pa_spec
       ⊕ set_sync_chan_to ↦ gensem set_sync_chan_to_spec
       ⊕ set_sync_chan_count ↦ gensem set_sync_chan_count_spec
       ⊕ set_sync_chan_paddr ↦ gensem set_sync_chan_paddr_spec
       ⊕ thread_wakeup ↦ gensem thread_wakeup_spec.
       

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SyncReceiveChanBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** get_state *)

        Variable bget_state: block.
        Hypothesis hget_state1 : Genv.find_symbol ge get_state = Some bget_state.
        Hypothesis hget_state2 : Genv.find_funct_ptr ge bget_state = Some (External (EF_external get_state (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** get_sync_chan_to *)
        
        Variable bget_sync_chan_to: block.
        Hypothesis hget_sync_chan_to1: Genv.find_symbol ge get_sync_chan_to = Some bget_sync_chan_to.
        Hypothesis hget_sync_chan_to2: Genv.find_funct_ptr ge bget_sync_chan_to = Some (External (EF_external get_sync_chan_to (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** get_sync_chan_count *)
        
        Variable bget_sync_chan_count: block.
        Hypothesis hget_sync_chan_count1: Genv.find_symbol ge get_sync_chan_count = Some bget_sync_chan_count.
        Hypothesis hget_sync_chan_count2: Genv.find_funct_ptr ge bget_sync_chan_count = Some (External (EF_external get_sync_chan_count (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

         (** get_sync_chan_paddr *)
        
        Variable bget_sync_chan_paddr: block.
        Hypothesis hget_sync_chan_paddr1: Genv.find_symbol ge get_sync_chan_paddr = Some bget_sync_chan_paddr.
        Hypothesis hget_sync_chan_paddr2: Genv.find_funct_ptr ge bget_sync_chan_paddr = Some (External (EF_external get_sync_chan_paddr (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

         (** set_sync_chan_to *)
        
        Variable bset_sync_chan_to: block.
        Hypothesis hset_sync_chan_to1: Genv.find_symbol ge set_sync_chan_to = Some bset_sync_chan_to.
        Hypothesis hset_sync_chan_to2: Genv.find_funct_ptr ge bset_sync_chan_to = Some (External (EF_external set_sync_chan_to (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** set_sync_chan_count *)
        
        Variable bset_sync_chan_count: block.
        Hypothesis hset_sync_chan_count1: Genv.find_symbol ge set_sync_chan_count = Some bset_sync_chan_count.
        Hypothesis hset_sync_chan_count2: Genv.find_funct_ptr ge bset_sync_chan_count = Some (External (EF_external set_sync_chan_count (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** set_sync_chan_paddr *)
        
        Variable bset_sync_chan_paddr: block.
        Hypothesis hset_sync_chan_paddr1: Genv.find_symbol ge set_sync_chan_paddr = Some bset_sync_chan_paddr.
        Hypothesis hset_sync_chan_paddr2: Genv.find_funct_ptr ge bset_sync_chan_paddr = Some (External (EF_external set_sync_chan_paddr (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** flatmem_copy *)
        
        Variable bflatmem_copy: block.
        Hypothesis hflatmem_copy1: Genv.find_symbol ge flatmem_copy = Some bflatmem_copy.
        Hypothesis hflatmem_copy2: Genv.find_funct_ptr ge bflatmem_copy = Some (External (EF_external flatmem_copy (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) tvoid cc_default).

        (** get_kernal_pa *)
        Variable bget_kernel_pa: block.
        Hypothesis hget_kernel_pa1: Genv.find_symbol ge get_kernel_pa = Some bget_kernel_pa.
        Hypothesis hget_kernel_pa2: Genv.find_funct_ptr ge bget_kernel_pa = Some (External (EF_external get_kernel_pa (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).

        (** thread_wakeup *)

        Variable bthread_wakeup: block.
        Hypothesis hthread_wakeup1 : Genv.find_symbol ge thread_wakeup = Some bthread_wakeup. 
        Hypothesis hthread_wakeup2 : Genv.find_funct_ptr ge bthread_wakeup = Some (External (EF_external thread_wakeup (signature_of_type (Tcons tint Tnil) tvoid cc_default)) (Tcons tint Tnil) tvoid cc_default).



        Lemma syncreceive_chan_body_correct: forall m d d' env le fromid vaddrval rcountval val,
                                           env = PTree.empty _ ->
                                           PTree.get pid le = Some (Vint fromid) ->
                                           PTree.get vaddr le = Some (Vint vaddrval) ->
                                           PTree.get rcount le = Some (Vint rcountval) ->
                                           high_level_invariant d ->
                                           syncreceive_chan_spec (Int.unsigned fromid) (Int.unsigned vaddrval) (Int.unsigned rcountval) d  = Some (d', Int.unsigned val) ->
                                           0 <= Int.unsigned fromid < num_proc ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) syncreceive_chan_body E0 le' (m, d') (Out_return (Some (Vint val, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold syncreceive_chan_body.
          assert(valid_cid: 0 <= cid d < num_proc) by (destruct H3; auto).
          functional inversion H4; subst.

          esplit. 
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H9, H11, H10.
          instantiate (1:= (Int.repr (cid d'))).
          rewrite Int.unsigned_repr; try omega.
          reflexivity.

          unfold get_state0_spec. rewrite H10, H11, H9, H8.
          rewrite zle_lt_true. rewrite H13. simpl.
          instantiate (1:=3). rewrite Int.unsigned_repr; try omega.
          reflexivity.

          assumption.

          rewrite zeq_true. repeat vcgen.
          omega. rewrite muval; omega.

          repeat vcgen. 
          discharge_cmp.
          rewrite H7.
          rewrite Int.repr_unsigned.
          reflexivity.

          generalize (Z.min_spec (Int.unsigned scount) (Int.unsigned rcountval)).
          intro case.
          destruct case.

          esplit. 
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H9, H10, H11. instantiate (1:=(Int.repr (cid d))).
          rewrite Int.unsigned_repr; try omega. reflexivity.    
          repeat vcgen.
          unfold get_state0_spec. rewrite H10, H11, H9, H8.
          rewrite zle_lt_true. rewrite H13.
          reflexivity. assumption.
          unfold ThreadStatetoZ.
          destruct st; try omega.

          unfold ThreadStatetoZ; destruct st; try (rewrite muval); try omega.
          rewrite zeq_false. repeat vcgen. 
          unfold ThreadStatetoZ. destruct st; try omega.
          destruct _x1. reflexivity.
         
          unfold ThreadStatetoZ; destruct st; try omega.
          unfold ThreadStatetoZ; destruct st; try (rewrite muval); try omega.


          repeat vcgen.
          unfold get_sync_chan_to_spec. rewrite H9, H10, H8, H11. 
          rewrite zle_lt_true. rewrite H15.
          rewrite Int.unsigned_repr. 
          reflexivity. 
          rewrite _x2. rewrite muval. omega.
          
          assumption.

          repeat vcgen. rewrite _x2. omega.
          rewrite _x2; rewrite muval; try omega.
        
          repeat vcgen.
          unfold get_sync_chan_count_spec; rewrite H10, H11, H9, H8.
          rewrite zle_lt_true; try assumption.
          rewrite H15. reflexivity.

          unfold get_sync_chan_paddr_spec; rewrite H10, H11, H9, H8.
          rewrite zle_lt_true; try assumption. rewrite H15. reflexivity.
          vcgen. vcgen. vcgen. vcgen. vcgen. d3 vcgen. vcgen.
          vcgen.
          destruct H.
          rewrite H6 in H7.
          apply unsigned_inj in H7.
          rewrite H7.
          vcgen. repeat vcgen. repeat vcgen. repeat vcgen.
          repeat vcgen. repeat vcgen.

          unfold get_kernel_pa_spec. functional inversion H17.
          rewrite Int.unsigned_repr.
          rewrite H6. reflexivity. 
          rewrite H6. 
          
          functional inversion H18. omega.

          repeat vcgen.
          repeat vcgen. repeat vcgen. 
          rewrite Int.unsigned_repr; try omega.
          rewrite <- H7.
          rewrite H18. reflexivity.

          functional inversion H18; try omega.

          repeat vcgen. discharge_cmp. unfold sem_cast. simpl.
          instantiate (1:=Int.unsigned fromid); rewrite Int.repr_unsigned; try omega.
          reflexivity.

          unfold set_sync_chan_to_spec.
          functional inversion H18.
          simpl. rewrite H8, H9, H10, H11.
          rewrite zle_lt_true.
          rewrite H15. rewrite H6. vcgen.
          assumption. omega. rewrite muval; omega.

          repeat vcgen. repeat vcgen.
          unfold set_sync_chan_paddr_spec.
          simpl. functional inversion H18. simpl.
          rewrite H8, H9, H10, H11.
          rewrite zle_lt_true; try omega.
          simpl. 
          rewrite ZMap.gss. rewrite H6. repeat vcgen.
          repeat vcgen. repeat vcgen. repeat vcgen.

          unfold set_sync_chan_count_spec.
          functional inversion H18.
          simpl. rewrite H8, H9, H10, H11.
          rewrite zle_lt_true; try omega.
          rewrite ZMap.gss. rewrite H6. 

          destruct H. subst adt2. rewrite ZMap.set2. rewrite ZMap.set2.
          rewrite H31. rewrite Int.repr_unsigned. rewrite Int.repr_unsigned.
          rewrite <- H6. simpl. rewrite H6. rewrite H31 in H7.
          
          assert (Int.repr (Int.unsigned val)=Int.repr (Int.unsigned scount)).
          rewrite H7. reflexivity.
          rewrite Int.repr_unsigned in H32.
          rewrite Int.repr_unsigned in H32.
          rewrite H32.
          repeat vcgen.

          repeat vcgen. repeat vcgen.

          esplit. repeat vcgen.
          unfold get_curid_spec.
          rewrite H9, H10, H11. instantiate (1:=(Int.repr (cid d))).
          rewrite Int.unsigned_repr; try omega. reflexivity.    
          repeat vcgen.
          unfold get_state0_spec. rewrite H10, H11, H9, H8.
          rewrite zle_lt_true. rewrite H13.
          reflexivity. assumption.
          unfold ThreadStatetoZ.
          destruct st; try omega.

          unfold ThreadStatetoZ; destruct st; try (rewrite muval); try omega.
          rewrite zeq_false. repeat vcgen. 
          unfold ThreadStatetoZ. destruct st; try omega.
          destruct _x1. reflexivity.
         
          unfold ThreadStatetoZ; destruct st; try omega.
          unfold ThreadStatetoZ; destruct st; try (rewrite muval); try omega.


          repeat vcgen.
          unfold get_sync_chan_to_spec. rewrite H9, H10, H8, H11. 
          rewrite zle_lt_true. rewrite H15.
          rewrite Int.unsigned_repr. 
          reflexivity. 
          rewrite _x2. rewrite muval. omega.
          
          assumption.

          repeat vcgen. rewrite _x2. omega.
          rewrite _x2; rewrite muval; try omega.
        
          repeat vcgen.
          unfold get_sync_chan_count_spec; rewrite H10, H11, H9, H8.
          rewrite zle_lt_true; try assumption.
          rewrite H15. reflexivity.

          unfold get_sync_chan_paddr_spec; rewrite H10, H11, H9, H8.
          rewrite zle_lt_true; try assumption. rewrite H15. reflexivity.
          repeat vcgen. repeat vcgen.
          destruct H.
          rewrite H6 in H7.
          apply unsigned_inj in H7.
          rewrite H7. repeat vcgen.
          repeat vcgen. repeat vcgen. repeat vcgen.
          repeat vcgen. repeat vcgen.

          unfold get_kernel_pa_spec. functional inversion H17.
          rewrite Int.unsigned_repr.
          rewrite H6. reflexivity. 
          rewrite H6. 
          
          functional inversion H18. omega.

          repeat vcgen.
          repeat vcgen. repeat vcgen. 
          rewrite Int.unsigned_repr; try omega.
          rewrite <- H7.
          rewrite H18. reflexivity.

          functional inversion H18; try omega.

          repeat vcgen. discharge_cmp. unfold sem_cast. simpl.
          instantiate (1:=Int.unsigned fromid); rewrite Int.repr_unsigned; try omega.
          reflexivity.

          unfold set_sync_chan_to_spec.
          functional inversion H18.
          simpl. rewrite H8, H9, H10, H11.
          rewrite zle_lt_true.
          rewrite H15. rewrite H6. vcgen.
          assumption. omega. rewrite muval; omega.

          repeat vcgen. repeat vcgen.
          unfold set_sync_chan_paddr_spec.
          simpl. functional inversion H18. simpl.
          rewrite H8, H9, H10, H11.
          rewrite zle_lt_true; try omega.
          simpl. 
          rewrite ZMap.gss. rewrite H6. repeat vcgen.
          repeat vcgen. repeat vcgen. repeat vcgen.

          unfold set_sync_chan_count_spec.
          functional inversion H18.
          simpl. rewrite H8, H9, H10, H11.
          rewrite zle_lt_true; try omega.
          rewrite ZMap.gss. rewrite H6. 

          destruct H. subst adt2. rewrite ZMap.set2. rewrite ZMap.set2.
          rewrite H31. rewrite Int.repr_unsigned. rewrite Int.repr_unsigned.
          rewrite <- H6. simpl. rewrite H6. rewrite H31 in H7.
          apply unsigned_inj in H7. 
          rewrite H7.
          repeat vcgen.

          repeat vcgen. repeat vcgen.

          (* Final error case: 1027. *)
          esplit. repeat vcgen.

          unfold get_curid_spec.
          rewrite H9, H10, H11. instantiate (1:=(Int.repr (cid d'))).
          rewrite Int.unsigned_repr; try omega. reflexivity.    
          repeat vcgen.
          unfold get_state0_spec. rewrite H10, H11, H9, H8.
          rewrite zle_lt_true. rewrite H13.
          reflexivity. assumption.
          unfold ThreadStatetoZ.
          destruct st; try omega.

          unfold ThreadStatetoZ; destruct st; try (rewrite muval); try omega.
          rewrite zeq_false. repeat vcgen. 
          unfold ThreadStatetoZ. destruct st; try omega.
          destruct _x1. reflexivity.
         
          unfold ThreadStatetoZ; destruct st; try omega.
          unfold ThreadStatetoZ; destruct st; try (rewrite muval); try omega.


          repeat vcgen.
          unfold get_sync_chan_to_spec. rewrite H9, H10, H8, H11. 
          rewrite zle_lt_true. rewrite H15.
          rewrite Int.unsigned_repr. 
          reflexivity. rewrite muval. apply Int.unsigned_range_2.
          assumption.
          
          repeat vcgen.
          apply Int.unsigned_range_2. apply Int.unsigned_range_2.

           
          repeat vcgen. discharge_cmp. rewrite H7. rewrite Int.repr_unsigned. reflexivity.
         Qed.

      End SyncReceiveChanBody.

      Theorem syncreceive_chan_code_correct:

        spec_le (syncreceive_chan ↦ syncreceive_chan_spec_low) (〚syncreceive_chan ↦ f_syncreceive_chan 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (syncreceive_chan_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b7 Hb7fs Hb7fp b8 Hb8fs Hb8fp b9 Hb9fs Hb9fp b5 Hb5fs Hb5fp b6 Hb6fs Hb6fp b10 Hb10fs Hb10fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_syncreceive_chan)
                                                               (Vint fromid :: Vint vaddr :: Vint rcount :: nil)
                                                               (create_undef_temps (fn_temps f_syncreceive_chan)))) H1. 
      Qed.

    End SYNCRECEIVECHAN.


    Section PROCINIT.

      Let L: compatlayer (cdata RData) := sched_init ↦ gensem sched_init_spec
           ⊕ init_sync_chan ↦ gensem init_sync_chan_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ProcInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** init_sync_chan *)

        Variable binit_sync_chan: block.

        Hypothesis hinit_sync_chan1 : Genv.find_symbol ge init_sync_chan = Some binit_sync_chan. 
        
        Hypothesis hinit_sync_chan2 : Genv.find_funct_ptr ge binit_sync_chan = Some (External (EF_external init_sync_chan (signature_of_type (Tcons tint Tnil) tvoid cc_default)) (Tcons tint Tnil) tvoid cc_default).
        
        (** sched_init *)

        Variable bsched_init: block.

        Hypothesis hsched_init1 : Genv.find_symbol ge sched_init = Some bsched_init. 
        
        Hypothesis hsched_init2 : Genv.find_funct_ptr ge bsched_init = Some (External (EF_external sched_init (signature_of_type (Tcons tint Tnil) tvoid cc_default)) (Tcons tint Tnil) tvoid cc_default).

        Definition proc_init_mk_rdata (adt: RData) (index: Z) :=
            adt {syncchpool: (init_zmap (index + 1) (SyncChanValid (Int.repr num_chan) Int.zero Int.zero) (syncchpool adt))}.

        Section proc_init_loop_proof.

          Variable minit: memb.
          Variable adt: RData.

          Hypothesis pg: pg adt = true.
          Hypothesis ikern: ikern adt = true.
          Hypothesis ihost: ihost adt = true.
          Hypothesis ipt: ipt adt = true.

          Definition proc_init_loop_body_P (le: temp_env) (m: mem): Prop :=
            PTree.get ti le = Some (Vint (Int.repr 0)) /\ 
            m = (minit, adt).

          Definition proc_init_loop_body_Q (le : temp_env) (m: mem): Prop :=
            m = (minit, proc_init_mk_rdata adt (num_chan - 1)). 

          Lemma proc_init_loop_correct_aux : LoopProofSimpleWhile.t proc_init_while_condition proc_init_while_body ge (PTree.empty _) (proc_init_loop_body_P) (proc_init_loop_body_Q).
          Proof.
            generalize max_unsigned_val; intro muval.
            apply LoopProofSimpleWhile.make with
            (W := Z)
              (lt := fun z1 z2 => (0 <= z2 /\ z1 < z2)%Z)
              (I := fun le m w => exists i,
                                    PTree.get ti le = Some (Vint i) /\
                                    0 <= Int.unsigned i <= num_chan /\ 
                                    (Int.unsigned i = 0 /\ m = (minit, adt) \/ Int.unsigned i > 0 /\ m = (minit, proc_init_mk_rdata adt (Int.unsigned i - 1))) /\
                                    w = num_chan - Int.unsigned i 
              )
            .
            apply Zwf_well_founded.
            intros.
            unfold proc_init_loop_body_P in H.
            destruct H as [tile msubst].
            subst.
            esplit. esplit.
            repeat vcgen.
            intros.
            destruct H as [i tmpH].
            destruct tmpH as [tile tmpH].
            destruct tmpH as [irange tmpH].
            destruct tmpH as [icase nval].
            subst.
            unfold proc_init_while_body.
            destruct irange as [ilow ihigh].
            apply Zle_lt_or_eq in ihigh.
            destruct m.

            Caseeq ihigh.
            Case "Int.unsigned i < num_chan".
            intro ihigh.

            Caseeq icase.
            SCase "Int.unsigned i = 0".
            intro tmpH; destruct tmpH as [ival mval].
            rewrite ival in *.
            injection mval; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            exists (num_chan - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold proc_init_mk_rdata.
            rewrite ival.
            reflexivity.

            SCase "Int.unsigned i > 0".
            intro tmpH; destruct tmpH as [ival mval].
            injection mval; intros; subst.
            esplit. esplit.
            repeat vcgen.
            esplit. esplit.
            repeat vcgen.
            unfold proc_init_mk_rdata.
            unfold init_sync_chan_spec; simpl.
            rewrite ipt, pg, ikern, ihost.
            rewrite zle_lt_true.
            reflexivity.
            omega.
            exists (num_chan - Int.unsigned i - 1).
            repeat vcgen.
            esplit.
            repeat vcgen.
            right.
            split.
            omega.
            unfold proc_init_mk_rdata.
            replace (Int.unsigned i + 1 - 1) with (Int.unsigned i - 1 + 1) by omega.
            replace (Int.unsigned i - 1 + 1) with (Int.unsigned i) by omega.
            rewrite init_zmap_eq by omega.
            reflexivity.

            Case "Int.unsigned i = num_chan".
            intro ival.
            rewrite ival.
            esplit. esplit.
            repeat vcgen.
            unfold proc_init_loop_body_Q.
            Caseeq icase; intro tmpH; destruct tmpH as [iv mval].
            exfalso; rewrite iv in ival; omega.
            rewrite ival in mval; assumption.
          Qed.

        End proc_init_loop_proof.

        Lemma proc_init_loop_correct: forall m d d' le,
                                        PTree.get ti le = Some (Vint (Int.repr 0)) -> 
                                        pg d = true ->
                                        ihost d = true ->
                                        ipt d = true ->
                                        ikern d = true ->
                                        d' = proc_init_mk_rdata d (num_chan - 1) ->
                                        exists le',
                                          exec_stmt ge (PTree.empty _) le ((m, d): mem) (Swhile proc_init_while_condition proc_init_while_body) E0 le' (m, d') Out_normal.
        Proof.
          intros.
          generalize (proc_init_loop_correct_aux m d H0 H3 H1 H2).
          unfold proc_init_loop_body_P.
          unfold proc_init_loop_body_Q.
          intro LP.
          refine (_ (LoopProofSimpleWhile.termination _ _ _ _ _ _ LP le (m, d) _)).
          intro pre.
          destruct pre as [le'' tmppre].
          destruct tmppre as [m'' tmppre].
          destruct tmppre as [stmp m''val].
          exists le''.
          subst.
          assumption.
          auto.
        Qed.

        Lemma proc_init_body_correct: forall m d d' env le mbi_adr,
                                        env = PTree.empty _ ->
                                        PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                        proc_init_spec (Int.unsigned mbi_adr) d = Some d' ->
                                        exists le',
                                          exec_stmt ge env le ((m, d): mem) proc_init_body E0 le' (m, d') Out_normal.
        Proof.
          intros.
          subst.
          unfold proc_init_body.
          functional inversion H1.

          set (di:= d {vmxinfo: real_vmxinfo} {pg : true} {LAT : real_LAT (LAT d)} {nps : real_nps}
                      {AC : real_AC} {init : true} {PT : 0} {ptpool : CalRealPT.real_pt (ptpool d)}
                      {idpde : CalRealIDPDE.real_idpde (idpde d)} 
                      {smspool: CalRealSMSPool.real_smspool (smspool d)}
                      {abtcb: ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb (abtcb d))}
                      {abq: real_abq (abq d)} {cid : 0}).
          exploit (proc_init_loop_correct m di d' (PTree.set ti (Vint (Int.repr 0)) (set_opttemp None Vundef le))); 
            unfold di in *; simpl in *; try assumption; try reflexivity. 
          repeat vcgen.
          unfold proc_init_mk_rdata.
          rewrite <- H.
          symmetry.
          simpl.
          unfold real_syncchpool.
          reflexivity.
          intro tmpH.
          destruct tmpH as [le' stmt].
          rewrite <- H in stmt.

          esplit.
          repeat vcgen.
        Qed.

      End ProcInitBody.

      Theorem proc_init_code_correct:
        spec_le (proc_init ↦ proc_init_spec_low) (〚proc_init ↦ f_proc_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (proc_init_body_correct s (Genv.globalenv p) makeglobalenv b1 Hb1fs Hb1fp b0 Hb0fs Hb0fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_proc_init)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_proc_init)))) H0. 
      Qed.

    End PROCINIT.



(*
    Section ISCHANREADY.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ get_chan_info ↦ gensem get_chan_info_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section IsChanReadyBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** get_chan_info *)

        Variable bget_chan_info: block.

        Hypothesis hget_chan_info1 : Genv.find_symbol ge get_chan_info = Some bget_chan_info. 
        
        Hypothesis hget_chan_info2 : Genv.find_funct_ptr ge bget_chan_info = Some (External (EF_external get_chan_info (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        Lemma is_chan_ready_body_correct: forall m d env le ready,
                                            env = PTree.empty _ ->
                                            high_level_invariant d ->
                                            is_chan_ready_spec d = Some (Int.unsigned ready) ->
                                            exists le',
                                              exec_stmt ge env le ((m, d): mem) is_chan_ready_body E0 le' (m, d) (Out_return (Some (Vint ready, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          assert(valid_cid: 0 <= cid d < num_proc) by (destruct H0; auto).
          unfold is_chan_ready_body.
          functional inversion H1; subst.
          unfold Int.eq in H8.
          destruct (zeq (Int.unsigned ib) (Int.unsigned Int.zero)); try discriminate H8.
          rewrite <- Int.repr_unsigned with ready.
          rewrite <- H2.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H4, H5, H6.
          rewrite <- Int.unsigned_repr with (cid d); try omega.
          reflexivity.
          unfold get_chan_info_spec.
          rewrite H3, H4, H5, H6.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr; try omega.
          rewrite H7.
          repeat zdestruct.
          rewrite e.
          reflexivity.
          rewrite Int.unsigned_repr; try omega.
          discharge_cmp.
          repeat vcgen.

          unfold Int.eq in H8.
          destruct (zeq (Int.unsigned ib) (Int.unsigned Int.zero)); try discriminate H8.
          change (Int.unsigned Int.zero) with 0 in n.
          rewrite <- Int.repr_unsigned with ready.
          rewrite <- H2.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H4, H5, H6.
          rewrite <- Int.unsigned_repr with (cid d); try omega.
          reflexivity.
          unfold get_chan_info_spec.
          rewrite H3, H4, H5, H6.
          rewrite zle_lt_true.
          rewrite Int.unsigned_repr; try omega.
          rewrite H7.
          repeat zdestruct.
          discharge_cmp.
          rewrite Int.unsigned_repr; try omega.
          repeat vcgen.
          repeat vcgen.
        Qed.

      End IsChanReadyBody.

      Theorem is_chan_ready_code_correct:
        spec_le (is_chan_ready ↦ is_chan_ready_spec_low) (〚is_chan_ready ↦ f_is_chan_ready 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (is_chan_ready_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp m'0 labd (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_is_chan_ready)
                                                               nil
                                                               (create_undef_temps (fn_temps f_is_chan_ready)))) H0. 
      Qed.

    End ISCHANREADY. 


    Section SENDTOCHAN.

      Let L: compatlayer (cdata RData) := get_chan_info ↦ gensem get_chan_info_spec
           ⊕ set_chan_info ↦ gensem set_chan_info_spec
           ⊕ set_chan_content ↦ gensem set_chan_content_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SendToChanBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_chan_info *)

        Variable bget_chan_info: block.

        Hypothesis hget_chan_info1 : Genv.find_symbol ge get_chan_info = Some bget_chan_info. 
        
        Hypothesis hget_chan_info2 : Genv.find_funct_ptr ge bget_chan_info = Some (External (EF_external get_chan_info (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** set_chan_info *)

        Variable bset_chan_info: block.

        Hypothesis hset_chan_info1 : Genv.find_symbol ge set_chan_info = Some bset_chan_info. 
        
        Hypothesis hset_chan_info2 : Genv.find_funct_ptr ge bset_chan_info = Some (External (EF_external set_chan_info (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** set_chan_content *)

        Variable bset_chan_content: block.

        Hypothesis hset_chan_content1 : Genv.find_symbol ge set_chan_content = Some bset_chan_content. 
        
        Hypothesis hset_chan_content2 : Genv.find_funct_ptr ge bset_chan_content = Some (External (EF_external set_chan_content (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        Lemma sendto_chan_body_correct: forall m d d' env le chan_index content val,
                                          env = PTree.empty _ ->
                                          PTree.get tchan_index le = Some (Vint chan_index) ->
                                          PTree.get tcontent le = Some (Vint content) ->
                                          sendto_chan_spec (Int.unsigned chan_index) (Int.unsigned content) d = Some (d', Int.unsigned val) ->
                                          exists le',
                                            exec_stmt ge env le ((m, d): mem) sendto_chan_body E0 le' (m, d') (Out_return (Some (Vint val, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold sendto_chan_body.
          functional inversion H2; subst.

          unfold Int.eq in H11.
          destruct (zeq (Int.unsigned ib) (Int.unsigned Int.zero)); try discriminate H11.
          change (Int.unsigned Int.zero) with 0 in e.
          rewrite <- Int.repr_unsigned with val.
          rewrite <- H4.
          esplit.
          repeat vcgen.
          unfold get_chan_info_spec.
          rewrite H5, H6, H7, H8, H10.
          rewrite zle_lt_true.
          repeat zdestruct.
          discharge_cmp.
          omega.
          repeat vcgen.
          repeat vcgen.
          unfold set_chan_content_spec; simpl.
          rewrite ZMap.gss.
          rewrite ZMap.set2.
          rewrite Int.repr_unsigned.
          change (Int.repr 1) with Int.one.
          rewrite H5, H6, H7, H8.
          rewrite zle_lt_true.
          reflexivity.
          omega.

          unfold Int.eq in H11.
          destruct (zeq (Int.unsigned ib) (Int.unsigned Int.zero)); try discriminate H11.
          change (Int.unsigned Int.zero) with 0 in n.
          rewrite <- Int.repr_unsigned with val.
          rewrite <- H4.
          esplit.
          repeat vcgen.
          unfold get_chan_info_spec.
          rewrite H5, H6, H7, H8, H10.
          rewrite zle_lt_true.
          repeat zdestruct.
          discharge_cmp.
          omega.
          repeat vcgen.
          repeat vcgen.
   
          rewrite <- Int.repr_unsigned with val.
          rewrite <- H4.
          destruct _x.

          esplit.
          repeat vcgen.

          esplit.
          repeat vcgen.
        Qed.

      End SendToChanBody.

      Theorem sendto_chan_code_correct:
        spec_le (sendto_chan ↦ sendto_chan_spec_low) (〚sendto_chan ↦ f_sendto_chan 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (sendto_chan_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_sendto_chan)
                                                               (Vint n::Vint i::nil)
                                                               (create_undef_temps (fn_temps f_sendto_chan)))) H0. 
      Qed.

    End SENDTOCHAN.


    Section RECEIVECHAN.

      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ get_chan_info ↦ gensem get_chan_info_spec
           ⊕ get_chan_content ↦ gensem get_chan_content_spec
           ⊕ set_chan_info ↦ gensem set_chan_info_spec
           ⊕ set_chan_content ↦ gensem set_chan_content_spec
           ⊕ thread_wakeup ↦ gensem thread_wakeup_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ReceiveChanBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : Genv.find_funct_ptr ge bget_curid = Some (External (EF_external get_curid (signature_of_type Tnil tint cc_default)) Tnil tint cc_default).

        (** get_chan_info *)

        Variable bget_chan_info: block.

        Hypothesis hget_chan_info1 : Genv.find_symbol ge get_chan_info = Some bget_chan_info. 
        
        Hypothesis hget_chan_info2 : Genv.find_funct_ptr ge bget_chan_info = Some (External (EF_external get_chan_info (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** get_chan_content *)

        Variable bget_chan_content: block.

        Hypothesis hget_chan_content1 : Genv.find_symbol ge get_chan_content = Some bget_chan_content. 
        
        Hypothesis hget_chan_content2 : Genv.find_funct_ptr ge bget_chan_content = Some (External (EF_external get_chan_content (signature_of_type (Tcons tint Tnil) tint cc_default)) (Tcons tint Tnil) tint cc_default).

        (** set_chan_info *)

        Variable bset_chan_info: block.

        Hypothesis hset_chan_info1 : Genv.find_symbol ge set_chan_info = Some bset_chan_info. 
        
        Hypothesis hset_chan_info2 : Genv.find_funct_ptr ge bset_chan_info = Some (External (EF_external set_chan_info (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** set_chan_content *)

        Variable bset_chan_content: block.

        Hypothesis hset_chan_content1 : Genv.find_symbol ge set_chan_content = Some bset_chan_content. 
        
        Hypothesis hset_chan_content2 : Genv.find_funct_ptr ge bset_chan_content = Some (External (EF_external set_chan_content (signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default)) (Tcons tint (Tcons tint Tnil)) tvoid cc_default).

        (** thread_wakeup *)

        Variable bthread_wakeup: block.

        Hypothesis hthread_wakeup1 : Genv.find_symbol ge thread_wakeup = Some bthread_wakeup. 
        
        Hypothesis hthread_wakeup2 : Genv.find_funct_ptr ge bthread_wakeup = Some (External (EF_external thread_wakeup (signature_of_type (Tcons tint Tnil) tvoid cc_default)) (Tcons tint Tnil) tvoid cc_default).


        Lemma receive_chan_body_correct: forall m d d' env le val,
                                           env = PTree.empty _ ->
                                           high_level_invariant d ->
                                           receive_chan_spec d = Some (d', Int.unsigned val) ->
                                           exists le',
                                             exec_stmt ge env le ((m, d): mem) receive_chan_body E0 le' (m, d') (Out_return (Some (Vint val, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          unfold receive_chan_body.
          assert(valid_cid: 0 <= cid d < num_proc) by (destruct H0; auto).
          functional inversion H1; subst.

          unfold Int.eq in H9.
          destruct (zeq (Int.unsigned ib) (Int.unsigned Int.one)); try discriminate H9.
          change (Int.unsigned Int.one) with 1 in e.
          rewrite <- Int.repr_unsigned with val.
          rewrite <- H3.
          unfold i in *.
          functional inversion H10; subst.
          simpl in *.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H5, H6, H7.
          (* in previous proof it is with (cid d) *)
          rewrite <- Int.unsigned_repr with (cid adt').
          reflexivity.
          omega.
          unfold get_chan_info_spec.
          rewrite Int.unsigned_repr; try omega.
          rewrite H4, H5, H6, H7, H8.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.
          repeat vcgen.
          repeat vcgen.
          unfold get_chan_content_spec.
          rewrite H4, H5, H6, H7, H8.
          rewrite zle_lt_true.          
          repeat zdestruct.
          omega.
          unfold set_chan_content_spec; simpl.
          rewrite H4, H5, H6, H7.
          rewrite ZMap.gss.
          rewrite zle_lt_true.
          rewrite ZMap.set2.
          repeat zdestruct.
          omega.

          simpl in *.
          unfold i in *.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H5, H6, H7.
          rewrite <- Int.unsigned_repr with (cid d).
          reflexivity.
          omega.
          unfold get_chan_info_spec.
          rewrite Int.unsigned_repr; try omega.
          rewrite H4, H5, H6, H7, H8.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.
          discharge_cmp.
          repeat vcgen.
          unfold get_chan_content_spec.
          rewrite H4, H5, H6, H7, H8.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.
          unfold set_chan_info_spec; simpl.
          rewrite H4, H5, H6, H7, H8.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.
          unfold set_chan_content_spec; simpl.
          rewrite ZMap.gss.
          rewrite ZMap.set2.
          change (Int.repr 0) with Int.zero.
          rewrite H4, H5, H6, H7.
          rewrite zle_lt_true.
          repeat zdestruct.
          omega.

          unfold Int.eq in H9.
          destruct (zeq (Int.unsigned ib) (Int.unsigned Int.one)); try discriminate H9.
          change (Int.unsigned Int.one) with 1 in n.
          rewrite <- Int.repr_unsigned with val.
          rewrite <- H3.
          unfold i in *.
          esplit.
          repeat vcgen.
          unfold get_curid_spec.
          rewrite H5, H6, H7.
          rewrite <- Int.unsigned_repr with (cid d').
          reflexivity.
          omega.
          unfold get_chan_info_spec.
          rewrite Int.unsigned_repr; try omega.
          rewrite H4, H5, H6, H7, H8.
          rewrite zle_lt_true.
          repeat zdestruct.
          discharge_cmp.
          omega.
          repeat vcgen.
          repeat vcgen.
        Qed.

      End ReceiveChanBody.

      Theorem receive_chan_code_correct:
        spec_le (receive_chan ↦ receive_chan_spec_low) (〚receive_chan ↦ f_receive_chan 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (receive_chan_body_correct s (Genv.globalenv p) makeglobalenv b0 Hb0fs Hb0fp b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp b4 Hb4fs Hb4fp b5 Hb5fs Hb5fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_receive_chan)
                                                               nil
                                                               (create_undef_temps (fn_temps f_receive_chan)))) H0. 
      Qed.

    End RECEIVECHAN.
*)



  End WithPrimitives.

End PIPCINTROCODE.
