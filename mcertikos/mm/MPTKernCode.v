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
(*          for the C functions implemented in the MPTKern layer       *)
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
Require Import MPTKern.
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
Require Import PTInitGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CalRealPT.
Require Import AbstractDataType.
Require Import MPTKernCSource.


Module MPTKERNCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.


    Section PTINIT.

      Let L: compatlayer (cdata RData) := set_pg ↦ gensem setPG1_spec
                                                 ⊕ set_pt ↦ gensem setPT'_spec
                                                 ⊕ pt_init_kern ↦ gensem pt_init_kern_spec.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Local Open Scope Z_scope.

      Section PTInitBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** * Hypotheses on the primitives called *)

        (** set_pt *)

        Variable bsetpt: block.

        Hypothesis hset_pt1 : Genv.find_symbol ge set_pt = Some bsetpt. 
        
        Hypothesis hset_pt2 : Genv.find_funct_ptr ge bsetpt = Some (External (EF_external set_pt (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        (** set_pg *)

        Variable bsetpg: block.

        Hypothesis hset_pg1 : Genv.find_symbol ge set_pg = Some bsetpg. 
        
        Hypothesis hset_pg2 : Genv.find_funct_ptr ge bsetpg = Some (External (EF_external set_pg (signature_of_type Tnil Tvoid cc_default)) Tnil Tvoid cc_default).
        
        (** pt_init_kern *)

        Variable bptinitkern: block.

        Hypothesis hpt_init_kern1 : Genv.find_symbol ge pt_init_kern = Some bptinitkern. 
        
        Hypothesis hpt_init_kern2 : Genv.find_funct_ptr ge bptinitkern = Some (External (EF_external pt_init_kern (signature_of_type (Tcons tint Tnil) Tvoid cc_default)) (Tcons tint Tnil) Tvoid cc_default).

        Lemma pt_init_body_correct: forall m d d' env le mbi_adr,
                                      env = PTree.empty _ ->
                                      PTree.get tmbi_adr le = Some (Vint mbi_adr) ->
                                      pt_init_spec (Int.unsigned mbi_adr) d = Some d' ->
                                      exists le',
                                        exec_stmt ge env le ((m, d): mem) pt_init_body E0 le' (m, d') Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          intros.
          subst.
          unfold pt_init_body.
          functional inversion H1.
          subst.
          simpl in *.
          assert(tmp: 0 <= 0 < num_proc) by omega.
          generalize (real_pt_PMap_valid (ptpool d) 0 tmp); intro ptcomm.
          generalize (real_pt_PMap_kern (ptpool d)); intro ptkern.

          esplit.
          repeat vcgen.
          unfold setPT'_spec.
          simpl.
          rewrite H2, H3, H4.
          destruct (PMap_valid_dec (ZMap.get 0 (real_pt (ptpool d)))); try contradiction.
          destruct (PMap_kern_dec (ZMap.get 0 (real_pt (ptpool d)))); try contradiction.
          reflexivity.
          unfold setPG1_spec; simpl.
          rewrite H2, H3, H4, H5.
          destruct (PMap_valid_dec (ZMap.get 0 (real_pt (ptpool d)))); try contradiction.
          destruct (PMap_kern_dec (ZMap.get 0 (real_pt (ptpool d)))); try contradiction.
          reflexivity.
        Qed.

      End PTInitBody.


      Theorem pt_init_code_correct:
        spec_le (pt_init ↦ pt_init_spec_low) (〚pt_init ↦ f_pt_init 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        fbigstep (pt_init_body_correct s (Genv.globalenv p) makeglobalenv b1 Hb1fs Hb1fp b0 Hb0fs Hb0fp b2 Hb2fs Hb2fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_pt_init)
                                                               (Vint mbi_adr::nil)
                                                               (create_undef_temps (fn_temps f_pt_init)))) H0.
      Qed.

    End PTINIT.

  End WithPrimitives.

End MPTKERNCODE.
