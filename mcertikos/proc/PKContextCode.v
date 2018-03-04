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
(*         for the C functions implemented in the PKContext layer      *)
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
Require Import PKContext.
Require Import ZArith.Zwf.
Require Import LoopProof.
Require Import VCGen.
Require Import RealParams.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import KContextNewGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import PKContextCSource.

Require Import AbstractDataType.


Module PKCONTEXTCODE.

  Section WithPrimitives.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.
    

    
    Section KCTXTNEW.

      Let L: compatlayer (cdata RData) := pt_new ↦ gensem pt_new_spec
           ⊕ set_RA ↦ kctxt_ra_compatsem
           ⊕ set_SP ↦ kctxt_sp_compatsem.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Lemma stack_array_size: sizeof (Tarray tvoid PgSize noattr) = PgSize.
      Proof. reflexivity. Qed.

      Lemma unsigned_repr_zero: Int.unsigned (Int.repr 0) = 0.
      Proof. rewrite Int.unsigned_repr; generalize max_unsigned_val; omega. Qed.

      Section KCTxtNewBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (* parameters *)
        Variables (id q: int).

        (** * Hypotheses on the primitives called *)

        (** pt_new *)

        Variable bpt_new: block.

        Hypothesis hpt_new1 : Genv.find_symbol ge pt_new = Some bpt_new. 
        
        Hypothesis hpt_new2 : Genv.find_funct_ptr ge bpt_new = Some (External (EF_external pt_new 
          (signature_of_type (Tcons tint (Tcons tint Tnil)) tint cc_default)) (Tcons tint (Tcons tint Tnil)) tint cc_default).
        
        (** set_RA *)

        Variable bset_RA: block.

        Hypothesis hset_RA1 : Genv.find_symbol ge set_RA = Some bset_RA. 
        
        Hypothesis hset_RA2 : Genv.find_funct_ptr ge bset_RA = Some (External (EF_external set_RA (signature_of_type (Tcons tint (Tcons (tptr tvoid) Tnil)) Tvoid cc_default)) (Tcons tint (Tcons (tptr tvoid) Tnil)) Tvoid cc_default).

        
        (** set_SP *)

        Variable bset_SP: block.

        Hypothesis hset_SP1 : Genv.find_symbol ge set_SP = Some bset_SP. 
        
        Hypothesis hset_SP2 : Genv.find_funct_ptr ge bset_SP = Some (External (EF_external set_SP (signature_of_type (Tcons tint (Tcons (tptr tvoid) Tnil)) Tvoid cc_default)) (Tcons tint (Tcons (tptr tvoid) Tnil)) Tvoid cc_default).

        Lemma kctxt_new_body_correct: 
          forall m d d' env le bstack_loc b n ofs',
            env = PTree.empty _ -> le ! tentry = Some (Vptr b ofs') ->
            le ! tid = Some (Vint id) -> le ! tquota = Some (Vint q) ->
            Genv.find_symbol ge STACK_LOC = Some bstack_loc ->
            (exists id, Genv.find_symbol ge id = Some b) ->
            kctxt_new_spec d bstack_loc b ofs' (Int.unsigned id) (Int.unsigned q) = Some (d', Int.unsigned n) ->
            exists le',
              exec_stmt ge env le ((m, d): mem) kctxt_new_body E0 le' (m, d') (Out_return (Some (Vint n, tint))).
        Proof.
          generalize stack_array_size.
          generalize max_unsigned_val.
          generalize unsigned_repr_zero.
          generalize tvoid_size.
          generalize (tptrsize tvoid); intro tptrsize.
          intros.
          subst.
          unfold kctxt_new_body.
          functional inversion H9.
          + (* i = num_id *) 
            subst. destruct H8. 
            rewrite <- Int.unsigned_repr in H10 at 1.
            apply unsigned_inj in H10.
            rewrite <- H10 in *.
            esplit.
            repeat vcgen.
            omega.
          + (* i <> num_id *) 
            functional inversion H11; subst.
            unfold ofs in *.
            destruct H8.
            esplit.
            d13 vcgen; try rewrite stack_array_size; try rewrite tptr_size; try d8 vcgen.
            Opaque Z.mul.
            simpl.
            replace (4096 * Int.unsigned n + 4 * 1023) with ((Int.unsigned n + 1) * 4096 - 4) by omega.
            reflexivity.
            erewrite <- stencil_matches_symbols; eauto.
            erewrite <- stencil_matches_symbols; eauto.
       Qed.

      End KCTxtNewBody.

      Theorem kctxt_new_code_correct:
        spec_le (kctxt_new ↦ kctxt_new_spec_low) (〚kctxt_new ↦ f_kctxt_new 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        assert(exists id : ident, Genv.find_symbol (Genv.globalenv p) id = Some b').
        {
          destruct H1.
          esplit.
          erewrite stencil_matches_symbols; eauto.
        }
        fbigstep (kctxt_new_body_correct s (Genv.globalenv p) makeglobalenv id q b1 Hb1fs Hb1fp 
                                         b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp m'0 labd labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_kctxt_new)
                                                               (Vptr b' ofs'::Vint id:: Vint q::nil)
                                                               (create_undef_temps (fn_temps f_kctxt_new)))) H2. 
      Qed.

    End KCTXTNEW.

  End WithPrimitives.

End PKCONTEXTCODE.
