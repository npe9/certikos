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
(*         for the C functions implemented in the PUCtxtIntro layer    *)
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
Require Import PUCtxtIntro.
Require Import ZArith.Zwf.
Require Import RealParams.
Require Import VCGen.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import ProcGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import CLemmas.
Require Import TacticsForTesting.
Require Import PUCtxtIntroCSource.
Require Import AbstractDataType.


Module PUCTXTINTROCODE.

  Section WithPrimitives.

    Lemma Heq:
      forall d k ab aq u u0 u1 u2 u3 u4 u5,
        Some (d {kctxt: k} {abtcb: ab} {abq: aq}
                {uctxt: u5} {uctxt: u4}{uctxt: u3}
                {uctxt: u2} {uctxt: u1} {uctxt: u0} {uctxt: u}) =
        Some (d {kctxt: k} {abtcb: ab} {abq : aq} {uctxt: u}).
    Proof.
      symmetry.
      reflexivity.
    Qed.

    Context `{real_params: RealParams}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.
    
    Section PROCCREATE.
 
      Let L: compatlayer (cdata RData) := get_curid ↦ gensem get_curid_spec
           ⊕ thread_spawn ↦ dnew_compatsem thread_spawn_spec
           ⊕ uctx_set ↦ gensem uctx_set_spec
           ⊕ uctx_set_eip ↦ uctx_set_eip_compatsem uctx_set_eip_spec
           ⊕ elf_load ↦ elf_load_compatsem.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ProcCreateBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).

        (** parameter *)
        Variable (quota : int).

        (** * Hypotheses on the primitives called *)

        (** get_curid *)

        Variable bget_curid: block.

        Hypothesis hget_curid1 : Genv.find_symbol ge get_curid = Some bget_curid. 
        
        Hypothesis hget_curid2 : 
          Genv.find_funct_ptr ge bget_curid = 
          Some (External (EF_external get_curid
                (signature_of_type Tnil tint cc_default)) 
                                   Tnil tint cc_default).

        (** thread_spawn *)

        Variable bthread_spawn: block.

        Hypothesis hthread_spawn1 : Genv.find_symbol ge thread_spawn = Some bthread_spawn. 
        
        Hypothesis hthread_spawn2 : 
          Genv.find_funct_ptr ge bthread_spawn = 
          Some (External (EF_external thread_spawn 
                (signature_of_type (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil))) tint cc_default)) 
                                   (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil))) tint cc_default).

        (** uctx_set *)

        Variable buctx_set: block.

        Hypothesis huctx_set1 : Genv.find_symbol ge uctx_set = Some buctx_set. 
        
        Hypothesis huctx_set2 : Genv.find_funct_ptr ge buctx_set = Some (External (EF_external uctx_set (signature_of_type (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default)) (Tcons tint (Tcons tint (Tcons tint Tnil))) Tvoid cc_default).
        
        (** uctx_set_eip *)

        Variable buctx_set_eip: block.

        Hypothesis huctx_set_eip1 : Genv.find_symbol ge uctx_set_eip = Some buctx_set_eip. 
        
        Hypothesis huctx_set_eip2 : Genv.find_funct_ptr ge buctx_set_eip = Some (External (EF_external uctx_set_eip (signature_of_type (Tcons tint (Tcons (tptr tvoid) Tnil)) Tvoid cc_default)) (Tcons tint (Tcons (tptr tvoid) Tnil)) Tvoid cc_default).

        (** elf_load *)

        Variable belf_load: block.

        Hypothesis helf_load1 : Genv.find_symbol ge elf_load = Some belf_load. 
        
        Hypothesis helf_load2 : Genv.find_funct_ptr ge belf_load = Some (External (EF_external elf_load (signature_of_type (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid cc_default)) (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid cc_default).


        Lemma proc_create_body_correct: 
          forall m d d' env le proc_index b b' buc ofs be ofs' ofse,
            env = PTree.empty _ ->
            le ! telf_addr = Some (Vptr be ofse) -> le ! tfun_addr = Some (Vptr buc ofs') ->
            le ! tquota = Some (Vint quota) ->
            proc_create_spec d b b' buc ofs' (Int.unsigned quota) = 
              Some (d', Int.unsigned proc_index) ->
            high_level_invariant d ->
            Genv.find_symbol ge STACK_LOC = Some b ->
            Int.unsigned ofs = (Int.unsigned proc_index + 1) * PgSize - 4 ->
            Genv.find_symbol ge proc_start_user = Some b' ->
            (exists fun_id, Genv.find_symbol ge fun_id = Some buc) -> 
            (exists elf_id, Genv.find_symbol ge elf_id = Some be) ->
            exists le',
              exec_stmt ge env le ((m, d): mem) proc_create_body E0 le' (m, d') 
                        (Out_return (Some (Vint proc_index, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          intros; subst.
          unfold proc_create_body.
          rename H3 into Hspec.
          unfold proc_create_spec in Hspec.
          case_eq (ikern d); intro ikern; rewrite ikern in Hspec; try discriminate Hspec.
          case_eq (ihost d); intro ihost; rewrite ihost in Hspec; try discriminate Hspec.
          case_eq (pg d); intro pe; rewrite pe in Hspec; try discriminate Hspec.
          case_eq (ipt d); intro ipt; rewrite ipt in Hspec; try discriminate Hspec.
          destruct (zle_lt 0 (cid d * max_children + 1 + 
                              Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d)))))
                           num_id) eqn:Hchild; try discriminate Hspec.
          destruct (zlt (Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d))))) max_children)
                   eqn:Hnc; try discriminate Hspec.
          destruct (zle_le 0 (Int.unsigned quota)
                           (cquota (ZMap.get (cid d) (AC d)) -
                            cusage (ZMap.get (cid d) (AC d)))) eqn:Hquota; try discriminate Hspec.
          case_eq (ZMap.get num_id (abq d)); [intro zget | intros ? zget]; rewrite zget in Hspec; try discriminate Hspec.
          injection Hspec; intros; subst.
          destruct H4, H8, H9.
          destruct correct_curid as [Hused _]; auto; try omega.

          unfold update_cusage, update_cchildren in *.
          esplit.
          d9 vcgen; vcgen; vcgen.
          unfold get_curid_spec.
          rewrite ikern, ihost, pe.
          rewrite Int.unsigned_repr; eauto; omega.
          vcgen; try discriminate.
          vcgen; discriminate.
          vcgen.
          unfold thread_spawn_spec.
          rewrite Int.unsigned_repr; try omega.
          rewrite pe, ikern, ihost, ipt, Hused, Hchild, Hnc, Hquota, zget.
          unfold update_cusage, update_cchildren.
          instantiate (1:= proc_index); instantiate (2:= b).
          rewrite <- H; reflexivity.
          erewrite <- stencil_matches_symbols; eauto.
          erewrite <- stencil_matches_symbols; eauto.
          vcgen.
          vcgen.
          vcgen.
          ptreesolve.
          reflexivity.
          vcgen; ptreesolve.
          vcgen.
          vcgen.
          vcgen; eauto.
          erewrite <- stencil_matches_symbols; eauto.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          vcgen.
          repeat vcgen.
          vcgen.
          vcgen.
          repeat vcgen.
          unfold uctx_set_spec; simpl.
          rewrite zle_lt_true.
          rewrite ikern, ihost, ipt, pe.
          repeat zdestruct.
          repeat vcgen.
          repeat vcgen.
          unfold uctx_set_spec; simpl.
          rewrite ikern, ihost, pe, ipt, zle_lt_true.
          repeat zdestruct.
          omega.
          repeat vcgen.
          unfold uctx_set_spec; simpl.
          rewrite ikern, ihost, pe, ipt, zle_lt_true.
          repeat zdestruct.
          omega.
          unfold uctx_set_spec; simpl.
          rewrite ikern, ihost, pe, ipt, zle_lt_true.
          repeat zdestruct.
          omega.
          unfold uctx_set_spec; simpl.
          rewrite ikern, ihost, pe, ipt, zle_lt_true.
          repeat zdestruct.
          omega.
          unfold uctx_set_spec; simpl.
          rewrite ikern, ihost, pe, ipt, zle_lt_true.
          repeat zdestruct.
          omega.
          unfold uctx_set_eip_spec; simpl.
          rewrite ikern, ihost, pe, ipt, zle_lt_true.
          repeat zdestruct.
          repeat rewrite ZMap.set2.
          repeat rewrite ZMap.gss.
          rewrite Hused; rewrite <- H; eapply Heq.
          omega.
          erewrite <- stencil_matches_symbols; eauto.
        Qed.

      End ProcCreateBody.

      Theorem proc_create_code_correct:
        spec_le (proc_create ↦ proc_create_spec_low) (〚proc_create ↦ f_proc_create 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct H2, H3.
        rename H into Hspec, labd into d; assert (Hspec':= Hspec); unfold proc_create_spec in Hspec.
        case_eq (ikern d); intro ikern; rewrite ikern in Hspec; try discriminate Hspec.
        case_eq (ihost d); intro ihost; rewrite ihost in Hspec; try discriminate Hspec.
        case_eq (pg d); intro pe; rewrite pe in Hspec; try discriminate Hspec.
        case_eq (ipt d); intro ipt; rewrite ipt in Hspec; try discriminate Hspec.
        destruct (zle_lt 0 (cid d * max_children + 1 + 
                            Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d)))))
                         num_id) eqn:Hchild; try discriminate Hspec.
        destruct (zlt (Z.of_nat (length (cchildren (ZMap.get (cid d) (AC d))))) max_children)
                 eqn:Hnc; try discriminate Hspec.
        destruct (zle_le 0 (Int.unsigned q)
                         (cquota (ZMap.get (cid d) (AC d)) -
                          cusage (ZMap.get (cid d) (AC d)))) eqn:Hquota; try discriminate Hspec.
        case_eq (ZMap.get num_id (abq d)); [intro zget | intros ? zget]; rewrite zget in Hspec; try discriminate Hspec.
        injection Hspec; intros.
        fbigsteptest (proc_create_body_correct s (Genv.globalenv p) makeglobalenv q b0 Hb0fs Hb0fp 
                                               b1 Hb1fs Hb1fp b2 Hb2fs Hb2fp b3 Hb3fs Hb3fp 
                                               b4 Hb4fs Hb4fp m'0 d labd' (PTree.empty _) 
                                        (bind_parameter_temps' (fn_params f_proc_create)
                                                               (Vptr be ofse::Vptr buc ofs_uc::Vint q::nil)
                                                               (create_undef_temps (fn_temps f_proc_create)))) H4. 
        reflexivity.
        omega.
        omega.
        esplit; erewrite stencil_matches_symbols; eassumption.
        esplit; erewrite stencil_matches_symbols; eassumption.
        intro stmt.
        destruct stmt.
        repeat fbigstep_post.
      Qed.

    End PROCCREATE.

  End WithPrimitives.

End PUCTXTINTROCODE.
