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
(*       for the C functions implemented in the MShareIntro layer      *)
(*                                                                     *)
(*                                                                     *)
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
(*Require Import MShare.*)
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
Require Import PTNewGenSpec.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import XOmega.
Require Import MPTNewCSource.
Require Import ShareIntroGenSpec.
Require Import AbstractDataType.

Module MSHAREINTROCODE.


    Lemma structsize: sizeof t_smsp_struct = 12.
    Proof.
      generalize max_unsigned_val; intro muval.
      simpl.
      unfold align; simpl.
      trivial.
    Qed.

    Lemma zle_max: 0 <= Int.max_unsigned.
    Proof.
      generalize max_unsigned_val; intro muval.
      omega.
    Qed.

    Lemma size_of_struct_array: sizeof (Tarray t_smsp_struct 64 noattr) = 768.
    Proof.
      reflexivity.
    Qed.

    Lemma size_of_t_smsp_struct: sizeof t_smsp_struct = 12.
    Proof.
      reflexivity.
    Qed.

  Section WithPrimitives.

    Context `{real_params_ops: RealParamsOps}.
    Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
    Context `{Hmwd: UseMemWithData memb}.

    Let mem := mwd (cdata RData).

    Context `{Hstencil: Stencil}.
    Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
    Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

    (*************************************************************************)

    Section CLEARSHAREDMEM.

      Let L: compatlayer (cdata RData) := SHRDMEMPOOL_LOC ↦ smspool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section ClearSharedMemBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable (bsmspool_loc: block).

        Hypothesis hsmspool_loc : Genv.find_symbol ge SHRDMEMPOOL_LOC = Some bsmspool_loc.

        (*******************)

        Lemma clear_shared_mem_body__correct: forall m m' m'' m''' d env le pid1 pid2,
                                      env = PTree.empty _ ->
                                      Mem.store Mint32 ((m, d): mem) bsmspool_loc
                                                (Int.unsigned
                                                   (Int.repr
                                                      (768 * Int.unsigned pid1 +
                                                       12 * Int.unsigned pid2 + 0)))
                                                (Vint Int.zero)
                                      = Some (m', d) ->
                                      Mem.store Mint32 ((m', d): mem) bsmspool_loc
                                                (Int.unsigned
                                                   (Int.repr
                                                      (768 * Int.unsigned pid1 +
                                                       12 * Int.unsigned pid2 + 4)))
                                                (Vint (Int.repr (SHARED_MEM_DEAD)))
                                      = Some (m'', d) ->
                                      Mem.store Mint32 ((m'', d): mem) bsmspool_loc
                                                (Int.unsigned
                                                   (Int.repr
                                                      (768 * Int.unsigned pid1 +
                                                       12 * Int.unsigned pid2 + 8)))
                                                (Vint Int.one)
                                      = Some (m''', d) ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      0 <= Int.unsigned pid1 < num_proc ->
                                      0 <= Int.unsigned pid2 < num_proc ->
                                      kernel_mode d ->
                                      exec_stmt ge env le ((m, d): mem) clear_shared_mem_body
                                                E0 le (m''', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro strsz.
          generalize zle_max; intro zle_mint.
          generalize size_of_struct_array; intro sizeof_sa.
          generalize size_of_t_smsp_struct; intro sizeof_s.
          intros; subst.
          unfold clear_shared_mem_body.
          vcgen.
          vcgen.
          econstructor.
          {
            econstructor; [ | repeat vcgen | repeat vcgen |].
            econstructor; [ | repeat vcgen | repeat vcgen ].
            econstructor.
            repeat vcgen.
            apply deref_loc_copy. reflexivity.
            repeat vcgen.
          }
          vcgen.
          vcgen.
          {
            econstructor; [ | repeat vcgen | repeat vcgen |].
            econstructor; [ | repeat vcgen | repeat vcgen ].
            econstructor.
            repeat vcgen.
            apply deref_loc_copy. reflexivity.
            repeat vcgen.
          }
          vcgen.
          vcgen.
          {
            econstructor.
            repeat vcgen.
            apply deref_loc_copy. reflexivity.
          }
          repeat vcgen.
          reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
        Qed.

      End ClearSharedMemBody.

      Theorem clear_shared_mem_code_correct:
        spec_le (clear_shared_mem ↦ clear_shared_mem_spec_low)
                (〚clear_shared_mem ↦ f_clear_shared_mem 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        generalize structsize; intro strsz.
        generalize zle_max; intro zle_mint.
        generalize size_of_struct_array; intro sizeof_sa.
        generalize size_of_t_smsp_struct; intro sizeof_s.
        Opaque Z.mul.
        Opaque sizeof.
        fbigstep_pre L'.
        destruct m as (m & c).
        destruct m1 as (m1 & c1).
        destruct m2 as (m2 & c3).
        destruct m' as (m' & c').
        unfold fst in *.
        destruct H1, H2.
        fbigsteptest (clear_shared_mem_body__correct (Genv.globalenv p)
                                                   b0 H
                                                   m m1 m2 m' c
                                                   (PTree.empty _) 
                                                   (bind_parameter_temps' (fn_params f_clear_shared_mem)
                                                          (Vint pid1 :: Vint pid2 :: nil)
                                                          (create_undef_temps (fn_temps f_clear_shared_mem))))
                 H0.
        rewrite Int.unsigned_repr in H0.
        rewrite H0. trivial.
        omega.
        rewrite Int.unsigned_repr in H1.
        rewrite H1. trivial.
        omega.
        rewrite Int.unsigned_repr in H2.
        rewrite H2. trivial.
        omega.
        repeat fbigstep_post.
      Qed.

    End CLEARSHAREDMEM.


    (*********************)


    Section SETSHAREDMEMLOC.

      Let L: compatlayer (cdata RData) := SHRDMEMPOOL_LOC ↦ smspool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetSharedMemLocBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable (bsmspool_loc: block).

        Hypothesis hsmspool_loc : Genv.find_symbol ge SHRDMEMPOOL_LOC = Some bsmspool_loc.      

        (*******************)

        Lemma set_shared_mem_loc_body__correct: forall m m' d env le pid1 pid2 loc,
                                      env = PTree.empty _ ->
                                      Mem.store Mint32 ((m, d): mem) bsmspool_loc
                                                      (768 * Int.unsigned pid1 +
                                                       sizeof t_smsp_struct *
                                                       Int.unsigned pid2 + 0)
                                                (Vint loc)
                                      = Some (m', d) ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      PTree.get _loc le = Some (Vint loc) ->
                                      0 <= Int.unsigned pid1 < num_proc ->
                                      0 <= Int.unsigned pid2 < num_proc ->
                                      kernel_mode d ->
                                      exec_stmt ge env le ((m, d): mem) set_shared_mem_loc_body
                                                E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro strsz.
          generalize zle_max; intro zle_mint.
          generalize size_of_struct_array; intro sizeof_sa.
          generalize size_of_t_smsp_struct; intro sizeof_s.
          intros; subst.
          unfold set_shared_mem_loc_body.
          econstructor; [ | repeat vcgen | repeat vcgen |].
          econstructor; [ | repeat vcgen | repeat vcgen ].
          econstructor.
          repeat vcgen.
          apply deref_loc_copy. reflexivity.
          repeat vcgen.
          rewrite sizeof_sa, sizeof_s.
          rewrite sizeof_s in H0.
          Opaque Z.mul.
          simpl.
          repeat vcgen.
        Qed.

      End SetSharedMemLocBody.

      Theorem set_shared_mem_loc_code_correct:
        spec_le (set_shared_mem_loc ↦ set_shared_mem_loc_spec_low)
                (〚set_shared_mem_loc ↦ f_set_shared_mem_loc 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        generalize structsize; intro strsz.
        generalize zle_max; intro zle_mint.
        generalize size_of_struct_array; intro sizeof_sa.
        generalize size_of_t_smsp_struct; intro sizeof_s.
        fbigstep_pre L'.
        destruct m as (m & c).
        destruct m' as (m' & c').
        fbigstep (set_shared_mem_loc_body__correct (Genv.globalenv p)
                                                   b0 H
                                                   m m' c
                                                   (PTree.empty _) 
                                                   (bind_parameter_temps' (fn_params f_set_shared_mem_loc)
                                                          (Vint pid1 :: Vint pid2 :: Vint loc :: nil)
                                                          (create_undef_temps (fn_temps f_set_shared_mem_loc))))
                 H0.
      Qed.

    End SETSHAREDMEMLOC.


    (*********************)


    Section GETSHAREDMEMLOC.

      Let L: compatlayer (cdata RData) := SHRDMEMPOOL_LOC ↦ smspool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.


      Section GetSharedMemLocBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).


        Variable (bsmspool_loc: block).

        Hypothesis hsmspool_loc : Genv.find_symbol ge SHRDMEMPOOL_LOC = Some bsmspool_loc.      

        (*******************)

        Lemma get_shared_mem_loc__correct: forall m d env le pid1 pid2 n,
                                      env = PTree.empty _ ->
                                      Mem.load Mint32 ((m, d): mem) bsmspool_loc
                                                (768 * Int.unsigned pid1 +
                                                 sizeof t_smsp_struct * Int.unsigned pid2 + 0)
                                      = Some (Vint n) ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      0 <= Int.unsigned pid1 < num_proc ->
                                      0 <= Int.unsigned pid2 < num_proc ->
                                        exec_stmt ge env le ((m, d): mem) get_shared_mem_loc_body
                                                  E0 le (m, d) (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          generalize zle_max; intro zle_mint.
          generalize size_of_struct_array; intro sizeof_sa.
          generalize size_of_t_smsp_struct; intro sizeof_s.
          intros. subst.
          constructor.
          econstructor; [ | repeat vcgen].
          econstructor; [| repeat vcgen |].
          econstructor.  repeat vcgen.
          apply deref_loc_copy. reflexivity.
          repeat vcgen.
          unfold Mem.loadv.
          repeat vcgen.
        Qed.

      End GetSharedMemLocBody.

      Theorem get_shared_mem_loc_code_correct:
        spec_le (get_shared_mem_loc ↦ get_shared_mem_loc_spec_low)
                (〚get_shared_mem_loc ↦ f_get_shared_mem_loc 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        generalize structsize; intro strsz.
        generalize zle_max; intro zle_mint.
        generalize size_of_struct_array; intro sizeof_sa.
        generalize size_of_t_smsp_struct; intro sizeof_s.
        fbigstep_pre L'.
        destruct m' as (m & c).
        unfold fst in *.
        assert (PTree.empty (block × type) = PTree.empty (block × type)); trivial.
        fbigstep (get_shared_mem_loc__correct (Genv.globalenv p)
                                                   b0 H
                                                   m c
                                                   (PTree.empty _)
                                                   (bind_parameter_temps' (fn_params f_get_shared_mem_loc)
                                                          (Vint pid1 :: Vint pid2 :: nil)
                                                          (create_undef_temps (fn_temps f_get_shared_mem_loc)))
                     pid1 pid2 n H4 H0)
                 H0.
      Qed.

    End GETSHAREDMEMLOC.


    (*************************************************************************)


    Section SETSHAREDMEMSEEN.

      Let L: compatlayer (cdata RData) := SHRDMEMPOOL_LOC ↦ smspool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetSharedMemSeenBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variables (ge: genv).

        Variable (bsmspool_loc: block).

        Hypothesis hsmspool_loc : Genv.find_symbol ge SHRDMEMPOOL_LOC = Some bsmspool_loc.      

        (*******************)

        Lemma set_shared_mem_seen_body__correct: forall m m' d env le pid1 pid2 loc,
                                      env = PTree.empty _ ->
                                      Mem.store Mint32 ((m, d): mem) bsmspool_loc
                                                      (768 * Int.unsigned pid1 +
                                                       12 * Int.unsigned pid2 + 8)
                                                (Vint loc)
                                      = Some (m', d) ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      PTree.get _seen le = Some (Vint loc) ->
                                      0 <= Int.unsigned pid1 < num_proc ->
                                      0 <= Int.unsigned pid2 < num_proc ->
                                      kernel_mode d ->
                                      exec_stmt ge env le ((m, d): mem) set_shared_mem_seen_body
                                                E0 le ((m', d): mem) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro strsz.
          generalize zle_max; intro zle_mint.
          generalize size_of_struct_array; intro sizeof_sa.
          generalize size_of_t_smsp_struct; intro sizeof_s.
          intros; subst.
          econstructor; [ | repeat vcgen | repeat vcgen |].
          econstructor; [ | repeat vcgen | repeat vcgen ].
          econstructor.
          repeat vcgen.
          apply deref_loc_copy. reflexivity.
          repeat vcgen.
          rewrite sizeof_sa, sizeof_s.
          Opaque Z.mul.
          simpl.
          Transparent Z.mul.
          repeat vcgen.
        Qed.

      End SetSharedMemSeenBody.

      Theorem set_shared_mem_seen_code_correct:
        spec_le (set_shared_mem_seen ↦ set_shared_mem_seen_spec_low)
                (〚set_shared_mem_seen ↦ f_set_shared_mem_seen 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m as (m & c).
        destruct m' as (m' & c').
        fbigstep (set_shared_mem_seen_body__correct (Genv.globalenv p)
                                                   b0 H
                                                   m m' c
                                                   (PTree.empty _) 
                                                   (bind_parameter_temps' (fn_params f_set_shared_mem_seen)
                                                          (Vint pid1 :: Vint pid2 :: Vint loc :: nil)
                                                          (create_undef_temps (fn_temps f_set_shared_mem_seen)))
                                                   pid1 pid2 loc)
                 H0.
      Qed.

    End SETSHAREDMEMSEEN.


    (*********************)


    Section GETSHAREDMEMSEEN.

      Let L: compatlayer (cdata RData) := SHRDMEMPOOL_LOC ↦ smspool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.


      Section GetSharedMemSeenBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv).


        Variable (bsmspool_loc: block).

        Hypothesis hsmspool_loc : Genv.find_symbol ge SHRDMEMPOOL_LOC = Some bsmspool_loc.      

        (*******************)

        Lemma get_shared_mem_seen__correct: forall m d env le pid1 pid2 n,
                                      env = PTree.empty _ ->
                                      Mem.load Mint32 ((m, d): mem) bsmspool_loc
                                               (768 * Int.unsigned pid1 +
                                                sizeof t_smsp_struct * Int.unsigned pid2 + 8)
                                      = Some (Vint n) ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      0 <= Int.unsigned pid1 < num_proc ->
                                      0 <= Int.unsigned pid2 < num_proc ->
                                      kernel_mode d ->
                                        exec_stmt ge env le ((m, d): mem) get_shared_mem_seen_body
                                                  E0 le (m, d) (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          generalize zle_max; intro zle_mint.
          generalize size_of_struct_array; intro sizeof_sa.
          generalize size_of_t_smsp_struct; intro sizeof_s.
          intros. subst.
          constructor.
          econstructor; [ | repeat vcgen].
          econstructor; [| repeat vcgen |].
          econstructor.  repeat vcgen.
          apply deref_loc_copy. reflexivity.
          repeat vcgen.
          unfold Mem.loadv.
          repeat vcgen.
        Qed.

      End GetSharedMemSeenBody.

      Theorem get_shared_mem_seen_code_correct:
        spec_le (get_shared_mem_seen ↦ get_shared_mem_seen_spec_low)
                (〚get_shared_mem_seen ↦ f_get_shared_mem_seen 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        generalize structsize; intro strsz.
        (*generalize zle_max; intro zle_mint.
        generalize size_of_struct_array; intro sizeof_sa.
        generalize size_of_t_smsp_struct; intro sizeof_s.*)
        Opaque Z.mul.
        Opaque sizeof.
        fbigstep_pre L'.
        destruct m' as (m & c).
        unfold fst in *.
        fbigstep (get_shared_mem_seen__correct (Genv.globalenv p)
                                               b0 H
                                               m c
                                               (PTree.empty _)
                                               (bind_parameter_temps' (fn_params f_get_shared_mem_seen)
                                                                      (Vint pid1 :: Vint pid2 :: nil)
                                                                      (create_undef_temps (fn_temps f_get_shared_mem_seen))))
                 H3.
      Qed.

    End GETSHAREDMEMSEEN.


    (*************************************************************************)


    Section SETSHAREDMEMSTATE.

      Let L: compatlayer (cdata RData) := SHRDMEMPOOL_LOC ↦ smspool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

      Section SetSharedMemStateBody.

        Context `{Hwb: WritableBlockAllowGlobals}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).


        Variable (bsmspool_loc: block).

        Hypothesis hsmspool_loc : Genv.find_symbol ge SHRDMEMPOOL_LOC = Some bsmspool_loc.      

        (*******************)

        Lemma set_shared_mem_state_body__correct: forall m m' d env le pid1 pid2 state,
                                      env = PTree.empty _ ->
                                      Mem.store Mint32 ((m, d): mem) bsmspool_loc
                                                (768 * Int.unsigned pid1 +
                                                 sizeof t_smsp_struct * Int.unsigned pid2 + 4)
                                                (Vint state) = Some (m', d) ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      PTree.get _state le = Some (Vint state) ->
                                      0 <= Int.unsigned pid1 < num_proc ->
                                      0 <= Int.unsigned pid2 < num_proc ->
                                      kernel_mode d ->
                                      exec_stmt ge env le ((m, d): mem) set_shared_mem_state_body E0 le (m', d) Out_normal.
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro strsz.
          generalize zle_max; intro zle_mint.
          generalize size_of_struct_array; intro sizeof_sa.
          generalize size_of_t_smsp_struct; intro sizeof_s.
          intros; subst.
          econstructor; [ | repeat vcgen | repeat vcgen |].
          econstructor; [ | repeat vcgen | repeat vcgen ].
          econstructor.
          repeat vcgen.
          apply deref_loc_copy. reflexivity.
          repeat vcgen.
          rewrite sizeof_sa, sizeof_s.
          rewrite sizeof_s in H0.
          Opaque Z.mul.
          simpl.
          repeat vcgen.
          Transparent Z.mul.
(*alt afte destruct
          econstructor.
          econstructor.
          econstructor.
          constructor.
          econstructor.
          econstructor.
          constructor.
          econstructor.
          econstructor.
          apply eval_Evar_global; auto.
          rewrite hsmspool_loc. reflexivity.
          repeat vcgen.
          econstructor. rewrite H1. reflexivity.
          repeat vcgen. apply deref_loc_reference. reflexivity.
          econstructor. rewrite H2. reflexivity.
          repeat vcgen. apply deref_loc_copy. reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.*)
        Qed.

      End SetSharedMemStateBody.

      Theorem set_shared_mem_state_code_correct:
        spec_le (set_shared_mem_state ↦ set_shared_mem_state_spec_low)
                (〚set_shared_mem_state ↦ f_set_shared_mem_state 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        fbigstep_pre L'.
        destruct m as (m & c).
        destruct m' as (m' & c').
        fbigstep (set_shared_mem_state_body__correct (Genv.globalenv p)
                                                   b0 H
                                                   m m' c
                                                   (PTree.empty _) 
                                                   (bind_parameter_temps' (fn_params f_set_shared_mem_state)
                                                          (Vint pid1 :: Vint pid2 :: Vint loc :: nil)
                                                          (create_undef_temps (fn_temps f_set_shared_mem_state)))
                                                   pid1 pid2 loc)
                 H0.
      Qed.

    End SETSHAREDMEMSTATE.


    (*********************)


    Section GETSHAREDMEMSTATE.

      Let L: compatlayer (cdata RData) := SHRDMEMPOOL_LOC ↦ smspool_loc_type.

      Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.

      Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.


      Section GetSharedMemStateBody.

        Context `{Hwb: WritableBlockOps}.

        Variable (sc: stencil).

        Variables (ge: genv)
                  (STENCIL_MATCHES: stencil_matches sc ge).


        Variable (bsmspool_loc: block).

        Hypothesis hsmspool_loc : Genv.find_symbol ge SHRDMEMPOOL_LOC = Some bsmspool_loc.      

        (*******************)

        Lemma get_shared_mem_state__correct: forall m d env le pid1 pid2 n,
                                      env = PTree.empty _ ->
                                      Mem.load Mint32 m bsmspool_loc
                                               (768 * Int.unsigned pid1 +
                                                sizeof t_smsp_struct * Int.unsigned pid2 + 4)
                                      = Some (Vint n) ->
                                      PTree.get _source le = Some (Vint pid1) ->
                                      PTree.get _dest le = Some (Vint pid2) ->
                                      0 <= Int.unsigned pid1 < num_proc ->
                                      0 <= Int.unsigned pid2 < num_proc ->
                                      kernel_mode d ->
                                      high_level_invariant d ->
                                        exec_stmt ge env le ((m, d): mem) get_shared_mem_state_body E0 le (m, d) (Out_return (Some (Vint n, tint))).
        Proof.
          generalize max_unsigned_val; intro muval.
          generalize structsize; intro stsize.
          generalize zle_max; intro zle_mint.
          generalize size_of_struct_array; intro sizeof_sa.
          generalize size_of_t_smsp_struct; intro sizeof_s.
          intros. subst.
          constructor.
          econstructor; [ | repeat vcgen].
          econstructor; [| repeat vcgen |].
          econstructor.  repeat vcgen.
          apply deref_loc_copy. reflexivity.
          repeat vcgen.
          unfold Mem.loadv.
          repeat vcgen.
          (*esplit.
          constructor.
          econstructor.
          econstructor.
          constructor.
          econstructor.
          econstructor.
          apply eval_Evar_global; auto.
          rewrite hsmspool_loc. reflexivity.
          repeat vcgen.
          econstructor. rewrite H1. reflexivity.
          repeat vcgen. apply deref_loc_reference. reflexivity.
          econstructor. rewrite H2. reflexivity.
          repeat vcgen. apply deref_loc_copy. reflexivity.
          repeat vcgen.
          repeat vcgen.
          repeat vcgen.
          unfold Mem.loadv.
          rewrite Int.unsigned_repr.
          eassumption.
          repeat vcgen.*)
        Qed.

      End GetSharedMemStateBody.

      Theorem get_shared_mem_state_code_correct:
        spec_le (get_shared_mem_state ↦ get_shared_mem_state_spec_low)
                (〚get_shared_mem_state ↦ f_get_shared_mem_state 〛L).
      Proof.
        set (L' := L) in *. unfold L in *.
        generalize structsize; intro strsz.
        Opaque Z.mul.
        Opaque sizeof.
        fbigstep_pre L'.
        destruct m' as (m & c).
        unfold fst in *.
        fbigstep (get_shared_mem_state__correct (Genv.globalenv p)
                                                b0 H
                                                m c
                                                (PTree.empty _)
                                                (bind_parameter_temps' (fn_params f_get_shared_mem_state)
                                                                       (Vint pid1 :: Vint pid2 :: nil)
                                                                       (create_undef_temps (fn_temps f_get_shared_mem_state))))
                 H3.
      Qed.

    End GETSHAREDMEMSTATE.

  End WithPrimitives.

End MSHAREINTROCODE.
