#!/bin/sh -e

CMD="$0"
FORCE=

if [ "$1" = "-f" ]; then
    FORCE=1
    shift
fi

if [ $# != 4 ]; then
    echo >&2 "Usage: $0 [-f] <subdir> <low name> <high name> <high prefix>"
    echo >&2 "Exmpl: $0 mm MPTNew MShareIntro ShareIntro"
    echo >&2
    echo >&2 "Will create the files: <subdir>/<high prefix>GenLink{,Source}.v"
    echo >&2 "Will overwrite if -f is given."
    exit 1
fi

SUBDIR="$1"
LOW="$2"
HIGH="$3"
HPRE="$4"
low=$(echo "$LOW" | tr '[A-Z]' '[a-z]')
high=$(echo "$HIGH" | tr '[A-Z]' '[a-z]')

SOURCEFILE="${SUBDIR}/${HPRE}GenLinkSource.v"
LINKFILE="${SUBDIR}/${HPRE}GenLink.v"

if [ -z "$FORCE" ] && { [ -e "$SOURCEFILE" ] || [ -e "$LINKFILE" ]; }; then
    echo >&2 "The files $SOURCEFILE and/or $LINKFILE already exist."
    echo >&2 "Use -f to overwrite them."
    exit 1
fi

cat >"$SOURCEFILE" <<EOF
Require Import LinkSourceTemplate.
Require Import ${LOW}.
Require Import ${LOW}CSource.

Definition ${HIGH}_module: link_module :=
  {|
    lm_cfun :=
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition ${HIGH}_impl \`{CompCertiKOS} \`{RealParams} :=
  link_impl ${HIGH}_module ${low}.
EOF

cat >"$LINKFILE" <<EOF
Require Import LinkTemplate.
Require Import ${HIGH}.
Require Import ${HPRE}Gen.
Require Import ${HPRE}GenLinkSource.
Require Import ${LOW}.
Require Import ${LOW}CSource.
Require Import ${LOW}Code.

Section WITHCOMPCERTIKOS.
  Context \`{compcertikos_prf: CompCertiKOS} \`{real_params_prf: RealParams}.

  Lemma init_correct:
    init_correct_type ${HIGH}_module ${low} ${high}.
  Proof.
    init_correct.
    (* <Your extra obligations here, if needed> *)
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type ${HIGH}_module ${low} ${high}.
  Proof.
    link_correct_aux.
    - (* <Your link_cfunction/link_asmfunction statements here> *)
    - apply passthrough_correct.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type ${HIGH}_module ${low} ${high}.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type ${HIGH}_module ${low} ${high}.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
