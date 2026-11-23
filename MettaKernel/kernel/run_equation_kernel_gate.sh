#!/usr/bin/env bash
# Gate for the tier-0 equation kernel (equation_kernel_v0.metta).
#
# Suites, each run on every selected engine. Every suite loads the seal
# emulation (equation_kernel_registry_v0.metta) and the kernel first.
#   controls   equation_kernel_controls_v0.metta             Lean-generated worked examples,
#                                                            sealed scripts, theory scoping
#   space      equation_kernel_space_controls_v0.metta       the check controls, certificates as
#                                                            space atoms; recording into a space
#   leaks      equation_kernel_leaks_v0.metta                what the emulated seal still leaks,
#                                                            and what the kernel already closes
#   primitives equation_kernel_primitives_controls_v0.metta  emulations of proposed primitives
#   compressed equation_kernel_compressed_controls_v0.metta  Lean-generated computed matching
#   review     equation_kernel_review_controls_v0.metta      the review's probes as refusals
#   verbatim   equation_kernel_review_verbatim_v0.metta      the review's mixing probe in its
#                                                            original call shapes
#   mutants    equation_kernel_mutants_v0.metta              Lean-generated mutation corpus
#
# Every control prints (ek:pass ctl-name) or (ek:FAIL ctl-name value). A suite
# passes on an engine when every control passes; the gate passes when every
# suite passes on every engine and the normalized outputs are identical across
# engines. One exception: PeTTa refuses the verbatim suite when it loads,
# because it checks the arity of calls to kernel functions; the gate requires
# that refusal. The digest is the sha256 of the normalized outputs.
#
# A suite with more than CHUNK controls (default 50) runs in chunks of CHUNK
# controls, each chunk with the suite's definitions; HE loads one large file
# much more slowly than several small ones. Chunked control files hold one
# atom per line, as the generated files do.
# JOBS controls the number of independent chunk processes per engine. Their
# output is always joined in source order before any comparison.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
PETTA="${PETTA:-$AIHUB/hyperon/PeTTa/run.sh}"
HE="${HE:-$AIHUB/hyperon/hyperon-experimental/target/release/metta-repl}"
ENGINES="${ENGINES:-cetta petta he}"
SUITES="${SUITES:-controls space leaks primitives compressed review verbatim mutants}"
CHUNK="${CHUNK:-50}"
JOBS="${JOBS:-1}"
[[ "$JOBS" =~ ^[1-9][0-9]*$ ]] || { echo "JOBS must be positive" >&2; exit 2; }
LOGDIR="$ROOT/parity_logs/equation_kernel_v0"
mkdir -p "$LOGDIR"
WORK="$(mktemp -d "$LOGDIR/work.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

suite_sources() {
  local base="equation_kernel_registry_v0.metta equation_kernel_v0.metta"
  case "$1" in
    controls) echo "$base equation_kernel_controls_v0.metta" ;;
    space) echo "$base equation_kernel_space_v0.metta equation_kernel_space_controls_v0.metta" ;;
    leaks) echo "$base equation_kernel_space_v0.metta equation_kernel_leaks_v0.metta" ;;
    primitives) echo "$base equation_kernel_primitives_v0.metta equation_kernel_primitives_controls_v0.metta" ;;
    compressed) echo "$base equation_kernel_primitives_v0.metta equation_kernel_compressed_controls_v0.metta" ;;
    review) echo "$base equation_kernel_space_v0.metta equation_kernel_review_controls_v0.metta" ;;
    verbatim) echo "$base equation_kernel_space_v0.metta equation_kernel_review_verbatim_v0.metta" ;;
    mutants) echo "$base equation_kernel_mutants_v0.metta" ;;
    *) echo "unknown suite $1" >&2; exit 2 ;;
  esac
}

control_file() {
  case "$1" in
    controls) echo "equation_kernel_controls_v0.metta" ;;
    space) echo "equation_kernel_space_controls_v0.metta" ;;
    leaks) echo "equation_kernel_leaks_v0.metta" ;;
    primitives) echo "equation_kernel_primitives_controls_v0.metta" ;;
    compressed) echo "equation_kernel_compressed_controls_v0.metta" ;;
    review) echo "equation_kernel_review_controls_v0.metta" ;;
    verbatim) echo "equation_kernel_review_verbatim_v0.metta" ;;
    mutants) echo "equation_kernel_mutants_v0.metta" ;;
  esac
}

run_engine() {
  local engine=$1 program=$2
  case "$engine" in
    # This lane compares HE's inert-call behavior; never inherit a changing CLI default.
    cetta) "$CETTA" --lang he "$program" ;;
    petta) bash "$PETTA" "$program" --silent ;;
    he) "$HE" "$program" ;;
    *) echo "unknown engine $engine" >&2; exit 2 ;;
  esac
}

normalize() {
  sed -e 's/^\[//' -e 's/\]$//' | grep -E '^\(ek:(pass|FAIL) ' || true
}

# Split a suite into chunk programs: the definitions of every source and the
# control file's own definitions, then CHUNK consecutive control lines with
# the atoms and comments that precede each of them.
make_chunks() {
  local suite=$1 sources definitions controls source
  sources=$(suite_sources "$suite")
  controls="$ROOT/$(control_file "$suite")"
  if [[ "$(grep -c '^!(ek:control ' "$controls")" -le "$CHUNK" ]]; then
    : > "$WORK/$suite.part.0000.metta"
    for source in $sources; do
      cat "$ROOT/$source" >> "$WORK/$suite.part.0000.metta"
    done
    return
  fi
  definitions="$WORK/$suite.definitions.metta"
  : > "$definitions"
  for source in $sources; do
    if [[ "$ROOT/$source" != "$controls" ]]; then
      cat "$ROOT/$source" >> "$definitions"
    fi
  done
  awk -v chunk="$CHUNK" -v prefix="$WORK/$suite.part." -v definitions="$definitions" '
    BEGIN { part = 0; count = 0; started = 0 }
    /^\(= / { print > (prefix "header"); next }
    {
      if (!started) { file = sprintf("%s%04d.body", prefix, part); started = 1 }
      print > file
      if ($0 ~ /^!\(ek:control /) {
        count++
        if (count % chunk == 0) { close(file); part++; started = 0 }
      }
    }' "$controls"
  for body in "$WORK/$suite".part.*.body; do
    cat "$definitions" "$WORK/$suite.part.header" "$body" > "${body%.body}.metta"
  done
}

status=0
for suite in $SUITES; do
  make_chunks "$suite"
  expected=$(grep -c '^!(ek:control ' "$ROOT/$(control_file "$suite")")
  reference=""
  for engine in $ENGINES; do
    log="$LOGDIR/$suite.$engine.log"
    : > "$log"
    failed_process=0
    programs=("$WORK/$suite".part.*.metta)
    for ((start=0; start<${#programs[@]}; start+=JOBS)); do
      pids=()
      for ((i=start; i<start+JOBS && i<${#programs[@]}; i++)); do
        run_engine "$engine" "${programs[i]}" > "$WORK/chunk.$i.log" 2>&1 &
        pids+=("$!")
      done
      for pid in "${pids[@]}"; do
        if ! wait "$pid"; then failed_process=1; fi
      done
      for ((i=start; i<start+${#pids[@]}; i++)); do
        cat "$WORK/chunk.$i.log" >> "$log"
      done
    done
    if [[ "$failed_process" -ne 0 && ! ( "$suite" == verbatim && "$engine" == petta ) ]]; then
      echo "EQUATION KERNEL GATE: FAIL ($suite on $engine: process failed; log: $log)"
      status=1
      continue
    fi
    if [[ "$suite" == verbatim && "$engine" == petta ]]; then
      if grep -q 'function_input_arities(ek:lcf-step' "$log" && ! grep -q '(ek:pass ' "$log"; then
        echo "  $suite on $engine: refused when loading (arity of ek:lcf-step)"
      else
        echo "EQUATION KERNEL GATE: FAIL ($suite on $engine: expected a refusal when loading; log: $log)"
        status=1
      fi
      continue
    fi
    normalize < "$log" > "$WORK/$suite.$engine.norm"
    passed=$(grep -c '^(ek:pass ' "$WORK/$suite.$engine.norm" || true)
    failed=$(grep -c '^(ek:FAIL ' "$WORK/$suite.$engine.norm" || true)
    if [[ "$passed" -ne "$expected" || "$failed" -ne 0 ]]; then
      echo "EQUATION KERNEL GATE: FAIL ($suite on $engine: $passed/$expected passed, $failed failed; log: $log)"
      status=1
      continue
    fi
    if [[ -z "$reference" ]]; then
      reference="$WORK/$suite.$engine.norm"
      cp "$reference" "$LOGDIR/$suite.normalized"
    elif ! cmp -s "$reference" "$WORK/$suite.$engine.norm"; then
      echo "EQUATION KERNEL GATE: FAIL ($suite: $engine output differs from the first engine)"
      status=1
      continue
    fi
    echo "  $suite on $engine: $passed/$expected passed"
  done
done

if [[ "$status" -ne 0 ]]; then
  exit 1
fi

digest=$(for suite in $SUITES; do cat "$LOGDIR/$suite.normalized"; done | sha256sum | cut -d' ' -f1)
echo "EQUATION KERNEL GATE: PASS (suites: $SUITES; engines: $ENGINES; digest $digest)"
