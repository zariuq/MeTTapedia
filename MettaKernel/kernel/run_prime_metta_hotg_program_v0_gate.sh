#!/usr/bin/env bash
# shellcheck disable=SC2016 # MeTTa variable names are literal gate patterns.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
# Default to the exact Prime-enabled runtime used to validate this fixture.
# Callers may override CETTA to test another candidate binary.
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
MEGALODON="${MEGALODON:-$AIHUB/repos/megalodon-1.13/bin/megalodon}"
SOURCE="$ROOT/prime_metta_hotg_program_v0.metta"
HOTG_SOURCE="$ROOT/../Curriculum/Megalodon/05_tg_universe.mg"
HOTG_NEGATIVE="$ROOT/../Curriculum/Megalodon/neg_wrong_exact.mg"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/prime_metta_hotg_program_v0.log"
MEGALODON_LOG="$LOGDIR/prime_metta_hotg_program_v0_megalodon.log"
MEGALODON_NEGATIVE_LOG="$LOGDIR/prime_metta_hotg_program_v0_megalodon_negative.log"
EXPECTED_ASSERTIONS=32
EXPECTED_RUNTIME_CALLS=4
EXPECTED_SUBJECT_CHECKS=4
EXPECTED_BAG_CHECKS=3
EXPECTED_INERT_FORGED_SUBJECTS=4

mkdir -p "$LOGDIR"

if ! "$CETTA" --list-languages 2>/dev/null |
    grep -Eq '^[[:space:]]+prime[[:space:]]+implemented'; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (CETTA must name a Prime-enabled binary)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$SOURCE")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

actual_runtime_calls="$(grep -c 'prime-judge &self' "$SOURCE")"
if [[ "$actual_runtime_calls" -ne "$EXPECTED_RUNTIME_CALLS" ]]; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (expected $EXPECTED_RUNTIME_CALLS runtime judgments, found $actual_runtime_calls)"
  exit 1
fi

actual_subject_checks="$(grep -c '== (quote \$judgment)' "$SOURCE")"
if [[ "$actual_subject_checks" -ne "$EXPECTED_SUBJECT_CHECKS" ]]; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (expected $EXPECTED_SUBJECT_CHECKS subject checks, found $actual_subject_checks)"
  exit 1
fi

actual_bag_checks="$(grep -c 'pmh-choose-bag-agrees (collapse' "$SOURCE")"
if [[ "$actual_bag_checks" -ne "$EXPECTED_BAG_CHECKS" ]]; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (expected $EXPECTED_BAG_CHECKS answer-bag checks, found $actual_bag_checks)"
  exit 1
fi

actual_inert_forged_subjects="$(grep -c 'noeval (PrimeVerdict' "$SOURCE")"
if [[ "$actual_inert_forged_subjects" -ne "$EXPECTED_INERT_FORGED_SUBJECTS" ]]; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (expected $EXPECTED_INERT_FORGED_SUBJECTS inert forged-subject probes, found $actual_inert_forged_subjects)"
  exit 1
fi

if [[ ! -x "$MEGALODON" ]]; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (Megalodon reference checker unavailable)"
  exit 1
fi

if ! grep -Fq 'Axiom UnivOf_In' "$HOTG_SOURCE" ||
   ! grep -Fq 'Axiom UnivOf_Power' "$HOTG_SOURCE" ||
   ! grep -Fq 'exact (UnivOf_Power N N (UnivOf_In N)).' "$HOTG_SOURCE" ||
   ! grep -Fq '"pmh.hotg.univ-in"' "$SOURCE" ||
   ! grep -Fq '"pmh.hotg.univ-power"' "$SOURCE"; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (TG-universe reference shape drifted)"
  exit 1
fi

if ! "$MEGALODON" "$HOTG_SOURCE" >"$MEGALODON_LOG" 2>&1; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (Megalodon rejected TG-universe anchor; log: $MEGALODON_LOG)"
  exit 1
fi

if "$MEGALODON" "$HOTG_NEGATIVE" >"$MEGALODON_NEGATIVE_LOG" 2>&1; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (Megalodon accepted wrong-proof negative; log: $MEGALODON_NEGATIVE_LOG)"
  exit 1
fi

if ! "$CETTA" --lang prime "$SOURCE" >"$LOG" 2>&1; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (assertion failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '(PrimeMettaHOTGProgramSummary 32 32 0)' "$LOG")" -ne 1 ]]; then
  echo "PRIME METTA HOTG PROGRAM V0 GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

echo "PRIME METTA HOTG PROGRAM V0 GATE: PASS (32/32 assertions; 4 subject-bound certificates; answer-bag mutants and forged subjects rejected; Megalodon TG anchor accepted; wrong proof rejected)"
