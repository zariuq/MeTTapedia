#!/usr/bin/env bash
# shellcheck disable=SC2016 # MeTTa variable names are literal gate patterns.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
# Default = the exact tested Prime-enabled binary (review finding: the gate must
# not silently point at main CeTTa). Tested identity SHA-256:
# ce0f8646b1a885227cf714d20fe42bcf08ca594acba449cfa608301c1a73b8a6
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
MEGALODON="${MEGALODON:-$AIHUB/repos/megalodon-1.13/bin/megalodon}"
MEGALODON_PREAMBLE="${MEGALODON_PREAMBLE:-$AIHUB/repos/megalodon-1.13/examples/egal/PfgEAug2022Preamble.mgs}"
SOURCE="$ROOT/prime_raw_checking_worked_metta_programs_v0.metta"
MEGALODON_SOURCE="$ROOT/../Curriculum/Megalodon/08_metta_add_eval_graph.mg"
MEGALODON_NEGATIVE="$ROOT/../Curriculum/Megalodon/neg_metta_add_wrong_result.mg"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/prime_raw_checking_worked_metta_programs_v0.log"
HE_NEGATIVE_LOG="$LOGDIR/prime_raw_checking_worked_metta_programs_v0_he_negative.log"
MEGALODON_LOG="$LOGDIR/prime_worked_metta_megalodon.log"
MEGALODON_NEGATIVE_LOG="$LOGDIR/prime_worked_metta_megalodon_negative.log"
EXPECTED_ASSERTIONS=32
EXPECTED_PRIME_JUDGMENTS=2
EXPECTED_SUBJECT_CHECKS=2
EXPECTED_NON_EVALUATING_DESTRUCTURES=2

mkdir -p "$LOGDIR"

if ! "$CETTA" --list-languages 2>/dev/null |
    grep -Eq '^[[:space:]]+prime[[:space:]]+implemented'; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (CETTA must name a Prime-enabled binary)"
  exit 1
fi

if [[ ! -x "$MEGALODON" || ! -f "$MEGALODON_PREAMBLE" ]]; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (Megalodon checker or Egal preamble unavailable)"
  exit 1
fi

if ! grep -Fq '(wex-add (NS (NS NZ)) (NS NZ))' "$SOURCE" ||
   ! grep -Fq 'Definition AddInput211 : set := (2,1).' "$MEGALODON_SOURCE" ||
   ! grep -Fq 'Definition AddComputedRecord211 : set := (AddInput211,add_nat 2 1).' "$MEGALODON_SOURCE" ||
   ! grep -Fq 'Theorem add_nat_2_1_eq_3 : add_nat 2 1 = 3.' "$MEGALODON_SOURCE"; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (MeTTa/Megalodon W1 differential shape drifted)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$SOURCE")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

actual_prime_judgments="$(grep -c 'prime-judge &self' "$SOURCE")"
if [[ "$actual_prime_judgments" -ne "$EXPECTED_PRIME_JUDGMENTS" ]]; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (expected $EXPECTED_PRIME_JUDGMENTS live Prime judgments, found $actual_prime_judgments)"
  exit 1
fi

actual_subject_checks="$(grep -c '== (quote \$judgment)' "$SOURCE")"
if [[ "$actual_subject_checks" -ne "$EXPECTED_SUBJECT_CHECKS" ]]; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (expected $EXPECTED_SUBJECT_CHECKS subject checks, found $actual_subject_checks)"
  exit 1
fi

actual_non_evaluating_destructures="$(grep -c 'case (noeval \$verdict)' "$SOURCE")"
if [[ "$actual_non_evaluating_destructures" -ne "$EXPECTED_NON_EVALUATING_DESTRUCTURES" ]]; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (expected $EXPECTED_NON_EVALUATING_DESTRUCTURES non-evaluating verdict destructures, found $actual_non_evaluating_destructures)"
  exit 1
fi

if ! "$CETTA" --lang prime "$SOURCE" >"$LOG" 2>&1; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (assertion failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '(PrimeMinimalCheckingSummary 23 23 0)' "$LOG")" -ne 1 ]]; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (imported base fixture summary absent; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '(PrimeWorkedMettaProgramsSummary 32 32 0)' "$LOG")" -ne 1 ]]; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

# Dialect negative: HE leaves prime-judge inert.  The worked file must therefore
# fail at that exact boundary and must not emit the all-green summary.
"$CETTA" --lang he "$SOURCE" >"$HE_NEGATIVE_LOG" 2>&1 || true
if ! grep -q 'Error.*prime-judge &self' "$HE_NEGATIVE_LOG"; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (HE negative did not fail at prime-judge; log: $HE_NEGATIVE_LOG)"
  exit 1
fi
if grep -Fq '(PrimeWorkedMettaProgramsSummary 32 32 0)' "$HE_NEGATIVE_LOG"; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (HE negative emitted the Prime success summary; log: $HE_NEGATIVE_LOG)"
  exit 1
fi

if ! "$MEGALODON" -I "$MEGALODON_PREAMBLE" "$MEGALODON_SOURCE" \
    >"$MEGALODON_LOG" 2>&1; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (Megalodon rejected W1 extensional graph; log: $MEGALODON_LOG)"
  exit 1
fi
if "$MEGALODON" -I "$MEGALODON_PREAMBLE" "$MEGALODON_NEGATIVE" \
    >"$MEGALODON_NEGATIVE_LOG" 2>&1; then
  echo "PRIME WORKED METTA PROGRAMS V0 GATE: FAIL (Megalodon accepted W1 wrong-result proof; log: $MEGALODON_NEGATIVE_LOG)"
  exit 1
fi

echo "PRIME WORKED METTA PROGRAMS V0 GATE: PASS (32/32 assertions, including 2 subject-bound live Prime judgments + imported 23/23 base; wrong-subject, HE dialect, and Megalodon wrong-result negatives rejected)"
