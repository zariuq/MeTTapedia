#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOSITORY="$(cd "$ROOT/../.." && pwd)"
AIHUB="${AIHUB:-$(cd "$REPOSITORY/.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
SOURCE="$ROOT/prime_subject_ref_v1.metta"
LOGDIR="$ROOT/parity_logs"
PRIME_LOG="$LOGDIR/prime_subject_ref_v1_prime.log"
HE_LOG="$LOGDIR/prime_subject_ref_v1_he.log"
EXPECTED_ASSERTIONS=23

mkdir -p "$LOGDIR"

if [[ "$(grep -c '^!(assertEqual' "$SOURCE")" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME SUBJECT REF V1 GATE: FAIL (assertion census changed)"
  exit 1
fi

if grep -Fq '(== (quote' "$SOURCE"; then
  echo "PRIME SUBJECT REF V1 GATE: FAIL (quotation equality returned as authority)"
  exit 1
fi

if ! "$CETTA" --lang prime "$SOURCE" >"$PRIME_LOG" 2>&1; then
  echo "PRIME SUBJECT REF V1 GATE: FAIL (Prime execution failed; log: $PRIME_LOG)"
  exit 1
fi
if grep -q 'Error\|❌' "$PRIME_LOG"; then
  echo "PRIME SUBJECT REF V1 GATE: FAIL (Prime assertion failed; log: $PRIME_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimeSubjectRefV1Summary 23 23 0)' "$PRIME_LOG")" -ne 1 ]]; then
  echo "PRIME SUBJECT REF V1 GATE: FAIL (Prime summary absent or duplicated)"
  exit 1
fi

# The same file must not gain authority in a dialect that leaves Prime
# judgments uninterpreted.  CeTTa intentionally may exit zero after the first
# failed assertion, so the positive summary is the gate rather than exit code.
"$CETTA" --lang he "$SOURCE" >"$HE_LOG" 2>&1 || true
if grep -Fq '(PrimeSubjectRefV1Summary 23 23 0)' "$HE_LOG"; then
  echo "PRIME SUBJECT REF V1 GATE: FAIL (HE dialect produced Prime authority)"
  exit 1
fi

echo "PRIME SUBJECT REF V1 GATE: PASS (23/23 indexed subject, snapshot, dialect, package, occurrence, digest, and handle checks; HE authority rejected)"
