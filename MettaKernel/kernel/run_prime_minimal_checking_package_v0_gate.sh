#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
# Default to the exact Prime-enabled runtime used to validate this fixture.
# Callers may override CETTA to test another candidate binary.
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
SOURCE="$ROOT/prime_minimal_checking_package_v0.metta"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/prime_minimal_checking_package_v0.log"
EXPECTED_ASSERTIONS=23

mkdir -p "$LOGDIR"

if ! "$CETTA" --list-languages 2>/dev/null |
    grep -Eq '^[[:space:]]+prime[[:space:]]+implemented'; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 GATE: FAIL (CETTA must name a Prime-enabled binary)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$SOURCE")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

if ! "$CETTA" --lang prime "$SOURCE" >"$LOG" 2>&1; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 GATE: FAIL (assertion failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '(PrimeMinimalCheckingSummary 23 23 0)' "$LOG")" -ne 1 ]]; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

echo "PRIME MINIMAL CHECKING PACKAGE V0 GATE: PASS (23/23 assertions; 0 failures)"
