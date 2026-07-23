#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
SOURCE="$ROOT/hol_dual_anchor_gic_v0.metta"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/hol_dual_anchor_gic_v0.log"
EXPECTED_ASSERTIONS=12

mkdir -p "$LOGDIR"

actual_assertions="$(grep -c '^!(assertEqual' "$SOURCE")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "HOL GIC GATE: FAIL (expected $EXPECTED_ASSERTIONS source assertions, found $actual_assertions)"
  exit 1
fi

if ! "$CETTA" "$SOURCE" >"$LOG" 2>&1; then
  echo "HOL GIC GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "HOL GIC GATE: FAIL (checker assertion failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(HOLGICSummary 2 12 12 0)]' "$LOG")" -ne 1 ]]; then
  echo "HOL GIC GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

echo "HOL GIC GATE: PASS (2 profiles; 12/12 assertions; 0 failures)"
