#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
SOURCE="$ROOT/generic_inference_checker_v0.metta"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/generic_inference_checker_v0.log"
EXPECTED_ASSERTIONS=43

mkdir -p "$LOGDIR"

actual_assertions="$(grep -c '^!(assertEqual' "$SOURCE")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "GIC GATE: FAIL (expected $EXPECTED_ASSERTIONS source assertions, found $actual_assertions)"
  exit 1
fi

if ! "$CETTA" "$SOURCE" >"$LOG" 2>&1; then
  echo "GIC GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "GIC GATE: FAIL (checker assertion failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(GICSummary 43 43 0)]' "$LOG")" -ne 1 ]]; then
  echo "GIC GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

echo "GIC GATE: PASS (43/43 assertions; 0 failures)"
