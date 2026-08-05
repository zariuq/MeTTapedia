#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
SOURCE="$ROOT/gslt_checked_source_v1.metta"
SUITE="$ROOT/gslt_checked_source_v1_suite.metta"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/gslt_checked_source_v1.log"
EXPECTED_ASSERTIONS=29

mkdir -p "$LOGDIR"

actual_assertions="$(grep -c '^!(assertEqual' "$SUITE")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "GSLT SOURCE V1 GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

if rg -n '^\(= \([^[:space:]()]+\?' "$SOURCE" "$SUITE" >/dev/null; then
  echo "GSLT SOURCE V1 GATE: FAIL (forbidden question-suffix definition)"
  exit 1
fi

if ! "$CETTA" "$SUITE" >"$LOG" 2>&1; then
  echo "GSLT SOURCE V1 GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "GSLT SOURCE V1 GATE: FAIL (assertion failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(GSLTSourceV1Summary 29 29 0)]' "$LOG")" -ne 1 ]]; then
  echo "GSLT SOURCE V1 GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

echo "GSLT SOURCE V1 GATE: PASS (29/29 assertions; 0 failures)"
