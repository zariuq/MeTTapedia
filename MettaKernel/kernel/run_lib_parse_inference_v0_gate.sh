#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
SOURCE="$ROOT/lib_parse_inference_v0.metta"
SUITE="$ROOT/lib_parse_inference_v0_suite.metta"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/lib_parse_inference_v0.log"
EXPECTED_ASSERTIONS=39

mkdir -p "$LOGDIR"

actual_assertions="$(grep -c '^!(assertEqual' "$SUITE")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "LIB_PARSE INFERENCE V0 GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

duplicate_heads="$({
  rg -o '^\(= \(lib_parse:[^[:space:]()]+' "$SOURCE" \
    | sed 's/^(= (//' \
    | sort \
    | uniq -c \
    | awk '$1 > 1 { print $1 " " $2 }'
} || true)"
expected_duplicates=$'2 lib_parse:append\n2 lib_parse:decl-add\n2 lib_parse:pr-append'
if [[ "$duplicate_heads" != "$expected_duplicates" ]]; then
  echo "LIB_PARSE INFERENCE V0 GATE: FAIL (unexpected multi-equation helper)"
  printf '%s\n' "$duplicate_heads"
  exit 1
fi

if ! "$CETTA" --lang he --profile he-prime --quiet "$SUITE" >"$LOG" 2>&1; then
  echo "LIB_PARSE INFERENCE V0 GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "LIB_PARSE INFERENCE V0 GATE: FAIL (assertion failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(LPInferenceV0Summary 39 39 0)]' "$LOG")" -ne 1 ]]; then
  echo "LIB_PARSE INFERENCE V0 GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

echo "LIB_PARSE INFERENCE V0 GATE: PASS (39/39 assertions; deterministic helpers single-result)"
