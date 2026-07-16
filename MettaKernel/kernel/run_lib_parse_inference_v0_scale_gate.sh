#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
SOURCE="$ROOT/lib_parse_inference_v0_scale.metta"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/lib_parse_inference_v0_scale.log"

mkdir -p "$LOGDIR"

if ! "$CETTA" --lang he --profile he-prime --quiet "$SOURCE" >"$LOG" 2>&1; then
  echo "LIB_PARSE INFERENCE V0 SCALE GATE: FAIL (CeTTa process failed; log: $LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$LOG"; then
  echo "LIB_PARSE INFERENCE V0 SCALE GATE: FAIL (admission failed; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc 'ScaleOK' "$LOG")" -ne 1 ]]; then
  echo "LIB_PARSE INFERENCE V0 SCALE GATE: FAIL (success sentinel absent or duplicated; log: $LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(LPInferenceScaleSummary 4096 1 1 0)]' "$LOG")" -ne 1 ]]; then
  echo "LIB_PARSE INFERENCE V0 SCALE GATE: FAIL (exact summary absent or duplicated; log: $LOG)"
  exit 1
fi

echo "LIB_PARSE INFERENCE V0 SCALE GATE: PASS (4096 checked tokens; exact success sentinel)"
