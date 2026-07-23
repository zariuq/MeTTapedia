#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean"
SOURCE="$AIHUB/repos/itp-curriculum-sources/nik_metamath_set_mm/hol.mm"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
ARTIFACT="$ROOT/holmm_tru_generated_v0.metta"
LOGDIR="$ROOT/parity_logs"
FRESH="$LOGDIR/holmm_tru_generated_v0.fresh.metta"
EXPORT_LOG="$LOGDIR/holmm_tru_export.log"
RUN_LOG="$LOGDIR/holmm_tru_gic.log"
EXPECTED_SHA256="ca967a2d351dd178bc0b85e04fec8279cf2d2d8c48fe17c399a2e79f4b9e21c5"
EXPECTED_BYTES=96976
EXPECTED_ACTIONS=3
EXPECTED_ASSERTIONS=1

mkdir -p "$LOGDIR"

actual_sha256="$(sha256sum "$SOURCE" | awk '{print $1}')"
if [[ "$actual_sha256" != "$EXPECTED_SHA256" ]]; then
  echo "HOL.MM TRU GIC GATE: FAIL (source hash changed: $actual_sha256)"
  exit 1
fi

if [[ "$(wc -c < "$SOURCE")" -ne "$EXPECTED_BYTES" ]]; then
  echo "HOL.MM TRU GIC GATE: FAIL (source byte count changed)"
  exit 1
fi

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" \
    hol-tru "$SOURCE" "$FRESH"
) >"$EXPORT_LOG" 2>&1; then
  echo "HOL.MM TRU GIC GATE: FAIL (source projection/lowering failed; log: $EXPORT_LOG)"
  exit 1
fi

if ! cmp -s "$ARTIFACT" "$FRESH"; then
  echo "HOL.MM TRU GIC GATE: FAIL (generated artifact is stale; fresh: $FRESH)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$ARTIFACT")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "HOL.MM TRU GIC GATE: FAIL (expected $EXPECTED_ASSERTIONS batch assertion, found $actual_assertions)"
  exit 1
fi

if ! (
  cd "$ROOT"
  "$CETTA" "$(basename "$ARTIFACT")"
) >"$RUN_LOG" 2>&1; then
  echo "HOL.MM TRU GIC GATE: FAIL (CeTTa process failed; log: $RUN_LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$RUN_LOG"; then
  echo "HOL.MM TRU GIC GATE: FAIL (checker assertion failed; log: $RUN_LOG)"
  exit 1
fi

expected_summary="[(MMHOLTRUSummary $EXPECTED_BYTES $EXPECTED_ACTIONS 5 5 0)]"
if [[ "$(grep -Fxc "$expected_summary" "$RUN_LOG")" -ne 1 ]]; then
  echo "HOL.MM TRU GIC GATE: FAIL (exact summary absent or duplicated; log: $RUN_LOG)"
  exit 1
fi

echo "HOL.MM TRU GIC GATE: PASS ($EXPECTED_BYTES bytes; $EXPECTED_ACTIONS decoded actions; 5/5 gates; 0 failures)"
