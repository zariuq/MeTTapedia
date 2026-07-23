#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean"
SOURCE="$AIHUB/hyperon/metamath/metamath-test/demo0.mm"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
ARTIFACT="$ROOT/metamath_demo0_generated_v0.metta"
LOGDIR="$ROOT/parity_logs"
FRESH="$LOGDIR/metamath_demo0_generated_v0.fresh.metta"
EXPORT_LOG="$LOGDIR/metamath_demo0_export.log"
RUN_LOG="$LOGDIR/metamath_demo0_gic.log"
EXPECTED_SHA256="b68d7488bdbf2d55d1a955f3a6a3efac68ca9e3009d24f867e1a75aacb7b03d3"
EXPECTED_BYTES=1353
EXPECTED_TOKENS=34
EXPECTED_ASSERTIONS=6

mkdir -p "$LOGDIR"

actual_sha256="$(sha256sum "$SOURCE" | awk '{print $1}')"
if [[ "$actual_sha256" != "$EXPECTED_SHA256" ]]; then
  echo "MM DEMO0 GIC GATE: FAIL (source hash changed: $actual_sha256)"
  exit 1
fi

if [[ "$(wc -c < "$SOURCE")" -ne "$EXPECTED_BYTES" ]]; then
  echo "MM DEMO0 GIC GATE: FAIL (source byte count changed)"
  exit 1
fi

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" \
    demo0 "$SOURCE" "$FRESH"
) >"$EXPORT_LOG" 2>&1; then
  echo "MM DEMO0 GIC GATE: FAIL (source projection/lowering failed; log: $EXPORT_LOG)"
  exit 1
fi

if ! cmp -s "$ARTIFACT" "$FRESH"; then
  echo "MM DEMO0 GIC GATE: FAIL (generated artifact is stale; fresh: $FRESH)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$ARTIFACT")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "MM DEMO0 GIC GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

if ! (
  cd "$ROOT"
  "$CETTA" "$(basename "$ARTIFACT")"
) >"$RUN_LOG" 2>&1; then
  echo "MM DEMO0 GIC GATE: FAIL (CeTTa process failed; log: $RUN_LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$RUN_LOG"; then
  echo "MM DEMO0 GIC GATE: FAIL (checker assertion failed; log: $RUN_LOG)"
  exit 1
fi

expected_summary="[(MMDEMO0Summary $EXPECTED_BYTES $EXPECTED_TOKENS 6 6 0)]"
if [[ "$(grep -Fxc "$expected_summary" "$RUN_LOG")" -ne 1 ]]; then
  echo "MM DEMO0 GIC GATE: FAIL (exact summary absent or duplicated; log: $RUN_LOG)"
  exit 1
fi

echo "MM DEMO0 GIC GATE: PASS ($EXPECTED_BYTES bytes; $EXPECTED_TOKENS real proof tokens; 6/6 assertions; 0 failures)"
