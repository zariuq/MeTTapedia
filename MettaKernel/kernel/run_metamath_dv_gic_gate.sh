#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
SOURCE="$ROOT/metamath_dv_fixture_v0.mm"
ARTIFACT="$ROOT/metamath_dv_source_generated_v1.metta"
LOGDIR="$ROOT/parity_logs"
FRESH="$LOGDIR/metamath_dv_source_generated_v1.fresh.metta"
EXPORT_LOG="$LOGDIR/metamath_dv_export.log"
RUN_LOG="$LOGDIR/metamath_dv_gic.log"
EXPECTED_SHA256="46bfd4628307e20b9541682265fa7e815404cb362f12311330d43879579879da"
EXPECTED_BYTES=532
EXPECTED_ASSERTIONS=1

mkdir -p "$LOGDIR"

actual_sha256="$(sha256sum "$SOURCE" | awk '{print $1}')"
if [[ "$actual_sha256" != "$EXPECTED_SHA256" ]]; then
  echo "MM DV GIC GATE: FAIL (source hash changed: $actual_sha256)"
  exit 1
fi

if [[ "$(wc -c < "$SOURCE")" -ne "$EXPECTED_BYTES" ]]; then
  echo "MM DV GIC GATE: FAIL (source byte count changed)"
  exit 1
fi

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" \
    target "$SOURCE" th "$FRESH"
) >"$EXPORT_LOG" 2>&1; then
  echo "MM DV GIC GATE: FAIL (canonical source admission/export failed; log: $EXPORT_LOG)"
  exit 1
fi

if ! cmp -s "$ARTIFACT" "$FRESH"; then
  echo "MM DV GIC GATE: FAIL (generated artifact is stale; fresh: $FRESH)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$ARTIFACT")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "MM DV GIC GATE: FAIL (expected $EXPECTED_ASSERTIONS batch assertion, found $actual_assertions)"
  exit 1
fi

if ! "$CETTA" "$ARTIFACT" >"$RUN_LOG" 2>&1; then
  echo "MM DV GIC GATE: FAIL (CeTTa process failed; log: $RUN_LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$RUN_LOG"; then
  echo "MM DV GIC GATE: FAIL (checker assertion failed; log: $RUN_LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(MMTARGETSummary "th" 532 4 6 6 0)]' "$RUN_LOG")" -ne 1 ]]; then
  echo "MM DV GIC GATE: FAIL (exact summary absent or duplicated; log: $RUN_LOG)"
  exit 1
fi

echo "MM DV GIC GATE: PASS (canonical 532-byte source; generated DV evidence; 6/6 checks; 0 failures)"
