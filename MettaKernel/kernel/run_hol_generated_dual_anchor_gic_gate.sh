#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/GSLT/LanguageDef/HOLInferenceMeTTaExport.lean"
MODULE="Mettapedia.GSLT.LanguageDef.HOLInferenceMeTTaExport"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
ARTIFACT="$ROOT/hol_generated_dual_anchor_gic_v0.metta"
LOGDIR="$ROOT/parity_logs"
FRESH="$LOGDIR/hol_generated_dual_anchor_gic_v0.fresh.metta"
EXPORT_LOG="$LOGDIR/hol_generated_dual_anchor_export.log"
RUN_LOG="$LOGDIR/hol_generated_dual_anchor_gic_v0.log"

mkdir -p "$LOGDIR"

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake build "$MODULE"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" "$FRESH"
) >"$EXPORT_LOG" 2>&1; then
  echo "HOL GENERATED GIC GATE: FAIL (extraction/export; log: $EXPORT_LOG)"
  exit 1
fi

if ! cmp -s "$ARTIFACT" "$FRESH"; then
  echo "HOL GENERATED GIC GATE: FAIL (generated artifact stale; fresh: $FRESH)"
  exit 1
fi

if [[ "$(grep -c '^!(assertEqual' "$ARTIFACT")" -ne 12 ]]; then
  echo "HOL GENERATED GIC GATE: FAIL (expected 12 assertions)"
  exit 1
fi

if ! (
  cd "$ROOT"
  "$CETTA" "$(basename "$ARTIFACT")"
) >"$RUN_LOG" 2>&1; then
  echo "HOL GENERATED GIC GATE: FAIL (CeTTa process; log: $RUN_LOG)"
  exit 1
fi

if grep -Eqi 'Error|❌|fatal|out of memory|signal' "$RUN_LOG"; then
  echo "HOL GENERATED GIC GATE: FAIL (runtime/assertion failure; log: $RUN_LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(HOLGeneratedInventory 15 8 3 3)]' "$RUN_LOG")" -ne 1 ]]; then
  echo "HOL GENERATED GIC GATE: FAIL (inventory summary absent or duplicated)"
  exit 1
fi

if [[ "$(grep -Fxc '[(HOLGeneratedGICSummary 2 12 12 0)]' "$RUN_LOG")" -ne 1 ]]; then
  echo "HOL GENERATED GIC GATE: FAIL (checker summary absent or duplicated)"
  exit 1
fi

echo "HOL GENERATED GIC GATE: PASS (15 HOL Light rules; 8 HOL4 rules; 12/12 assertions; 0 failures)"
