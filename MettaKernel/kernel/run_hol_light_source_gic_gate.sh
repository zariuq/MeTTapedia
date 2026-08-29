#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
MK_ROOT="$AIHUB/Mettapedia/MettaKernel"
EXPORTER="Mettapedia/GSLT/LanguageDef/HOLSourceInferenceMeTTaExport.lean"
MODULE="Mettapedia.GSLT.LanguageDef.HOLSourceInferenceMeTTaExport"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
ADAPTER="$MK_ROOT/tools/hol_light_prooftrace_to_gic.py"
TRACE="$MK_ROOT/parity_logs/hol_light_source/self_imp_924faf0c"
BASE="$ROOT/hol_source_languages_generated_v0.metta"
ARTIFACT="$ROOT/hol_light_self_imp_source_gic_v0.metta"
LOGDIR="$ROOT/parity_logs/hol_light_source_gic"
FRESHDIR="$LOGDIR/fresh"
FRESH_BASE="$FRESHDIR/hol_source_languages_generated_v0.metta"
FRESH_ARTIFACT="$FRESHDIR/hol_light_self_imp_source_gic_v0.metta"
EXPORT_LOG="$LOGDIR/export.log"
ADAPTER_LOG="$LOGDIR/adapter.log"
RUN_LOG="$LOGDIR/run.log"

mkdir -p "$FRESHDIR"

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake build "$MODULE"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" "$FRESH_BASE"
) >"$EXPORT_LOG" 2>&1; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (language export; log: $EXPORT_LOG)"
  exit 1
fi

if ! cmp -s "$BASE" "$FRESH_BASE"; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (generated language stale)"
  exit 1
fi

if ! python3 "$ADAPTER" \
  --proofs "$TRACE.proofs" \
  --theorems "$TRACE.theorems" \
  --names "$TRACE.names" \
  --language "$FRESH_BASE" \
  --output "$FRESH_ARTIFACT" >"$ADAPTER_LOG" 2>&1; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (ProofTrace lowering; log: $ADAPTER_LOG)"
  exit 1
fi

if ! cmp -s "$ARTIFACT" "$FRESH_ARTIFACT"; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (generated source artifact stale)"
  exit 1
fi

if [[ "$(grep -c '^!(assertEqual' "$ARTIFACT")" -ne 2 ]]; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (expected 2 batch assertions)"
  exit 1
fi

if ! (
  cd "$ROOT"
  "$CETTA" "$(basename "$ARTIFACT")"
) >"$RUN_LOG" 2>&1; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (CeTTa process; log: $RUN_LOG)"
  exit 1
fi

if grep -Eqi 'Error|❌|fatal|out of memory|signal|stack overflow' "$RUN_LOG"; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (runtime/assertion failure; log: $RUN_LOG)"
  exit 1
fi

if [[ "$(grep -Fxc '[(HOLLightSourceGICSummary "SELF_IMP" 171 378 6 6 0)]' "$RUN_LOG")" -ne 1 ]]; then
  echo "HOL LIGHT SOURCE GIC GATE: FAIL (exact summary absent or duplicated)"
  exit 1
fi

echo "HOL LIGHT SOURCE GIC GATE: PASS (official SELF_IMP closure; 171 proof nodes; 378 source-evidence nodes; 6/6 checks; 0 failures)"
