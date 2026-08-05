#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/GSLT/LanguageDef/LF/FirstOrderConversionMeTTaExport.lean"
MODULE="Mettapedia.GSLT.LanguageDef.LF.FirstOrderConversionMeTTaExport"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
ARTIFACT="$ROOT/lf_first_order_conversion_generated_v0.metta"
BRIDGE="$ROOT/kernel_signature_lf_indexed_conversion_frontend_bridge_lib_v0.metta"
LOGDIR="$ROOT/parity_logs"
FRESH="$LOGDIR/lf_first_order_conversion_generated_v0.fresh.metta"
MUTATED="$LOGDIR/lf_first_order_conversion_generated_v0.mutated.metta"
BUILD_LOG="$LOGDIR/lf_first_order_conversion_build.log"
EXPORT_LOG="$LOGDIR/lf_first_order_conversion_export.log"
RUN_LOG="$LOGDIR/lf_first_order_conversion_generated_v0.log"
MUTATION_LOG="$LOGDIR/lf_first_order_conversion_mutation.log"
EXPECTED_ASSERTIONS=13

LEAN_SOURCES=(
  "$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/LF/FirstOrderContextualConversion.lean"
  "$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/LF/FirstOrderContextualCorrespondence.lean"
  "$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/LF/FirstOrderArithmeticCorrespondence.lean"
  "$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/LF/FirstOrderOperationalCorrespondence.lean"
  "$LEAN_ROOT/$EXPORTER"
)

mkdir -p "$LOGDIR"

if ! (
  cd "$LEAN_ROOT"
  lake build "$MODULE"
) >"$BUILD_LOG" 2>&1; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (Lean build failed; log: $BUILD_LOG)"
  exit 1
fi

if ! (
  cd "$LEAN_ROOT"
  lake env lean --run "$EXPORTER" "$FRESH"
) >"$EXPORT_LOG" 2>&1; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (export failed; log: $EXPORT_LOG)"
  exit 1
fi

if ! cmp -s "$ARTIFACT" "$FRESH"; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (generated artifact is stale; fresh: $FRESH)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$ARTIFACT")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

if ! (
  cd "$ROOT"
  "$CETTA" "$(basename "$ARTIFACT")"
) >"$RUN_LOG" 2>&1; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (CeTTa process failed; log: $RUN_LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$RUN_LOG"; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (checker assertion failed; log: $RUN_LOG)"
  exit 1
fi

expected_summary='[(LFFirstOrderConversionLiveSummary 3 5 13 13 0)]'
if [[ "$(grep -Fxc "$expected_summary" "$RUN_LOG")" -ne 1 ]]; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (exact summary absent or duplicated; log: $RUN_LOG)"
  exit 1
fi

python3 "$ROOT/mutate_lf_first_order_conversion.py" "$ARTIFACT" "$MUTATED"
(
  cd "$LOGDIR"
  "$CETTA" --import-mode ancestor-walk "$(basename "$MUTATED")"
) >"$MUTATION_LOG" 2>&1 || true

if ! grep -q 'Error\|❌' "$MUTATION_LOG"; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (proof mutation escaped detection; log: $MUTATION_LOG)"
  exit 1
fi

if rg -n '(^|[^[:alnum:]_])(sorry|admit|theorem_wanted|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
    "${LEAN_SOURCES[@]}"; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (Lean source contains an unproved or disallowed shortcut)"
  exit 1
fi

if rg -n '^\s*\(=\s+\([^()[:space:]]+\?' "$BRIDGE" "$ARTIFACT"; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (MeTTa definition uses a question-mark suffix)"
  exit 1
fi

if rg -n '/home/|/shared/|/tmp/|prompt|respond to' \
    "$BRIDGE" "$ARTIFACT" "${LEAN_SOURCES[@]}"; then
  echo "LF FIRST-ORDER CONVERSION GATE: FAIL (public artifact leakage detected)"
  exit 1
fi

echo "LF FIRST-ORDER CONVERSION GATE: PASS (validated source; beta/eta/transitive live KW checks; 5 semantic mutations; 13/13 assertions; external proof mutation caught)"
