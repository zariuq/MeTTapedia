#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/GSLT/LanguageDef/HOLNativeGSLTMeTTaExport.lean"
ADEQUACY_MODULE="Mettapedia.GSLT.LanguageDef.HOLNativeSourceAdequacy"
SLICE_FILE="$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/HOLNativeGSLTSlice.lean"
ADEQUACY_FILE="$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/HOLNativeSourceAdequacy.lean"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
ARTIFACT="$ROOT/hol_native_gslt_generated_v0.metta"
LOGDIR="$ROOT/parity_logs"
FRESH="$LOGDIR/hol_native_gslt_generated_v0.fresh.metta"
MUTATED="$LOGDIR/hol_native_gslt_generated_v0.mutated.metta"
EXPORT_LOG="$LOGDIR/hol_native_gslt_export.log"
RUN_LOG="$LOGDIR/hol_native_gslt_generated_v0.log"
MUTATION_LOG="$LOGDIR/hol_native_gslt_mutation.log"
EXPECTED_ASSERTIONS=9
HOL_LIGHT_SOURCE="${HOL_LIGHT_SOURCE:-$AIHUB/repos/itp-curriculum-sources/hol_light/fusion.ml}"
HOL4_SIGNATURE="${HOL4_SIGNATURE:-$AIHUB/repos/itp-curriculum-sources/hol4/src/prekernel/FinalThm-sig.sml}"
HOL4_KERNEL="${HOL4_KERNEL:-$AIHUB/repos/itp-curriculum-sources/hol4/src/thm/std-thm.ML}"
HOL_LIGHT_DIGEST=29544be92d9cc1e6b3b59ba5b210604b9a748366a68b3bcdc2619717d68fd98a
HOL4_SIGNATURE_DIGEST=12f5e757c56dd0d13b1a5f8f09abdb96eedc1d80ce9800aec5abebb011d8629c
HOL4_KERNEL_DIGEST=6f559a177e8c59d0c92702b5a8fcecfc4b48f7672c743855c904c3bb126fb25a

mkdir -p "$LOGDIR"

check_source_digest() {
  local label="$1"
  local source="$2"
  local expected="$3"
  local actual
  [[ -f "$source" ]] || {
    echo "HOL NATIVE GSLT GATE: FAIL ($label source absent: $source)"
    exit 1
  }
  actual="$(sha256sum "$source" | awk '{print $1}')"
  [[ "$actual" == "$expected" ]] || {
    echo "HOL NATIVE GSLT GATE: FAIL ($label source identity changed: $actual)"
    exit 1
  }
}

check_source_digest "HOL Light fusion" "$HOL_LIGHT_SOURCE" "$HOL_LIGHT_DIGEST"
check_source_digest "HOL4 theorem signature" "$HOL4_SIGNATURE" "$HOL4_SIGNATURE_DIGEST"
check_source_digest "HOL4 theorem kernel" "$HOL4_KERNEL" "$HOL4_KERNEL_DIGEST"

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake build "$ADEQUACY_MODULE"
) >"$LOGDIR/hol_native_source_adequacy_build.log" 2>&1; then
  echo "HOL NATIVE GSLT GATE: FAIL (Lean source-adequacy build failed; log: $LOGDIR/hol_native_source_adequacy_build.log)"
  exit 1
fi

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" "$FRESH"
) >"$EXPORT_LOG" 2>&1; then
  echo "HOL NATIVE GSLT GATE: FAIL (export failed; log: $EXPORT_LOG)"
  exit 1
fi

if ! cmp -s "$ARTIFACT" "$FRESH"; then
  echo "HOL NATIVE GSLT GATE: FAIL (generated artifact is stale; fresh: $FRESH)"
  exit 1
fi

actual_assertions="$(grep -c '^!(assertEqual' "$ARTIFACT")"
if [[ "$actual_assertions" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "HOL NATIVE GSLT GATE: FAIL (expected $EXPECTED_ASSERTIONS assertions, found $actual_assertions)"
  exit 1
fi

if ! (
  cd "$ROOT"
  "$CETTA" "$(basename "$ARTIFACT")"
) >"$RUN_LOG" 2>&1; then
  echo "HOL NATIVE GSLT GATE: FAIL (CeTTa process failed; log: $RUN_LOG)"
  exit 1
fi

if grep -q 'Error\|❌' "$RUN_LOG"; then
  echo "HOL NATIVE GSLT GATE: FAIL (checker assertion failed; log: $RUN_LOG)"
  exit 1
fi

expected_summary='[(HOLNativeGSLTSummary 2 5 8 9 9 0)]'
if [[ "$(grep -Fxc "$expected_summary" "$RUN_LOG")" -ne 1 ]]; then
  echo "HOL NATIVE GSLT GATE: FAIL (exact summary absent or duplicated; log: $RUN_LOG)"
  exit 1
fi

python3 "$ROOT/mutate_hol_native_gslt.py" "$ARTIFACT" "$MUTATED"
(
  cd "$LOGDIR"
  "$CETTA" --import-mode ancestor-walk "$(basename "$MUTATED")"
) >"$MUTATION_LOG" 2>&1 || true

if ! grep -q 'Error\|❌' "$MUTATION_LOG"; then
  echo "HOL NATIVE GSLT GATE: FAIL (proof mutation escaped detection; log: $MUTATION_LOG)"
  exit 1
fi

if rg -n '(^|[^[:alnum:]_])(sorry|admit|theorem_wanted|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
    "$SLICE_FILE" "$ADEQUACY_FILE"; then
  echo "HOL NATIVE GSLT GATE: FAIL (Lean native slice contains an unproved or disallowed shortcut)"
  exit 1
fi

if rg -n '^\s*\(=\s+\([^()[:space:]]+\?' "$ARTIFACT"; then
  echo "HOL NATIVE GSLT GATE: FAIL (MeTTa definition uses a question-mark suffix)"
  exit 1
fi

echo "HOL NATIVE GSLT GATE: PASS (3 source artifacts pinned; 2 admitted source packages; 2 source/native anchor certificates; 5 primitives; 8 side rules; 9/9 assertions; mutation caught)"
