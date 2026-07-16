#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
LEAN_MODULE=Mettapedia.Languages.Metamath.NativeSourceCalculus
LEAN_FILE="$LEAN_ROOT/Mettapedia/Languages/Metamath/NativeSourceCalculus.lean"
SEMANTIC_VIEW_FILE="$LEAN_ROOT/Mettapedia/Languages/Metamath/MMLean4SemanticView.lean"
LEAN_EXPORTER=Mettapedia/Languages/Metamath/NativeSourceCalculusMeTTaExport.lean
LEAN_EXPORTER_FILE="$LEAN_ROOT/$LEAN_EXPORTER"
GRAMMAR="$AIHUB/hyperon/CeTTa/lib/lib_parse_metamath_grammar_generated_v0.metta"
SOURCE="$AIHUB/hyperon/metamath/metamath-test/tests/unit/test_compressed_simple.mm"
DIGEST=c80051de58b21dd7007d6e7650c3de5ac789ac6a9de13c756db8b02cfdb63772
LOGDIR="$ROOT/parity_logs/metamath_native_source_calculus_v0"
REFERENCE="$ROOT/metamath_native_source_calculus_reference_v0.metta"

mkdir -p "$LOGDIR"

fail() {
  echo "METAMATH NATIVE SOURCE CALCULUS V0 GATE: FAIL ($*)"
  exit 1
}

LEAN_BUILD_LOG="$LOGDIR/native-source-calculus-lean-build.log"
if ! (
  cd "$LEAN_ROOT"
  lake build "$LEAN_MODULE"
) >"$LEAN_BUILD_LOG" 2>&1; then
  fail "Lean native-source calculus; log: $LEAN_BUILD_LOG"
fi

FRESH_REFERENCE="$LOGDIR/metamath_native_source_calculus_reference_v0.fresh.metta"
LEAN_EXPORT_LOG="$LOGDIR/native-source-calculus-export.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
    lake env lean --run "$LEAN_EXPORTER" "$SOURCE" "$FRESH_REFERENCE"
) >"$LEAN_EXPORT_LOG" 2>&1; then
  fail "Lean native-source export; log: $LEAN_EXPORT_LOG"
fi
cmp -s "$REFERENCE" "$FRESH_REFERENCE" ||
  fail "Lean-rendered reference slice is stale: $FRESH_REFERENCE"

REFERENCE_LOG="$LOGDIR/native-source-calculus-reference.log"
if ! (
  cd "$ROOT"
  "$CETTA" "$(basename "$REFERENCE")"
) >"$REFERENCE_LOG" 2>&1; then
  fail "Lean-rendered reference slice process; log: $REFERENCE_LOG"
fi
if grep -q '(Error\|❌' "$REFERENCE_LOG"; then
  fail "Lean-rendered reference slice emitted an error; log: $REFERENCE_LOG"
fi
[[ "$(grep -Fxc '[(MMNativeReferenceSliceSummary 1 1 0)]' "$REFERENCE_LOG")" -eq 1 ]] ||
  fail "Lean-rendered reference summary absent or duplicated; log: $REFERENCE_LOG"

run_expression() {
  local label="$1"
  local expression="$2"
  local expected="$3"
  local log="$LOGDIR/$label.log"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e '!(import! &self metamath_native_source_calculus_v0_suite)' \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "$label process; log: $log"
  fi
  if grep -q '(Error\|❌' "$log"; then
    fail "$label emitted an error; log: $log"
  fi
  [[ "$(grep -Fxc "$expected" "$log")" -eq 1 ]] ||
    fail "$label exact verdict absent or duplicated; log: $log"
}

compile_expression() {
  local source="$1"
  local revision="$2"
  local digest="$3"
  printf '%s' "(mm-native:compile-target (metamath-ledger:parse-file \"$GRAMMAR\" (MMSourceIdentityV0 \"$revision\" \"$digest\") \"$source\") \"th\")"
}

actual_digest="$(sha256sum "$SOURCE" | awk '{print $1}')"
[[ "$actual_digest" == "$DIGEST" ]] ||
  fail "source hash changed: $actual_digest"

slice="$(compile_expression "$SOURCE" \
  metamath-test/test_compressed_simple.mm "$DIGEST")"

run_expression positive-and-adversarial \
  "!(mm-native-suite:run $slice)" \
  '[(MMNativeSourceSuite True False False False)]'

run_expression accepted-source \
  "!(mm-native:check-slice $slice)" \
  '[(MMNativeSourceCheck "th" SourceAcceptedV1 True)]'

EXACT_COMPARISON_LOG="$LOGDIR/operational-reference-exact-agreement.log"
if ! (
  cd "$ROOT"
  "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
    -e '!(import! &self metamath_native_source_calculus_reference_v0)' \
    -e "!(== $slice (mm-native-reference-slice-v0))"
) >"$EXACT_COMPARISON_LOG" 2>&1; then
  fail "operational/reference exact comparison process; log: $EXACT_COMPARISON_LOG"
fi
if grep -q '(Error\|❌' "$EXACT_COMPARISON_LOG"; then
  fail "operational/reference exact comparison emitted an error; log: $EXACT_COMPARISON_LOG"
fi
[[ "$(grep -Fxc '[True]' "$EXACT_COMPARISON_LOG")" -eq 1 ]] ||
  fail "operational compiler output differs from Lean-rendered slice; log: $EXACT_COMPARISON_LOG"

MUTATED="$LOGDIR/test_compressed_simple_wrong_premise_order.mm"
perl -0pe 's/tR tS tT th\.1 th\.2 ax-syl/tS tR tT th.1 th.2 ax-syl/' \
  "$SOURCE" >"$MUTATED"
MUTATED_DIGEST="$(sha256sum "$MUTATED" | awk '{print $1}')"
mutated_slice="$(compile_expression "$MUTATED" \
  negative/wrong-premise-order "$MUTATED_DIGEST")"
run_expression source-premise-order-mutation \
  "!$mutated_slice" \
  '[(MMNativeElaborationError premise-formula-mismatch)]'

if rg -n '^\s*\(=\s+\([^()[:space:]]+\?' \
    "$ROOT/metamath_native_source_calculus_v0.metta" \
    "$ROOT/metamath_native_source_calculus_v0_suite.metta" \
    "$REFERENCE"; then
  fail "MeTTa definition uses a question-mark suffix"
fi

if rg -n '(^|[^[:alnum:]_])(sorry|admit|theorem_wanted|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
    "$SEMANTIC_VIEW_FILE" "$LEAN_FILE" "$LEAN_EXPORTER_FILE"; then
  fail "Lean native-source calculus contains an unproved or disallowed shortcut"
fi

if ! git -C "$AIHUB/Mettapedia" diff --check -- \
    MettaKernel/kernel/metamath_native_source_calculus_v0.metta \
    MettaKernel/kernel/metamath_native_source_calculus_v0_suite.metta \
    MettaKernel/kernel/metamath_native_source_calculus_reference_v0.metta \
    MettaKernel/kernel/run_metamath_native_source_calculus_v0_gate.sh \
    lean/mettapedia/Mettapedia/Languages/Metamath/MMLean4SemanticView.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/NativeSourceCalculus.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/NativeSourceCalculusMeTTaExport.lean; then
  fail "source has whitespace errors"
fi

echo "METAMATH NATIVE SOURCE CALCULUS V0 GATE: PASS (checked gparse ledger to source-derived native multi-premise proof; mm-lean4 semantic database matches all 15 source objects; operational output exactly equals the Lean-rendered checked slice; source identity, child order, child cardinality, and source proof order protected)"
