#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
MM_TEST="$AIHUB/hyperon/metamath/metamath-test"
HOL_SOURCE="$AIHUB/repos/itp-curriculum-sources/nik_metamath_set_mm/hol.mm"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
EXPORTER="Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean"
AUDIT="Mettapedia/Languages/Metamath/InferenceSourceAdmissionAudit.lean"
LOGDIR="$ROOT/parity_logs/canonical_admission"
INCLUDE_DIGEST="e46e11351db773937bfa01845e6e8b6c7403d7cc4fa3b32cc8f5cd0e9c6fd6e1"

mkdir -p "$LOGDIR"

fail() {
  echo "MM CANONICAL ADMISSION GATE: FAIL ($*)"
  exit 1
}

check_source() {
  local label="$1"
  local source="$2"
  local expected_hash="$3"
  local expected_bytes="$4"
  local actual_hash
  local actual_bytes
  actual_hash="$(sha256sum "$source" | awk '{print $1}')"
  actual_bytes="$(wc -c < "$source")"
  [[ "$actual_hash" == "$expected_hash" ]] ||
    fail "$label source hash changed: $actual_hash"
  [[ "$actual_bytes" -eq "$expected_bytes" ]] ||
    fail "$label source byte count changed: $actual_bytes"
}

generate_and_compare() {
  local artifact="$1"
  shift
  local basename
  local fresh
  local export_log
  basename="$(basename "$artifact")"
  fresh="$LOGDIR/${basename%.metta}.fresh.metta"
  export_log="$LOGDIR/${basename%.metta}.export.log"
  if ! (
    cd "$LEAN_ROOT"
    LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" "$@" "$fresh"
  ) >"$export_log" 2>&1; then
    fail "$basename source admission or rendering; log: $export_log"
  fi
  cmp -s "$artifact" "$fresh" ||
    fail "$basename differs from a newly generated artifact: $fresh"
}

run_cetta() {
  local artifact="$1"
  local expected_summary="$2"
  local basename
  local run_log
  basename="$(basename "$artifact")"
  run_log="$LOGDIR/${basename%.metta}.cetta.log"
  if ! (
    cd "$ROOT"
    "$CETTA" "$basename"
  ) >"$run_log" 2>&1; then
    fail "$basename CeTTa process; log: $run_log"
  fi
  if grep -q 'Error\|❌' "$run_log"; then
    fail "$basename emitted an error; log: $run_log"
  fi
  [[ "$(grep -Fxc "$expected_summary" "$run_log")" -eq 1 ]] ||
    fail "$basename exact summary absent or duplicated; log: $run_log"
}

DEMO0="$MM_TEST/demo0.mm"
MIU="$MM_TEST/miu.mm"
PEANO="$MM_TEST/peano-fixed.mm"
INCLUDER="$MM_TEST/demo0-includer.mm"
INCLUDEE="$MM_TEST/demo0-includee.mm"
DV_SOURCE="$ROOT/metamath_dv_fixture_v0.mm"
DV_VIOLATION="$ROOT/metamath_dv_violation_v0.mm"
MALFORMED_INCLUDE="$ROOT/metamath_malformed_include_v0.mm"
REJECTED_SOURCE="$MM_TEST/demo0-bad1.mm"

check_source demo0 "$DEMO0" \
  b68d7488bdbf2d55d1a955f3a6a3efac68ca9e3009d24f867e1a75aacb7b03d3 1353
check_source miu "$MIU" \
  43ead5a0b37e968462cd66331dec324d42959c8f54460eab35cfb869b423d3f2 4649
check_source peano "$PEANO" \
  c5314f062315415f5ad730df00cf74a000c881a11e707cda5dd932e11523e163 27843
check_source includer "$INCLUDER" \
  677f25cc98e63e08f68ad20f0c79f8fe8101029079e03a1ce18d2a1039ee21d3 520
check_source includee "$INCLUDEE" \
  00dc5b1fb7f59cec3a8c8c7b49b11250dd0e96aa34f199cc540d28a484bb8ed0 1145
check_source hol "$HOL_SOURCE" \
  ca967a2d351dd178bc0b85e04fec8279cf2d2d8c48fe17c399a2e79f4b9e21c5 96976
check_source dv "$DV_SOURCE" \
  46bfd4628307e20b9541682265fa7e815404cb362f12311330d43879579879da 532
check_source dv-violation "$DV_VIOLATION" \
  7b6059c5adb7c430fa328c25701f62fdf16d0427685ee0b6c514fa53603f9892 532
check_source malformed-include "$MALFORMED_INCLUDE" \
  01e3c474e8379d63e0dac9734e48f31d6a02ca52b92f42075af63bd7215d8f29 20
check_source rejected "$REJECTED_SOURCE" \
  8f618630b19e1699fea882f691b7506793d1108fb62b9f52f79939323e3784d8 1354

actual_include_digest="$(
  cd "$MM_TEST"
  sha256sum demo0-includer.mm demo0-includee.mm | sha256sum | awk '{print $1}'
)"
[[ "$actual_include_digest" == "$INCLUDE_DIGEST" ]] ||
  fail "include manifest digest changed: $actual_include_digest"

LEAN_AUDIT_FILES=(
  Mettapedia/GSLT/LanguageDef/CheckedSource.lean
  Mettapedia/GSLT/LanguageDef/CheckedInferenceExtraction.lean
  Mettapedia/GSLT/LanguageDef/InferenceMeTTaRender.lean
  Mettapedia/Languages/Metamath/InferenceSourceAdmission.lean
  Mettapedia/Languages/Metamath/InferenceSourceAdmissionAudit.lean
  Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean
  Mettapedia/Languages/Metamath.lean
)
LEAN_BUILD_LOG="$LOGDIR/lean-build.log"
if ! (
  cd "$LEAN_ROOT"
  for source in "${LEAN_AUDIT_FILES[@]}"; do
    LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean "$source"
  done
) >"$LEAN_BUILD_LOG" 2>&1; then
  fail "Lean build; log: $LEAN_BUILD_LOG"
fi

NEGATIVE_LOG="$LOGDIR/negative-audit.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$AUDIT" \
    "$DEMO0" "$REJECTED_SOURCE" "$DV_VIOLATION" "$MALFORMED_INCLUDE"
) >"$NEGATIVE_LOG" 2>&1; then
  fail "adversarial Lean audit; log: $NEGATIVE_LOG"
fi
[[ "$(grep -Fxc 'MMCanonicalAdmissionNegativeSummary 9 9 0' "$NEGATIVE_LOG")" -eq 1 ]] ||
  fail "adversarial Lean audit summary absent or duplicated; log: $NEGATIVE_LOG"

generate_and_compare "$ROOT/metamath_demo0_generated_v0.metta" \
  demo0 "$DEMO0"
generate_and_compare "$ROOT/metamath_miu_theorem1_generated_v1.metta" \
  target "$MIU" theorem1
generate_and_compare "$ROOT/metamath_peano_database_generated_v1.metta" \
  database "$PEANO"
generate_and_compare "$ROOT/metamath_demo0_include_database_generated_v1.metta" \
  database-include "$INCLUDER" "sha256:$INCLUDE_DIGEST"
generate_and_compare "$ROOT/metamath_dv_source_generated_v1.metta" \
  target "$DV_SOURCE" th

HOL_LABELS=(idi idt syl jca syl2anc syldan)
HOL_ACTIONS=(1 1 6 6 13 30)
HOL_SAVES=(0 0 0 0 0 2)
HOL_SAVED_REFERENCES=(0 0 0 0 0 2)
for index in "${!HOL_LABELS[@]}"; do
  label="${HOL_LABELS[$index]}"
  generate_and_compare "$ROOT/holmm_${label}_generated_v0.metta" \
    target "$HOL_SOURCE" "$label"
done
generate_and_compare "$ROOT/holmm_tru_generated_v0.metta" \
  hol-tru "$HOL_SOURCE"
generate_and_compare "$ROOT/holmm_syldan_dag_generated_v0.metta" \
  target-dag "$HOL_SOURCE" syldan

CANONICAL_ARTIFACTS=(
  "$ROOT/metamath_demo0_generated_v0.metta"
  "$ROOT/metamath_miu_theorem1_generated_v1.metta"
  "$ROOT/metamath_peano_database_generated_v1.metta"
  "$ROOT/metamath_demo0_include_database_generated_v1.metta"
  "$ROOT/metamath_dv_source_generated_v1.metta"
  "$ROOT/holmm_idi_generated_v0.metta"
  "$ROOT/holmm_idt_generated_v0.metta"
  "$ROOT/holmm_syl_generated_v0.metta"
  "$ROOT/holmm_jca_generated_v0.metta"
  "$ROOT/holmm_syl2anc_generated_v0.metta"
  "$ROOT/holmm_syldan_generated_v0.metta"
  "$ROOT/holmm_tru_generated_v0.metta"
  "$ROOT/holmm_syldan_dag_generated_v0.metta"
)
for artifact in "${CANONICAL_ARTIFACTS[@]}"; do
  grep -Fq '(GSLTSourceV1 ' "$artifact" ||
    fail "$(basename "$artifact") lacks GSLTSourceV1"
  grep -Fq 'gslt-source-' "$artifact" ||
    fail "$(basename "$artifact") lacks a source-indexed operation"
  if grep -Eq '\(gic-check(-batch)? ' "$artifact"; then
    fail "$(basename "$artifact") invokes the raw checker directly"
  fi
done

THEOREM_ARTIFACTS=(
  "$ROOT/metamath_demo0_generated_v0.metta"
  "$ROOT/metamath_miu_theorem1_generated_v1.metta"
  "$ROOT/metamath_dv_source_generated_v1.metta"
  "$ROOT/holmm_idi_generated_v0.metta"
  "$ROOT/holmm_idt_generated_v0.metta"
  "$ROOT/holmm_syl_generated_v0.metta"
  "$ROOT/holmm_jca_generated_v0.metta"
  "$ROOT/holmm_syl2anc_generated_v0.metta"
  "$ROOT/holmm_syldan_generated_v0.metta"
)
for artifact in "${THEOREM_ARTIFACTS[@]}"; do
  grep -Fq 'wrong-goal' "$artifact" ||
    fail "$(basename "$artifact") lacks the wrong-goal negative"
  if ! grep -Eq 'missing-child|wrong-child-count' "$artifact"; then
    fail "$(basename "$artifact") lacks the missing-child negative"
  fi
done

grep -Fq '(GRuleInst "$mm.dv-lists.cons"' "$ROOT/metamath_dv_source_generated_v1.metta" ||
  fail "DV source proof lacks generated DV-list evidence"
grep -Fq '(GRuleInst "$mm.all-pairs.cons"' "$ROOT/metamath_dv_source_generated_v1.metta" ||
  fail "DV source proof lacks generated pairwise-DV evidence"
grep -Fq 'mm-lean4-sound-default/include-aware/inference-projection-v1' \
  "$ROOT/metamath_demo0_include_database_generated_v1.metta" ||
  fail "include artifact lacks the include-aware source profile"
grep -Fq "sha256:$INCLUDE_DIGEST" \
  "$ROOT/metamath_demo0_include_database_generated_v1.metta" ||
  fail "include artifact lacks the verified manifest digest"

CANONICAL_LEAN_FILES=(
  "$LEAN_ROOT/Mettapedia/Languages/Metamath/InferenceSourceAdmission.lean"
  "$LEAN_ROOT/Mettapedia/Languages/Metamath/InferenceSourceAdmissionAudit.lean"
  "$LEAN_ROOT/Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean"
  "$LEAN_ROOT/Mettapedia/Languages/Metamath.lean"
  "$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/InferenceMeTTaRender.lean"
  "$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/CheckedSource.lean"
  "$LEAN_ROOT/Mettapedia/GSLT/LanguageDef/CheckedInferenceExtraction.lean"
)
if rg -n 'authoredProof|check_sig|kernel_binding_waist|noDVProof|renderDVFixture|InferenceProjectionDVFixture|MMGICSummary|generic_inference_checker_v0' \
    "${CANONICAL_LEAN_FILES[@]}" "$ROOT/run_metamath_dv_gic_gate.sh"; then
  fail "canonical path still references a hand adapter or fallback"
fi
if rg -n 'metamath_dv_generated_v0' "$ROOT" --glob '*.sh' \
    --glob '!run_metamath_canonical_admission_gate.sh'; then
  fail "an active gate still references the superseded raw DV artifact"
fi
if rg -n 'target-trace|holmm_syldan_trace_generated_v0' \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean" \
    "$ROOT" --glob '*.sh' --glob '!run_metamath_canonical_admission_gate.sh'; then
  fail "an active path still references the rejected experimental trace exporter"
fi
if rg -n '\bsorry\b|_wanted\b|\bnative_decide\b' "${CANONICAL_LEAN_FILES[@]}"; then
  fail "canonical Lean path contains an unproved or disallowed proof shortcut"
fi
if rg -n '^\s*\(=\s+\([^()[:space:]]+\?' "$AIHUB/Mettapedia/MettaKernel" \
    --glob '*.metta' --glob '!kernel/parity_logs/**'; then
  fail "MeTTa definition uses a question-mark suffix"
fi

if [[ -n "$(git -C "$AIHUB/Mettapedia/lean/externals/mm-lean4" status --porcelain)" ]]; then
  fail "the mm-lean4 dependency was modified"
fi
if ! git -C "$AIHUB/Mettapedia" diff --check -- \
    lean/mettapedia/Mettapedia/Languages/Metamath/InferenceSourceAdmission.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/InferenceSourceAdmissionAudit.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath.lean \
    lean/mettapedia/Mettapedia/GSLT/LanguageDef/InferenceMeTTaRender.lean \
    lean/mettapedia/Mettapedia/GSLT/LanguageDef/CheckedSource.lean \
    lean/mettapedia/Mettapedia/GSLT/LanguageDef/CheckedInferenceExtraction.lean; then
  fail "tracked canonical source has whitespace errors"
fi
if rg -n '[[:blank:]]+$' "${CANONICAL_LEAN_FILES[@]}" \
    "$ROOT/gslt_checked_source_v1.metta" "$ROOT/run_metamath_canonical_admission_gate.sh"; then
  fail "canonical source has trailing whitespace"
fi

SOURCE_SUITE_LOG="$LOGDIR/source-suite.log"
if ! "$ROOT/run_gslt_checked_source_v1_gate.sh" >"$SOURCE_SUITE_LOG" 2>&1; then
  fail "GSLT source-indexed checker suite; log: $SOURCE_SUITE_LOG"
fi
grep -Fq 'PASS (24/24 assertions; 0 failures)' "$SOURCE_SUITE_LOG" ||
  fail "GSLT source-indexed checker summary absent; log: $SOURCE_SUITE_LOG"

run_cetta "$ROOT/metamath_demo0_generated_v0.metta" \
  '[(MMDEMO0Summary 1353 34 6 6 0)]'
run_cetta "$ROOT/metamath_miu_theorem1_generated_v1.metta" \
  '[(MMTARGETSummary "theorem1" 4649 33 6 6 0)]'
run_cetta "$ROOT/metamath_peano_database_generated_v1.metta" \
  '[(MMDatabaseSummary "exact-bytes" 27843 88 1 1 0)]'
run_cetta "$ROOT/metamath_demo0_include_database_generated_v1.metta" \
  '[(MMDatabaseSummary "include-aware" 520 35 1 1 0)]'
run_cetta "$ROOT/metamath_dv_source_generated_v1.metta" \
  '[(MMTARGETSummary "th" 532 4 6 6 0)]'

for index in "${!HOL_LABELS[@]}"; do
  label="${HOL_LABELS[$index]}"
  actions="${HOL_ACTIONS[$index]}"
  saves="${HOL_SAVES[$index]}"
  saved_references="${HOL_SAVED_REFERENCES[$index]}"
  run_cetta "$ROOT/holmm_${label}_generated_v0.metta" \
    "[(MMTARGETSummary \"$label\" 96976 $actions 6 6 0)]"
  hol_log="$LOGDIR/holmm_${label}_generated_v0.cetta.log"
  expected_stats="[(MMTARGETCompressedStats \"$label\" $saves $saved_references)]"
  [[ "$(grep -Fxc "$expected_stats" "$hol_log")" -eq 1 ]] ||
    fail "holmm_${label}_generated_v0.metta compressed statistics absent or duplicated"
done
run_cetta "$ROOT/holmm_tru_generated_v0.metta" \
  '[(MMHOLTRUSummary 96976 3 5 5 0)]'
run_cetta "$ROOT/holmm_syldan_dag_generated_v0.metta" \
  '[(MMTARGETDAGSummary "syldan" 96976 30 153 2 2 3 3 0)]'
echo "MM CANONICAL ADMISSION GATE: PASS (5 required corpora; generated DV evidence; 9/9 adversarial negatives; 13 current artifacts; Lean and CeTTa agree)"
