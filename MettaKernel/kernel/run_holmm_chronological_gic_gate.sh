#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/Languages/Metamath/InferenceMeTTaExport.lean"
SOURCE="$AIHUB/repos/itp-curriculum-sources/nik_metamath_set_mm/hol.mm"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
LOGDIR="$ROOT/parity_logs"
EXPECTED_SHA256="ca967a2d351dd178bc0b85e04fec8279cf2d2d8c48fe17c399a2e79f4b9e21c5"
EXPECTED_BYTES=96976
LABELS=(idi idt syl jca syl2anc syldan)
EXPECTED_ACTIONS=(1 1 6 6 13 30)
EXPECTED_SAVES=(0 0 0 0 0 2)
EXPECTED_SAVED_REFERENCES=(0 0 0 0 0 2)

mkdir -p "$LOGDIR"

actual_sha256="$(sha256sum "$SOURCE" | awk '{print $1}')"
if [[ "$actual_sha256" != "$EXPECTED_SHA256" ]]; then
  echo "HOL.MM CHRONO GATE: FAIL (source hash changed: $actual_sha256)"
  exit 1
fi

if [[ "$(wc -c < "$SOURCE")" -ne "$EXPECTED_BYTES" ]]; then
  echo "HOL.MM CHRONO GATE: FAIL (source byte count changed)"
  exit 1
fi

for index in "${!LABELS[@]}"; do
  label="${LABELS[$index]}"
  expected_actions="${EXPECTED_ACTIONS[$index]}"
  expected_saves="${EXPECTED_SAVES[$index]}"
  expected_saved_references="${EXPECTED_SAVED_REFERENCES[$index]}"
  artifact="$ROOT/holmm_${label}_generated_v0.metta"
  fresh="$LOGDIR/holmm_${label}_generated_v0.fresh.metta"
  export_log="$LOGDIR/holmm_${label}_export.log"
  run_log="$LOGDIR/holmm_${label}_gic.log"

  if ! (
    cd "$LEAN_ROOT"
    LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$EXPORTER" \
      target "$SOURCE" "$label" "$fresh"
  ) >"$export_log" 2>&1; then
    echo "HOL.MM CHRONO GATE: FAIL ($label extraction/lowering; log: $export_log)"
    exit 1
  fi

  if ! cmp -s "$artifact" "$fresh"; then
    echo "HOL.MM CHRONO GATE: FAIL ($label artifact stale; fresh: $fresh)"
    exit 1
  fi

  if [[ "$(grep -c '^!(assertEqual' "$artifact")" -ne 1 ]]; then
    echo "HOL.MM CHRONO GATE: FAIL ($label must contain one batch assertion)"
    exit 1
  fi

  if ! (
    cd "$ROOT"
    "$CETTA" "$(basename "$artifact")"
  ) >"$run_log" 2>&1; then
    echo "HOL.MM CHRONO GATE: FAIL ($label CeTTa process; log: $run_log)"
    exit 1
  fi

  if grep -q 'Error\|❌' "$run_log"; then
    echo "HOL.MM CHRONO GATE: FAIL ($label checker assertion; log: $run_log)"
    exit 1
  fi

  expected_summary="[(MMTARGETSummary \"$label\" $EXPECTED_BYTES $expected_actions 6 6 0)]"
  if [[ "$(grep -Fxc "$expected_summary" "$run_log")" -ne 1 ]]; then
    echo "HOL.MM CHRONO GATE: FAIL ($label exact summary absent or duplicated)"
    exit 1
  fi

  expected_compressed_stats="[(MMTARGETCompressedStats \"$label\" $expected_saves $expected_saved_references)]"
  if [[ "$(grep -Fxc "$expected_compressed_stats" "$run_log")" -ne 1 ]]; then
    echo "HOL.MM CHRONO GATE: FAIL ($label compressed stats absent or duplicated)"
    exit 1
  fi
done

echo "HOL.MM CHRONO GATE: PASS (first 6 selected theorems; 57 expanded actions; 2 saves/2 saved references; 36/36 gates; 0 failures)"
