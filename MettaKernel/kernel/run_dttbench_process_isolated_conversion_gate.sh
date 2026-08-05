#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/GSLT/LanguageDef/LF/DTTBenchProofCarryingDAGMeTTaExport.lean"
MODULE="Mettapedia.GSLT.LanguageDef.LF.DTTBenchProofCarryingDAGMeTTaExport"
CETTA="${CETTA:-$AIHUB/hyperon/CeTTa/cetta}"
SHARDS="$ROOT/dttbench_proof_carrying_conversion_dag_shards_v0"
LOGDIR="$ROOT/parity_logs/dttbench_process_isolated_gate_v0"
FRESH_SHARDS="$LOGDIR/fresh_shards"
FRESH_PROCESS_ROOT="$LOGDIR/fresh_process64_bundles_v1"
PROCESS_RUN_ROOT="$LOGDIR/process64_entry_runs_v1"
MUTATED_PROCESS="$LOGDIR/mutated_process64_bundle_28_v1"
MUTATED_RUN="$LOGDIR/mutated_process64_entry_28_runs_v1"
EXPECTED_ENTRIES=31
PROCESS_ENTRIES=(16 17 18 19 20 21 22 23 24 25 26 27 28)
MUTATION_ENTRY=28

mkdir -p \
  "$LOGDIR" \
  "$FRESH_SHARDS" \
  "$FRESH_PROCESS_ROOT" \
  "$PROCESS_RUN_ROOT" \
  "$MUTATED_PROCESS" \
  "$MUTATED_RUN"

is_process_entry() {
  local candidate="$1"
  local process_entry
  for process_entry in "${PROCESS_ENTRIES[@]}"; do
    if [[ "$candidate" -eq "$process_entry" ]]; then
      return 0
    fi
  done
  return 1
}

process_bundle() {
  local process_entry="$1"
  printf '%s/parity_logs/dttbench_pure_process64_bundle_%d_v1' \
    "$ROOT" "$process_entry"
}

fresh_process_bundle() {
  local process_entry="$1"
  printf '%s/entry_%d' "$FRESH_PROCESS_ROOT" "$process_entry"
}

process_run_directory() {
  local process_entry="$1"
  printf '%s/entry_%d' "$PROCESS_RUN_ROOT" "$process_entry"
}

if ! (
  cd "$LEAN_ROOT"
  lake build "$MODULE"
) >"$LOGDIR/exporter_build.log" 2>&1; then
  echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (Lean build)"
  exit 1
fi

if ! (
  cd "$LEAN_ROOT"
  lake env lean --run "$EXPORTER" \
    --shard-directory "$FRESH_SHARDS"
) >"$LOGDIR/shard_export.log" 2>&1; then
  echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (shard export)"
  exit 1
fi

for process_entry in "${PROCESS_ENTRIES[@]}"; do
  fresh_process="$(fresh_process_bundle "$process_entry")"
  mkdir -p "$fresh_process"
  if ! (
    cd "$LEAN_ROOT"
    lake env lean --run "$EXPORTER" \
      --process-entry-directory "$process_entry" "$fresh_process"
  ) >"$LOGDIR/process_export_${process_entry}.log" 2>&1; then
    echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (entry $process_entry process export)"
    exit 1
  fi
done

shopt -s nullglob
checked_shards=(
  "$SHARDS"/dttbench_proof_carrying_conversion_dag_shard_*_generated_v0.metta
)
fresh_shards=(
  "$FRESH_SHARDS"/dttbench_proof_carrying_conversion_dag_shard_*_generated_v0.metta
)
if [[ "${#checked_shards[@]}" -ne "$EXPECTED_ENTRIES" ||
      "${#fresh_shards[@]}" -ne "$EXPECTED_ENTRIES" ]]; then
  echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (shard cardinality)"
  exit 1
fi

for checked in "${checked_shards[@]}"; do
  fresh="$FRESH_SHARDS/$(basename "$checked")"
  if ! cmp -s "$checked" "$fresh"; then
    echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (stale shard: $(basename "$checked"))"
    exit 1
  fi
done

for process_entry in "${PROCESS_ENTRIES[@]}"; do
  process_bundle_path="$(process_bundle "$process_entry")"
  fresh_process_path="$(fresh_process_bundle "$process_entry")"
  checked_process=(
    "$process_bundle_path"/manifest.tsv
    "$process_bundle_path"/common.metta
    "$process_bundle_path"/final.template.metta
    "$process_bundle_path"/term_chunk_*.template.metta
    "$process_bundle_path"/type_chunk_*.template.metta
  )
  fresh_process=(
    "$fresh_process_path"/manifest.tsv
    "$fresh_process_path"/common.metta
    "$fresh_process_path"/final.template.metta
    "$fresh_process_path"/term_chunk_*.template.metta
    "$fresh_process_path"/type_chunk_*.template.metta
  )
  if [[ "${#checked_process[@]}" -ne "${#fresh_process[@]}" ]]; then
    echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (entry $process_entry process-bundle cardinality)"
    exit 1
  fi
  for checked in "${checked_process[@]}"; do
    fresh="$fresh_process_path/$(basename "$checked")"
    if ! cmp -s "$checked" "$fresh"; then
      echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (entry $process_entry stale process file: $(basename "$checked"))"
      exit 1
    fi
  done
done

passed=0
for index in $(seq 0 30); do
  if is_process_entry "$index"; then
    continue
  fi
  printf -v suffix "%02d" "$index"
  shard="$SHARDS/dttbench_proof_carrying_conversion_dag_shard_${suffix}_generated_v0.metta"
  log="$LOGDIR/shard_${suffix}.log"
  if ! (
    cd "$SHARDS"
    "$CETTA" --quiet --import-mode ancestor-walk "$(basename "$shard")"
  ) >"$log" 2>&1; then
    echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (entry $index process)"
    exit 1
  fi
  if grep -q 'Error\|❌' "$log"; then
    echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (entry $index assertion)"
    exit 1
  fi
  expected="[(DTTBenchProofCarryingConversionDAGShardLiveSummary $index 1 1 0)]"
  if [[ "$(grep -Fxc "$expected" "$log")" -ne 1 ]]; then
    echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (entry $index summary)"
    exit 1
  fi
  passed=$((passed + 1))
done

for process_entry in "${PROCESS_ENTRIES[@]}"; do
  process_bundle_path="$(process_bundle "$process_entry")"
  process_run_path="$(process_run_directory "$process_entry")"
  mkdir -p "$process_run_path"
  if ! python3 "$ROOT/run_pure_streaming_process_bundle.py" \
      "$process_bundle_path" \
      --cetta "$CETTA" \
      --run-directory "$process_run_path" \
      >"$LOGDIR/process_entry_${process_entry}.log" 2>&1; then
    echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (entry $process_entry process chain)"
    exit 1
  fi
  passed=$((passed + 1))
done

mutation_bundle="$(process_bundle "$MUTATION_ENTRY")"
python3 "$ROOT/mutate_dttbench_pure_process_bundle.py" \
  "$mutation_bundle" "$MUTATED_PROCESS"
if python3 "$ROOT/run_pure_streaming_process_bundle.py" \
    "$MUTATED_PROCESS" \
    --cetta "$CETTA" \
    --run-directory "$MUTATED_RUN" \
    >"$LOGDIR/mutated_process_entry_28.log" 2>&1; then
  echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (mutation escaped)"
  exit 1
fi
if ! grep -q 'checker reported failure\|CeTTa exited' \
    "$LOGDIR/mutated_process_entry_28.log"; then
  echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (mutation failure was not checker-bound)"
  exit 1
fi

if [[ "$passed" -ne "$EXPECTED_ENTRIES" ]]; then
  echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: FAIL (only $passed entries passed)"
  exit 1
fi

cetta_sha256="$(sha256sum "$CETTA" | cut -d' ' -f1)"
process_entries_csv="$(IFS=,; printf '%s' "${PROCESS_ENTRIES[*]}")"
{
  printf 'schema\tdttbench-process-isolated-conversion-gate-v3\n'
  printf 'entries\t%d\n' "$passed"
  printf 'process_isolated_entries\t%s\n' "$process_entries_csv"
  printf 'conversion_mutation\tCAUGHT\n'
  printf 'cetta_sha256\t%s\n' "$cetta_sha256"
  printf 'status\tPASS\n'
} >"$LOGDIR/summary.tsv"

echo "DTTBENCH PROCESS-ISOLATED CONVERSION GATE: PASS (31/31 source-bound indexed-LF conversions; entries 16-28 bounded across processes; conversion mutation caught)"
