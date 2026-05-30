#!/usr/bin/env bash
set -euo pipefail

POLY=${POLY:-/home/zar/claude/CakeML/polyml-local/bin/poly}
CML_RUNNER=${CML_RUNNER:-./cml/metta_m1_runner.cake}
CURATED_DIR=${CURATED_DIR:-tests/curated}

if [[ ! -x "$CML_RUNNER" ]]; then
  echo "missing executable: $CML_RUNNER" >&2
  exit 1
fi

shopt -s nullglob
tests=("$CURATED_DIR"/*.metta)
shopt -u nullglob

if [[ ${#tests[@]} -eq 0 ]]; then
  echo "no curated tests found in $CURATED_DIR" >&2
  exit 1
fi

failures=0

run_and_diff() {
  local label=$1
  local test_file=$2
  local expected_file=$3
  shift 3

  if diff -u "$expected_file" <("$@") >/dev/null; then
    echo "PASS $label $(basename "$test_file")"
  else
    echo "FAIL $label $(basename "$test_file")" >&2
    diff -u "$expected_file" <("$@") || true
    failures=$((failures + 1))
  fi
}

for test_file in "${tests[@]}"; do
  expected_file=${test_file%.metta}.expected
  if [[ ! -f "$expected_file" ]]; then
    echo "FAIL $(basename "$test_file"): missing expected file $expected_file" >&2
    failures=$((failures + 1))
    continue
  fi

  run_and_diff "sml" "$test_file" "$expected_file" \
    env METTA_FILE="$test_file" "$POLY" --script tests/run_metta_file.sml
  run_and_diff "cml" "$test_file" "$expected_file" \
    "$CML_RUNNER" "$test_file"
done

if [[ $failures -eq 0 ]]; then
  echo "Curated local SML/CakeML tests passed: ${#tests[@]}"
else
  echo "Curated local tests failed: $failures comparisons" >&2
  exit 1
fi
